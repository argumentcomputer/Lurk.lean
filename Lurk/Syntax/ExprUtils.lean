import Lurk.Syntax.AST
import Lurk.Syntax.DSL
import Lurk.Syntax.StringSucc

namespace Lurk.Syntax.AST

def mkLambda (args : List String) (body : AST) : AST :=
  ~[sym "LAMBDA", consWith (args.map sym) nil, body]

def mkBindings (binders : List $ String × AST) : AST :=
  consWith (binders.map fun (s, v) => ~[sym s, v]) nil

def mkBlock (kind : String) (binders : List $ String × AST) (body : AST) : AST :=
  ~[sym kind, mkBindings binders, body]

def mkLet (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LET" binders body

def mkLetrec (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LETREC" binders body

def asArgs : AST → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

def asBindings : AST → Except String (List (String × AST))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

/-- Given a list of ASTs `xs := [x₁, x₂, ..]` and `tail`, 
  create the explicit list `(cons x₁ (cons x₂ (cons .. tail)))`.
  Note that this is *different* from creating the literal list
  `(x₁ x₂ .. . tail)` -/
def mkConsListWith (xs : List AST) (tail : AST) : AST :=
  xs.foldr (init := tail) fun x acc => ~[.sym "CONS", x, acc]

/-- Given a list of ASTs `xs := [x₁, x₂, ..]`, 
  create the explicit list `(cons x₁ (cons x₂ (cons .. nil)))`.
  Note that this is *different* from creating the literal list
  `(x₁ x₂ ..)` -/
def mkConsList (xs : List AST) : AST :=
  mkConsListWith xs (.sym "NIL")

partial def getFreeVars (bVars acc : Std.RBSet String compare := default) :
    AST → Except String (Std.RBSet String compare)
  | .sym s =>
    return if bVars.contains s || reservedSyms.contains s then acc else acc.insert s
  | ~[.sym "LAMBDA", as, b] => do
    let bVars := (← as.asArgs).foldl (init := bVars) fun acc a => acc.insert a
    b.getFreeVars bVars acc
  | ~[.sym "LET", bs, b] => do
    let (bindersNames, bindersFreeVars) ← (← bs.asBindings).foldlM
      (init := default)
      fun (prevBinders, fVars) (s, v) =>
        return (
          prevBinders.insert s,
          fVars.union $ ← v.getFreeVars (bVars.union prevBinders) acc)
    b.getFreeVars (bVars.union bindersNames) (acc.union bindersFreeVars)
  | ~[.sym "LETREC", bs, b] => do
    let (bindersNames, bindersFreeVars) ← (← bs.asBindings).foldlM
      (init := default)
      fun (prevBinders, fVars) (s, v) =>
        let allBinders := prevBinders.insert s -- s is a bound variable in v
        return (
          allBinders,
          fVars.union $ ← v.getFreeVars (bVars.union allBinders) acc)
    b.getFreeVars (bVars.union bindersNames) (acc.union bindersFreeVars)
  | .cons x y => return (← x.getFreeVars bVars acc).union $ ← y.getFreeVars bVars acc
  | _ => return acc

def containsCurrentEnv : AST → Bool
  | .sym "CURRENT-ENV" => true
  | .cons x y => x.containsCurrentEnv || y.containsCurrentEnv
  | _ => false

/-- Eagerly remove unecessary binders from `let` and `letrec` blocks. -/
partial def pruneBlocks : AST → Except String AST
  | x@~[.sym "LET", bs, b] =>
    if b.containsCurrentEnv then pure x else do
      let newBinders ← (← bs.asBindings).foldrM
        (init := (default, ← b.getFreeVars))
        fun (s, v) (accBinders, accFVars) =>
          if accFVars.contains s || reservedSyms.contains s then
            return (
              (s, ← v.pruneBlocks) :: accBinders,
              accFVars.union $ ← v.getFreeVars)
          else return (accBinders, accFVars) -- drop binder
      return mkLet newBinders.1 (← b.pruneBlocks)
  | x@~[.sym "LETREC", bs, b] =>
    if b.containsCurrentEnv then pure x else do
      let newBinders ← (← bs.asBindings).foldrM
        (init := (default, ← b.getFreeVars))
        fun (s, v) (accBinders, accFVars) =>
          if accFVars.contains s || reservedSyms.contains s then
            return (
              (s, ← v.pruneBlocks) :: accBinders,
              accFVars.union $ ← v.getFreeVars (.single s)) -- s is not free in v
          else return (accBinders, accFVars) -- drop binder
      return mkLetrec newBinders.1 (← b.pruneBlocks)
  | .cons x y => return .cons (← x.pruneBlocks) (← y.pruneBlocks)
  | x => pure x

mutual

partial def replaceBindersFreeVars
  (map : Std.RBMap String AST compare)
  (bindings : List $ String × AST)
  (rec : Bool) :
    Except String (List $ String × AST) := do
  let mut ret := #[]
  -- `map'` will keep track of the free vars that will be replaced if found.
  let mut map' := map
  -- as we iterate on binders, occurrences of what looked like a free variable
  -- gradually turn into bound variables with local semantics. we erase them
  -- from `map'` because we don't want to replace them
  for (n, e) in bindings do
    if rec then
      -- an occurrence of `n` in `e` can be a recursion, so we can't replace it
      -- right away
      map' := map'.erase n
      ret := ret.push (n, ← replaceFreeVars map' e)
    else
      -- any occurrence of `n` in `e` is definitely a free variable, so we first
      -- try to replace it
      ret := ret.push (n, ← replaceFreeVars map' e)
      map' := map'.erase n
  return ret.data

partial def replaceFreeVars (map : Std.RBMap String AST compare) :
    AST → Except String AST
  | x@(num _)
  | x@(char _)
  | x@(str _) => return x
  | sym s =>
    return if reservedSyms.contains s then sym s else match map.find? s with
      | some x => x
      | none => sym s
  | ~[sym "LAMBDA", as, b] => do
    let b ← b.replaceFreeVars (map.filterOut (.ofList (← asArgs as) _))
    return ~[sym "LAMBDA", as, b]
  | ~[sym "LET", bs, b] => do
    let bs ← asBindings bs
    let map' := map.filterOut $ .ofList (bs.map Prod.fst) _
    let bs := mkBindings $ ← replaceBindersFreeVars map bs false
    let b ← replaceFreeVars map' b
    return ~[sym "LET", bs, b]
  | ~[sym "LETREC", bs, b] => do
    let bs ← asBindings bs
    let map' := map.filterOut $ .ofList (bs.map Prod.fst) _
    let bs := mkBindings $ ← replaceBindersFreeVars map bs true
    let b ← replaceFreeVars map' b
    return ~[sym "LETREC", bs, b]
  | cons a b => return cons (← a.replaceFreeVars map) (← b.replaceFreeVars map)

end

open Lurk.Syntax.DSL

def mkIfElses (ifThens : List (AST × AST)) (finalElse : AST := .nil) : AST :=
  match ifThens with
  | [] => .nil
  | [(cond, body)] => ⟦(if $cond $body $finalElse)⟧
  | (cond, body) :: es => ⟦(if $cond $body $(mkIfElses es finalElse))⟧

/--
Transforms a list of named expressions that were mutually defined into a
"switch" function `S` and a set of projections (named after the original names)
that call `S` with their respective indices.

For example, suppose we have two binders `(a (+ a 1))` and `(b (+ b 2))`.
Calling `mkMutualBlock` on them will generate the binders:

1. (mut_a_b (LAMBDA (key)
    (IF (= key 0)
      (+ (mut_a_b 0) 1)
      (IF (= key 1)
        (+ (mut_a_b 1) 2)
        NIL))))
2. (a (mut_a_b 0))
3. (b (mut_a_b 1))

Important: the resulting binders must be in a `letrec` block.
-/
def mkMutualBlock
  (binders : List $ String × AST)
  (init := "mut")
  (merge : String → String → String := fun acc n => s!"{acc}_{n}")
  (key := "key") :
    Except String (List $ String × AST) :=
  match binders with
  | x@([ ])
  | x@([_]) => return x
  | _ => do
    let names := binders.map Prod.fst
    let mutualName := names.foldl merge init
    let projs := names.enum.map fun (i, n) => (n, ~[.sym mutualName, .num i])
    let map := projs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let key := AST.sym key
    let ifThens ← binders.enum.mapM
      fun (i, (_, e)) => do pure (⟦(= $key $i)⟧, ← replaceFreeVars map e)
    let mutualBlock := mkIfElses ifThens
    return (mutualName, ⟦(lambda ($key) $mutualBlock)⟧) :: projs

namespace Anon

structure AnonCtx where
  highest : String
  map : Std.RBMap String String compare
  deriving Inhabited

def AnonCtx.next (ctx : AnonCtx) (k : String) : String × AnonCtx :=
  if reservedSyms.contains k then (k, ctx)
  else
    let v := ctx.highest.succ
    -- avoiding a clash with a reserved symbol
    let v := if reservedSyms.contains v then v.succ else v
    (v, ⟨v, ctx.map.insert k v⟩)

def AnonCtx.update (ctx : AnonCtx) (k v : String) : AnonCtx :=
  if ctx.highest.lt v then ⟨v, ctx.map.insert k v⟩
  else { ctx with map := ctx.map.insert k v }

end Anon

open Anon in
/--
Anonymizes variable names with incrementing strings whose most significant
characters are on the left. This function is meant to generate Lurk code that
can be hashed more efficiently, with symbol names that share maximized tails.
-/
partial def anon (x : AST) : Except String AST :=
  let rec aux (ctx : AnonCtx) : AST → Except String (AST × AnonCtx)
    | sym s => if reservedSyms.contains s then return (sym s, ctx) else
      match ctx.map.find? s with
      | some s => return (sym s, ctx)
      | none => let (next, ctx) := ctx.next s; return (sym next, ctx)
    | x@~[sym "QUOTE", _] => return (x, ctx)
    | x@~[sym "LAMBDA", as, b] =>
      if b.containsCurrentEnv then return (x, ctx) else do
        let as ← as.asArgs
        let (as, ctx) := as.foldl (init := (#[], ctx))
          fun (as, ctx) s =>
            let (curr, ctx) := ctx.next s
            (as.push curr, ctx.update s curr)
        let (b, ctx) ← aux ctx b
        return (mkLambda as.data b, ctx)
    | x@~[sym "LET", bs, b] =>
      if b.containsCurrentEnv then return (x, ctx) else do
        let bs ← bs.asBindings
        let (bs, ctx) ← bs.foldlM (init := (#[], ctx))
          fun (bs, ctx) (s, v) => do
            let (curr, ctx) := ctx.next s
            let (v, ctx) ← aux ctx v
            let ctx := ctx.update s curr
            pure (bs.push (curr, v), ctx)
        let (b, ctx) ← aux ctx b
        return (mkLet bs.data b, ctx)
    | x@~[sym "LETREC", bs, b] =>
      if b.containsCurrentEnv then return (x, ctx) else do
        let bs ← bs.asBindings
        let (bs, ctx) ← bs.foldlM (init := (#[], ctx))
          fun (bs, ctx) (s, v) => do
            let (curr, ctx) := ctx.next s
            let ctx := ctx.update s curr
            let (v, ctx) ← aux ctx v
            pure (bs.push (curr, v), ctx)
        let (b, ctx) ← aux ctx b
        return (mkLetrec bs.data b, ctx)
    | cons x y => do
      let (x, ctx) ← aux ctx x
      let (y, ctx) ← aux ctx y
      return (cons x y, ctx)
    | x => pure (x, ctx)
  aux default x |>.map Prod.fst

end Lurk.Syntax.AST
