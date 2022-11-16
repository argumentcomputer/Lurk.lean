import Lurk.Syntax.AST
import Lurk.Syntax.DSL

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

open Lurk.Syntax.DSL

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

def mkIfElses (ifThens : List (AST × AST)) (finalElse : AST := .nil) : AST :=
  match ifThens with
  | [] => .nil
  | [(cond, body)] => ⟦(if $cond $body $finalElse)⟧
  | (cond, body) :: es => ⟦(if $cond $body $(mkIfElses es finalElse))⟧

/--
Transforms a list of named expressions that were mutually defined into a
"switch" function `S` and a set of projections (named after the original names)
that call `S` with their respective indices.

Important: the resulting expressions must be bound in a `letrec`.
-/
def mkMutualBlock : List (String × AST) → Except String (List $ String × AST)
  | [] => throw "can't make a mutual block with an empty list of binders"
  | x@([_]) => return x
  | mutuals => do
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (fun acc n => s!"{acc}.{n}") "__mutual__"
    let fnProjs := names.enum.map fun (i, n) => (n, ~[.sym mutualName, .num i])
    let map := fnProjs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let ifThens ← mutuals.enum.mapM
      fun (i, _, e) => do pure (⟦(= mutidx $i)⟧, ← replaceFreeVars map e)
    let mutualBlock := mkIfElses ifThens
    return (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs

end Lurk.Syntax.AST
