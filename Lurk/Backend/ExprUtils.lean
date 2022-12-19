import Lurk.Backend.Expr
import Lurk.Backend.StringSucc
import Std.Data.RBMap

namespace Lurk.Backend.Expr

def mkLambda (args : List String) (body : Expr) : Expr :=
  args.foldr (init := body) fun s acc => .lambda s acc

def mkLet (binders : List $ String × Expr) (body : Expr) : Expr :=
  binders.foldr (init := body) fun (s, v) acc => .let s v acc

def mkLetrec (binders : List $ String × Expr) (body : Expr) : Expr :=
  binders.foldr (init := body) fun (s, v) acc => .letrec s v acc

/--
Given a list of Exprs `xs := [x₁, x₂, ..]` and `tail`, create the explicit list
`(cons x₁ (cons x₂ (cons .. tail)))`. Note that this is *different* from
creating the literal list `(x₁ x₂ .. . tail)` -/
def mkConsListWith (xs : List Expr) (tail : Expr := .atom .nil) : Expr :=
  xs.foldr (init := tail) fun x acc => .op₂ .cons x acc

def getFreeVars (bVars acc : Std.RBSet String compare := default) :
    Expr → Std.RBSet String compare
  | .atom _ | .env | .quote _ => acc
  | .sym s => if bVars.contains s then acc else acc.insert s
  | .op₁ _ e => e.getFreeVars bVars acc
  | .op₂ _ e₁ e₂ => e₂.getFreeVars bVars (e₁.getFreeVars bVars acc)
  | .begin e₁ e₂ => e₂.getFreeVars bVars (e₁.getFreeVars bVars acc)
  | .if a b c =>
    c.getFreeVars bVars (b.getFreeVars bVars (a.getFreeVars bVars acc))
  | .app₀ e => e.getFreeVars bVars acc
  | .app e₁ e₂ => e₂.getFreeVars bVars (e₁.getFreeVars bVars acc)
  | .lambda s b => b.getFreeVars (bVars.insert s) acc
  | .let s v b => b.getFreeVars (bVars.insert s) (v.getFreeVars bVars acc)
  | .letrec s v b =>
    let bVars := bVars.insert s; b.getFreeVars bVars (v.getFreeVars bVars acc)

def containsCurrentEnv : Expr → Bool
  | .env => true
  | .op₁ _    e
  | .app₀     e
  | .lambda _ e => e.containsCurrentEnv
  | .op₂ _    e₁ e₂
  | .begin    e₁ e₂
  | .app      e₁ e₂
  | .let _    e₁ e₂
  | .letrec _ e₁ e₂ => e₁.containsCurrentEnv || e₂.containsCurrentEnv
  | .if       e₁ e₂ e₃ =>
    e₁.containsCurrentEnv || e₂.containsCurrentEnv || e₃.containsCurrentEnv
  | _ => false

/-- Eagerly remove unnecessary binders from `let` and `letrec` blocks. -/
partial def pruneBlocks (letAtoms : Std.RBMap String Expr compare := default) : Expr → Expr
  | x@(.letrec s v b)
  | x@(.let s v b) =>
    let letrec := x matches .letrec _ _ _
    let (bs, b) := b.telescopeLet #[(s, v)]
    if b.containsCurrentEnv then x else
    -- remove unused binders
    let (bs, _) := bs.foldr (init := (default, b.getFreeVars))
      fun (s, v) (accBinders, accFVars) =>
        if accFVars.contains s then
          ((s, v) :: accBinders, (accFVars.erase fun s' => compare s' s).union -- `s` is no longer a free variable TODO double-check ordering of arguments to "compare"
            $ v.getFreeVars (if letrec then .single s else default)) -- if letrec, s is not free in v
        else (accBinders, accFVars) -- drop binder
    -- remove atom binders
    let (bs, letAtoms) := bs.foldl (init := (default, letAtoms))
      fun (accBinders, letAtoms) (s, v) =>
        let v := v.pruneBlocks letAtoms
        let isSym := match v with
        | .sym s' => not letrec || s' != s -- handle the annoying (and perhaps unnecessary) `letrec r r` edge case
        | _ => false
        if v matches (.atom _) || isSym then
          (accBinders, letAtoms.insert s v) -- drop binder
        else ((accBinders ++ [(s, v)]), letAtoms.erase s)
    if letrec then
      mkLetrec bs (b.pruneBlocks letAtoms)
    else
      mkLet bs (b.pruneBlocks letAtoms)
  | .op₁    o e => .op₁ o (e.pruneBlocks letAtoms)
  | .app₀     e => .app₀ (e.pruneBlocks letAtoms)
  | .lambda s e => .lambda s (e.pruneBlocks letAtoms)
  | .sym    n   => match letAtoms.find? n with -- replace atom binders
                   | .some expr => expr
                   | .none => .sym n
  | .op₂    o e₁ e₂ => .op₂ o (e₁.pruneBlocks letAtoms) (e₂.pruneBlocks letAtoms)
  | .begin    e₁ e₂ => .begin (e₁.pruneBlocks letAtoms) (e₂.pruneBlocks letAtoms)
  | .app      e₁ e₂ => .app (e₁.pruneBlocks letAtoms) (e₂.pruneBlocks letAtoms)
  | .if       e₁ e₂ e₃ => .if (e₁.pruneBlocks letAtoms) (e₂.pruneBlocks letAtoms) (e₃.pruneBlocks letAtoms)
  | x => x

def replaceFreeVars (map : Std.RBMap String Expr compare) : Expr → Expr
  | .sym s => match map.find? s with | some x => x | none => sym s
  | .lambda s b => .lambda s (b.replaceFreeVars (map.erase s))
  | .let s v b => .let s (v.replaceFreeVars map) (b.replaceFreeVars (map.erase s))
  | .letrec s v b =>
    let map := map.erase s
    .letrec s (v.replaceFreeVars map) (b.replaceFreeVars map)
  | .op₁    o e => .op₁ o (e.replaceFreeVars map)
  | .app₀     e => .app₀ (e.replaceFreeVars map)
  | .op₂    o e₁ e₂ => .op₂ o (e₁.replaceFreeVars map) (e₂.replaceFreeVars map)
  | .begin    e₁ e₂ => .begin (e₁.replaceFreeVars map) (e₂.replaceFreeVars map)
  | .app      e₁ e₂ => .app (e₁.replaceFreeVars map) (e₂.replaceFreeVars map)
  | .if       e₁ e₂ e₃ =>
    .if (e₁.replaceFreeVars map) (e₂.replaceFreeVars map) (e₃.replaceFreeVars map)
  | x => x

def mkIfElses (ifThens : List (Expr × Expr)) (finalElse : Expr := .atom .nil) : Expr :=
  match ifThens with
  | [] => .atom .nil
  | [(cond, body)] => .if cond body finalElse
  | (cond, body) :: es => .if cond body (mkIfElses es finalElse)

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
  (binders : List $ String × Expr)
  (init := "mut")
  (merge : String → String → String := fun acc n => s!"{acc}_{n}")
  (key := "key") :
    List $ String × Expr :=
  match binders with
  | x@([ ])
  | x@([_]) => x
  | _ =>
    let names := binders.map Prod.fst
    let mutualName := names.foldl merge init
    let projs := names.enum.map fun (i, n) =>
      (n, .app (.sym mutualName) (Expr.toExpr i))
    let map := projs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let keySym := Expr.sym key
    let ifThens := binders.enum.map
      fun (i, (_, e)) => (.op₂ .numEq keySym (toExpr i), e.replaceFreeVars map)
    let mutualBlock := mkIfElses ifThens
    (mutualName, .lambda key mutualBlock) :: projs

namespace Anon

structure AnonCtx where
  highest : String
  map : Std.RBMap String String compare
  deriving Inhabited

def AnonCtx.next (ctx : AnonCtx) (k : String) : String × AnonCtx :=
  let v := ctx.highest.succ
  (v, ⟨v, ctx.map.insert k v⟩)

def AnonCtx.update (ctx : AnonCtx) (k v : String) : AnonCtx :=
  if ctx.highest.lt v then ⟨v, ctx.map.insert k v⟩
  else { ctx with map := ctx.map.insert k v }

end Anon

open Anon in
/--
Anonymizes variable names with incrementing strings whose most significant
characters are on the left. This function is meant to generate Lurk code that
can be hashed more efficiently, with short symbol names that share maximized tails.
-/
partial def anon (x : Expr) : Expr :=
  let rec aux (ctx : AnonCtx) : Expr → Expr × AnonCtx
    | sym s => match ctx.map.find? s with
      | some s => (sym s, ctx)
      | none => let (next, ctx) := ctx.next s; (sym next, ctx)
    | .lambda "_" b => (.lambda "_" (aux ctx b).1, ctx)
    | x@(.lambda ..) =>
      let (as, b) := x.telescopeLam
      if b.containsCurrentEnv then (x, ctx) else
        let (as, ctx) := as.foldl (init := (#[], ctx))
          fun (as, ctx) s =>
            let (curr, ctx) := ctx.next s
            (as.push curr, ctx.update s curr)
        (mkLambda as.data (aux ctx b).1, ctx)
    | x@(.let ..) =>
      let (bs, b) := x.telescopeLet
      if b.containsCurrentEnv then (x, ctx) else
        let (bs, ctx) := bs.foldl (init := (#[], ctx))
          fun (bs, ctx) (s, v) =>
            let (v, _) := aux ctx v
            let (curr, ctx) := ctx.next s
            (bs.push (curr, v), ctx)
        (mkLet bs.data (aux ctx b).1, ctx)
    | x@(.letrec ..) =>
      let (bs, b) := x.telescopeLet
      if b.containsCurrentEnv then (x, ctx) else
        let (bs, ctx) := bs.foldl (init := (#[], ctx))
          fun (bs, ctx) (s, v) =>
            let (curr, ctx) := ctx.next s
            let (v, _) := aux ctx v
            (bs.push (curr, v), ctx)
        (mkLetrec bs.data (aux ctx b).1, ctx)
    | .op₁    o e => (.op₁ o (aux ctx e).1, ctx)
    | .app₀     e => (.app₀  (aux ctx e).1, ctx)
    | .op₂    o e₁ e₂ => (.op₂ o (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .begin    e₁ e₂ => (.begin (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .app      e₁ e₂ => (.app   (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .if       e₁ e₂ e₃ => (.if (aux ctx e₁).1 (aux ctx e₂).1 (aux ctx e₃).1, ctx)
    | x => (x, ctx)
  (aux default x).1

end Lurk.Backend.Expr
