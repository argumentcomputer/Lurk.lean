import Lurk.Backend.Expr
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

/-- Eagerly remove unecessary binders from `let` and `letrec` blocks. -/
partial def pruneBlocks : Expr → Expr
  | x@(.let s v b) =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    if b.containsCurrentEnv then x else
    let bs := bs.foldr (init := (default, b.getFreeVars))
      fun (s, v) (accBinders, accFVars) =>
        if accFVars.contains s then
          ((s, v.pruneBlocks) :: accBinders, accFVars.union v.getFreeVars)
        else (accBinders, accFVars) -- drop binder
    mkLet bs.1 b.pruneBlocks
  | x@(.letrec s v b) =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    if b.containsCurrentEnv then x else
    let bs := bs.foldr (init := (default, b.getFreeVars))
      fun (s, v) (accBinders, accFVars) =>
        if accFVars.contains s then
          ((s, v.pruneBlocks) :: accBinders,
            accFVars.union $ v.getFreeVars (.single s)) -- s is not free in v)
        else (accBinders, accFVars) -- drop binder
    mkLetrec bs.1 b.pruneBlocks
  | .op₁    o e => .op₁ o e.pruneBlocks
  | .app₀     e => .app₀ e.pruneBlocks
  | .lambda s e => .lambda s e.pruneBlocks
  | .op₂    o e₁ e₂ => .op₂ o e₁.pruneBlocks e₂.pruneBlocks
  | .begin    e₁ e₂ => .begin e₁.pruneBlocks e₂.pruneBlocks
  | .app      e₁ e₂ => .app e₁.pruneBlocks e₂.pruneBlocks
  | .if       e₁ e₂ e₃ => .if e₁.pruneBlocks e₂.pruneBlocks e₃.pruneBlocks
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

end Lurk.Backend.Expr
