import Lurk.Expr
import Lurk.StringSucc
import Std.Data.RBMap
import Lean.Util.SCC

namespace Lurk.Expr

def mkApp (f : Expr) (args : List Expr) : Expr :=
  args.foldl (init := f) fun acc e => .app acc e

def mkLambda (args : List String) (body : Expr) : Expr :=
  args.foldr (init := body) fun s acc => .lambda s acc

def mkLet (binders : List $ String × Expr) (body : Expr) : Expr :=
  binders.foldr (init := body) fun (s, v) acc => .let s v acc

def mkLetrec (binders : List $ String × Expr) (body : Expr) : Expr :=
  binders.foldr (init := body) fun (s, v) acc => .letrec s v acc

/--
Given a list of Exprs `xs := [x₁, x₂, ..]` and `tail`, create the explicit list
`(cons x₁ (cons x₂ (cons .. tail)))`.

Note: this is *different* from creating the literal list `(x₁ x₂ .. . tail)`.
-/
def mkConsListWith (xs : List Expr) (tail : Expr := .nil) : Expr :=
  xs.foldr (init := tail) fun x acc => .op₂ .cons x acc

open Std (RBMap RBSet)

def getFreeVars (bVars acc : RBSet String compare := default) :
    Expr → RBSet String compare
  | .atom _ | .env | .quote _ => acc
  | .sym s => if bVars.contains s then acc else acc.insert s
  | .op₁ _ e
  | .app₀  e
  | .eval  e .nil => e.getFreeVars bVars acc
  | .op₂ _ e₁ e₂
  | .begin e₁ e₂
  | .app   e₁ e₂
  | .eval  e₁ e₂ => e₂.getFreeVars bVars (e₁.getFreeVars bVars acc)
  | .if a b c => c.getFreeVars bVars (b.getFreeVars bVars (a.getFreeVars bVars acc))
  | .lambda s   b => b.getFreeVars (bVars.insert s) acc
  | .let    s v b => b.getFreeVars (bVars.insert s) (v.getFreeVars bVars acc)
  | .letrec s v b =>
    let bVars := bVars.insert s; b.getFreeVars bVars (v.getFreeVars bVars acc)

def countFreeVarOccs
  (bVars : RBSet String compare := default)
  (acc : RBMap String Nat compare := default) :
    Expr → RBMap String Nat compare
  | .atom _ | .env | .quote _ => acc
  | .sym s => if bVars.contains s then acc else acc.insert s (acc.findD s 0).succ
  | .op₁ _ e
  | .app₀  e
  | .eval e .nil => e.countFreeVarOccs bVars acc
  | .op₂ _ e₁ e₂
  | .begin e₁ e₂
  | .app   e₁ e₂
  | .eval  e₁ e₂ => e₂.countFreeVarOccs bVars (e₁.countFreeVarOccs bVars acc)
  | .if a b c => c.countFreeVarOccs bVars (b.countFreeVarOccs bVars (a.countFreeVarOccs bVars acc))
  | .lambda s   b => b.countFreeVarOccs (bVars.insert s) acc
  | .let    s v b => b.countFreeVarOccs (bVars.insert s) (v.countFreeVarOccs bVars acc)
  | .letrec s v b =>
    let bVars := bVars.insert s; b.countFreeVarOccs bVars (v.countFreeVarOccs bVars acc)

def containsCurrentEnv : Expr → Bool
  | .env => true
  | .op₁ _    e
  | .app₀     e
  | .eval     e .nil
  | .lambda _ e => e.containsCurrentEnv
  | .op₂ _    e₁ e₂
  | .begin    e₁ e₂
  | .app      e₁ e₂
  | .let _    e₁ e₂
  | .eval     e₁ e₂
  | .letrec _ e₁ e₂ => e₁.containsCurrentEnv || e₂.containsCurrentEnv
  | .if       e₁ e₂ e₃ =>
    e₁.containsCurrentEnv || e₂.containsCurrentEnv || e₃.containsCurrentEnv
  | _ => false

def replaceFreeVars (map : RBMap String Expr compare) : Expr → Expr
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
  | .eval e .nil => .eval (e.replaceFreeVars map) .nil
  | .eval e env? => .eval (e.replaceFreeVars map) (env?.replaceFreeVars map)
  | .if       e₁ e₂ e₃ =>
    .if (e₁.replaceFreeVars map) (e₂.replaceFreeVars map) (e₃.replaceFreeVars map)
  | x => x

partial def dropInlineAux : Expr → Expr
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    let b := b.dropInlineAux
    let bs := bs.map fun (s, v) => (s, v.dropInlineAux)
    -- drop unused binders
    let (bs, _) := bs.foldr (init := (default, b.getFreeVars))
      fun (s, v) (accBinders, accFreeVars) =>
        if accFreeVars.contains s then -- include binder and its free variables
          ((s, v) :: accBinders, (accFreeVars.erase (compare · s)).union
            v.getFreeVars)
        else (accBinders, accFreeVars) -- drop binder
    -- inline trivial binders
    let (bs, trivs) : (Array $ String × Expr) × RBMap String Expr compare :=
      bs.foldl (init := default) fun (accBinders, accTrivials) (s, v) =>
        let v := v.replaceFreeVars accTrivials
        if v matches .atom _ | .sym _ | .quote _ then
          (accBinders, accTrivials.insert s v)
        else (accBinders.push (s, v), accTrivials)
    mkLet bs.data (b.replaceFreeVars trivs)
  | .letrec s v b =>
    let (bs, b) := b.telescopeLetrec #[(s, v)]
    let b := b.dropInlineAux
    let bs := bs.map fun (s, v) => (s, v.dropInlineAux)
    -- drop unused binders
    let (bs, _) := bs.foldr (init := (default, b.getFreeVars))
      fun (s, v) (accBinders, accFreeVars) =>
        if accFreeVars.contains s then -- include binder and its free variables
          ((s, v) :: accBinders, (accFreeVars.erase (compare · s)).union $
            v.getFreeVars $ .single s) -- s is not free in v
        else (accBinders, accFreeVars) -- drop binder
    -- inline trivial binders
    let (bs, trivs) : (Array $ String × Expr) × RBMap String Expr compare :=
      bs.foldl (init := default) fun (accBinders, accTrivials) (s, v) =>
        let v := v.replaceFreeVars (accTrivials.erase s) -- s is not free in v
        match v with
        | .atom _ | .quote _ => (accBinders, accTrivials.insert s v)
        | .sym s' =>
          if s != s' then (accBinders, accTrivials.insert s v)
          else (accBinders.push (s, v), accTrivials) -- an unfortunate loop
        | _ => (accBinders.push (s, v), accTrivials)
    mkLetrec bs.data (b.replaceFreeVars trivs)
  | .op₁    o e => .op₁    o e.dropInlineAux
  | .app₀     e => .app₀     e.dropInlineAux
  | .lambda s e => .lambda s e.dropInlineAux
  | .op₂ o e₁ e₂ => .op₂ o e₁.dropInlineAux e₂.dropInlineAux
  | .begin e₁ e₂ => .begin e₁.dropInlineAux e₂.dropInlineAux
  | .app   e₁ e₂ => .app   e₁.dropInlineAux e₂.dropInlineAux
  | .eval  e₁ e₂ => .eval  e₁.dropInlineAux e₂.dropInlineAux
  | .if e₁ e₂ e₃ => .if e₁.dropInlineAux e₂.dropInlineAux e₃.dropInlineAux
  | x => x

/-- Eagerly remove unnecessary binders from `let` and `letrec` blocks. -/
@[inline] def dropUnusedAndInlineImmediates (e : Expr) : Expr :=
  if e.containsCurrentEnv then e else e.dropInlineAux

def mkIfElses (ifThens : List (Expr × Expr)) (finalElse : Expr := .nil) : Expr :=
  match ifThens with
  | [] => .nil
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

/--
Given a list of binders which are naively mutually recursive, 
collect all the strongly connected components and then make them into mutual blocks.
-/
def mutualize (binders : List $ String × Expr) : List $ String × Expr :=
  let names := binders.map Prod.fst
  let binders := RBMap.ofList binders compare
  let blocks := Lean.SCC.scc names fun name =>
    binders.find! name |>.getFreeVars default default |>.toList
  List.join <| blocks.map fun block =>
    let block := block.map fun name => (name, binders.find! name)
    mkMutualBlock block

namespace Anon

structure AnonCtx where
  highest : String
  map : RBMap String String compare
  deriving Inhabited

def AnonCtx.next (ctx : AnonCtx) (k : String) : String × AnonCtx :=
  let v := ctx.highest.succ
  let v := if LDON.reservedSyms.contains v then v.succ else v
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
      let (as, ctx) := as.foldl (init := (#[], ctx))
        fun (as, ctx) s =>
          let (curr, ctx) := ctx.next s
          (as.push curr, ctx.update s curr)
      (mkLambda as.data (aux ctx b).1, ctx)
    | x@(.let ..) =>
      let (bs, b) := x.telescopeLet
      let (bs, ctx) := bs.foldl (init := (#[], ctx))
        fun (bs, ctx) (s, v) =>
          let (v, _) := aux ctx v
          let (curr, ctx) := ctx.next s
          (bs.push (curr, v), ctx)
      (mkLet bs.data (aux ctx b).1, ctx)
    | x@(.letrec ..) =>
      let (bs, b) := x.telescopeLetrec
      let (bs, ctx) := bs.foldl (init := (#[], ctx))
        fun (bs, ctx) (s, v) =>
          let (curr, ctx) := ctx.next s
          let (v, _) := aux ctx v
          (bs.push (curr, v), ctx)
      (mkLetrec bs.data (aux ctx b).1, ctx)
    | .op₁ o e => (.op₁ o (aux ctx e).1, ctx)
    | .app₀  e => (.app₀  (aux ctx e).1, ctx)
    | .op₂ o e₁ e₂ => (.op₂ o (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .begin e₁ e₂ => (.begin (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .app   e₁ e₂ => (.app   (aux ctx e₁).1 (aux ctx e₂).1, ctx)
    | .eval e .nil => (.eval (aux ctx e).1 .nil, ctx)
    | .eval e env? => (.eval (aux ctx e).1 (aux ctx env?).1, ctx)
    | .if    e₁ e₂ e₃ => (.if (aux ctx e₁).1 (aux ctx e₂).1 (aux ctx e₃).1, ctx)
    | x => (x, ctx)
  if x.containsCurrentEnv then x else (aux default x).1

def depthLE (e : Expr) (n : Nat) : Bool :=
  if n == 0 then false else
  match e with
  | .atom _ | .sym _ | .quote _ | .env => true
  | .op₁ _ e | .app₀ e | .lambda _ e => e.depthLE n.pred
  | .op₂ _ e₁ e₂ | .begin e₁ e₂ | .app e₁ e₂
  | .let _ e₁ e₂ | .letrec _ e₁ e₂ | .eval e₁ e₂ =>
    let n := n.pred; e₁.depthLE n && e₂.depthLE n
  | .if e₁ e₂ e₃ => let n := n.pred; e₁.depthLE n && e₂.depthLE n && e₃.depthLE n

end Lurk.Expr
