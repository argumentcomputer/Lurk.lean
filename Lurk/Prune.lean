import Lurk.SSA

namespace Lurk.Expr

private abbrev Counts := Std.RBMap String Nat compare

/--
For each binder in the given expression, count how many
non-recursive references there are.

ASSUMES the given expression is well-formed and in SSA form
-/
def countBVarOccs (counts : Counts := .empty) : Expr → Counts
  | .atom _ | .env | .quote _ => counts
  | .sym s => match counts.find? s with
    | some n => counts.insert s (n + 1)
    | none   => counts
  | .op₁    _ e
  | .app₀     e      
  | .lambda _ e   => countBVarOccs counts e
  | .op₂ _ e₁ e₂
  | .begin e₁ e₂
  | .app   e₁ e₂
  | .eval  e₁ e₂  => countBVarOccs (countBVarOccs counts e₁) e₂
  | .if a b c     => countBVarOccs (countBVarOccs (countBVarOccs counts a) b) c
  | .let    s v b => countBVarOccs ((countBVarOccs counts v).insert s 0) b
  | .letrec s v b => countBVarOccs ((countBVarOccs counts v).insert s 0) b


mutual

partial def replace (sym : String) (expr : Expr) (f : Expr → Expr) (e : Expr) :=
    let (e, replaced?) := replaceFirstOcc sym expr e
    (f e, replaced?)

partial def replace₂ (sym : String) (expr : Expr) 
    (f : Expr → Expr → Expr) (e₁ e₂ : Expr) :=
  let (e₁, replaced?) := replaceFirstOcc sym expr e₁
  if replaced? then
    (f e₁ e₂, replaced?)
  else
    let (e₂, replaced?) := replaceFirstOcc sym expr e₂
    (f e₁ e₂, replaced?)

partial def replace₃ (sym : String) (expr : Expr) 
    (f : Expr → Expr → Expr → Expr) (e₁ e₂ e₃ : Expr) :=
  let (e₁, replaced?) := replaceFirstOcc sym expr e₁
  if replaced? then
    (f e₁ e₂ e₃, replaced?)
  else
    let (e₂, replaced?) := replaceFirstOcc sym expr e₂
    if replaced? then
      (f e₁ e₂ e₃, replaced?)
    else
      let (e₃, replaced?) := replaceFirstOcc sym expr e₃
      (f e₁ e₂ e₃, replaced?)
    
partial def replaceFirstOcc (sym : String) (expr : Expr) : Expr → Expr × Bool
  | .sym s   => if s == sym then (expr, true) else (.sym s, false)
  | .atom a  => (.atom a,  false)
  | .env     => (.env,     false)
  | .quote d => (.quote d, false)
  | .op₁ op e     => replace  sym expr (.op₁ op)   e
  | .app₀ e       => replace  sym expr .app₀       e
  | .lambda b e   => replace  sym expr (.lambda b) e
  | .op₂ op   e₁ e₂ => replace₂ sym expr (.op₂ op)   e₁ e₂
  | .begin    e₁ e₂ => replace₂ sym expr .begin      e₁ e₂
  | .app      e₁ e₂ => replace₂ sym expr .app        e₁ e₂
  | .eval     e₁ e₂ => replace₂ sym expr .eval       e₁ e₂
  | .let    s e₁ e₂ => replace₂ sym expr (.let s)    e₁ e₂
  | .letrec s e₁ e₂ => replace₂ sym expr (.letrec s) e₁ e₂
  | .if e₁ e₂ e₃  => replace₃ sym expr .if         e₁ e₂ e₃

end

namespace Prune

abbrev ExprMap   := Std.RBMap String Expr compare

structure Context where
  prunable : Std.RBSet String compare
  erasable : Std.RBSet String compare
deriving Inhabited, Repr, BEq

def Context.update (ctx : Context) (cnt : Nat) (sym : String) :=
  if cnt == 0 then
    { ctx with erasable := ctx.erasable.insert sym }
  else if cnt == 1 then
    { ctx with prunable := ctx.prunable.insert sym }
  else
    ctx

def Context.union (c₁ c₂ : Context) : Context :=
  let p := c₁.prunable.union c₂.prunable
  let e := c₁.erasable.union c₂.erasable
  ⟨p, e⟩

/--
If the count is `0`, then the binder can be removed.
If the count is `1`, then the binder can be inlined.
If the count is `2` or more, then nothing is done.

recr? | counts  | what to do
yes   | 0       | delete
yes   | 1       | can't inline due to recursion => HACK, just make it 2
no    | 0       | delete
no    | 1       | inline
-/
def init (ctx : Context := default) 
    (counts : Counts) (recrs : Std.RBSet String compare) (e : Expr) : 
    Except String Context :=
  match e with
  | .let    s v b
  | .letrec s v b => do
    let ctx ← init ctx counts recrs v
    match counts.find? s with
    | some n =>
      let n := if recrs.contains s && n == 1 then 2 else n -- HACK, just make it 2
      init (ctx.update n s) counts recrs b
    | none   => throw s!"bad expr: expected {s} to be in context"
  | .sym _ | .atom _ | .env | .quote _ => return ctx
  | .app₀ e | .op₁ _ e | .lambda _ e => init ctx counts recrs e
  | .op₂ _ e₁ e₂
  | .begin e₁ e₂
  | .app   e₁ e₂
  | .eval  e₁ e₂ => do init (← init ctx counts recrs e₁) counts recrs e₂
  | .if cond e₁ e₂ => do
    let ctx ← init ctx counts recrs cond
    let ctx ← init ctx counts recrs e₁
    init ctx counts recrs e₂

abbrev M := ReaderT Context $ Except String

partial def erase (e : Expr) : M Expr := do
  match e with
  | .let    s v b =>
    match (← read).erasable.find? s with
    | some _ => erase b
    | none   => return .let s v (← erase b)
  | .letrec s v b =>
    match (← read).erasable.find? s with
    | some _ => erase b
    | none   => return .letrec s v (← erase b)
  | .sym s         => return .sym s
  | .atom a        => return .atom a
  | .env           => return .env
  | .op₁ op e      => return .op₁ op (← erase e)
  | .op₂ op e₁ e₂  => return .op₂ op (← erase e₁) (← erase e₂)
  | .begin e₁ e₂   => return .begin (← erase e₁) (← erase e₂)
  | .if cond e₁ e₂ => return .if (← erase cond) (← erase e₁) (← erase e₂)
  | .app₀ fn       => return .app₀ (← erase fn)
  | .app  f a      => return .app  (← erase f) (← erase a)
  | .quote ldon    => return .quote ldon
  | .eval e env?   => return .eval (← erase e) (← erase env?)
  | .lambda s b    => return .lambda s (← erase b)

mutual

partial def replaceAndPrune (sym : String) (expr e : Expr) : M Expr := do
  let (e, replaced?) := replaceFirstOcc sym expr e
  if !replaced? then
    throw s!"bad expr: was expecting to replace {sym} in {e}"
  prune e

/--
Assumes the given `prunable` map is nondegenerate
-/
partial def prune (e : Expr) : M Expr := do
  match e with
  | .let    s v b =>
    let v ← prune v
    match (← read).prunable.find? s with
    | none   => return .let s v (← prune b)
    | some _ => replaceAndPrune s v b
  | .letrec s v b =>
    let v ← prune v
    match (← read).prunable.find? s with
    | none   => return .letrec s v (← prune b)
    | some _ => replaceAndPrune s v b
  | .sym s         => return .sym s
  | .atom a        => return .atom a
  | .env           => return .env
  | .op₁ op e      => return .op₁ op (← prune e)
  | .op₂ op e₁ e₂  => return .op₂ op (← prune e₁) (← prune e₂)
  | .begin e₁ e₂   => return .begin (← prune e₁) (← prune e₂)
  | .if cond e₁ e₂ => return .if (← prune cond) (← prune e₁) (← prune e₂)
  | .app₀ fn       => return .app₀ (← prune fn)
  | .app  f a      => return .app  (← prune f) (← prune a)
  | .quote ldon    => return .quote ldon
  | .eval e env?   => return .eval (← prune e) (← prune env?)
  | .lambda s b    => return .lambda s (← prune b)

end

end Prune

open Prune in
def pruneWith (e : Expr) (ctx : Context) : Except String Expr :=
  let x : M Expr := do prune e
  ReaderT.run x ctx

def eraseAndPrune (e : Expr) (recrs : Std.RBSet String compare) : Except String Expr := do
  let counts := e.countBVarOccs
  let ctx ← Prune.init default counts recrs e
  pruneWith e ctx

end Lurk.Expr