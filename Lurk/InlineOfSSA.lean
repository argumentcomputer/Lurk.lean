import Lurk.Expr

namespace Lurk.Expr

namespace SSA

/-!
# Utils for SSA optimization passes for `Lurk.Expr`
-/

/-
The current scope of the identifers were reassigning so far.
-/
abbrev Scope := Batteries.RBMap String Nat compare
abbrev IdMap := Batteries.RBMap Nat String compare

structure Context where
  currScope     : Scope
  currRecrScope : Scope
deriving Inhabited, Repr, BEq

structure State where
  usernames : IdMap
  freeVars  : Batteries.RBMap String Nat compare
  /-- Set of recursive id's -/
  recursive : Batteries.RBSet String compare
  nextId    : Nat
deriving Inhabited, Repr, BEq

abbrev M := ReaderT Context $ EStateM String State

-- when we hit the same symbol in a different context
-- update which id we should match to in the rest of the tree
def withUpdateScope (sym : String) (id : Nat) (x : M α) :=
  withReader (fun ctx => { ctx with currScope := ctx.currScope.insert sym id }) x

def withUpdateRecrScope (sym : String) (id : Nat) (x : M α) :=
  withReader (fun ctx => { ctx with currRecrScope := ctx.currRecrScope.insert sym id }) x

def insertSym (sym : String) : M Nat :=
  modifyGet fun ⟨usernames, freeVars, recursive, id⟩ =>
    (id, ⟨usernames.insert id sym, freeVars, recursive, id.succ⟩)

def insertFreeVar (sym : String) : M Nat :=
  modifyGet fun ⟨usernames, freeVars, recursive, id⟩ =>
    (id, ⟨usernames.insert id sym, freeVars.insert sym id, recursive, id.succ⟩)

partial def toSSA (e : Expr) : M Expr := do
  match e with
  | .sym s => do
    if let some n := (← read).currRecrScope.find? s then
      modify fun σ => { σ with recursive := σ.recursive.insert s!"{n}" }
    let n := ← match (← read).currScope.find? s with
      | some n => return n
      | none   => do match (← get).freeVars.find? s with
        | some n => return n
        | none   => insertFreeVar s
    return .sym (ToString.toString n)
  | .lambda s b => do
    let id ← insertSym s
    let b ← withUpdateScope s id $ toSSA b
    return .lambda (ToString.toString id) b
  | .let    s v b => do
    let id ← insertSym s
    let v ← toSSA v
    let b ← withUpdateScope s id $ toSSA b
    return .let (ToString.toString id) v b
  | .letrec s v b  => do
    let id ← insertSym s
    withUpdateScope s id do
      let v ← withUpdateRecrScope s id $ toSSA v
      let b ← toSSA b
      return .letrec (ToString.toString id) v b
  | .atom a        => return .atom a
  | .env           => return .env
  | .op₁ op e      => return .op₁ op (← toSSA e)
  | .op₂ op e₁ e₂  => return .op₂ op (← toSSA e₁) (← toSSA e₂)
  | .begin e₁ e₂   => return .begin (← toSSA e₁) (← toSSA e₂)
  | .if cond e₁ e₂ => return .if (← toSSA cond) (← toSSA e₁) (← toSSA e₂)
  | .app₀ fn       => return .app₀ (← toSSA fn)
  | .app  f a      => return .app  (← toSSA f) (← toSSA a)
  | .quote ldon    => return .quote ldon
  | .eval e env?   => return .eval (← toSSA e) (← toSSA env?)

end SSA

def toSSA (e : Expr) : Except String (Expr × SSA.State) :=
  match ReaderT.run (SSA.toSSA e) default |>.run default with
  | .ok    e s => return (e, s)
  | .error e _ => throw e

def ofSSA (e : Expr) (σ : SSA.State) : Except String Expr :=
  match e with
  | .sym s        => .sym <$> getSym s
  | .lambda s b   => return .lambda (← getSym s) (← ofSSA b σ)
  | .let    s v b => return .let    (← getSym s) (← ofSSA v σ) (← ofSSA b σ)
  | .letrec s v b => return .letrec (← getSym s) (← ofSSA v σ) (← ofSSA b σ)
  | .atom a        => return .atom a
  | .env           => return .env
  | .quote ldon    => return .quote ldon
  | .op₁ op e      => return .op₁ op (← ofSSA e σ)
  | .op₂ op e₁ e₂  => return .op₂ op (← ofSSA e₁ σ) (← ofSSA e₂ σ)
  | .begin e₁ e₂   => return .begin (← ofSSA e₁ σ) (← ofSSA e₂ σ)
  | .app₀ fn       => return .app₀ (← ofSSA fn σ)
  | .app  f a      => return .app  (← ofSSA f σ) (← ofSSA a σ)
  | .eval e env?   => return .eval (← ofSSA e σ) (← ofSSA env? σ)
  | .if cond e₁ e₂ => return .if (← ofSSA cond σ) (← ofSSA e₁ σ) (← ofSSA e₂ σ)
where getSym (n : String) := do
  let some n := n.toNat?
    | throw s!"bad expr: expected only numerical symbols in SSA, got {n}"
  match σ.usernames.find? n with
  | some s => return s
  | none   => throw s!"bad expr: expected {n} to be in context"

private abbrev Counts := Batteries.RBMap String Nat compare

/--
For each binder in the given expression, count how many
non-recursive references there are.

ASSUMES the given expression is well-formed and in SSA form
-/
def countBVarOccs (counts : Counts := .empty) : Expr → Counts
  | .atom _ | .env | .quote _ => counts
  | .sym s => match counts.find? s with
    | some n => counts.insert s n.succ
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

abbrev ExprMap := Batteries.RBMap String Expr compare

structure Context where
  prunable : Batteries.RBSet String compare
  erasable : Batteries.RBSet String compare
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
def init (ctx : Context := default) (counts : Counts)
    (recrs : Batteries.RBSet String compare) : Expr → Except String Context
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
def inlineOfSSA (e : Expr) (recrs : Batteries.RBSet String compare) : Except String Expr := do
  let counts := e.countBVarOccs
  let ctx ← Prune.init default counts recrs e
  ReaderT.run (prune e) ctx

end Lurk.Expr
