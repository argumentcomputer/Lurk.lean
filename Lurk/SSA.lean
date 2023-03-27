import Lurk.Expr
/-!

# Utils for SSA optimization passes for `Lurk.Expr`

-/

namespace Lurk.Expr

namespace SSA

/-
The current scope of the identifers were reassigning so far.
-/
abbrev Scope := Std.RBMap String Nat compare
abbrev IdMap := Std.RBMap Nat String compare

structure Context where
  currScope     : Scope
  currRecrScope : Scope
deriving Inhabited, Repr, BEq

structure State where
  usernames : IdMap
  freeVars  : Std.RBMap String Nat compare
  /-- Set of recursive id's -/
  recursive : Std.RBSet String compare
  nextId    : Nat
deriving Inhabited, Repr, BEq

abbrev M := ReaderT Context $ EStateM String State

-- when we hit the same symbol in a different context
-- update which id we should match to in the rest of the tree
def withUpdateScope (sym : String) (id : Nat) (x : M α) :=
  withReader (fun ctx => { ctx with currScope := ctx.currScope.insert sym id }) x

def withUpdateRecrScope (sym : String) (id : Nat) (x : M α) :=
  withReader (fun ctx => { ctx with currRecrScope := ctx.currRecrScope.insert sym id }) x

def insertSym (sym : String) : M Nat := do
  let ⟨usernames, freeVars, recursive, id⟩ ← get
  let usernames := usernames.insert id sym
  let nextId := id + 1
  set (State.mk usernames freeVars recursive nextId)
  return id

def insertFreeVar (sym : String) : M Nat := do
  let ⟨usernames, freeVars, recursive, id⟩ ← get
  let usernames := usernames.insert id sym
  let freeVars := freeVars.insert sym id
  let nextId := id + 1
  set (State.mk usernames freeVars recursive nextId)
  return id

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
    return .sym s!"{n}"
  | .lambda s b => do
    let id ← insertSym s
    let b ← withUpdateScope s id $ toSSA b
    return .lambda s!"{id}" b
  | .let    s v b => do
    let id ← insertSym s
    let v ← toSSA v
    let b ← withUpdateScope s id $ toSSA b
    return .let s!"{id}" v b
  | .letrec s v b  => do
    let id ← insertSym s
    withUpdateScope s id do 
      let v ← withUpdateRecrScope s id $ toSSA v
      let b ← toSSA b
      return .letrec s!"{id}" v b
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

def ofSSA (e : Expr) (σ : SSA.State) : Except String Expr := do
  match e with
  | .sym s        => .sym <$> getSym s
  | .lambda s b   => do return .lambda (← getSym s) (← ofSSA b σ)
  | .let    s v b => do return .let    (← getSym s) (← ofSSA v σ) (← ofSSA b σ)
  | .letrec s v b => do return .letrec (← getSym s) (← ofSSA v σ) (← ofSSA b σ)
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


end Lurk.Expr