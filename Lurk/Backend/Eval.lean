import Lurk.Backend.Expr

namespace Lurk.Backend

set_option genSizeOfSpec false in
mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Thunk (Except String Value)) → Env

inductive Value where
  | atom  : Atom → Value
  | sym   : String → Value
  | cons  : Value → Value → Value
  | comm  : F → Value
  | «fun» : String → Env → Expr → Value
  deriving Inhabited

end

namespace Value

declare_syntax_cat                      value
scoped syntax ident                   : value
scoped syntax char                    : value
scoped syntax num                     : value
scoped syntax str                     : value
scoped syntax "(" value "." value ")" : value
scoped syntax "(" value+ ")"          : value

open Lean Meta Elab Term in
partial def elabValue : Lean.TSyntax `value → TermElabM Lean.Expr
  | `(value| $i:ident) => mkAppM ``Value.sym #[mkStrLit i.getId.toString]
  | `(value| $c:char) => do
    mkAppM ``Value.atom #[← mkAppM ``Atom.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]]
  | `(value| $n:num) => do
    mkAppM ``Value.atom #[← mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]]
  | `(value| $s:str) => do
    mkAppM ``Value.atom #[← mkAppM ``Atom.str #[mkStrLit s.getString]]
  | `(value| ($v₁:value . $v₂:value)) => do
    mkAppM ``Value.cons #[← elabValue v₁, ← elabValue v₂]
  | `(value| ($vs:value*)) => do
    vs.foldrM (init := ← mkAppM ``Value.atom #[mkConst ``Atom.nil])
      fun v acc => do mkAppM ``Value.cons #[← elabValue v, acc]
  | _ => throwUnsupportedSyntax

scoped elab "⦃" v:value "⦄" : term =>
  elabValue v

partial def telescopeCons (acc : Array Value := #[]) : Value → Array Value × Value
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

partial def toString : Value → String
  | .atom a => a.toString
  | .sym s => s
  | v@(.cons ..) => match v.telescopeCons with
    | (#[], .atom .nil) => "NIL"
    | (vs, v) =>
      let vs := vs.data.map toString |> " ".intercalate
      match v with
      | .atom .nil => "(" ++ vs ++ ")"
      | _ => s!"({vs} . {v.toString})"
  | .comm c => s!"<comm {c.asHex}>"
  | .fun n .. => s!"<fun ({n})>"

end Value

instance : ToString Value where
  toString := Value.toString

instance : Inhabited Env := ⟨.mk .leaf⟩

abbrev Result := Except String Value

namespace Env

def find? (s : String) : Env → Option (Thunk Result)
  | mk e => e.find compare s

def insert (s : String) (v : Thunk Result) : Env → Env
  | mk e => mk $ e.insert compare s v

def toArray : Env → Array (String × (Thunk Result))
  | mk e => e.fold (init := #[]) fun acc k v => acc.push (k, v)

end Env

mutual

partial def Env.eqAux : List (String × Result) → List (String × Result) → Bool
  | [], [] => true
  | (s₁, v₁)::xs, (s₂, v₂)::ys => match (v₁, v₂) with
    | (Except.ok v₁, Except.ok v₂) => v₁.beq v₂ && s₁ == s₂ && Env.eqAux xs ys
    | (Except.error e₁, Except.error e₂) => e₁ == e₂ && s₁ == s₂ && Env.eqAux xs ys
    | _ => false
  | _, _ => false

partial def Env.eq (e₁ e₂ : Env) : Bool :=
  Env.eqAux (e₁.toArray.data.map fun (s, v) => (s, v.get))
    (e₂.toArray.data.map fun (s, v) => (s, v.get))

partial def Value.beq : Value → Value → Bool
  | .atom l₁, .atom l₂ => l₁ == l₂
  | .sym s₁, .sym s₂ => s₁ == s₂
  | .cons c₁ d₁, .cons c₂ d₂ => c₁.beq c₂ && d₁.beq d₂
  | .comm c₁, .comm c₂ => c₁ == c₂
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ => ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

def Value.num : Value → Except String F
  | .atom (.num x) => pure x
  | v => throw s!"expected number, got\n  {v}"

instance : Coe Bool Value where coe
  | true  => .atom .t
  | false => .atom .nil

instance : Coe Char Value where
  coe c := .atom (.char c)

instance : Coe String Value where
  coe c := .atom (.str c)

instance : OfNat Value n where
  ofNat := .atom $ .num (.ofNat n)

def Expr.evalOp₁ : Op₁ → Value → Result
  | .atom, .cons .. => return .atom .nil
  | .atom, _ => return .atom .t
  | .car, .cons car _ => return car
  | .car, .atom (.str ⟨[]⟩) => return .atom .nil
  | .car, .atom (.str ⟨h::_⟩) => return .atom (.char h)
  | .car, v => throw s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, .atom (.str ⟨[]⟩) => return .atom (.str "")
  | .cdr, .atom (.str ⟨_::t⟩) => return .atom (.str ⟨t⟩)
  | .cdr, v => throw s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace v; return v
  | .commit, _ => throw "TODO commit"
  | .comm, v => return .comm (← v.num)
  | .open, _ => throw "TODO open"
  | .num, .atom (.num n) => return .atom (.num n)
  | .num, .atom (.char c) => return .atom $ .num (.ofNat c.toNat)
  | .num, .comm c => return .atom (.num c)
  | .num, v => throw s!"expected char, num, or comm value, got\n  {v}"
  | .char, .atom (.char c) => return .atom (.char c)
  | .char, .atom (.num ⟨n, _⟩) =>
    if h : isValidChar n.toUInt32 then
      return .atom (.char ⟨n.toUInt32, h⟩)
    else
      throw s!"{n.toUInt32} is not a valid char value"
  | .char, v => throw s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ : Op₂ → Value → Value → Result
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .atom (.char c), .atom (.str s) => return .atom (.str ⟨c :: s.data⟩)
  | .strcons, v₁, v₂ => throw s!"expected char and string value, got {v₁} and {v₂}"
  | .add, v₁, v₂ => return .atom $ .num ((← v₁.num) + (← v₂.num))
  | .sub, v₁, v₂ => return .atom $ .num ((← v₁.num) - (← v₂.num))
  | .mul, v₁, v₂ => return .atom $ .num ((← v₁.num) * (← v₂.num))
  | .div, v₁, v₂ => return .atom $ .num ((← v₁.num) / (← v₂.num))
  | .numEq, v₁, v₂ => return (← v₁.num) == (← v₂.num)
  | .lt, v₁, v₂ => return decide $ (← v₁.num) < (← v₂.num)
  | .gt, v₁, v₂ => return decide $ (← v₁.num) > (← v₂.num)
  | .le, v₁, v₂ => return decide $ (← v₁.num) <= (← v₂.num)
  | .ge, v₁, v₂ => return decide $ (← v₁.num) >= (← v₂.num)
  | .eq, v₁, v₂ => return v₁.beq v₂
  | .hide, _, _ => throw "TODO hide"

partial def Expr.eval (env : Env := default) : Expr → Result
  | .atom l => return .atom l
  | .sym n => match env.find? n with
    | some v => v.get
    | none => throw s!"{n} not found"
  | .env =>
    env.toArray.foldrM (init := .atom .nil)
      fun (k, v) acc => return .cons (.cons (.sym k) (← v.get)) acc
  | .begin x (.atom .nil) => x.eval env
  | .begin x y => do discard $ x.eval env; y.eval env
  | .if x y z => do match ← x.eval env with
    | .atom .nil => z.eval env
    | _ => y.eval env
  | .app₀ fn => do match ← fn.eval env with
    | .fun "_" env' body => body.eval env'
    | _ => throw s!"error evaluating\n{fn}\ninvalid 0-arity app"
  | .app fn arg => do match ← fn.eval env with
    | .fun "_" .. => throw s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun n env' body => body.eval (env'.insert n (arg.eval env))
    | x => throw s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"
  | .op₁ op e => do evalOp₁ op (← e.eval env)
  | .op₂ op e₁ e₂ => do evalOp₂ op (← e₁.eval env) (← e₂.eval env)
  | .lambda s e => return .fun s env e
  | .let s v b => b.eval (env.insert s (v.eval env))
  | .letrec s v b => do
    let v' : Expr := .letrec s v v
    let env' := env.insert s $ .mk fun _ => eval env v'
    b.eval (env.insert s (eval env' v))
  | .quote _ => throw "TODO quote"

end Lurk.Backend
