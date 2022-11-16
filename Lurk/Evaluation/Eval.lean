import Lean
import Lurk.Evaluation.Expr

namespace Lurk.Evaluation

set_option genSizeOfSpec false in
mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Thunk (Except String Value)) → Env

inductive Value where
  | lit : Lit → Value
  | sym : String → Value
  | cons : Value → Value → Value
  | comm : F → Value
  | «fun» : String → Env → Expr → Value
  deriving Inhabited

end

namespace Value

partial def telescopeCons (acc : Array Value := #[]) : Value → Array Value × Value
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

partial def toString : Value → String
  | .lit l => l.toString
  | .sym s => s
  | v@(.cons ..) => match v.telescopeCons with
    | (#[], .lit .nil) => "NIL"
    | (vs, v) =>
      let vs := vs.data.map toString |> " ".intercalate
      match v with
      | .lit .nil => "(" ++ vs ++ ")"
      | _ => s!"({vs} . {v.toString})"
  | .comm c => s!"<comm {c.asHex}>"
  | .fun n .. => s!"<fun ({n})>"

end Value

instance : ToString Value where
  toString := Value.toString

def Value.ofAST : Syntax.AST → Value
  | .nil => .lit .nil
  | .num n => .lit $ .num (.ofNat n)
  | .char c => .lit $ .char c
  | .str s => .lit $ .str s
  | .sym "T" => .lit .t
  | .sym s => .sym s
  | .cons x y => .cons (Value.ofAST x) (Value.ofAST y)

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
  | .lit l₁, .lit l₂ => l₁ == l₂
  | .sym s₁, .sym s₂ => s₁ == s₂
  | .cons c₁ d₁, .cons c₂ d₂ => c₁.beq c₂ && d₁.beq d₂
  | .comm c₁, .comm c₂ => c₁ == c₂
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ => ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

def Value.num : Value → Except String F
  | .lit (.num x) => pure x
  | v => throw s!"expected number, got\n  {v}"

instance : Coe Bool Value where coe
  | true  => .lit .t
  | false => .lit .nil

instance : Coe Char Value where
  coe c := .lit (.char c)

instance : Coe String Value where
  coe c := .lit (.str c)

instance : OfNat Value n where
  ofNat := .lit $ .num (.ofNat n)

def Expr.evalOp₁ : Op₁ → Value → Result
  | .atom, .cons .. => return .lit .nil
  | .atom, _ => return .lit .t
  | .car, .cons car _ => return car
  | .car, .lit (.str ⟨[]⟩) => return .lit .nil
  | .car, .lit (.str ⟨h::_⟩) => return .lit (.char h)
  | .car, v => throw s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, .lit (.str ⟨[]⟩) => return .lit (.str "")
  | .cdr, .lit (.str ⟨_::t⟩) => return .lit (.str ⟨t⟩)
  | .cdr, v => throw s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace s!"{v.toString}"; return v
  | .commit, _ => throw "TODO commit"
  | .comm, v => return .comm (← v.num)
  | .open, _ => throw "TODO open"
  | .num, .lit (.num n) => return .lit (.num n)
  | .num, .lit (.char c) => return .lit $ .num (.ofNat c.toNat)
  | .num, .comm c => return .lit (.num c)
  | .num, v => throw s!"expected char, num, or comm value, got\n  {v}"
  | .char, .lit (.char c) => return .lit (.char c)
  | .char, .lit (.num ⟨n, _⟩) =>
    if h : isValidChar n.toUInt32 then
      return .lit (.char ⟨n.toUInt32, h⟩)
    else
      throw s!"{n.toUInt32} is not a valid char value"
  | .char, v => throw s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ : Op₂ → Value → Value → Result
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .lit (.char c), .lit (.str s) => return .lit (.str ⟨c :: s.data⟩)
  | .strcons, v₁, v₂ => throw s!"expected char and string value, got\n  {v₁}\n  {v₂}"
  | .add, v₁, v₂ => return .lit $ .num ((← v₁.num) + (← v₂.num))
  | .sub, v₁, v₂ => return .lit $ .num ((← v₁.num) - (← v₂.num))
  | .mul, v₁, v₂ => return .lit $ .num ((← v₁.num) * (← v₂.num))
  | .div, v₁, v₂ => return .lit $ .num ((← v₁.num) / (← v₂.num))
  | .numEq, v₁, v₂ => return (← v₁.num) == (← v₂.num)
  | .lt, v₁, v₂ => return decide $ (← v₁.num) < (← v₂.num)
  | .gt, v₁, v₂ => return decide $ (← v₁.num) > (← v₂.num)
  | .le, v₁, v₂ => return decide $ (← v₁.num) <= (← v₂.num)
  | .ge, v₁, v₂ => return decide $ (← v₁.num) >= (← v₂.num)
  | .eq, v₁, v₂ => return v₁.beq v₂
  | .hide, _, _ => throw "TODO hide"

partial def Expr.eval (env : Env := default) : Expr → Result
  | .lit l => return .lit l
  | .sym n => match env.find? n with
    | some v => v.get
    | none => throw s!"{n} not found"
  | .env => do
    env.toArray.foldrM (init := .lit .nil)
      fun (k, v) acc => return .cons (.cons (.sym k) (← v.get)) acc
  | .begin x (.lit .nil) => x.eval env
  | .begin x y => do discard $ x.eval env; y.eval env
  | .if x y z => do match ← x.eval env with
    | .lit .t => y.eval env
    | _ => z.eval env
  | .app₀ fn => do match ← fn.eval env with
    | .fun "_" env' body => body.eval env'
    | _ => throw s!"invalid 0-arity app"
  | .app fn arg => do match ← fn.eval env with
    | .fun "_" .. => throw "cannot apply argument to 0-arg lambda"
    | .fun n env' body => body.eval (env'.insert n (arg.eval env))
    | _ => throw "lambda was expected"
  | .op₁ op e => do evalOp₁ op (← e.eval env)
  | .op₂ op e₁ e₂ => do evalOp₂ op (← e₁.eval env) (← e₂.eval env)
  | .lambda s e => return .fun s env e
  | .let s v b => b.eval (env.insert s (v.eval env))
  | .letrec s v b => do
    let v' : Expr := .letrec s v v
    let env' := env.insert s $ .mk fun _ => eval env v'
    b.eval (env.insert s (eval env' v))
  | .quote x => return .ofAST x

end Lurk.Evaluation
