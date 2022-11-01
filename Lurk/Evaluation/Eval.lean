import Lean
import Lurk.Evaluation.Expr

namespace Lurk.Evaluation

set_option genSizeOfSpec false in
mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Thunk (Except String Value)) → Env

inductive Value where
  | ast : Syntax.AST → Value
  | comm : F → Value
  | «fun» : String → Env → Expr → Value
  deriving Inhabited

end

abbrev Result := Except String Value

partial def Value.toString : Value → String
  | .ast x => ToString.toString x
  | .comm c => s!"<comm {c.asHex}>"
  | .fun n .. => s!"<fun ({n})>"

instance : Inhabited Env := ⟨.mk .leaf⟩

namespace Env

def find? (s : String) : Env → Option (Thunk Result)
  | mk e => e.find compare s

def insert (s : String) (v : Thunk Result) : Env → Env
  | mk e => mk $ e.insert compare s v

def node : Env → Lean.RBNode String (fun _ => Thunk Result)
  | mk e => e

def toList : Env → List (String × (Thunk Result))
  | mk e => e.fold (init := []) fun acc k v => (k, v) :: acc

end Env

mutual

partial def Env.eqAux : List (String × Result) → List (String × Result) → Bool
  | [], [] => true
  | (s₁, v₁)::xs, (s₂, v₂)::ys => match (v₁, v₂) with
    | (Except.ok v₁, Except.ok v₂) => v₁.eq v₂ && s₁ == s₂ && Env.eqAux xs ys
    | (Except.error e₁, Except.error e₂) => e₁ == e₂ && s₁ == s₂ && Env.eqAux xs ys
    | _ => false    
  | _, _ => false

partial def Env.eq (e₁ e₂ : Env) : Bool :=
  Env.eqAux (e₁.toList.map fun (s, v) => (s, v.get)) (e₂.toList.map fun (s, v) => (s, v.get))

partial def Value.eq : Value → Value → Bool
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ =>
    ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | .ast x, .ast y => x == y
  -- | .env e₁, .env e₂ => Env.eqAux e₁ e₂
  | .comm c₁, .comm c₂ => c₁ == c₂
  | _, _ => false

end

def Value.num : Value → Except String F
  | .ast (.num x) => pure $ .ofNat x
  | v => throw s!"expected numerical value, got\n  {v.toString}"

partial def Expr.evalOp₁ (op : Op₁) (v : Value) : Except String Value := match op, v with
  | .atom, .ast (.cons ..) => return .ast .nil
  | .atom, _ => return .ast (.sym "T")
  | .car, .ast (.cons car _) => return .ast car
  | .car, v => throw s!"expected cons value, got\n  {v.toString}"
  | .cdr, .ast (.cons _ cdr) => return .ast cdr
  | .cdr, v => throw s!"expected cons value, got\n  {v.toString}"
  | .emit, v => dbg_trace s!"{v.toString}"; return v
  | .commit, v => throw "TODO"
  | .comm, v => return .comm (← v.num)
  | .open, v => throw "TODO"
  | .num, .ast (.num n) => return .ast (.num n)
  | .num, .ast (.char c) => return .ast (.num c.toNat)
  | .num, .comm c => return .ast (.num c)
  | .num, v => throw s!"expected char, num, or comm value, got\n  {v.toString}"
  | .char, .ast (.char c) => return .ast (.char c)
  | .char, .ast (.num n) => 
    if h : isValidChar n.toUInt32 then
      return .ast (.char ⟨n.toUInt32, h⟩)
    else 
      throw s!"{n.toUInt32} is not a valid char value"
  | .char, v => throw s!"expected char or num value, got\n  {v.toString}"

-- partial def Expr.evalOp₂ (op : Op₂) (v₁ v₂ : Value) : Except String Value := match op, v₁, v₂ with
--   | .cons, v₁, v₂ => return .ast (.cons v₁ v₂)
--   | _, _, _ => _

partial def Expr.eval (env : Env := default) : Expr → Except String Value
  | .lit l => return .ast l.toAST
  | .sym n => match env.find? n with
    | some v => v.get
    | none => throw s!"{n} not found"
  | .env => throw "TODO env"--return .env $ env.node.fold (fun acc k v => (k, v) :: acc) []
  | .if x y z => do match ← x.eval env with
    | .ast (.sym "T") => y.eval env
    | _ => z.eval env
  | .app₀ fn => do match ← fn.eval env with
    | e@(.env _) => return e
    | l@(.lam ..) => return l
    | _ => throw "invalid 0-arity app"
  | .app fn arg => do match ← fn.eval env with
    | .fun n env' body => body.eval (env'.insert n (arg.eval env))
    | _ => throw "lambda was expected"
  | .op₁ op e => do evalOp₁ op (← e.eval env)
  | .op₂ op e₁ e₂ => match op with
    | .add => return .ast $ .num $ (← (← e₁.eval env).num!) + (← (← e₂.eval env).num!)
    | .sub => return .ast $ .num $ (← (← e₁.eval env).num!) - (← (← e₂.eval env).num!)
    | .mul => return .ast $ .num $ (← (← e₁.eval env).num!) * (← (← e₂.eval env).num!)
    | .numEq => return match (← (← e₁.eval env).num!) == (← (← e₂.eval env).num!) with
      | true => .ast (.sym "T")
      | false => .ast .nil
    | _ => throw "TODO op₂"
  | .lam s e => return .fun s env e
  | .let s v b => b.eval (env.insert s (v.eval env))
  | .letrec s v b => do
    let v' : Expr := .letrec s v v
    let env' := env.insert s $ .mk fun _ => eval env v'
    b.eval (env.insert s (eval env' v))
  | .quote x => return .ast x

end Lurk.Evaluation
