import Lean
import Lurk.Evaluation.Expr

namespace Lurk.Evaluation

set_option genSizeOfSpec false in
mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Thunk (Except String Value)) → Env

inductive Value where
  | lit : Lit → Value
  | lam : String → Env → Expr → Value
  | env : List (String × Value) → Value
  | ast : Syntax.AST → Value
  deriving Inhabited

end

abbrev Result := Except String Value

partial def Value.toString : Value → String
  | .lit l => l.toString
  | .ast x => ToString.toString x
  | .env l =>
    if l.isEmpty then "NIL"
    else
      let pairs := " ".intercalate (l.map fun (s, v) => s!"({s} . {v.toString})")
      s!"({pairs})"
  | .lam n .. => s!"<λ{n}>"

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
  | .lit l₁, .lit l₂ => l₁ == l₂
  | .lam ns₁ env₁ e₁, .lam ns₂ env₂ e₂ =>
    ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | .ast x, .ast y => x == y
  -- | .env e₁, .env e₂ => Env.eqAux e₁ e₂
  | _, _ => false

end

def Value.num! : Value → Except String (Fin N)
  | .lit (.num x) => pure x
  | v => throw s!"expected numerical value, got\n {v.toString}"

partial def Expr.eval (env : Env := default) : Expr → Except String Value
  | .lit l => return .lit l
  | .sym n => match env.find? n with
    | some v => v.get
    | none => throw s!"{n} not found"
  | .env => throw "TODO env"--return .env $ env.node.fold (fun acc k v => (k, v) :: acc) []
  | .if x y z => do match ← x.eval env with
    | .lit .t => y.eval env
    | _ => z.eval env
  | .app₀ fn => do match ← fn.eval env with
    | e@(.env _) => return e
    | l@(.lam ..) => return l
    | _ => throw "invalid 0-arity app"
  | .app fn arg => do match ← fn.eval env with
    | .lam n env' body => body.eval (env'.insert n (arg.eval env))
    | _ => throw "lambda was expected"
  | .op₁ op e => throw "TODO op₁"
  | .op₂ op e₁ e₂ => match op with
    | .add => return .lit $ .num $ (← (← e₁.eval env).num!) + (← (← e₂.eval env).num!)
    | .sub => return .lit $ .num $ (← (← e₁.eval env).num!) - (← (← e₂.eval env).num!)
    | .mul => return .lit $ .num $ (← (← e₁.eval env).num!) * (← (← e₂.eval env).num!)
    | .numEq => return match (← (← e₁.eval env).num!) == (← (← e₂.eval env).num!) with
      | true => .lit .t
      | false => .lit .nil
    | _ => throw "TODO op₂"
  | .lam s e => return .lam s env e
  | .let s v b => b.eval (env.insert s (v.eval env))
  | .letrec s v b => do
    let v' : Expr := .letrec s v v
    let env' := env.insert s $ .mk fun _ => eval env v'
    b.eval (env.insert s (eval env' v))
  | .quote x => return .ast x

end Lurk.Evaluation
