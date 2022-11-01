import Lean
import Lurk.Evaluation2.Expr

namespace Lurk.Evaluation

mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Value) → Env

inductive Value where
  | lit : Lit → Value
  | lam : List String → Env → Expr → Value
  | env : List (String × Value) → Value
  | ast : Syntax.AST → Value
  deriving Inhabited

end

partial def Value.toString : Value → String
  | .lit l => l.toString
  | .ast x => ToString.toString x
  | .env l =>
    if l.isEmpty then "NIL"
    else "(" ++ " ".intercalate (l.map fun (s, v) => s!"({s} . {v.toString})") ++ ")"
  | .lam ns .. => s!"<FUNCTION {ns}>"


instance : Inhabited Env := ⟨.mk .leaf⟩

namespace Env

def find? (s : String) : Env → Option (Value)
  | mk e => e.find compare s

def insert (s : String) (v : Value) : Env → Env
  | mk e => mk $ e.insert compare s v

def node : Env → Lean.RBNode String (fun _ => Value)
  | mk e => e

def toList : Env → List (String × Value)
  | mk e => e.fold (init := []) fun acc k v => (k, v) :: acc

end Env

mutual

partial def Env.eqAux : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (s₁, v₁)::xs, (s₂, v₂)::ys => s₁ == s₂ && v₁.eq v₂ && Env.eqAux xs ys
  | _, _ => false

partial def Env.eq (e₁ e₂ : Env) : Bool :=
  Env.eqAux e₁.toList e₂.toList

partial def Value.eq : Value → Value → Bool
  | .lit l₁, .lit l₂ => l₁ == l₂
  | .lam ns₁ env₁ e₁, .lam ns₂ env₂ e₂ =>
    ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | .ast x, .ast y => x == y
  | .env e₁, .env e₂ => Env.eqAux e₁ e₂
  | _, _ => false

end

partial def Expr.eval (env : Env := default) : Expr → Except String Value
  | .lit l => return .lit l
  | .sym n => match env.find? n with
    | some v => return v
    | none => throw s!"{n} not found"
  | .env => return .env $ env.node.fold (fun acc k v => (k, v) :: acc) []
  | .if x y z => do match ← x.eval env with
    | .lit .t => y.eval env
    | _ => z.eval env
  | .app₀ fn => do match ← fn.eval env with
    | e@(.env _) => return e
    | l@(.lam ..) => return l
    | _ => throw "invalid 0-arity app"
  | .app fn arg => do match ← fn.eval env with
    | .lam [] .. => throw "too many arguments"
    | .lam [n] env' body => body.eval (env'.insert n (← arg.eval env))
    | .lam (n :: ns) env' body =>
      return .lam ns (env'.insert n (← arg.eval env)) body
    | _ => throw "lambda was expected"
  | .op₁ op e => throw "TODO op₁"
  | .op₂ op e₁ e₂ => throw "TODO op₂"
  | .lam s e => return .lam [s] default e
  | .let s v b => do
    let v ← v.eval env
    b.eval (env.insert s v)
  | .letrec s v b => throw "TODO letrec"
  | .quote x => return .ast x

end Lurk.Evaluation
