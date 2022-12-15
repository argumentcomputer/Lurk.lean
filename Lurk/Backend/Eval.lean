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

/- The following metaprogramming layer is merely for testing -/

declare_syntax_cat                      value
scoped syntax ident                   : value
scoped syntax char                    : value
scoped syntax num                     : value
scoped syntax str                     : value
scoped syntax "(" value "." value ")" : value
scoped syntax "(" value+ ")"          : value

open Lean Meta Elab Term in
partial def elabValue : Lean.TSyntax `value → TermElabM Lean.Expr
  | `(value| $i:ident) => mkAppM ``Value.sym #[mkStrLit i.getId.toString.toUpper]
  | `(value| $c:char) => do
    mkAppM ``Value.atom #[← mkAppM ``Atom.char
      #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]]
  | `(value| $n:num) => do
    mkAppM ``Value.atom
      #[← mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]]
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

@[inline] def consWith (vs : Array Value) (v : Value := .atom .nil) : Value :=
  vs.foldr .cons v

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

partial def Env.eq (e₁ e₂ : Env) : Bool :=
  let rec aux : List (String × Result) → List (String × Result) → Bool
    | [], [] => true
    | (s₁, v₁)::xs, (s₂, v₂)::ys => match (v₁, v₂) with
      | (Except.ok    v₁, Except.ok    v₂) => v₁.beq v₂ && s₁ == s₂ && aux xs ys
      | (Except.error e₁, Except.error e₂) => e₁ == e₂  && s₁ == s₂ && aux xs ys
      | _ => false
    | _, _ => false
  aux
    (e₁.toArray.data.map fun (s, v) => (s, v.get))
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

instance : Coe Bool Value where coe
  | true  => .atom .t
  | false => .atom .nil

instance : Coe Char Value where
  coe c := .atom (.char c)

instance : Coe String Value where
  coe c := .atom (.str c)

instance : OfNat Value n where
  ofNat := .atom $ .num (.ofNat n)

def numAdd : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return .atom $ .num (x + y)
  | .atom $ .u64 x, .atom $ .u64 y => return .atom $ .u64 (x + y)
  | .atom $ .num x, .atom $ .u64 y => return .atom $ .num (x + (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return .atom $ .num ((.ofNat x.toNat) + y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numSub : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return .atom $ .num (x - y)
  | .atom $ .u64 x, .atom $ .u64 y => return .atom $ .u64 (x - y)
  | .atom $ .num x, .atom $ .u64 y => return .atom $ .num (x - (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return .atom $ .num ((.ofNat x.toNat) - y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMul : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return .atom $ .num (x * y)
  | .atom $ .u64 x, .atom $ .u64 y => return .atom $ .u64 (x * y)
  | .atom $ .num x, .atom $ .u64 y => return .atom $ .num (x * (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return .atom $ .num ((.ofNat x.toNat) * y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numDiv : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return .atom $ .num (x / y)
  | .atom $ .u64 x, .atom $ .u64 y => return .atom $ .u64 (x / y)
  | .atom $ .num x, .atom $ .u64 y => return .atom $ .num (x / (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return .atom $ .num ((.ofNat x.toNat) / y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numEq : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return decide (x == y)
  | .atom $ .u64 x, .atom $ .u64 y => return decide (x == y)
  | .atom $ .num x, .atom $ .u64 y => return decide (x == (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return decide ((.ofNat x.toNat) == y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLt : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return decide (x < y)
  | .atom $ .u64 x, .atom $ .u64 y => return decide (x < y)
  | .atom $ .num x, .atom $ .u64 y => return decide (x < (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return decide ((.ofNat x.toNat) < y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGt : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return decide (x > y)
  | .atom $ .u64 x, .atom $ .u64 y => return decide (x > y)
  | .atom $ .num x, .atom $ .u64 y => return decide (x > (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return decide ((.ofNat x.toNat) > y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLe : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return decide (x <= y)
  | .atom $ .u64 x, .atom $ .u64 y => return decide (x <= y)
  | .atom $ .num x, .atom $ .u64 y => return decide (x <= (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return decide ((.ofNat x.toNat) <= y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGe : Value → Value → Result
  | .atom $ .num x, .atom $ .num y => return decide (x >= y)
  | .atom $ .u64 x, .atom $ .u64 y => return decide (x >= y)
  | .atom $ .num x, .atom $ .u64 y => return decide (x >= (.ofNat y.toNat))
  | .atom $ .u64 x, .atom $ .num y => return decide ((.ofNat x.toNat) >= y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

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
  | .comm, (.atom (.num n)) => return .comm n
  | .comm, v => throw s!"expected a num, got\n  {v}"
  | .open, _ => throw "TODO open"
  | .num, x@(.atom (.num _)) => return x
  | .num, .atom (.u64 n) => return .atom (.num (.ofNat n.toNat))
  | .num, .atom (.char c) => return .atom $ .num (.ofNat c.toNat)
  | .num, .comm c => return .atom (.num c)
  | .num, v => throw s!"expected char, num, u64, or comm value, got\n  {v}"
  | .u64, x@(.atom (.u64 _)) => return x
  | .u64, .atom (.num n) => return .atom (.u64 (.ofNat n.val))
  | .u64, v => throw s!"expected num or u64, got\n  {v}"
  | .char, .atom (.char c) => return .atom (.char c)
  | .char, .atom (.num ⟨n, _⟩) =>
    let charVal := n.toUInt32
    if h : isValidChar charVal then return .atom (.char ⟨charVal, h⟩)
    else throw s!"{charVal} is not a valid char value"
  | .char, v => throw s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ : Op₂ → Value → Value → Result
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .atom (.char c), .atom (.str s) => return .atom (.str ⟨c :: s.data⟩)
  | .strcons, v₁, v₂ => throw s!"expected char and string value, got {v₁} and {v₂}"
  | .add, v₁, v₂ => numAdd v₁ v₂
  | .sub, v₁, v₂ => numSub v₁ v₂
  | .mul, v₁, v₂ => numMul v₁ v₂
  | .div, v₁, v₂ => numDiv v₁ v₂
  | .numEq, v₁, v₂ => numEq v₁ v₂
  | .lt, v₁, v₂ => numLt v₁ v₂
  | .gt, v₁, v₂ => numGt v₁ v₂
  | .le, v₁, v₂ => numLe v₁ v₂
  | .ge, v₁, v₂ => numGe v₁ v₂
  | .eq, v₁, v₂ => return v₁.beq v₂
  | .hide, _, _ => throw "TODO hide"

partial def Expr.asValue : Expr → Value
  | .atom a => .atom a
  | .sym s => .sym s
  | .env => .consWith #[.sym "CURRENT-ENV"]
  | .op₁ o e => .consWith #[.sym o.toString, e.asValue]
  | .op₂ o e₁ e₂ => .consWith #[.sym o.toString, e₁.asValue, e₂.asValue]
  | e@(.begin ..) =>
    .consWith $ #[Value.sym "BEGIN"] ++ (e.telescopeBegin.map asValue)
  | .if a b c => .consWith #[.sym "IF", a.asValue, b.asValue, c.asValue]
  | .app₀ e => .consWith #[e.asValue]
  | .app f a => .consWith ⟨(f.telescopeApp [a]).map asValue⟩
  | .lambda s b =>
    let (ss, b) := b.telescopeLam #[s]
    .consWith #[.sym "LAMBDA", .consWith $ ss.map Value.sym, b.asValue]
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    let bs := bs.map fun (s, v) => .consWith #[.sym s, v.asValue]
    .consWith #[.sym "LET", .consWith bs, b.asValue]
  | .letrec s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    let bs := bs.map fun (s, v) => .consWith #[.sym s, v.asValue]
    .consWith #[.sym "LETREC", .consWith bs, b.asValue]
  | .quote e => .consWith #[.sym "QUOTE", e.asValue]

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
  | .quote e => return e.asValue

end Lurk.Backend
