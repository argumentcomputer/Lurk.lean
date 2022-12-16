import Lurk.Backend.Expr

namespace Lurk.Backend

set_option genSizeOfSpec false in
mutual

inductive Env
  | mk : Lean.RBNode String (fun _ => Thunk (Except String Value)) → Env

inductive Value where
  | num  : Fin N  → Value
  | u64  : UInt64 → Value
  | char : Char   → Value
  | str  : String → Value
  | sym  : String → Value
  | comm  : F → Value
  | «fun» : String → Env → Expr → Value
  | cons : Value  → Value → Value
  deriving Inhabited

end

namespace Value

@[match_pattern] def t   := Value.sym "T"
@[match_pattern] def nil := Value.sym "NIL"

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
  | `(value| $i:ident) => mkAppM ``Value.sym #[mkStrLit i.getId.toString]
  | `(value| $c:char) => do
    mkAppM ``Value.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(value| $n:num) => do
    mkAppM ``Value.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(value| $s:str) => do
    mkAppM ``Value.str #[mkStrLit s.getString]
  | `(value| ($v₁:value . $v₂:value)) => do
    mkAppM ``Value.cons #[← elabValue v₁, ← elabValue v₂]
  | `(value| ($vs:value*)) => do
    vs.foldrM (init := mkConst ``Value.nil) fun v acc => do
      mkAppM ``Value.cons #[← elabValue v, acc]
  | _ => throwUnsupportedSyntax

scoped elab "⦃" v:value "⦄" : term =>
  elabValue v

partial def telescopeCons (acc : Array Value := #[]) : Value → Array Value × Value
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

partial def toString : Value → String
  | .num x | .sym x => ToString.toString x
  | .u64 x => s!"{x}u64"
  | .char c => s!"#\\{c}"
  | .str s => s!"\"{s}\""
  | v@(.cons ..) => match v.telescopeCons with
    | (#[], .nil) => "NIL"
    | (vs, v) =>
      let vs := vs.data.map toString |> " ".intercalate
      match v with
      | .nil => "(" ++ vs ++ ")"
      | _ => s!"({vs} . {v.toString})"
  | .comm c => s!"<comm {c.asHex}>"
  | .fun n .. => s!"<fun ({n})>"

def ofDatum : Datum → Value
  | .num  x => .num  x
  | .u64  x => .u64  x
  | .char x => .char x
  | .str  x => .str  x
  | .sym  x => .sym  x
  | .cons x y => .cons (ofDatum x) (ofDatum y)

def ofAtom : Atom → Value
  | .t      => .sym "T"
  | .nil    => .sym "NIL"
  | .num  x => .num  x
  | .u64  x => .u64  x
  | .char x => .char x
  | .str  x => .str  x

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
  | .num    x, .num    y => x == y
  | .u64    x, .u64    y => x == y
  | .char   x, .char   y => x == y
  | .str    x, .str    y => x == y
  | .sym    x, .sym    y => x == y
  | .cons x y, .cons w z => x.beq w && y.beq z
  | .comm c₁,  .comm c₂  => c₁ == c₂
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ => ns₁ == ns₂ && env₁.eq env₂ && e₁ == e₂
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

instance : Coe Bool Value where coe
  | true  => .t
  | false => .nil

instance : Coe Char Value := ⟨.char⟩

instance : Coe String Value := ⟨.str⟩

instance : OfNat Value n where
  ofNat := .num (.ofNat n)

def numAdd : Value → Value → Result
  | .num x, .num y => return .num (x + y)
  | .u64 x, .u64 y => return .u64 (x + y)
  | .num x, .u64 y => return .num (x + (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) + y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numSub : Value → Value → Result
  | .num x, .num y => return .num (x - y)
  | .u64 x, .u64 y => return .u64 (x - y)
  | .num x, .u64 y => return .num (x - (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) - y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMul : Value → Value → Result
  | .num x, .num y => return .num (x * y)
  | .u64 x, .u64 y => return .u64 (x * y)
  | .num x, .u64 y => return .num (x * (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) * y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numDiv : Value → Value → Result
  | .num x, .num y => return .num (x / y)
  | .u64 x, .u64 y => return .u64 (x / y)
  | .num x, .u64 y => return .num (x / (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) / y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numEq : Value → Value → Result
  | .num x, .num y => return decide (x == y)
  | .u64 x, .u64 y => return decide (x == y)
  | .num x, .u64 y => return decide (x == (.ofNat y.toNat))
  | .u64 x, .num y => return decide ((.ofNat x.toNat) == y)
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLt : Value → Value → Result
  | .num x, .num y => return F.lt x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.lt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.lt (.ofNat x.toNat) y
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGt : Value → Value → Result
  | .num x, .num y => return F.gt x y
  | .u64 x, .u64 y => return decide (x > y)
  | .num x, .u64 y => return F.gt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.gt (.ofNat x.toNat) y
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLe : Value → Value → Result
  | .num x, .num y => return F.le x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.le x (.ofNat y.toNat)
  | .u64 x, .num y => return F.le (.ofNat x.toNat) y
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGe : Value → Value → Result
  | .num x, .num y => return F.ge x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.ge x (.ofNat y.toNat)
  | .u64 x, .num y => return F.ge (.ofNat x.toNat) y
  | v₁, v₂ => throw s!"expected numeric values, got\n  {v₁} and {v₂}"

def Expr.evalOp₁ : Op₁ → Value → Result
  | .atom, .cons .. => return .nil
  | .atom, _ => return .t
  | .car, .cons car _ => return car
  | .car, (.str ⟨[]⟩) => return .nil
  | .car, (.str ⟨h::_⟩) => return (.char h)
  | .car, v => throw s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, (.str ⟨[]⟩) => return (.str "")
  | .cdr, (.str ⟨_::t⟩) => return (.str ⟨t⟩)
  | .cdr, v => throw s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace v; return v
  | .commit, _ => throw "TODO commit"
  | .comm, ((.num n)) => return .comm n
  | .comm, v => throw s!"expected a num, got\n  {v}"
  | .open, _ => throw "TODO open"
  | .num, x@((.num _)) => return x
  | .num, (.u64 n) => return (.num (.ofNat n.toNat))
  | .num, (.char c) => return .num (.ofNat c.toNat)
  | .num, .comm c => return (.num c)
  | .num, v => throw s!"expected char, num, u64, or comm value, got\n  {v}"
  | .u64, x@((.u64 _)) => return x
  | .u64, (.num n) => return (.u64 (.ofNat n.val))
  | .u64, v => throw s!"expected num or u64, got\n  {v}"
  | .char, (.char c) => return (.char c)
  | .char, (.num ⟨n, _⟩) =>
    let charVal := n.toUInt32
    if h : isValidChar charVal then return (.char ⟨charVal, h⟩)
    else throw s!"{charVal} is not a valid char value"
  | .char, v => throw s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ : Op₂ → Value → Value → Result
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, (.char c), (.str s) => return (.str ⟨c :: s.data⟩)
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

partial def Expr.eval (env : Env := default) : Expr → Result
  | .atom a => return .ofAtom a
  | .sym n => match env.find? n with
    | some v => v.get
    | none => throw s!"{n} not found"
  | .env =>
    env.toArray.foldrM (init := .nil)
      fun (k, v) acc => return .cons (.cons (.sym k) (← v.get)) acc
  | .begin x (atom .nil) => x.eval env
  | .begin x y => do discard $ x.eval env; y.eval env
  | .if x y z => do match ← x.eval env with
    | .nil => z.eval env
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
  | .quote d => return .ofDatum d

end Lurk.Backend
