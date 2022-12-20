import Lurk.Backend.Expr
import Std.Data.RBMap

namespace Lurk.Backend

set_option genSizeOfSpec false in
mutual

inductive Frames
  | mk : List (Expr × Env) → Frames

inductive Env
  | mk : Lean.RBNode String
    (fun _ => Thunk (Except (String × Frames) Value)) → Env

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

declare_syntax_cat                        value
scoped syntax ident                     : value
scoped syntax char                      : value
scoped syntax num                       : value
scoped syntax str                       : value
scoped syntax "(" value " . " value ")" : value
scoped syntax "(" value+ ")"            : value

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

abbrev Result := Except (String × Frames) Value

namespace Env

def find? (s : String) : Env → Option (Thunk Result)
  | mk e => e.find compare s

def insert (s : String) (v : Thunk Result) : Env → Env
  | mk e => mk $ e.insert compare s v

def toArray : Env → Array (String × (Thunk Result))
  | mk e => e.fold (init := #[]) fun acc k v => acc.push (k, v)

def toRBMap : Env → Std.RBMap String (Thunk Result) compare
  | mk e => e.fold (init := default) fun acc k v => acc.insert k v

end Env

def Frames.toString : Frames → String
  | .mk frames => sorry

instance : ToString Frames := ⟨Frames.toString⟩

#exit

mutual

partial def Env.eq (e₁ e₂ : Env) : Bool :=
  let rec aux : List (String × Result) → List (String × Result) → Bool
    | [], [] => true
    | (s₁, v₁)::xs, (s₂, v₂)::ys => match (v₁, v₂) with
      | (Except.ok v₁, Except.ok v₂) => v₁.beq v₂ && s₁ == s₂ && aux xs ys
      | (Except.error (e₁, _), Except.error (e₂, _)) =>
        e₁ == e₂  && s₁ == s₂ && aux xs ys
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

def error (e : Expr) (frames : Frames) (msg : String) : Result :=
  throw (s!"Error when evaluating {e}:\n{msg}", frames)

def numAdd (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return .num (x + y)
  | .u64 x, .u64 y => return .u64 (x + y)
  | .num x, .u64 y => return .num (x + (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) + y)
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numSub (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return .num (x - y)
  | .u64 x, .u64 y => return .u64 (x - y)
  | .num x, .u64 y => return .num (x - (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) - y)
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMul (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return .num (x * y)
  | .u64 x, .u64 y => return .u64 (x * y)
  | .num x, .u64 y => return .num (x * (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) * y)
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numDiv (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return .num (x / y)
  | .u64 x, .u64 y => return .u64 (x / y)
  | .num x, .u64 y => return .num (x / (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) / y)
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numEq (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return decide (x == y)
  | .u64 x, .u64 y => return decide (x == y)
  | .num x, .u64 y => return decide (x == (.ofNat y.toNat))
  | .u64 x, .num y => return decide ((.ofNat x.toNat) == y)
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLt (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return F.lt x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.lt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.lt (.ofNat x.toNat) y
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGt (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return F.gt x y
  | .u64 x, .u64 y => return decide (x > y)
  | .num x, .u64 y => return F.gt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.gt (.ofNat x.toNat) y
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLe (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return F.le x y
  | .u64 x, .u64 y => return decide (x <= y)
  | .num x, .u64 y => return F.le x (.ofNat y.toNat)
  | .u64 x, .num y => return F.le (.ofNat x.toNat) y
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGe (e : Expr) (frames : Frames) : Value → Value → Result
  | .num x, .num y => return F.ge x y
  | .u64 x, .u64 y => return decide (x >= y)
  | .num x, .u64 y => return F.ge x (.ofNat y.toNat)
  | .u64 x, .num y => return F.ge (.ofNat x.toNat) y
  | v₁, v₂ => error e frames s!"expected numeric values, got\n  {v₁} and {v₂}"

def Expr.evalOp₁ (e : Expr) (frames : Frames) : Op₁ → Value → Result
  | .atom, .cons .. => return .nil
  | .atom, _ => return .t
  | .car, .cons car _ => return car
  | .car, .str ⟨[]⟩ => return .nil
  | .car, .str ⟨h::_⟩ => return .char h
  | .car, v => error e frames s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, .str ⟨[]⟩ => return .str ""
  | .cdr, .str ⟨_::t⟩ => return .str ⟨t⟩
  | .cdr, v => error e frames s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace v; return v
  | .commit, v => return .u64 v.toString.hash
  | .comm, .num n => return .comm n
  | .comm, v => error e frames s!"expected a num, got\n  {v}"
  | .open, _ => error e frames "TODO open"
  | .num, x@(.num _) => return x
  | .num, .u64 n => return .num (.ofNat n.toNat)
  | .num, .char c => return .num (.ofNat c.toNat)
  | .num, .comm c => return .num c
  | .num, v => error e frames s!"expected char, num, u64, or comm value, got\n  {v}"
  | .u64, x@(.u64 _) => return x
  | .u64, .num n => return .u64 (.ofNat n.val)
  | .u64, v => error e frames s!"expected num or u64, got\n  {v}"
  | .char, .char c => return .char c
  | .char, .num ⟨n, _⟩ =>
    let charVal := n.toUInt32
    if h : isValidChar charVal then return .char ⟨charVal, h⟩
    else error e frames s!"{charVal} is not a valid char value"
  | .char, v => error e frames s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ (e : Expr) (frames : Frames) : Op₂ → Value → Value → Result
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .char c, .str s => return .str ⟨c :: s.data⟩
  | .strcons, v₁, v₂ => error e frames s!"expected char and string value, got {v₁} and {v₂}"
  | .add, v₁, v₂ => numAdd e frames v₁ v₂
  | .sub, v₁, v₂ => numSub e frames v₁ v₂
  | .mul, v₁, v₂ => numMul e frames v₁ v₂
  | .div, v₁, v₂ => numDiv e frames v₁ v₂
  | .numEq, v₁, v₂ => numEq e frames v₁ v₂
  | .lt, v₁, v₂ => numLt e frames v₁ v₂
  | .gt, v₁, v₂ => numGt e frames v₁ v₂
  | .le, v₁, v₂ => numLe e frames v₁ v₂
  | .ge, v₁, v₂ => numGe e frames v₁ v₂
  | .eq, v₁, v₂ => return v₁.beq v₂
  | .hide, _, _ => error e frames "TODO hide"

partial def Expr.eval
    (e : Expr) (env : Env := default) (frames : Frames := .mk []) : Result :=
  let frames := match frames with | .mk frames => .mk $ (e, env) :: frames
  match e with
  | .atom a => return .ofAtom a
  | .sym n => match env.find? n with
    | some v => v.get
    | none => error e frames s!"{n} not found"
  | .env =>
    env.toArray.foldrM (init := .nil)
      fun (k, v) acc => return .cons (.cons (.sym k) (← v.get)) acc
  | .begin x (atom .nil) => x.eval env frames
  | .begin x y => do discard $ x.eval env frames; y.eval env frames
  | .if x y z => do match ← x.eval env frames with
    | .nil => z.eval env frames
    | _ => y.eval env frames
  | .app₀ fn => do match ← fn.eval env frames with
    | .fun "_" env' body => body.eval env' frames
    | _ => error e frames s!"error evaluating\n{fn}\ninvalid 0-arity app"
  | .app fn arg => do match ← fn.eval env frames with
    | .fun "_" .. => error e frames s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun n env' body => body.eval (env'.insert n (arg.eval env frames)) frames
    | x => error e frames s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"
  | x@(.op₁ op e) => do evalOp₁ x frames op (← e.eval env frames)
  | x@(.op₂ op e₁ e₂) => do evalOp₂ x frames op (← e₁.eval env frames) (← e₂.eval env frames)
  | .lambda s e => return .fun s env e
  | .let s v b => b.eval (env.insert s (v.eval env frames)) frames
  | .letrec s v b => do
    let v' : Expr := .letrec s v v
    let env' := env.insert s $ .mk fun _ => v'.eval env frames
    b.eval (env.insert s (v.eval env' frames)) frames
  | .quote d => return .ofDatum d

end Lurk.Backend
