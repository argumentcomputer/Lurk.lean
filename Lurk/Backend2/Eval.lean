import Lurk.Backend2.Expr
import Lurk.Backend2.ExprUtils
import Lurk.Backend2.LDON
import Std.Data.RBMap

namespace Lurk.Backend2

-- structure EvalContext where
--   recr : Option String

structure EvalError where
  err : String

structure EvalState where
  hashState : LDONHashState

-- set_option genSizeOfSpec false in
mutual

inductive EnvImg
  | mk : Bool → Value → EnvImg

inductive Env 
  | mk : Lean.RBNode String (fun _ => EnvImg) → Env

inductive Value where
  | num  : Fin N  → Value
  | u64  : UInt64 → Value
  | char : Char   → Value
  | str  : String → Value
  | sym  : String → Value
  | comm  : F → Value
  | «fun» : String → Env → Expr → Value
  | cons : Value  → Value → Value
  | exception : String → Value
  deriving Inhabited

end

def EnvImg.recr : EnvImg → Bool
  | .mk recr _ => recr

def EnvImg.value : EnvImg → Value
  | .mk _ value => value

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
  | .exception e => s!"<EXCEPTION: {e}>"

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

abbrev EvalM := EStateM String EvalState

-- @[inline] def EnvImg.toEvalM : EnvImg → EvalM Value
--   | .thunk v => match v.get with
--     | .exception e => throw e
--     | res => pure res
--   | .value v => pure v

namespace Env

def find? (s : String) : Env → Option EnvImg
  | mk e => e.find compare s

def insert (s : String) (v : EnvImg) : Env → Env
  | mk e => mk $ e.insert compare s v

def toArray : Env → Array (String × EnvImg)
  | mk e => e.fold (init := #[]) fun acc k v => acc.push (k, v)

def toList : Env → List (String × EnvImg)
  | mk e => e.fold (init := []) fun acc k v => (k, v) :: acc

end Env

mutual

partial def EnvImg.beq : EnvImg → EnvImg → EvalM Bool
  | .mk r₁ v₁, .mk r₂ v₂ => return r₁ == r₂ && (← v₁.beq v₂)

partial def Env.beq (e₁ e₂ : Env) : EvalM Bool :=
  let e := e₁.toList.zip e₂.toList
  e.allM fun ((n₁, v₁), (n₂, v₂)) => return n₁ == n₂ && (← v₁.beq v₂)

partial def Value.beq : Value → Value → EvalM Bool
  | .num    x, .num    y => return x == y
  | .u64    x, .u64    y => return x == y
  | .char   x, .char   y => return x == y
  | .str    x, .str    y => return x == y
  | .sym    x, .sym    y => return x == y
  | .cons x y, .cons w z => return (← x.beq w) && (← y.beq z)
  | .comm c₁,  .comm c₂  => return c₁ == c₂
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ => 
    return ns₁ == ns₂ && (← env₁.beq env₂) && e₁ == e₂
  | .exception e, _ => throw e
  | _, .exception e => throw e
  | _, _ => return false

end

instance : Coe Bool Value where coe
  | true  => .t
  | false => .nil

instance : Coe Char Value := ⟨.char⟩

instance : Coe String Value := ⟨.str⟩

instance : OfNat Value n where
  ofNat := .num (.ofNat n)

def error (e : Expr) (msg : String) : EvalM Value :=
  throw s!"Error when evaluating {e}:\n{msg}"

def numAdd (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x + y)
  | .u64 x, .u64 y => return .u64 (x + y)
  | .num x, .u64 y => return .num (x + (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) + y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numSub (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x - y)
  | .u64 x, .u64 y => return .u64 (x - y)
  | .num x, .u64 y => return .num (x - (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) - y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMul (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x * y)
  | .u64 x, .u64 y => return .u64 (x * y)
  | .num x, .u64 y => return .num (x * (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) * y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numDiv (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x / y)
  | .u64 x, .u64 y => return .u64 (x / y)
  | .num x, .u64 y => return .num (x / (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) / y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMod (e : Expr) : Value → Value → EvalM Value
  | .u64 x, .u64 y => return .u64 (x % y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numEq (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return decide (x == y)
  | .u64 x, .u64 y => return decide (x == y)
  | .num x, .u64 y => return decide (x == (.ofNat y.toNat))
  | .u64 x, .num y => return decide ((.ofNat x.toNat) == y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLt (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.lt x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.lt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.lt (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGt (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.gt x y
  | .u64 x, .u64 y => return decide (x > y)
  | .num x, .u64 y => return F.gt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.gt (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLe (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.le x y
  | .u64 x, .u64 y => return decide (x <= y)
  | .num x, .u64 y => return F.le x (.ofNat y.toNat)
  | .u64 x, .num y => return F.le (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGe (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.ge x y
  | .u64 x, .u64 y => return decide (x >= y)
  | .num x, .u64 y => return F.ge x (.ofNat y.toNat)
  | .u64 x, .num y => return F.ge (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def Expr.evalOp₁ (e : Expr) : Op₁ → Value → EvalM Value
  | .atom, .cons .. => return .nil
  | .atom, _ => return .t
  | .car, .cons car _ => return car
  | .car, .str ⟨[]⟩ => return .nil
  | .car, .str ⟨h::_⟩ => return .char h
  | .car, v => error e s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, .str ⟨[]⟩ => return .str ""
  | .cdr, .str ⟨_::t⟩ => return .str ⟨t⟩
  | .cdr, v => error e s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace v; return v
  | .commit, v => return .u64 v.toString.hash
  | .comm, .num n => return .comm n
  | .comm, v => error e s!"expected a num, got\n  {v}"
  | .open, _ => error e "TODO open"
  | .num, x@(.num _) => return x
  | .num, .u64 n => return .num (.ofNat n.toNat)
  | .num, .char c => return .num (.ofNat c.toNat)
  | .num, .comm c => return .num c
  | .num, v => error e s!"expected char, num, u64, or comm value, got\n  {v}"
  | .u64, x@(.u64 _) => return x
  | .u64, .num n => return .u64 (.ofNat n.val)
  | .u64, v => error e s!"expected num or u64, got\n  {v}"
  | .char, .char c => return .char c
  | .char, .num ⟨n, _⟩ =>
    let charVal := n.toUInt32
    if h : isValidChar charVal then return .char ⟨charVal, h⟩
    else error e s!"{charVal} is not a valid char value"
  | .char, v => error e s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ (e : Expr) : Op₂ → Value → Value → EvalM Value
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .char c, .str s => return .str ⟨c :: s.data⟩
  | .strcons, v₁, v₂ => error e s!"expected char and string value, got {v₁} and {v₂}"
  | .add, v₁, v₂ => numAdd e v₁ v₂
  | .sub, v₁, v₂ => numSub e v₁ v₂
  | .mul, v₁, v₂ => numMul e v₁ v₂
  | .div, v₁, v₂ => numDiv e v₁ v₂
  | .mod, v₁, v₂ => numMod e v₁ v₂
  | .numEq, v₁, v₂ => numEq e v₁ v₂
  | .lt, v₁, v₂ => numLt e v₁ v₂
  | .gt, v₁, v₂ => numGt e v₁ v₂
  | .le, v₁, v₂ => numLe e v₁ v₂
  | .ge, v₁, v₂ => numGe e v₁ v₂
  | .eq, v₁, v₂ => v₁.beq v₂
  | .hide, _, _ => error e "TODO hide"

mutual 

-- partial def suspend (e : Expr) (env : Env) (state : EvalState) : Thunk (Value × EvalState) :=
--   let thunk := { fn := fun _ =>
--     match EStateM.run (e.eval env) state with
--     | .ok a s => a
--     | .error e s => .exception e }
--   thunk

partial def Expr.evalApp₀ (fn : Expr) (env : Env) : EvalM Value := do
  match fn with
  | .sym n =>
    let some ⟨r, v⟩ := env.find? n 
      | error fn s!"{n} not found"
    let .fun "_" fnEnv body := v 
      | error fn s!"error evaluating\n{fn}\ninvalid 0-arity app"
    let fnEnv := if !r then fnEnv else fnEnv.insert n ⟨r, v⟩
    body.eval fnEnv
  | fn =>
    let .fun "_" fnEnv body ← fn.eval env 
      | error fn s!"error evaluating\n{fn}\ninvalid 0-arity app"
    body.eval fnEnv

partial def Expr.evalApp (fn : Expr) (arg : Expr) (env : Env) : EvalM Value := do
  match fn with
  | .sym n =>
    let some ⟨r, v⟩ := env.find? n 
      | error fn s!"{n} not found"
    match v with
    | .fun "_" .. => error fn s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun argname fnEnv body =>
      let fnEnv := if !r then fnEnv else fnEnv.insert n ⟨r, v⟩
      let fnEnv := fnEnv.insert argname ⟨false, ← arg.eval env⟩
      body.eval fnEnv
    | x => error fn s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"
  | fn =>
    match ← fn.eval env with
    | .fun "_" .. => error fn s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun argname fnEnv body =>
      let fnEnv := fnEnv.insert argname ⟨false, ← arg.eval env⟩
      body.eval fnEnv
    | x => error fn s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"

partial def Expr.eval
    (e : Expr) (env : Env := default) : EvalM Value :=
  -- let frames := match frames with | .mk frames => .mk $ (e, env) :: frames
  match e with
  | .atom a => return .ofAtom a
  | .sym n => 
    match env.find? n with
    | some ⟨r, v⟩ => return v
    | none => error e s!"{n} not found"
  | .env =>
    return env.toArray.foldr (init := .nil)
      fun (k, v) acc => .cons (.cons (.sym k) v.value) acc
  | .begin x (.atom .nil) => x.eval env
  | .begin x y => do discard $ x.eval env; y.eval env
  | .if x y z => do match ← x.eval env with
    | .nil => z.eval env
    | _ => y.eval env
  | .app₀ fn    => fn.evalApp₀ env
  | .app fn arg => fn.evalApp arg env
  | x@(.op₁ op e) => do evalOp₁ x op (← e.eval env)
  | x@(.op₂ op e₁ e₂) => do evalOp₂ x op (← e₁.eval env) (← e₂.eval env)
  | .lambda s e => return .fun s env e
  | .let s v b    => do b.eval (env.insert s ⟨false, ← v.eval env⟩)
  | .letrec s v b => do b.eval (env.insert s ⟨true, ← v.eval env⟩)
  | .quote d => return .ofDatum d

end

end Lurk.Backend2
