import Lurk.Field
import Std.Data.RBMap

namespace Lurk

inductive Tag
  | nil | cons | sym | «fun» | num | thunk
  | str | strCons | strNil | char | comm
  deriving Ord, BEq, Inhabited, Hashable

def Tag.toString : Tag → String
  | nil     => "nil"
  | cons    => "cons"
  | sym     => "sym"
  | .fun    => "fun"
  | num     => "num"
  | thunk   => "thunk"
  | str     => "str"
  | strCons => "strCons"
  | strNil  => "strNil"
  | char    => "char"
  | comm    => "comm"

instance : ToString Tag := ⟨Tag.toString⟩

def Tag.toF : Tag → F
  | nil     => .ofNat 0
  | cons    => .ofNat 1
  | sym     => .ofNat 2
  | .fun    => .ofNat 3
  | num     => .ofNat 4
  | thunk   => .ofNat 5
  | str     => .ofNat 6
  | strCons => .ofNat 7
  | strNil  => .ofNat 8
  | char    => .ofNat 9
  | comm    => .ofNat 10

inductive ContTag
  | outermost | call₀ | call | callnext | tail | error | lookup | op₁ | op₂
  | op₂next | «if» | «let» | letrec | dummy | terminal | emit
  deriving Ord, BEq, Inhabited, Hashable

def ContTag.toString : ContTag → String
  | outermost => "outermost" 
  | call₀ => "call₀" 
  | call => "call" 
  | callnext => "callnext" 
  | tail => "tail" 
  | error => "error" 
  | lookup => "lookup" 
  | op₁ => "op₁" 
  | op₂ => "op₂"
  | op₂next => "op₂next" 
  | «if» => "if" 
  | «let» => "let" 
  | letrec => "letrec" 
  | dummy => "dummy" 
  | terminal => "terminal" 
  | emit => "emit"

instance : ToString ContTag := ⟨ContTag.toString⟩

def ContTag.toUSize : ContTag → USize
  | outermost => Nat.toUSize 0 
  | call₀ => Nat.toUSize 1 
  | call => Nat.toUSize 2
  | callnext => Nat.toUSize 3
  | tail => Nat.toUSize 4
  | error => Nat.toUSize 5
  | lookup => Nat.toUSize 6
  | op₁ => Nat.toUSize 7
  | op₂ => Nat.toUSize 8
  | op₂next => Nat.toUSize 9
  | «if» => Nat.toUSize 10
  | «let» => Nat.toUSize 11
  | letrec => Nat.toUSize 12
  | dummy => Nat.toUSize 13
  | terminal => Nat.toUSize 14
  | emit => Nat.toUSize 15

namespace Hashing

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, BEq, Inhabited, Hashable

def ScalarPtr.toString : ScalarPtr → String
  | ⟨.num, n⟩ => s!"(num, {n.asHex})"
  | ⟨.char, val⟩ => s!"(char, \'{Char.ofNat val}\')"
  | ⟨tag, val⟩ => s!"({tag}, Scalar({val.asHex}))"

instance : ToString ScalarPtr := ⟨ScalarPtr.toString⟩

inductive ScalarExpr
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | comm (x : F) (ptr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | «fun» (arg : ScalarPtr) (body : ScalarPtr) (env : ScalarPtr)
  | num (val : F)
  | str (strCons : ScalarPtr)
  | strCons (head : ScalarPtr) (tail : ScalarPtr)
  | strNil
  | char (x : F)
  deriving BEq

def ScalarExpr.toString : ScalarExpr → String
  | .cons car cdr => s!"Cons({car}, {cdr})"
  | .comm x   ptr => s!"Comm({x}, {ptr})"
  | .sym ptr => s!"Sym({ptr})"
  | .fun arg body env => s!"Fun({arg}, {body}, {env})"
  | .num x => s!"Num({x.asHex})"
  | .str x => s!"Str({x})"
  | .strCons head tail => s!"StrCons({head}, {tail})"
  | .strNil => "StrNil"
  | .char x => s!"Char({x})"

instance : ToString ScalarExpr := ⟨ScalarExpr.toString⟩

open Std (RBMap) in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  comms : RBMap F ScalarPtr compare
  deriving Inhabited, BEq

def ScalarStore.toString (s : ScalarStore) : String :=
  let body := ",\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"  {k}: {v}"
  let exprs := "scalar_store: {\n" ++ body ++ "\n}"
  let body := ",\n".intercalate $ s.comms.toList.map fun (k, v) => s!"  {k}: {v}"
  let comms := "comm_store: {\n" ++ body ++ "\n}"
  exprs ++ "\n" ++ comms

instance : ToString ScalarStore := ⟨ScalarStore.toString⟩

def ScalarStore.ofList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore :=
  ⟨.ofList exprs _, default⟩

end Hashing
end Lurk
