import Lurk.Arithmetic
import Std.Data.RBMap

namespace Lurk.Hashing

inductive Tag
  | nil | cons | sym | «fun» | num | thunk | str | char | comm
  deriving Ord, BEq, Inhabited

def Tag.toString : Tag → String
  | nil   => "nil"
  | cons  => "cons"
  | sym   => "sym"
  | .fun  => "fun"
  | num   => "num"
  | thunk => "thunk"
  | str   => "str"
  | char  => "char"
  | comm  => "comm"

instance : ToString Tag := ⟨Tag.toString⟩

def Tag.toF : Tag → F
  | .nil   => .ofNat 0
  | .cons  => .ofNat 1
  | .sym   => .ofNat 2
  | .fun   => .ofNat 3
  | .num   => .ofNat 4
  | .thunk => .ofNat 5
  | .str   => .ofNat 6
  | .char  => .ofNat 7
  | .comm  => .ofNat 8

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord, BEq, Inhabited

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
  | strNil
  | strCons (head : ScalarPtr) (tail : ScalarPtr)
  | char (x : F)
  deriving BEq

def ScalarExpr.toString : ScalarExpr → String
  | .cons car cdr => s!"Cons({car}, {cdr})"
  | .comm x   ptr => s!"Comm({x}, {ptr})"
  | .sym ptr => s!"Sym({ptr})"
  | .fun arg body env => s!"Fun({arg}, {body}, {env})"
  | .num x => s!"Num({x.asHex})"
  | .strNil => "StrNil"
  | .strCons head tail => s!"StrCons({head}, {tail})"
  | .char x => s!"Char({x})"

instance : ToString ScalarExpr := ⟨ScalarExpr.toString⟩

open Std (RBMap) in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  comms : RBMap F ScalarPtr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited, BEq

def ScalarStore.toString (s : ScalarStore) : String :=
  let body := ",\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"  {k}: {v}"
  let exprs := "scalar_store: {\n" ++ body ++ "\n}"
  let body := ",\n".intercalate $ s.comms.toList.map fun (k, v) => s!"  {k}: {v}"
  let comms := "comm_store: {\n" ++ body ++ "\n}"
  exprs ++ "\n" ++ comms

instance : ToString ScalarStore := ⟨ScalarStore.toString⟩

def ScalarStore.ofExprList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore :=
  ⟨.ofList exprs _, default⟩

end Lurk.Hashing
