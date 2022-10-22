import Lurk.Syntax.ExprUtils
import Lurk.Syntax.Printing
import Lurk.Hashing.Markers

namespace Lurk.Hashing

open Syntax

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Inhabited, Ord, BEq

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

open Std in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

instance : BEq ScalarStore where
  beq x y := x.exprs.toList == y.exprs.toList

def ScalarStore.ofList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore :=
  ⟨.ofList exprs⟩

def ScalarStore.toString (s : ScalarStore) : String :=
  let body := ",\n".intercalate $ s.exprs.toList.map fun (k, v) => s!"  {k}: {v}"
  "scalar_store: {\n" ++ body ++ "\n}"

instance : ToString ScalarStore := ⟨ScalarStore.toString⟩

open Std in
structure HashState where
  exprs       : RBMap ScalarPtr ScalarExpr compare
  charCache   : RBMap Char   ScalarPtr compare
  stringCache : RBMap String ScalarPtr compare
  exprCache   : RBMap Expr   ScalarPtr compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev HashM := StateM HashState

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

end Lurk.Hashing
