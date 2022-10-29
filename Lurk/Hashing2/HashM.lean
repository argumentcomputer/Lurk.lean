import Lurk.Syntax2.AST
import Lurk.Arithmetic
import Std.Data.RBMap

namespace Lurk.Hashing

inductive Tag
  | nil | cons | sym | «fun» | num | thunk | str | char | comm
  deriving Ord, BEq, Inhabited

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

open Std (RBMap) in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

instance : BEq ScalarStore where
  beq x y := x.exprs == y.exprs

def ScalarStore.ofList (exprs : List (ScalarPtr × ScalarExpr)) : ScalarStore :=
  ⟨.ofList exprs _⟩

open Std (RBMap) in
structure HashState where
  exprs       : RBMap ScalarPtr  ScalarExpr compare
  stringCache : RBMap String     ScalarPtr  compare
  astCache    : RBMap Syntax.AST ScalarPtr  compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev HashM := StateM HashState

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

end Lurk.Hashing
