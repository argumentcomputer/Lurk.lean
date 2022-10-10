import Lurk.Literal

namespace Lurk

inductive Tag where
  | nil | cons | num

abbrev F := Fin N

def Tag.hash : Tag → F
  | .nil  => .ofNat 0
  | .cons => .ofNat 1
  | .num  => .ofNat 2

structure ScalarPtr where
  tag : F
  val : F

inductive ScalarExpr where
  | nil
  | cons (car: ScalarPtr) (cdr: ScalarPtr)
  | num (val: F)
  | chr (x : F)
  | str (head : Char) (tail : ScalarPtr)

def hashChar (c : Char) : ScalarPtr :=
  sorry

def hash4 : F → F → F → F → F := sorry

def getString : String → ScalarPtr := sorry

def hashString : String → F
  | ⟨[]⟩ => .ofNat 0
  | ⟨c :: cs⟩ =>
    let char := hashChar c
    let str := getString (String.mk cs)
    hash4 char.tag char.val str.tag str.val

def ScalarExpr.hash : ScalarExpr → F
  | .nil => hashString "nil"
  | .cons car cdr => hash4 car.tag car.val cdr.tag cdr.val
  | .num x => x
  | .chr x => sorry
  | .str c x => sorry

end Lurk
