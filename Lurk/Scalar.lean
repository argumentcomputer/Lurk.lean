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

def hashChar (c : Char) : F :=
  sorry

def hashString : String → F
  | ⟨[]⟩ => .ofNat 0
  | ⟨c :: cs⟩ =>
    let s := String.mk cs
    sorry

def hash3 : F → F → F → F := sorry

def hash4 : F → F → F → F → F := sorry

def ScalarExpr.hash : ScalarExpr → F
  | .nil => hashString "nil"
  | .cons car cdr => hash4 car.tag car.val cdr.tag cdr.val
  | .num x => x
  | .chr x => sorry
  | .str c x => hash3 (hashChar c) x.tag x.val

end Lurk
