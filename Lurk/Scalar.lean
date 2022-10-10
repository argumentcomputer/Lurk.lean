import Lurk.Literal

namespace Lurk

inductive Tag where
  | nil | cons | num

def Tag.hash : Tag → Fin N
  | .nil  => ⟨0, by simp⟩
  | .cons => ⟨1, by simp⟩
  | .num  => ⟨2, by simp⟩

structure ScalarPtr where
  tag : Fin N
  val : Fin N

inductive ScalarExpr where
| nil
| cons (car: ScalarPtr) (cdr: ScalarPtr)
| num (val: Fin N)

def ScalarExpr.hash : ScalarExpr → Fin N := sorry

end Lurk
