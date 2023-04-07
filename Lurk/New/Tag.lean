import Lurk.Field

inductive ExprTag
  | num | u64 | char | str | comm | «fun» | sym | cons
  deriving Ord, BEq

inductive UnOp
  | car
  deriving Ord, BEq

inductive BinOp
  | add
  | numEq
  deriving Ord, BEq

inductive ContTag
  | done
  | unOp : UnOp → ContTag
  | binOp₁ : BinOp → ContTag
  | binOp₂ : BinOp → ContTag
  | appFn | appArg
  | «if»
  | «let»
  | letrec
  deriving Ord, BEq

open Lurk (F)

def ExprTag.toF : ExprTag → F
  | .num  => .ofNat 0
  | .u64  => .ofNat 1
  | .char => .ofNat 2
  | .str  => .ofNat 3
  | .comm => .ofNat 4
  | .fun  => .ofNat 5
  | .sym  => .ofNat 6
  | .cons => .ofNat 7

def ContTag.toF : ContTag → F
  | .done => .ofNat 4096
  | .unOp .car => .ofNat 4097
  | .binOp₁ .add => .ofNat 4098
  | .binOp₁ .numEq => .ofNat 4099
  | .binOp₂ .add => .ofNat 4100
  | .binOp₂ .numEq => .ofNat 4101
  | .appFn => .ofNat 4102
  | .appArg => .ofNat 4103
  | .if => .ofNat 4104
  | .let => .ofNat 4105
  | .letrec => .ofNat 4106

theorem ExprTag.toF_inj {t₁ t₂ : ExprTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := by
  cases t₁ <;> cases t₂ <;> simp only [h] <;> contradiction

theorem ContTag.toF_inj {t₁ t₂ : ContTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := sorry

theorem toF_disj {et : ExprTag} {ct : ContTag} : et.toF ≠ ct.toF := sorry
