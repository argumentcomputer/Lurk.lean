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
  | .num  => .ofNat 2
  | .u64  => .ofNat 3
  | .char => .ofNat 5
  | .str  => .ofNat 7
  | .comm => .ofNat 11
  | .fun  => .ofNat 13
  | .sym  => .ofNat 17
  | .cons => .ofNat 19

def ContTag.toF : ContTag → F
  | .done => .ofNat 23
  | .unOp .car => .ofNat 29
  | .binOp₁ .add => .ofNat 31
  | .binOp₁ .numEq => .ofNat 37
  | .binOp₂ .add => .ofNat 41
  | .binOp₂ .numEq => .ofNat 43
  | .appFn => .ofNat 47
  | .appArg => .ofNat 53
  | .if => .ofNat 59
  | .let => .ofNat 61
  | .letrec => .ofNat 67

theorem ExprTag.toF_inj {t₁ t₂ : ExprTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := sorry

theorem ContTag.toF_inj {t₁ t₂ : ContTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := sorry

theorem toF_disj {et : ExprTag} {ct : ContTag} : et.toF ≠ ct.toF := sorry
