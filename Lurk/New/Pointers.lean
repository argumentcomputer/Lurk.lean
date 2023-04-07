import Lurk.Field

inductive ExprTag
  | num | u64 | char | str | comm | «fun» | sym | cons
  deriving Ord, BEq, Repr

inductive UnOp
  | car
  deriving Ord, BEq, Repr

inductive BinOp
  | add
  | numEq
  deriving Ord, BEq, Repr

inductive ContTag
  | done
  | appFn | appArg
  | «if»
  | «let»
  | letrec
  | unOp : UnOp → ContTag
  | binOp₁ : BinOp → ContTag
  | binOp₂ : BinOp → ContTag
  deriving Ord, BEq, Repr

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
  | .done => .ofNat 16
  | .appFn => .ofNat 17
  | .appArg => .ofNat 18
  | .if => .ofNat 19
  | .let => .ofNat 20
  | .letrec => .ofNat 21
  | .unOp .car => .ofNat 32
  | .binOp₁ .add => .ofNat 64
  | .binOp₁ .numEq => .ofNat 65
  | .binOp₂ .add => .ofNat 128
  | .binOp₂ .numEq => .ofNat 129

theorem ExprTag.toF_inj {t₁ t₂ : ExprTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := by
  cases t₁ <;> cases t₂ <;> simp only [h] <;> contradiction

theorem ContTag.toF_inj {t₁ t₂ : ContTag} (h : t₁ ≠ t₂) : t₁.toF ≠ t₂.toF := sorry

theorem toF_disj {et : ExprTag} {ct : ContTag} : et.toF ≠ ct.toF := sorry

structure ExprPtr where
  tag : ExprTag
  val : F
  deriving Ord, BEq, Repr

structure ContPtr where
  tag : ContTag
  val : F
  deriving Ord, BEq
