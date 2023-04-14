import Lurk.Field

inductive ExprTag
  | num | u64 | char | str | comm | «fun» | sym | cons
  deriving Ord, BEq

def ExprTag.toString : ExprTag → String
  | num => "num"
  | u64 => "u64"
  | char => "char"
  | str => "str"
  | comm => "comm"
  | .fun => "fun"
  | sym => "sym"
  | cons => "cons"

instance : ToString ExprTag := ⟨ExprTag.toString⟩

inductive UnOp
  | car
  deriving Ord, BEq

def UnOp.toString : UnOp → String
  | car => "car"

instance : ToString UnOp := ⟨UnOp.toString⟩

inductive BinOp
  | add
  | numEq
  deriving Ord, BEq

def BinOp.toString : BinOp → String
  | add => "add"
  | numEq => "numEq"

instance : ToString BinOp := ⟨BinOp.toString⟩

inductive ContTag
  | entry | halt
  | appFn | appArg
  | «if»
  | «let» | letrec
  | env | lookup
  | unOp : UnOp → ContTag
  | binOp₁ : BinOp → ContTag
  | binOp₂ : BinOp → ContTag
  deriving Ord, BEq

def ContTag.toString : ContTag → String
  | entry => "entry"
  | halt => "halt"
  | appFn => "appFn"
  | appArg => "appArg"
  | .if => "if"
  | .let => "let"
  | letrec => "letrec"
  | env => "env"
  | lookup => "lookup"
  | unOp op => s!"unOp[{op}]"
  | binOp₁ op => s!"binOp₁[{op}]"
  | binOp₂ op => s!"binOp₂[{op}]"

instance : ToString ContTag := ⟨ContTag.toString⟩

open Lurk (F)

def ExprTag.toF : ExprTag → F
  | .num   => .ofNat 0
  | .u64   => .ofNat 1
  | .char  => .ofNat 2
  | .str   => .ofNat 3
  | .comm  => .ofNat 4
  | .fun   => .ofNat 5
  | .sym   => .ofNat 6
  | .cons  => .ofNat 7

def ContTag.toF : ContTag → F
  | .entry => .ofNat 16
  | .halt => .ofNat 17
  | .appFn => .ofNat 18
  | .appArg => .ofNat 19
  | .if => .ofNat 20
  | .let => .ofNat 21
  | .letrec => .ofNat 22
  | .env => .ofNat 23
  | .lookup => .ofNat 24
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
  deriving Ord, BEq

instance : ToString ExprPtr where
  toString x := s!"{x.tag}#{x.val.asHex}"

structure ContPtr where
  tag : ContTag
  val : F
  deriving Ord, BEq

instance : ToString ContPtr where
  toString x := s!"{x.tag}#{x.val.asHex}"
