import Lurk.Field

inductive ExprTag
  | num | u64 | char | str | comm | «fun» | sym | cons | thunk
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
  | thunk => "thunk"

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
  | done
  | appFn | appArg
  | «if»
  | «let»
  | letrec
  | body
  | ret
  | unOp : UnOp → ContTag
  | binOp₁ : BinOp → ContTag
  | binOp₂ : BinOp → ContTag
  deriving Ord, BEq

def ContTag.toString : ContTag → String
  | done => "done"
  | appFn => "appFn"
  | appArg => "appArg"
  | .if => "if"
  | .let => "let"
  | letrec => "letrec"
  | body => "body"
  | ret => "ret"
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
  | .thunk => .ofNat 8

def ContTag.toF : ContTag → F
  | .done => .ofNat 16
  | .appFn => .ofNat 17
  | .appArg => .ofNat 18
  | .if => .ofNat 19
  | .let => .ofNat 20
  | .letrec => .ofNat 21
  | .body => .ofNat 22
  | .ret => .ofNat 23
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
