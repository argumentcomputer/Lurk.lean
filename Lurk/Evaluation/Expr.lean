import Lurk.Field
import Lurk.Syntax.AST

open Std

namespace Lurk.Evaluation

/-- Basic Lurk primitives -/
inductive Lit
  -- `t` and `nil`
  | t | nil
  -- Numerical values
  | num  : F → Lit
  -- Strings
  | str  : String → Lit
  -- Characters
  | char : Char → Lit
  deriving Repr, BEq

namespace Lit

def toString : Lit → String
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => ToString.toString n
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

def pprint : Lit → Format
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => n.asHex
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Lit where
  format := pprint

def toAST : Lit → Syntax.AST
  | .nil    => .nil
  | .t      => .t
  | .num n  => .num n
  | .str s  => .str s
  | .char c => .char c

end Lit

inductive Op₁
  | atom | car | cdr | emit
  | commit | comm | «open»
  | num | char
  deriving Repr, BEq

inductive Op₂
  | cons | strcons
  | add | sub | mul | div | numEq | lt | gt | le | ge | eq
  | hide
  deriving Repr, BEq

inductive Expr
  | lit : Lit → Expr
  | sym : String → Expr
  | env : Expr
  | op₁ : Op₁ → Expr → Expr
  | op₂ : Op₂ → Expr → Expr → Expr
  | begin : Expr → Expr → Expr
  | «if» : Expr → Expr → Expr → Expr
  | app₀ : Expr → Expr
  | app  : Expr → Expr → Expr
  | lambda : String → Expr → Expr
  | «let»  : String → Expr → Expr → Expr
  | letrec : String → Expr → Expr → Expr
  | quote : Syntax.AST → Expr
  deriving Repr, Inhabited, BEq

end Lurk.Evaluation
