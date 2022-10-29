import Lurk.Arithmetic
import Lurk.Syntax2.AST

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
  deriving Repr

inductive Op₁
  | quote | atom | car | cdr | emit
  | commit | comm | «open»
  | num | char
  deriving Repr

inductive Op₂
  | cons | strcons | begin
  | add | sub | mul | div | numEq | lt | gt | le | ge | eq
  | hide
  deriving Repr

inductive Expr
  | lit : Lit → Expr
  | sym : String → Expr
  | env : Expr
  | op₁ : Op₁ → Expr → Expr
  | op₂ : Op₂ → Expr → Expr → Expr
  | «if» : Expr → Expr → Expr → Expr
  | app  : Expr → Expr → Expr
  | lambda : String → Expr → Expr
  | «let»  : String → Expr → Expr → Expr
  | letrec : String → Expr → Expr → Expr
  deriving Repr

end Lurk.Evaluation
