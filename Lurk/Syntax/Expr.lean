import Lurk.Syntax.SExpr
import YatimaStdLib.Fin

namespace Lurk.Syntax

scoped notation "Name" => Lean.Name

/-- Binary operations on Lurk numerals -/
inductive BinaryOp 
  | sum | diff | prod | quot | numEq | lt | gt | le | ge | eq
  deriving Repr, BEq

/-- Basic Lurk expression AST -/
inductive Expr where
  -- `t`, `nil`, numeric, string and char literals
  | lit      : Literal → Expr
  -- Symbols to reference content in the environment
  | sym      : Name → Expr
  -- `if <test> <consequent> <alternate>`
  | ifE      : Expr → Expr → Expr → Expr
  -- `lambda <formals> <body>`
  | lam      : List Name → Expr → Expr
  -- `let <bindings> <body>`
  | letE     : List (Name × Expr) → Expr → Expr
  -- `letrec <bindings> <body>`
  | letRecE  : List (Name × Expr) → Expr → Expr
  -- `mutrec <bindings> <body>`
  | mutRecE  : List (Name × Expr) → Expr → Expr
  -- `<fun> <arg>`
  | app      : Expr → Option Expr → Expr
  -- `quote <datum>`
  | quote    : SExpr → Expr
  -- `<binop> <e1> <e2>`
  | binaryOp : BinaryOp → Expr → Expr → Expr
  -- `<cons> <e1> <e2>`
  | cons : Expr → Expr → Expr
  -- `<strcons> <e1> <e2>`
  | strcons  : Expr → Expr → Expr
  -- `atom <e>`
  | atom     : Expr → Expr
  -- `car <e>`
  | car      : Expr → Expr
  -- `cdr <e>`
  | cdr      : Expr → Expr
  -- `emit <e>`
  | emit     : Expr → Expr
  -- `begin <e1> <e2> ...`
  | begin    : Expr → Expr → Expr
  -- `current-env`
  | currEnv  : Expr
  | hide     : Expr → Expr → Expr
  | commit   : Expr → Expr
  | comm     : Expr → Expr
  deriving Repr, BEq, Inhabited

namespace Expr

def mkUnaryApp (f : Expr) : Expr :=
  .app f none

def mkApp (f : Expr) : List Expr → Expr
  | a :: as => as.foldl (init := .app f (some a)) fun acc a => .app acc (some a)
  | [] => .app f none

def mkListWith (es : List Expr) (tail : Expr) : Expr := 
  es.foldr (init := tail)
    fun n acc => .cons n acc

def mkList (es : List Expr) : Expr :=   
  mkListWith es (.lit .nil)

/--
Remove all binders from an expression, converting a lambda into
an "implicit lambda". This is useful for constructing the `rhs` of
recursor rules.
-/
def toImplicitLambda : Expr → Expr
  | .lam _ body => toImplicitLambda body
  | x => x

class ToExpr (α : Type u) where 
  toExpr : α → Expr 

instance : ToExpr Nat where 
  toExpr n := .lit $ .num (Fin.ofNat n)
  
instance : ToExpr Int where 
  toExpr n := .lit $ .num (Fin.ofInt n)

instance : ToExpr (Fin N) where 
  toExpr n := .lit $ .num n

instance : ToExpr Name where 
  toExpr := .sym

instance : ToExpr String where 
  toExpr s := .lit $ .str s

instance : ToExpr Char where 
  toExpr c := .lit $ .char c

instance : ToExpr Expr where 
  toExpr s := s

end Expr

end Lurk.Syntax
