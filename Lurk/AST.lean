import Lurk.SExpr

namespace Lurk

/-- Numerical values in Lurk (may be valued in a finite field) -/
structure Num where
  data     : Int
  modulus? : Option Nat
  deriving Repr

/-- Symbolic name values in Lurk -/
structure Name where
  data : String
  deriving Repr

/-- Operations on Lurk expressions -/
inductive ConsOp | car | cdr | atom | emit
deriving Repr, BEq

/-- Operations on Lurk numerals -/
inductive NumOp | sum | diff | prod | quot
deriving Repr, BEq

/-- Equality of evaluated expressions and numerical equality -/
inductive RelOp | eq | nEq
deriving Repr, BEq

/-- Basic Lurk primitives -/
inductive Literal
  -- `t` `nil`
  | t | nil
  -- Numerical values
  | num     : Num → Literal
  -- Strings
  | str     : String → Literal
  -- Characters
  | char    : Char → Literal
  deriving Repr

/-- Basic Lurk expression AST -/
inductive Expr where
  -- Symbols
  | sym     : Name → Expr
  -- Numeric, string and char literals
  | lit   : Literal → Expr
  -- `if <test> <consequent> <alternate>`
  | ifE     : Expr → Expr → Expr → Expr
  -- `lambda <formals> <body>`
  | lam     : (List Name) → Expr → Expr
  -- `let <bindings> <body>`
  | letE    : Expr → Expr → Expr
  -- `letrec <bindings> <body>`
  | letRecE : Expr → Expr → Expr
  -- `quote <datum>`
  | quote   : SExpr → Expr
  -- `cons <a> <d>`
  | cons    : Expr → Expr → Expr
  -- `strcons <a> <d>`
  | strcons : Expr → Expr → Expr
  -- `<consop> <e>`
  | consOp  : ConsOp → Expr → Expr
  -- `<numop> <e1> <e2>`
  | numOp   : NumOp → Expr → Expr → Expr    
  -- `<relop> <e1> <e2>`
  | relOp   : RelOp → Expr → Expr → Expr
  -- `emit <e>`
  | emit    : Expr → Expr
  -- `begin <e1> <e2> ... `
  | begin   : List Expr → Expr
  -- `current-env`
  | currEnv : Expr
  -- `eval <expr> <env>`
  | eval    : Expr → Option Expr → Expr
