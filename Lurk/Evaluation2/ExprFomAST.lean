import Lurk.Syntax2.AST
import Lurk.Evaluation2.Expr

namespace Lurk.Syntax.AST

def toExpr : AST → Evaluation.Expr
  -- trivial cases
  | nil    => .lit .nil
  | num n  => .lit $ .num (.ofNat n)
  | char c => .lit $ .char c
  | str s  => .lit $ .str s
  | sym s  => .sym s
  | cons (sym "CURRENT-ENV") .nil => .env
  -- unary operators
  | cons (sym "QUOTE")  (cons x .nil) => .op₁ .quote  x.toExpr
  | cons (sym "ATOM")   (cons x .nil) => .op₁ .atom   x.toExpr
  | cons (sym "CAR")    (cons x .nil) => .op₁ .car    x.toExpr
  | cons (sym "CDR")    (cons x .nil) => .op₁ .cdr    x.toExpr
  | cons (sym "EMIT")   (cons x .nil) => .op₁ .emit   x.toExpr
  | cons (sym "COMMIT") (cons x .nil) => .op₁ .commit x.toExpr
  | cons (sym "COMM")   (cons x .nil) => .op₁ .comm   x.toExpr
  | cons (sym "OPEN")   (cons x .nil) => .op₁ .open   x.toExpr
  | cons (sym "NUM")    (cons x .nil) => .op₁ .num    x.toExpr
  | cons (sym "CHAR")   (cons x .nil) => .op₁ .char   x.toExpr
  -- binary operators
  | cons (sym "CONS")  (cons x (cons y .nil)) => .op₂ .cons  x.toExpr y.toExpr
  | cons (sym "BEGIN") (cons x (cons y .nil)) => .op₂ .begin x.toExpr y.toExpr
  | cons (sym "+")     (cons x (cons y .nil)) => .op₂ .add   x.toExpr y.toExpr
  | cons (sym "-")     (cons x (cons y .nil)) => .op₂ .sub   x.toExpr y.toExpr
  | cons (sym "*")     (cons x (cons y .nil)) => .op₂ .mul   x.toExpr y.toExpr
  | cons (sym "/")     (cons x (cons y .nil)) => .op₂ .div   x.toExpr y.toExpr
  | cons (sym "=")     (cons x (cons y .nil)) => .op₂ .numEq x.toExpr y.toExpr
  | cons (sym "<")     (cons x (cons y .nil)) => .op₂ .lt    x.toExpr y.toExpr
  | cons (sym ">")     (cons x (cons y .nil)) => .op₂ .gt    x.toExpr y.toExpr
  | cons (sym "<=")    (cons x (cons y .nil)) => .op₂ .le    x.toExpr y.toExpr
  | cons (sym ">=")    (cons x (cons y .nil)) => .op₂ .ge    x.toExpr y.toExpr
  | cons (sym "EQ")    (cons x (cons y .nil)) => .op₂ .eq    x.toExpr y.toExpr
  | cons (sym "HIDE")  (cons x (cons y .nil)) => .op₂ .hide  x.toExpr y.toExpr
  -- `if` is a sequence of three expressions
  | cons (sym "IF") (cons x (cons y (cons z .nil))) => .if x.toExpr y.toExpr z.toExpr
  -- `lambda` requires a gradual consumption of a symbol
  | cons (sym "LAMBDA") (cons (cons (.sym arg) nil) (cons body nil)) =>
    .lambda arg body.toExpr
  | cons (sym "LAMBDA") (cons (cons (sym arg) args) tail) =>
    .lambda arg $ toExpr (cons (sym "LAMBDA") (cons args tail))
  -- `let` requires a gradual consumption of a symbol and an expression
  | cons (sym "LET") (cons (cons (cons (sym name) (cons val nil)) nil) (cons body nil)) =>
    .let name val.toExpr body.toExpr
  | cons (sym "LET") (cons (cons (cons (sym name) (cons val nil)) binders) tail) =>
    .let name val.toExpr $ toExpr (cons (sym "LET") (cons binders tail))
  -- `letrec` is similar to `let`
  | cons (sym "LETREC") (cons (cons (cons (sym name) (cons val nil)) nil) (cons body nil)) =>
    .letrec name val.toExpr body.toExpr
  | cons (sym "LETREC") (cons (cons (cons (sym name) (cons val nil)) binders) tail) =>
    .letrec name val.toExpr $ toExpr (cons (sym "LETREC") (cons binders tail))
  -- everything else is just an `app`
  | cons fn body => .app fn.toExpr body.toExpr

end Lurk.Syntax.AST
