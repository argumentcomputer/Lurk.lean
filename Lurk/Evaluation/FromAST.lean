import Lurk.Evaluation.Expr

namespace Lurk.Syntax.AST

open Evaluation (Expr)

abbrev ToExprM := Except String

def mkArgs : AST → ToExprM (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← mkArgs xs)
  | x => throw s!"expected list of symbols but got {x}"

def mkBindings : AST → ToExprM (List (String × AST))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← mkBindings xs)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

def toList : AST → ToExprM (List AST)
  | .nil => return []
  | .cons x xs => return x :: (← toList xs)
  | x => throw s!"expected list but got {x}"

def mkOp₁ (op₁ : String) : Expr → Expr := match op₁ with
  | "ATOM"   => .op₁ .atom
  | "CAR"    => .op₁ .car
  | "CDR"    => .op₁ .cdr
  | "EMIT"   => .op₁ .emit
  | "COMMIT" => .op₁ .commit
  | "COMM"   => .op₁ .comm
  | "OPEN"   => .op₁ .open
  | "NUM"    => .op₁ .num
  | "CHAR"   => .op₁ .char
  | x => fun y => .app (.sym x) y

def mkOp₂ (op₂ : String) : Expr → Expr → Expr := match op₂ with
  | "CONS"    => .op₂ .cons
  | "STRCONS" => .op₂ .strcons
  | "BEGIN"   => .op₂ .begin
  | "+"       => .op₂ .add
  | "-"       => .op₂ .sub
  | "*"       => .op₂ .mul
  | "/"       => .op₂ .div
  | "="       => .op₂ .numEq
  | "<"       => .op₂ .lt
  | ">"       => .op₂ .gt
  | "<="      => .op₂ .le
  | ">="      => .op₂ .ge
  | "EQ"      => .op₂ .eq
  | "HIDE"    => .op₂ .hide
  | x => fun y z => .app (.app (.sym x) y) z

partial def toExpr : AST → ToExprM Expr
  -- trivial cases
  | .nil    => return .lit .nil
  | .num n  => return .lit $ .num (.ofNat n)
  | .char c => return .lit $ .char c
  | .str s  => return .lit $ .str s
  | .sym "T" => return .lit .t
  | .sym "CURRENT-ENV" => return .env
  | .sym s  => return .sym s
  -- `if` is a sequence of (up to) three expressions
  | ~[.sym "IF"] => return .if (.lit .nil) (.lit .nil) (.lit .nil)
  | ~[.sym "IF", x] => return .if (← x.toExpr) (.lit .nil) (.lit .nil)
  | ~[.sym "IF", x, y] => return .if (← x.toExpr) (← y.toExpr) (.lit .nil)
  | ~[.sym "IF", x, y, z] => return .if (← x.toExpr) (← y.toExpr) (← z.toExpr)
  -- `lambda` requires a gradual consumption of a symbol
  | ~[.sym "LAMBDA", args, body] => do
    let args ← mkArgs args
    if args.isEmpty then
      return .lam "_" (← body.toExpr)
    else
      return args.foldr (init := ← body.toExpr) fun arg acc => .lam arg acc
  -- let and letrec are in the same case
  | ~[.sym "LET", bindings, body] => do
    let bindings ← mkBindings bindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .let n e acc
  | ~[.sym "LETREC", bindings, body] => do
    let bindings ← mkBindings bindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .letrec n e acc
  | ~[.sym "QUOTE", datum] => return .quote datum
  -- unary operators
  | ~[.sym op₁, x] => return mkOp₁ op₁ (← x.toExpr)
  -- binary operators
  | ~[.sym op₂, x, y] => return mkOp₂ op₂ (← x.toExpr) (← y.toExpr)
  -- everything else is just an `app`
  | cons fn args => do
    let args ← (← toList args) |>.mapM toExpr
    if args.isEmpty then
      return .app₀ (← fn.toExpr)
    else
      return args.foldl (init := ← fn.toExpr) fun acc arg => .app acc arg

end Lurk.Syntax.AST