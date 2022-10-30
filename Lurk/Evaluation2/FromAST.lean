import Lurk.Syntax2.Notation
import Lurk.Evaluation2.Expr

namespace Lurk.Syntax.AST
open Evaluation

abbrev ToExprM := Except String

def mkArgs (args : AST) : ToExprM (List String) := 
  match args with 
    | .nil => return []
    | .cons (.sym x) xs => return x :: (← mkArgs xs)
    | _ => throw "invalid arguments shape, expected list of symbols"

def mkBindings (bindings : AST) : ToExprM $ List (String × AST) := 
  match bindings with 
    | .nil => return []
    | .cons ~[(.sym x), y] xs => return (x, y) :: (← mkBindings xs)
    | _ => throw "invalid binding shape, expected list of (symbol, body) pairs"

def mkList (args : AST) : ToExprM (List AST) := 
  match args with 
    | .nil => return []
    | .cons x xs => return x :: (← mkList xs)
    | _ => throw "invalid arguments shape, expected list"

def mkOp₁ (op₁ : String) : Expr → Expr := match op₁ with
  | "ATOM" => .op₁ .atom
  | "CAR" => .op₁ .car
  | "CDR" => .op₁ .cdr
  | "EMIT" => .op₁ .emit
  | "COMMIT" => .op₁ .commit
  | "COMM" => .op₁ .comm
  | "OPEN" => .op₁ .open
  | "NUM" => .op₁ .num
  | "CHAR" => .op₁ .char
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
  | .sym "CURRENT-ENV" => return .env
  | .sym s  => return .sym s
  -- `if` is a sequence of three expressions
  | ~[.sym "IF", x, y, z] => return .if (← x.toExpr) (← y.toExpr) (← z.toExpr)
  -- `lambda` requires a gradual consumption of a symbol
  | ~[.sym "LAMBDA", args, body] => do
    let args ← mkArgs args
    if args == [] then 
      return .lambda "_" (← body.toExpr)
    else 
      return args.foldr (init := ← body.toExpr) 
        fun arg acc => .lambda arg acc
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
  | ~[.sym op₁, x] => do return mkOp₁ op₁ (← x.toExpr)
  -- binary operators
  | ~[.sym op₂, x, y] => do return mkOp₂ op₂ (← x.toExpr) (← y.toExpr)
  -- everything else is just an `app`
  | cons fn args => do
    let args ← (← mkList args) |>.mapM toExpr
    if args == [] then 
      return .app₀ (← fn.toExpr) 
    else 
      return args.foldl (init := ← fn.toExpr) fun acc arg => .app acc arg

end Lurk.Syntax.AST
