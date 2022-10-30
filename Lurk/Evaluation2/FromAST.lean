import Lurk.Syntax2.Notation
import Lurk.Evaluation2.Expr

namespace Lurk.Syntax.AST
open Evaluation

def mkArgs! (args : AST) : List String := 
  match args with 
    | .nil => []
    | .cons (.sym x) xs => x :: mkArgs! xs
    | _ => panic! "invalid arguments shape, expected list of symbols"

def mkBindings! (bindings : AST) : List (String × AST) := 
  match bindings with 
    | .nil => []
    | .cons ~[(.sym x), y] xs => (x, y) :: mkBindings! xs
    | _ => panic! "invalid binding shape, expected list of (symbol, body) pairs"

def mkList! (args : AST) : List AST := 
  match args with 
    | .nil => []
    | .cons x xs => x :: mkList! xs
    | _ => panic! "invalid arguments shape, expected list"

def mkOp₁ (op₁ : String) : Expr → Expr := match op₁ with
  | "QUOTE" => .op₁ .quote
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
  | "CONS"  => .op₂ .cons
  | "BEGIN" => .op₂ .begin
  | "+"     => .op₂ .add
  | "-"     => .op₂ .sub
  | "*"     => .op₂ .mul
  | "/"     => .op₂ .div
  | "="     => .op₂ .numEq
  | "<"     => .op₂ .lt
  | ">"     => .op₂ .gt
  | "<="    => .op₂ .le
  | ">="    => .op₂ .ge
  | "EQ"    => .op₂ .eq
  | "HIDE"  => .op₂ .hide
  | x => fun y z => .app (.app (.sym x) y) z

partial def toExpr : AST → Expr
  -- trivial cases
  | .nil    => .lit .nil
  | .num n  => .lit $ .num (.ofNat n)
  | .char c => .lit $ .char c
  | .str s  => .lit $ .str s
  | .sym "CURRENT-ENV" => .env
  | .sym s  => .sym s
  -- `if` is a sequence of three expressions
  | ~[.sym "IF", x, y, z] => .if x.toExpr y.toExpr z.toExpr
  -- `lambda` requires a gradual consumption of a symbol
  | ~[.sym "LAMBDA", args, body] =>
    let args := mkArgs! args
    if args == [] then 
      .lambda "_" body.toExpr
    else 
      args.foldr (init := body.toExpr) 
        fun arg acc => .lambda arg acc
  -- let and letrec are in the same case
  | ~[.sym "LET", bindings, body] =>
    let bindings := mkBindings! bindings
    let bindings := bindings.map fun (x, y) => (x, y.toExpr)
    bindings.foldr (init := body.toExpr) 
      fun (n, e) acc => .let n e acc
  | ~[.sym "LETREC", bindings, body] =>
    let bindings := mkBindings! bindings
    let bindings := bindings.map fun (x, y) => (x, y.toExpr)
    bindings.foldr (init := body.toExpr) 
      fun (n, e) acc => .letrec n e acc
  -- unary operators
  | ~[.sym op₁, x] => mkOp₁ op₁ x.toExpr
  -- binary operators
  | ~[.sym op₂, x, y] => mkOp₂ op₂ x.toExpr y.toExpr
  -- everything else is just an `app`
  | cons fn args => 
    let args := mkList! args |>.map toExpr
    if args == [] then 
      .app fn.toExpr none 
    else 
      args.foldl (init := fn.toExpr) fun acc arg => .app acc (some arg)

end Lurk.Syntax.AST
