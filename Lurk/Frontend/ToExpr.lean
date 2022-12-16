import Lurk.Frontend.AST
import Lurk.Backend.Expr

namespace Lurk.Frontend.AST

open Backend (Expr)

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

open Macro

def asArgs : AST → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

def asBindings : AST → Except String (List (String × AST))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

def toDatum : AST → Backend.Datum
  | .num x => .num (.ofNat x)
  | .char x => .char x
  | .str x => .str x
  | .sym "NIL" => .nil
  | .sym x => .sym x
  | .cons x y => .cons x.toDatum y.toDatum

partial def toExpr : AST → Except String Expr
  -- trivial cases
  | .nil     => return .atom .nil
  | .t       => return .atom .t
  | .num  n  => return .atom $ .num (.ofNat n)
  | .char c  => return .atom $ .char c
  | .str  s  => return .atom $ .str s
  | ~[.sym "CURRENT-ENV"] => return .env
  | .sym s  => return .sym s
  -- `begin` is a sequence of expressions
  | .cons (.sym "BEGIN") tail => do
    let (tail, ini) := tail.telescopeCons
    (← tail.mapM toExpr).foldrM (init := ← ini.toExpr)
      fun e acc => pure $ .begin e acc
  -- `if` is a sequence of (up to) three expressions
  | ~[.sym "IF"] => return .if (.atom .nil) (.atom .nil) (.atom .nil)
  | ~[.sym "IF", x] => return .if (← x.toExpr) (.atom .nil) (.atom .nil)
  | ~[.sym "IF", x, y] => return .if (← x.toExpr) (← y.toExpr) (.atom .nil)
  | ~[.sym "IF", x, y, z] => return .if (← x.toExpr) (← y.toExpr) (← z.toExpr)
  -- `lambda` requires a gradual consumption of a symbol
  | ~[.sym "LAMBDA", args, body] => do
    let args ← args.asArgs
    if args.isEmpty then
      return .lambda "_" (← body.toExpr)
    else
      return args.foldr (init := ← body.toExpr) fun arg acc => .lambda arg acc
  -- let and letrec are in the same case
  | ~[.sym "LET", bindings, body] => do
    let bindings ← bindings.asBindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .let n e acc
  | ~[.sym "LETREC", bindings, body] => do
    let bindings ← bindings.asBindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .letrec n e acc
  -- quoting consumes the expression as-is
  | ~[.sym "QUOTE", x] => return .quote x.toDatum
  -- binary operators
  | ~[.sym op₂, x, y] => return mkOp₂ op₂ (← x.toExpr) (← y.toExpr)
  -- unary operators
  | ~[.sym op₁, x] => return mkOp₁ op₁ (← x.toExpr)
  -- everything else is just an `app`
  | cons fn args => match args.telescopeCons with
    | (args, nil) =>
      return if args.isEmpty then
        .app₀ (← fn.toExpr)
      else
        (← args.mapM toExpr).foldl (fun acc arg => .app acc arg) (← fn.toExpr)
    | x => throw s!"expected a list terminating with `nil` but got {x}"

end Lurk.Frontend.AST
