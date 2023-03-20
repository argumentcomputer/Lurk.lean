import Lurk.LDON
import Lurk.Expr

namespace Lurk

def Atom.toLDON : Atom → LDON
  | .nil => .nil
  | .t   => .t
  | .num x => .num x
  | .u64 x => .u64 x
  | .str x => .str x
  | .char x => .char x

namespace Expr

open LDON Macro

partial def toLDON : Expr → LDON
  | .atom a => a.toLDON
  | .sym s => .sym s
  | .env => ~[.sym "CURRENT-ENV"]
  | .op₁ o e => ~[.sym o.toString, e.toLDON]
  | .op₂ o e₁ e₂ => ~[.sym o.toString, e₁.toLDON, e₂.toLDON]
  | e@(.begin ..) =>
    let (es, e) := e.telescopeBegin
    .cons (.sym "BEGIN") $ es.foldr (.cons ·.toLDON ·) e.toLDON
  | .if a b c => .cons (.sym "IF") $ .cons a.toLDON $ .cons b.toLDON $ .cons c.toLDON .nil
  | .app₀ e => ~[e.toLDON]
  | .app f a => ~[f.toLDON, a.toLDON]
  | .lambda s e =>
    let (ss, b) := e.telescopeLam #[s]
    .cons (.sym "LAMBDA") $
      .cons (ss.foldr (fun s acc => .cons (.sym s) acc) .nil) $ .cons b.toLDON .nil
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    .cons (.sym "LET") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .letrec s v b =>
    let (bs, b) := b.telescopeLetrec #[(s, v)]
    .cons (.sym "LETREC") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .quote d => ~[.sym "QUOTE", d]
  | .eval e env? =>
    if env? == .nil then
      ~[.sym "EVAL", e.toLDON]
    else
      ~[.sym "EVAL", e.toLDON, env?.toLDON]

def symOfString : String → Expr
  | "NIL" => .nil
  | "T"   => .t
  | x     => .sym x

end Expr

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
  | x => fun y => .app (.symOfString x) y

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
  | x => fun y z => .app (.app (.symOfString x) y) z

namespace LDON

def asArgs : LDON → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

open Macro

def asBindings : LDON → Except String (List (String × LDON))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

partial def toExpr : LDON → Except String Expr
  -- trivial cases
  | .num  n  => return .atom $ .num (.ofNat n)
  | .u64  n  => return .atom $ .u64 n
  | .char c  => return .atom $ .char c
  | .str  s  => return .atom $ .str s
  | ~[.sym "CURRENT-ENV"] => return .env
  | .sym s  => return .symOfString s
  -- `begin` is a sequence of expressions
  | .cons (.sym "BEGIN") tail => match tail.telescopeCons with
    | (xs, .nil) =>
      xs.foldrM (init := .nil) fun x acc => do
        pure $ .begin (← x.toExpr) acc
    | x => throw s!"expected a list terminating with `nil` but got {x}"
  -- `if` is a sequence of (up to) three expressions
  | ~[.sym "IF"] => return .if .nil .nil .nil
  | ~[.sym "IF", x] => return .if (← x.toExpr) .nil .nil
  | ~[.sym "IF", x, y] => return .if (← x.toExpr) (← y.toExpr) .nil
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
  | ~[.sym "QUOTE", x] => return .quote x
  | ~[.sym "EVAL", x] => return .eval (← x.toExpr) .nil
  | ~[.sym "EVAL", x, y] => return .eval (← x.toExpr) (← y.toExpr)
  -- binary operators
  | ~[.sym op₂, x, y] => return mkOp₂ op₂ (← x.toExpr) (← y.toExpr)
  -- unary operators
  | ~[.sym op₁, x] => return mkOp₁ op₁ (← x.toExpr)
  -- everything else is just an `app`
  | cons fn args => match args.telescopeCons with
    | (args, nil) =>
      if args.isEmpty then
        return .app₀ (← fn.toExpr)
      else do
        args.foldlM (init := ← fn.toExpr) fun acc arg => do
          pure $ .app acc (← arg.toExpr)
    | x => throw s!"expected a list terminating with `nil` but got {x}"

end Lurk.LDON
