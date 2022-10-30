namespace Lurk.Syntax

inductive AST
  | nil
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  deriving Ord, BEq, Repr

namespace AST

def mkCons (xs : List AST) : AST :=
  xs.foldr (init := .nil) fun x acc => .cons x acc

def mkQuote (x : AST) : AST :=
  mkCons [.sym "quote", x]

def upper : AST → AST
  | sym s => sym s.toUpper
  | cons a b => cons a.upper b.upper
  | x => x

def type : AST → String 
  | .nil      => "NIL"
  | .num _    => "NUM"
  | .char _   => "CHAR"
  | .str _    => "STR"
  | .sym _    => "SYM"
  | .cons _ _ => "CONS"

end AST

end Lurk.Syntax
