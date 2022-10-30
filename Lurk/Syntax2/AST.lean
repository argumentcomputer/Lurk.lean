namespace Lurk.Syntax

/-- Symbols are expected to be in uppercase -/
inductive AST
  | nil
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  deriving Ord, BEq, Repr

namespace AST

def mkCons (xs : List AST) (init : AST) : AST :=
  xs.foldr (init := init) fun x acc => .cons x acc

def mkQuote (x : AST) : AST :=
  mkCons [.sym "QUOTE", x] .nil

end AST
