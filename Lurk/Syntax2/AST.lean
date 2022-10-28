namespace Lurk.Syntax

inductive AST
  | nil
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  | stac : AST → AST

namespace AST

def upper : AST → AST
  | sym s => sym s.toUpper
  | cons a b => cons a.upper b.upper
  | x => x

end AST
