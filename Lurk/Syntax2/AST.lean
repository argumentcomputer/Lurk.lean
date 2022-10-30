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

def unfoldCons (acc : Array AST := #[]) : AST → Array AST
  | cons x nil => acc.push x
  | cons x y => y.unfoldCons $ acc.push x
  | x => acc.push x

open Std Format in
partial def toFormat : AST → Format
  | nil => "NIL"
  | num n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => s
  | cns => match ((cns.unfoldCons).map toFormat).data with
    | [] => "()"
    | x :: xs => paren $ xs.foldl (fun acc x => group $ acc ++ line ++ x) x

instance : Std.ToFormat AST := ⟨toFormat⟩
instance : ToString AST := ⟨toString ∘ toFormat⟩

end AST

end Lurk.Syntax
