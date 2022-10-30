namespace Lurk.Syntax

/-- Symbols are expected to be in uppercase -/
inductive AST
  | nil
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  deriving Ord, BEq, Repr, Inhabited

namespace AST

def mkCons (xs : List AST) (init : AST) : AST :=
  xs.foldr (init := init) fun x acc => .cons x acc

def mkQuote (x : AST) : AST :=
  mkCons [.sym "QUOTE", x] .nil

open Std Format in
partial def toFormat : AST → Format
  | nil => "NIL"
  | num n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => s
  | x@(.cons ..) =>
    let (xs, tail) := telescopeCons [] x
      let tail := match tail with
        | nil => Format.nil
        | _ => line ++ "." ++ line ++ tail.toFormat
      paren $ fmtList xs ++ tail
where
  telescopeCons (acc : List AST) : AST → List AST × AST
    | cons x y => telescopeCons (x :: acc) y
    | x => (acc.reverse, x)
  fmtList : List AST → Format
    | [ ]   => Format.nil
    | [n]   => n.toFormat
    | n::ns => format (n.toFormat) ++ line ++ fmtList ns

instance : Std.ToFormat AST := ⟨toFormat⟩
instance : ToString AST := ⟨toString ∘ toFormat⟩

end AST

end Lurk.Syntax
