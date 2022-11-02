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

open Std Format in
partial def toFormat : AST → Format
  | nil => "NIL"
  | num n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => s
  | x@(.cons ..) =>
    match telescopeCons #[] x with
    | (xs, nil) => paren $ fmtList xs.data
    | (xs, y)   => paren $ fmtList xs.data ++ line ++ "." ++ line ++ y.toFormat
where
  telescopeCons (acc : Array AST) : AST → Array AST × AST
    | cons x y => telescopeCons (acc.push x) y
    | x => (acc, x)
  fmtList : List AST → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ x.toFormat) x.toFormat

instance : Std.ToFormat AST := ⟨toFormat⟩
instance : ToString AST := ⟨toString ∘ toFormat⟩

section ASThelpers

def consWith (xs : List AST) (init : AST) : AST :=
  xs.foldr (init := init) fun x acc => cons x acc

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[$xs,*]) => do
    let mut x ← `(AST.nil)
    for i in xs.getElems.reverse do
      x ← `(AST.cons $i $x)
    return x

def mkQuote (x : AST) : AST :=
  ~[sym "QUOTE", x]

end ASThelpers

end Lurk.Syntax.AST