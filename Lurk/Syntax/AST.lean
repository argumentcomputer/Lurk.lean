import YatimaStdLib.RBMap

namespace Lurk.Syntax

/-- Reserved symbols are expected to be in uppercase -/
inductive AST
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  deriving Ord, BEq, Repr, Inhabited

namespace AST

@[match_pattern] def nil : AST := sym "NIL"
@[match_pattern] def t   : AST := sym "T"

def telescopeCons (acc : Array AST := #[]) : AST → Array AST × AST
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

def consWith (xs : List AST) (init : AST) : AST :=
  xs.foldr (init := init) cons

def reservedSyms : Std.RBSet String compare := .ofList [
  "NIL",
  "T",
  "CURRENT-ENV",
  "BEGIN",
  "IF",
  "LAMBDA",
  "LET",
  "LETREC",
  "QUOTE",
  "ATOM",
  "CAR",
  "CDR",
  "EMIT",
  "COMMIT",
  "COMM",
  "OPEN",
  "NUM",
  "CHAR",
  "CONS",
  "STRCONS",
  "+" ,
  "-" ,
  "*" ,
  "/" ,
  "=" ,
  "<" ,
  ">" ,
  "<=" ,
  ">=" ,
  "EQ",
  "HIDE"
] _

open Std Format in
partial def toFormat (esc : Bool) : AST → Format
  | num n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => if esc && !reservedSyms.contains s then s!"|{s}|" else s
  | x@(.cons ..) =>
    match x.telescopeCons with
    | (xs, nil) => paren $ fmtList xs.data
    | (xs, y) => paren $ fmtList xs.data ++ line ++ "." ++ line ++ (y.toFormat esc)
where
  fmtList : List AST → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ (x.toFormat esc)) (x.toFormat esc)

def toString (esc : Bool) : AST → String :=
  ToString.toString ∘ toFormat esc

instance : Std.ToFormat AST := ⟨toFormat false⟩
instance : ToString AST := ⟨toString false⟩

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[$xs,*]) => do
    let ret ← xs.getElems.foldrM (fun x xs => `(AST.cons $x $xs)) (← `(AST.nil))
    return ret

/-- This helper is needed for the DSL and for the parser -/
def mkQuote (x : AST) : AST :=
  ~[sym "QUOTE", x]

class ToAST (α : Type _) where
  toAST : α → AST

export ToAST (toAST)

instance : ToAST Nat where
  toAST := .num

instance : ToAST Char where
  toAST := .char

instance : ToAST String where
  toAST := .str

instance (priority := low) : ToAST Lean.Name where
  toAST n := .sym (n.toString false)

instance [ToAST α] : ToAST (List α) where
  toAST es := AST.consWith (es.map toAST) .nil

instance [ToAST α] : ToAST (Array α) where
  toAST es := AST.consWith (es.data.map toAST) .nil

instance : ToAST AST := ⟨id⟩

end Lurk.Syntax.AST
