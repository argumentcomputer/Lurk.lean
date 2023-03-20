import Lean
import Lurk.LDON
import Lurk.Keywords

namespace Lurk.LDON.DSL

open Lean Elab Meta Term

declare_syntax_cat    sym
scoped syntax ident : sym
scoped syntax atom_ : sym
scoped syntax op₁   : sym
scoped syntax op₂   : sym
-- these can't be simple idents because they'd clash with Lean's syntax
scoped syntax "if"  : sym
scoped syntax "IF"  : sym
scoped syntax "let" : sym
scoped syntax "LET" : sym
scoped syntax "letrec" : sym
scoped syntax "LETREC" : sym
scoped syntax "lambda" : sym
scoped syntax "LAMBDA" : sym
scoped syntax "begin" : sym
scoped syntax "BEGIN" : sym
scoped syntax "quote" : sym
scoped syntax "QUOTE" : sym
scoped syntax "eval" : sym
scoped syntax "EVAL" : sym
-- a workaround for the dash
scoped syntax "current-env" : sym
scoped syntax "CURRENT-ENV" : sym
-- escaping symbols
scoped syntax "|" sym "|" : sym
-- symbols with a dot followed by a number
scoped syntax ident noWs "." noWs num : sym
scoped syntax "[anonymous]" : sym

def mergeWithDot (s : String) (n : Nat) : String :=
  s!"{s}.{n}"

private def mkSym (sym : String) :=
  mkAppM ``LDON.sym #[mkStrLit sym]

open Lurk.DSL in
def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)   | `(atom_| t)   => mkSym "T"
  | `(atom_| NIL) | `(atom_| nil) => mkSym "NIL"
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
def elabOp₁ : TSyntax `op₁ → TermElabM Lean.Expr
  | `(op₁| ATOM)   | `(op₁| atom)   => mkSym "ATOM"
  | `(op₁| CAR)    | `(op₁| car)    => mkSym "CAR"
  | `(op₁| CDR)    | `(op₁| cdr)    => mkSym "CDR"
  | `(op₁| EMIT)   | `(op₁| emit)   => mkSym "EMIT"
  | `(op₁| COMMIT) | `(op₁| commit) => mkSym "COMMIT"
  | `(op₁| COMM)   | `(op₁| comm)   => mkSym "COMM"
  | `(op₁| OPEN)   | `(op₁| open)   => mkSym "OPEN"
  | `(op₁| NUM)    | `(op₁| num)    => mkSym "NUM"
  | `(op₁| U64)    | `(op₁| u64)    => mkSym "U64"
  | `(op₁| CHAR)   | `(op₁| char)   => mkSym "CHAR"
  | _ => throwUnsupportedSyntax
  
open Lurk.DSL in
def elabOp₂ : TSyntax `op₂ → TermElabM Lean.Expr
  | `(op₂| CONS)    | `(op₂| cons)    => mkSym "CONS"
  | `(op₂| STRCONS) | `(op₂| strcons) => mkSym "STRCONS"
  | `(op₂| EQ)      | `(op₂| eq)      => mkSym "EQ"
  | `(op₂| HIDE)    | `(op₂| hide)    => mkSym "HIDE"
  | `(op₂| +)  => mkSym "+"
  | `(op₂| -)  => mkSym "-"
  | `(op₂| *)  => mkSym "*"
  | `(op₂| /)  => mkSym "/"
  | `(op₂| %)  => mkSym "%"
  | `(op₂| =)  => mkSym "="
  | `(op₂| <)  => mkSym "<"
  | `(op₂| >)  => mkSym ">"
  | `(op₂| <=) => mkSym "<="
  | `(op₂| >=) => mkSym ">="
  | _ => throwUnsupportedSyntax

partial def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) =>
    let i  := i.getId.toString
    let iU := i.toUpper
    if LDON.reservedSyms.contains iU then
      mkSym iU
    else
      mkSym i
  | `(sym| $a:atom_) => elabAtom a
  | `(sym| $o:op₁) => elabOp₁ o
  | `(sym| $o:op₂) => elabOp₂ o
  | `(sym| current-env) | `(sym| CURRENT-ENV) => mkSym "CURRENT-ENV"
  | `(sym| if)          | `(sym| IF)          => mkSym "IF"
  | `(sym| let)         | `(sym| LET)         => mkSym "LET"
  | `(sym| letrec)      | `(sym| LETREC)      => mkSym "LETREC"
  | `(sym| lambda)      | `(sym| LAMBDA)      => mkSym "LAMBDA"
  | `(sym| begin)       | `(sym| BEGIN)       => mkSym "BEGIN"
  | `(sym| quote)       | `(sym| QUOTE)       => mkSym "QUOTE"
  | `(sym| eval)        | `(sym| EVAL)        => mkSym "EVAL"
  | `(sym| | $i:ident |) => mkSym i.getId.toString
  | `(sym| | current-env |)  => mkSym "current-env"
  | `(sym| | if |)  => mkSym "if"  
  | `(sym| | let |) => mkSym "let"
  | `(sym| $i:ident.$n:num)
  | `(sym| | $i:ident.$n:num |) => do
    let sym ← mkAppM ``mergeWithDot #[mkStrLit i.getId.toString, mkNatLit n.getNat]
    mkAppM ``LDON.sym #[sym]
  | `(sym| [anonymous])
  | `(sym| |[anonymous]|) => mkSym "[anonymous]"
  | _ => throwUnsupportedSyntax

declare_syntax_cat                       ldon
scoped syntax num                      : ldon
scoped syntax char                     : ldon
scoped syntax str                      : ldon
scoped syntax sym                      : ldon
scoped syntax "(" ldon* ")"            : ldon
scoped syntax "(" ldon+ " . " ldon ")" : ldon
scoped syntax "," ldon                 : ldon -- quoting

mutual

partial def elabLDONCons (xs : Array $ TSyntax `ldon) (init : Expr) : TermElabM Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``LDON.cons #[← elabLDON e, acc]

partial def elabLDON : TSyntax `ldon → TermElabM Expr
  | `(ldon| $n:num) => do mkAppM ``LDON.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(ldon| $c:char) => do
    mkAppM ``LDON.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ldon| $s:str) => mkAppM ``LDON.str #[mkStrLit s.getString]
  | `(ldon| $s:sym) => elabSym s
  | `(ldon| ()) => pure $ mkConst ``LDON.nil
  | `(ldon| ($xs*)) => elabLDONCons xs (mkConst ``LDON.nil)
  | `(ldon| ($x . $y)) => do mkAppM ``LDON.cons #[← elabLDON x, ← elabLDON y]
  | `(ldon| ($xs* . $x)) => do elabLDONCons xs (← elabLDON x)
  | `(ldon| ,$x:ldon) => do mkAppM ``LDON.mkQuote #[← elabLDON x]
  | `(ldon| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``LDON.toLDON #[e]
    else throwUnsupportedSyntax

end

scoped elab "⟪" x:ldon "⟫" : term =>
  elabLDON x

end Lurk.LDON.DSL
