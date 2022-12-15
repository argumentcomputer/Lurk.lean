import Lean
import Lurk.Backend.Expr

namespace Lurk.Backend.DSL
open Lean Elab Meta Term

/- `atom` clashes with something in core -/
declare_syntax_cat    atom_
scoped syntax "t"   : atom_
scoped syntax "nil" : atom_
scoped syntax "T"   : atom_
scoped syntax "NIL" : atom_
scoped syntax num   : atom_
scoped syntax char  : atom_
scoped syntax str   : atom_

def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)
  | `(atom_| t) => return mkConst ``Atom.t
  | `(atom_| NIL)
  | `(atom_| nil) => return mkConst ``Atom.nil
  | `(atom_| $n:num) => do mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(atom_| $c:char) => do
    mkAppM ``Atom.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(atom_| $s:str) => mkAppM ``Atom.str #[mkStrLit s.getString]
  | _ => throwUnsupportedSyntax

declare_syntax_cat       op₁
scoped syntax "atom"   : op₁
scoped syntax "ATOM"   : op₁
scoped syntax "car"    : op₁
scoped syntax "CAR"    : op₁
scoped syntax "cdr"    : op₁
scoped syntax "CDR"    : op₁
scoped syntax "emit"   : op₁
scoped syntax "EMIT"   : op₁
scoped syntax "commit" : op₁
scoped syntax "COMMIT" : op₁
scoped syntax "comm"   : op₁
scoped syntax "COMM"   : op₁
scoped syntax "open"   : op₁
scoped syntax "OPEN"   : op₁
scoped syntax "num"    : op₁
scoped syntax "NUM"    : op₁
scoped syntax "u64"    : op₁
scoped syntax "U64"    : op₁
scoped syntax "char"   : op₁
scoped syntax "CHAR"   : op₁

def elabOp₁ : TSyntax `op₁ → TermElabM Lean.Expr
  | `(op₁| ATOM)   | `(op₁| atom)   => return mkConst ``Op₁.atom
  | `(op₁| CAR)    | `(op₁| car)    => return mkConst ``Op₁.car
  | `(op₁| CDR)    | `(op₁| cdr)    => return mkConst ``Op₁.cdr
  | `(op₁| EMIT)   | `(op₁| emit)   => return mkConst ``Op₁.emit
  | `(op₁| COMMIT) | `(op₁| commit) => return mkConst ``Op₁.commit
  | `(op₁| COMM)   | `(op₁| comm)   => return mkConst ``Op₁.comm
  | `(op₁| OPEN)   | `(op₁| open)   => return mkConst ``Op₁.open
  | `(op₁| NUM)    | `(op₁| num)    => return mkConst ``Op₁.num
  | `(op₁| U64)    | `(op₁| u64)    => return mkConst ``Op₁.num
  | `(op₁| CHAR)   | `(op₁| char)   => return mkConst ``Op₁.char
  | _ => throwUnsupportedSyntax

declare_syntax_cat        op₂
scoped syntax "cons"    : op₂
scoped syntax "CONS"    : op₂
scoped syntax "strcons" : op₂
scoped syntax "STRCONS" : op₂
scoped syntax "+"       : op₂
scoped syntax "-"       : op₂
scoped syntax "*"       : op₂
scoped syntax "/"       : op₂
scoped syntax "="       : op₂
scoped syntax "<"       : op₂
scoped syntax ">"       : op₂
scoped syntax "<="      : op₂
scoped syntax ">="      : op₂
scoped syntax "eq"      : op₂
scoped syntax "EQ"      : op₂
scoped syntax "hide"    : op₂
scoped syntax "HIDE"    : op₂

def elabOp₂ : TSyntax `op₂ → TermElabM Lean.Expr
  | `(op₂| CONS)    | `(op₂| cons)    => return mkConst ``Op₂.cons
  | `(op₂| STRCONS) | `(op₂| strcons) => return mkConst ``Op₂.strcons
  | `(op₂| EQ)      | `(op₂| eq)      => return mkConst ``Op₂.eq
  | `(op₂| HIDE)    | `(op₂| hide)    => return mkConst ``Op₂.hide
  | `(op₂| +)  => return mkConst ``Op₂.add
  | `(op₂| -)  => return mkConst ``Op₂.sub
  | `(op₂| *)  => return mkConst ``Op₂.mul
  | `(op₂| /)  => return mkConst ``Op₂.div
  | `(op₂| =)  => return mkConst ``Op₂.numEq
  | `(op₂| <)  => return mkConst ``Op₂.lt
  | `(op₂| >)  => return mkConst ``Op₂.gt
  | `(op₂| <=) => return mkConst ``Op₂.le
  | `(op₂| >=) => return mkConst ``Op₂.ge
  | _ => throwUnsupportedSyntax

declare_syntax_cat          sym
scoped syntax ident       : sym
scoped syntax "|" sym "|" : sym

def elabSymStr : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) => return mkStrLit i.getId.toString.toUpper
  | `(sym| |$i:ident|) => return mkStrLit i.getId.toString
  | _ => throwUnsupportedSyntax

declare_syntax_cat                         expr
scoped syntax atom_                      : expr
scoped syntax sym                        : expr
scoped syntax "(" "current-env" ")"      : expr
scoped syntax "(" "CURRENT-ENV" ")"      : expr
scoped syntax op₁ expr                   : expr
scoped syntax op₂ expr expr              : expr
scoped syntax "begin" expr*              : expr
scoped syntax "BEGIN" expr*              : expr
scoped syntax "if" expr expr expr        : expr
scoped syntax "IF" expr expr expr        : expr
scoped syntax "(" expr+ ")"              : expr
scoped syntax "lambda" "(" sym* ")" expr : expr
scoped syntax "LAMBDA" "(" sym* ")" expr : expr
scoped syntax "quote" expr               : expr
scoped syntax "QUOTE" expr               : expr
scoped syntax "," expr                   : expr
scoped syntax "(" expr ")"               : expr

declare_syntax_cat binder
scoped syntax "(" sym expr ")" : binder

scoped syntax "let"    "(" binder* ")" expr : expr
scoped syntax "LET"    "(" binder* ")" expr : expr
scoped syntax "letrec" "(" binder* ")" expr : expr
scoped syntax "LETREC" "(" binder* ")" expr : expr

mutual

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $a:atom_) => do mkAppM ``Expr.atom #[← elabAtom a]
  | `(expr| ($a:atom_)) => do mkAppM ``Expr.app₀ #[← mkAppM ``Expr.atom #[← elabAtom a]]
  | `(expr| $s:sym) => do mkAppM ``Expr.sym #[← elabSymStr s]
  | `(expr| ($s:sym)) => do mkAppM ``Expr.app₀ #[← mkAppM ``Expr.sym #[← elabSymStr s]]
  | `(expr| (current-env)) | `(expr| (CURRENT-ENV)) => return mkConst ``Expr.env
  | `(expr| $o:op₁ $e:expr) => do mkAppM ``Expr.op₁ #[← elabOp₁ o, ← elabExpr e]
  | `(expr| $o:op₂ $e₁:expr $e₂:expr) => do
    mkAppM ``Expr.op₂ #[← elabOp₂ o, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| BEGIN) | `(expr| begin) => mkAppM ``Expr.atom #[mkConst ``Atom.nil]
  | `(expr| BEGIN $es:expr* $e:expr) | `(expr| begin $es:expr* $e:expr) => do
    es.foldrM (init := ← elabExpr e) fun e acc => do
      mkAppM ``Expr.begin #[← elabExpr e, acc]
  | `(expr| IF $a:expr $b:expr $c:expr)
  | `(expr| if $a:expr $b:expr $c:expr) => do
    mkAppM ``Expr.if #[← elabExpr a, ← elabExpr b, ← elabExpr c]
  | `(expr| ($e:expr $es:expr*)) => do
    es.foldlM (init := ← elabExpr e) fun acc e => do
      mkAppM ``Expr.app #[acc, ← elabExpr e]
  | `(expr| LAMBDA () $b:expr)
  | `(expr| lambda () $b:expr) => do
    mkAppM ``Expr.lambda #[mkStrLit "_", ← elabExpr b]
  | `(expr| ((LAMBDA () $b:expr)))
  | `(expr| ((lambda () $b:expr))) => do
    mkAppM ``Expr.app₀ #[← mkAppM ``Expr.lambda #[mkStrLit "_", ← elabExpr b]]
  | `(expr| LAMBDA ($ss:sym* $s:sym) $b:expr)
  | `(expr| lambda ($ss:sym* $s:sym) $b:expr) => do
    let init ← mkAppM ``Expr.lambda #[← elabSymStr s, ← elabExpr b]
    ss.foldrM (init := init) fun s acc => do
      mkAppM ``Expr.lambda #[← elabSymStr s, acc]
  | `(expr| LET () $bd:expr)
  | `(expr| let () $bd:expr) => elabExpr bd
  | `(expr| LET ($bs:binder* $b:binder) $bd:expr)
  | `(expr| let ($bs:binder* $b:binder) $bd:expr) => do
    let (initS, initV) ← elabBinder b
    let init ← mkAppM ``Expr.let #[initS, initV, ← elabExpr bd]
    bs.foldrM (init := init) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.let #[s, v, acc]
  | `(expr| LETREC () $bd:expr)
  | `(expr| letrec () $bd:expr) => elabExpr bd
  | `(expr| LETREC ($bs:binder* $b:binder) $bd:expr)
  | `(expr| letrec ($bs:binder* $b:binder) $bd:expr) => do
    let (initS, initV) ← elabBinder b
    let init ← mkAppM ``Expr.letrec #[initS, initV, ← elabExpr bd]
    bs.foldrM (init := init) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.letrec #[s, v, acc]
  | `(expr| QUOTE $e:expr) | `(expr| quote $e:expr) | `(expr| ,$e:expr) => do
    mkAppM ``Expr.quote #[← elabExpr e]
  | `(expr| ($e:expr)) => elabExpr e
  | `(expr| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``Expr.toExpr #[e]
    else throwUnsupportedSyntax

partial def elabBinder : TSyntax `binder → TermElabM (Lean.Expr × Lean.Expr)
  | `(binder| ($s:sym $v:expr)) => return (← elabSymStr s, ← elabExpr v)
  | _ => throwUnsupportedSyntax

end

scoped elab "⟦" e:expr "⟧" : term =>
  elabExpr e

end Lurk.Backend.DSL
