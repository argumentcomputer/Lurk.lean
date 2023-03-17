import Lean
import Lurk.ExprLDON

namespace Lurk.DSL
open Lean Elab Meta Term

declare_syntax_cat                      ldon
scoped syntax num                     : ldon
scoped syntax str                     : ldon
scoped syntax ident                   : ldon
scoped syntax "(" ldon " . " ldon ")" : ldon
scoped syntax "(" ldon* ")"           : ldon

partial def elabLDON : TSyntax `ldon → TermElabM Lean.Expr
  | `(ldon| $n:num) => do
    mkAppM ``LDON.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(ldon| $s:str) => mkAppM ``LDON.str #[mkStrLit s.getString]
  | `(ldon| $s:ident) => mkAppM ``LDON.sym #[mkStrLit s.getId.toString]
  | `(ldon| ($d₁:ldon . $d₂:ldon)) => do
    mkAppM ``LDON.cons #[← elabLDON d₁, ← elabLDON d₂]
  | `(ldon| ($ds:ldon*)) => do
    ds.foldrM (init := ← mkAppM ``LDON.sym #[mkStrLit "NIL"]) fun v acc => do
      mkAppM ``LDON.cons #[← elabLDON v, acc]
  | `(ldon| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``LDON.ToLDON.toLDON #[e]
    else throwUnsupportedSyntax

/- `atom` clashes with something in core -/
declare_syntax_cat    atom_
scoped syntax "t"   : atom_
scoped syntax "T"   : atom_
scoped syntax "nil" : atom_
scoped syntax "NIL" : atom_
scoped syntax num   : atom_
scoped syntax char  : atom_
scoped syntax str   : atom_

def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)   | `(atom_| t)   => return mkConst ``Atom.t
  | `(atom_| NIL) | `(atom_| nil) => return mkConst ``Atom.nil
  | `(atom_| $n:num) => do
    mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
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
  | `(op₁| U64)    | `(op₁| u64)    => return mkConst ``Op₁.u64
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
scoped syntax "%"       : op₂
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
  | `(op₂| %)  => return mkConst ``Op₂.mod
  | `(op₂| =)  => return mkConst ``Op₂.numEq
  | `(op₂| <)  => return mkConst ``Op₂.lt
  | `(op₂| >)  => return mkConst ``Op₂.gt
  | `(op₂| <=) => return mkConst ``Op₂.le
  | `(op₂| >=) => return mkConst ``Op₂.ge
  | _ => throwUnsupportedSyntax

declare_syntax_cat                           expr
scoped syntax atom_                        : expr
scoped syntax ident                        : expr
scoped syntax "(" "current-env" ")"        : expr
scoped syntax "(" "CURRENT-ENV" ")"        : expr
scoped syntax op₁ expr                     : expr
scoped syntax op₂ expr expr                : expr
scoped syntax "begin" expr*                : expr
scoped syntax "BEGIN" expr*                : expr
scoped syntax "if" expr expr expr          : expr
scoped syntax "IF" expr expr expr          : expr
scoped syntax "(" expr+ ")"                : expr
scoped syntax "lambda" "(" ident* ")" expr : expr
scoped syntax "LAMBDA" "(" ident* ")" expr : expr
scoped syntax "quote" ldon                 : expr
scoped syntax "QUOTE" ldon                 : expr
scoped syntax "eval" expr                  : expr
scoped syntax "eval" expr expr             : expr
scoped syntax "EVAL" expr                  : expr
scoped syntax "EVAL" expr expr             : expr
scoped syntax "," ldon                     : expr
scoped syntax "(" (expr)? ")"              : expr

scoped syntax (priority := low) "QUOTE" expr : expr
scoped syntax (priority := low) "quote" expr : expr

declare_syntax_cat binder
scoped syntax "(" ident expr ")" : binder

scoped syntax "let"    "(" binder* ")" expr : expr
scoped syntax "LET"    "(" binder* ")" expr : expr
scoped syntax "letrec" "(" binder* ")" expr : expr
scoped syntax "LETREC" "(" binder* ")" expr : expr

mutual

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $a:atom_) => do mkAppM ``Expr.atom #[← elabAtom a]
  | `(expr| ($a:atom_)) => do mkAppM ``Expr.app₀ #[← mkAppM ``Expr.atom #[← elabAtom a]]
  | `(expr| $s:ident) => do mkAppM ``Expr.sym #[mkStrLit s.getId.toString]
  | `(expr| ($s:ident)) => do mkAppM ``Expr.app₀ #[← mkAppM ``Expr.sym #[mkStrLit s.getId.toString]]
  | `(expr| (current-env)) | `(expr| (CURRENT-ENV)) => return mkConst ``Expr.env
  | `(expr| $o:op₁ $e:expr) => do mkAppM ``Expr.op₁ #[← elabOp₁ o, ← elabExpr e]
  | `(expr| $o:op₂ $e₁:expr $e₂:expr) => do
    mkAppM ``Expr.op₂ #[← elabOp₂ o, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| BEGIN) | `(expr| begin) => return mkConst ``Expr.nil
  | `(expr| BEGIN $es:expr*) | `(expr| begin $es:expr*) => do
    es.foldrM (init := mkConst ``Expr.nil) fun e acc => do
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
  | `(expr| LAMBDA ($ss:ident* $s:ident) $b:expr)
  | `(expr| lambda ($ss:ident* $s:ident) $b:expr) => do
    let init ← mkAppM ``Expr.lambda #[mkStrLit s.getId.toString, ← elabExpr b]
    ss.foldrM (init := init) fun s acc => do
      mkAppM ``Expr.lambda #[mkStrLit s.getId.toString, acc]
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
  | `(expr| QUOTE $d:ldon) | `(expr| quote $d:ldon) | `(expr| ,$d:ldon) => do
    mkAppM ``Expr.quote #[← elabLDON d]
  | `(expr| QUOTE $e:expr) | `(expr| quote $e:expr) => do
    mkAppM ``Expr.quote #[← mkAppM ``Expr.toLDON #[← elabExpr e]]
  | `(expr| EVAL $e:expr) | `(expr| eval $e:expr) => do
    mkAppM ``Expr.eval₁ #[← elabExpr e]
  | `(expr| EVAL $e₁:expr $e₂:expr) | `(expr| eval $e₁:expr $e₂:expr) => do
    mkAppM ``Expr.eval₂ #[← elabExpr e₁, ← elabExpr e₂]
  | `(expr| ()) => return mkConst ``Expr.nil
  | `(expr| ($e:expr)) => elabExpr e
  | `(expr| $x) =>
    if x.raw.isAntiquot then do
      let e ← elabTerm x.raw.getAntiquotTerm none
      mkAppM ``Expr.toExpr #[← whnf e]
    else throwUnsupportedSyntax

partial def elabBinder : TSyntax `binder → TermElabM (Lean.Expr × Lean.Expr)
  | `(binder| ($s:ident $v:expr)) => return (mkStrLit s.getId.toString, ← elabExpr v)
  | _ => throwUnsupportedSyntax

end

scoped elab "⟦" e:expr "⟧" : term =>
  elabExpr e

end Lurk.DSL
