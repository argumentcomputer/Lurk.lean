import Lean
import Lurk.LDONDSL
import Lurk.ExprLDON

namespace Lurk.Expr.DSL

open Lean Elab Meta Term

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

declare_syntax_cat                                   expr
scoped syntax atom_                                : expr
scoped syntax ident                                : expr
scoped syntax "(" "current-env" ")"                : expr
scoped syntax "(" "CURRENT-ENV" ")"                : expr
scoped syntax "(" op₁ expr ")"                     : expr
scoped syntax "(" op₂ expr expr ")"                : expr
scoped syntax "(" "begin" expr* ")"                : expr
scoped syntax "(" "BEGIN" expr* ")"                : expr
scoped syntax "(" "if" expr expr expr ")"          : expr
scoped syntax "(" "IF" expr expr expr ")"          : expr
scoped syntax "(" "lambda" "(" ident* ")" expr ")" : expr
scoped syntax "(" "LAMBDA" "(" ident* ")" expr ")" : expr
scoped syntax "(" "quote" ldon ")"                 : expr
scoped syntax "(" "QUOTE" ldon ")"                 : expr
scoped syntax "," ldon                             : expr
scoped syntax "(" "eval" expr (expr)? ")"          : expr
scoped syntax "(" "EVAL" expr (expr)? ")"          : expr
scoped syntax "(" expr+ ")"                        : expr

declare_syntax_cat binder
scoped syntax "(" ident expr ")" : binder

scoped syntax "(" "let"    "(" binder* ")" expr ")" : expr
scoped syntax "(" "LET"    "(" binder* ")" expr ")" : expr
scoped syntax "(" "letrec" "(" binder* ")" expr ")" : expr
scoped syntax "(" "LETREC" "(" binder* ")" expr ")" : expr

open Lurk.LDON.DSL in
mutual

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $a:atom_) => do mkAppM ``Expr.atom #[← elabAtom a]
  | `(expr| $s:ident) => do mkAppM ``Expr.sym #[mkStrLit s.getId.toString]
  | `(expr| (current-env)) | `(expr| (CURRENT-ENV)) => return mkConst ``Expr.env
  | `(expr| ($o:op₁ $e)) => do mkAppM ``Expr.op₁ #[← elabOp₁ o, ← elabExpr e]
  | `(expr| ($o:op₂ $e₁ $e₂)) => do
    mkAppM ``Expr.op₂ #[← elabOp₂ o, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| (BEGIN)) | `(expr| (begin)) => mkAppM ``Expr.atom #[mkConst ``Atom.nil]
  | `(expr| (BEGIN $es* $e)) | `(expr| (begin $es* $e)) => do
    es.foldrM (init := ← elabExpr e) fun e acc => do
      mkAppM ``Expr.begin #[← elabExpr e, acc]
  | `(expr| (IF $a $b $c)) | `(expr| (if $a $b $c)) => do
    mkAppM ``Expr.if #[← elabExpr a, ← elabExpr b, ← elabExpr c]
  | `(expr| (LAMBDA ($ss*) $b:expr))
  | `(expr| (lambda ($ss*) $b:expr)) => do
    if ss.size == 0 then
      mkAppM ``Expr.lambda #[mkStrLit "_", ← elabExpr b]
    else
      ss.foldrM (init := ← elabExpr b) fun s acc => do
        mkAppM ``Expr.lambda #[mkStrLit s.getId.toString, acc]
  | `(expr| (LET ($bs*) $bd:expr))
  | `(expr| (let ($bs*) $bd:expr)) => do
    bs.foldrM (init := ← elabExpr bd) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.let #[s, v, acc]
  | `(expr| (LETREC ($bs*) $bd:expr))
  | `(expr| (letrec ($bs*) $bd:expr)) => do
    bs.foldrM (init := ← elabExpr bd) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.letrec #[s, v, acc]
  | `(expr| (QUOTE $d)) | `(expr| (quote $d)) | `(expr| ,$d) => do
    mkAppM ``Expr.quote #[← elabLDON d]
  | `(expr| (EVAL $e $(env?)?)) | `(expr| (eval $e $(env?)?)) => do
    let env := ← match env? with
      | some env? => elabExpr env?
      | none => return mkConst ``Expr.nil
    mkAppM ``Expr.eval #[← elabExpr e, env]
  | `(expr| ($e:expr $es:expr*)) => do
    if es.size == 0 then
      mkAppM ``Expr.app₀ #[← elabExpr e]
    else
      es.foldlM (init := ← elabExpr e) fun acc e => do
        mkAppM ``Expr.app #[acc, ← elabExpr e]
  | `(expr| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``Expr.toExpr #[e]
    else throwUnsupportedSyntax

partial def elabBinder : TSyntax `binder → TermElabM (Lean.Expr × Lean.Expr)
  | `(binder| ($s:ident $v:expr)) => return (mkStrLit s.getId.toString, ← elabExpr v)
  | _ => throwUnsupportedSyntax

end


scoped elab "⟦" e:expr "⟧" : term =>
  elabExpr e

end Lurk.Expr.DSL
