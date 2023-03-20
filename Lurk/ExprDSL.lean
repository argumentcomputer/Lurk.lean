import Lean
import Lurk.LDONDSL
import Lurk.ExprLDON

namespace Lurk.Expr.DSL

open Lean Elab Meta Term

open Lurk.DSL in
def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)   | `(atom_| t)   => return mkConst ``Atom.t
  | `(atom_| NIL) | `(atom_| nil) => return mkConst ``Atom.nil
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
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

open Lurk.DSL in
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
scoped syntax num                                  : expr
scoped syntax char                                 : expr
scoped syntax str                                  : expr
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
scoped syntax (priority := low) "(" expr* ")"      : expr

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
  | `(expr| $n:num) => do
    let atom ← mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
    mkAppM ``Expr.atom #[atom]
  | `(expr| $c:char) => do
    let atom ← mkAppM ``Atom.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
    mkAppM ``Expr.atom #[atom]
  | `(expr| $s:str) => do
    let atom ← mkAppM ``Atom.str #[mkStrLit s.getString]
    mkAppM ``Expr.atom #[atom]
  | `(expr| (current-env)) | `(expr| (CURRENT-ENV)) => return mkConst ``Expr.env
  | `(expr| ($o:op₁ $e)) => do mkAppM ``Expr.op₁ #[← elabOp₁ o, ← elabExpr e]
  | `(expr| ($o:op₂ $e₁ $e₂)) => do
    mkAppM ``Expr.op₂ #[← elabOp₂ o, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| (BEGIN)) | `(expr| (begin)) => mkAppM ``Expr.atom #[mkConst ``Atom.nil]
  | `(expr| (BEGIN $es*)) | `(expr| (begin $es*)) => do
    es.foldrM (init := mkConst ``Expr.nil) fun e acc => do
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
  | `(expr| ()) => return mkConst ``Expr.nil
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
