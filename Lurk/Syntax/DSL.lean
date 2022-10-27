import Lurk.Syntax.ExprUtils

namespace Lurk.Syntax
open Lean Elab Meta Term

namespace DSL

def mkNameLit (name : String) :=
  mkAppM ``Name.mkSimple #[mkStrLit name]

declare_syntax_cat lurk_literal
scoped syntax "t"       : lurk_literal
scoped syntax "nil"     : lurk_literal
scoped syntax num       : lurk_literal
scoped syntax str       : lurk_literal
scoped syntax char      : lurk_literal

def elabLiteral : Syntax → TermElabM Lean.Expr
  | `(lurk_literal| t)   => return mkConst ``Lurk.Syntax.Literal.t
  | `(lurk_literal| nil) => return mkConst ``Lurk.Syntax.Literal.nil
  | `(lurk_literal| $n:num) => do
    mkAppM ``Lurk.Syntax.mkNumLit #[mkNatLit n.getNat]
  | `(lurk_literal| $s:str) =>
    mkAppM ``Lurk.Syntax.Literal.str #[mkStrLit s.getString]
  | `(lurk_literal| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Syntax.Literal.char #[c]
  | _ => throwUnsupportedSyntax

end DSL

namespace SExpr.DSL

declare_syntax_cat                         sexpr
scoped syntax lurk_literal               : sexpr
scoped syntax ident                      : sexpr
scoped syntax "(" sexpr* ")"             : sexpr
scoped syntax "(" sexpr+ " . " sexpr ")" : sexpr

partial def elabSExpr : Syntax → TermElabM Lean.Expr
  | `(sexpr| $l:lurk_literal) => do
    mkAppM ``SExpr.lit #[← DSL.elabLiteral l]
  | `(sexpr| $i:ident) => do
    mkAppM ``SExpr.sym #[← DSL.mkNameLit i.getId.toString]
  | `(sexpr| ($es*)) => do
    let es ← es.mapM fun e => elabSExpr e
    mkAppM ``mkList #[← mkListLit (mkConst ``SExpr) es.data]
  | `(sexpr| ($es* . $tail)) => do
    let es ← es.mapM fun e => elabSExpr e
    mkAppM ``mkListWith #[← mkListLit (mkConst ``SExpr) es.data, ← elabSExpr tail]
  | `(sexpr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``ToSExpr.toSExpr #[e]
    else 
      throwUnsupportedSyntax 

elab "[sexpr| " e:sexpr "]" : term =>
  elabSExpr e

end SExpr.DSL

namespace DSL

declare_syntax_cat lurk_bin_op
scoped syntax "+ "      : lurk_bin_op
scoped syntax "- "      : lurk_bin_op
scoped syntax "* "      : lurk_bin_op
scoped syntax "/ "      : lurk_bin_op
scoped syntax "= "      : lurk_bin_op
scoped syntax "< "      : lurk_bin_op
scoped syntax "> "      : lurk_bin_op
scoped syntax "<= "     : lurk_bin_op
scoped syntax ">= "     : lurk_bin_op
scoped syntax "eq "     : lurk_bin_op

def elabLurkBinOp : Syntax → TermElabM Lean.Expr
  | `(lurk_bin_op| +)  => return mkConst ``Lurk.Syntax.BinaryOp.sum
  | `(lurk_bin_op| -)  => return mkConst ``Lurk.Syntax.BinaryOp.diff
  | `(lurk_bin_op| *)  => return mkConst ``Lurk.Syntax.BinaryOp.prod
  | `(lurk_bin_op| /)  => return mkConst ``Lurk.Syntax.BinaryOp.quot
  | `(lurk_bin_op| =)  => return mkConst ``Lurk.Syntax.BinaryOp.numEq
  | `(lurk_bin_op| <)  => return mkConst ``Lurk.Syntax.BinaryOp.lt
  | `(lurk_bin_op| >)  => return mkConst ``Lurk.Syntax.BinaryOp.gt
  | `(lurk_bin_op| <=) => return mkConst ``Lurk.Syntax.BinaryOp.le
  | `(lurk_bin_op| >=) => return mkConst ``Lurk.Syntax.BinaryOp.ge
  | `(lurk_bin_op| eq) => return mkConst ``Lurk.Syntax.BinaryOp.eq
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_expr
declare_syntax_cat lurk_binding
declare_syntax_cat lurk_bindings

scoped syntax "(" ident lurk_expr ")" : lurk_binding
scoped syntax  "(" lurk_binding* ")"  : lurk_bindings

scoped syntax lurk_literal                               : lurk_expr
scoped syntax ident                                      : lurk_expr
scoped syntax "(" "if" lurk_expr lurk_expr lurk_expr ")" : lurk_expr
scoped syntax "(" "lambda" "(" ident* ")" lurk_expr ")"  : lurk_expr
scoped syntax "(" "let" lurk_bindings lurk_expr ")"      : lurk_expr
scoped syntax "(" "letrec" lurk_bindings lurk_expr ")"   : lurk_expr
scoped syntax "(" "mutrec" lurk_bindings lurk_expr ")"   : lurk_expr
scoped syntax "(" "quote " sexpr ")"                     : lurk_expr
scoped syntax "," sexpr                                  : lurk_expr
scoped syntax "(" lurk_bin_op lurk_expr lurk_expr ")"    : lurk_expr
scoped syntax "(" "car" lurk_expr ")"                    : lurk_expr
scoped syntax "(" "cdr" lurk_expr ")"                    : lurk_expr
scoped syntax "(" "atom" lurk_expr ")"                   : lurk_expr
scoped syntax "(" "emit" lurk_expr ")"                   : lurk_expr
scoped syntax "(" "cons" lurk_expr lurk_expr ")"         : lurk_expr
scoped syntax "(" "strcons" lurk_expr lurk_expr ")"      : lurk_expr
scoped syntax "(" "begin" lurk_expr*  ")"                : lurk_expr
scoped syntax "current-env"                              : lurk_expr
scoped syntax "(" lurk_expr* ")"                         : lurk_expr

/-- There are no type guarentees. -/
partial def elabLurkIdents (i : TSyntax `ident) : TermElabM Lean.Expr := do 
  if i.raw.isAntiquot then 
    let stx := i.raw.getAntiquotTerm
    let e ← elabTerm stx none
    let e ← whnf e
    let type ← inferType e
    match type.getAppFn with 
    | .const ``List _ => return e
    | _ => 
      let «nil» ← mkAppOptM ``List.nil #[some (mkConst ``Lean.Name)]
      mkAppM ``List.cons #[e, «nil»]
  else
    let «nil» ← mkAppOptM ``List.nil #[some (mkConst ``Lean.Name)]
    mkAppM ``List.cons #[← mkNameLit i.getId.toString, «nil»]

mutual 
partial def elabLurkBinding : Syntax → TermElabM Lean.Expr 
  | `(lurk_binding| ($name $body)) => do
    mkAppM ``Prod.mk #[← mkNameLit name.getId.toString, ← elabLurkExpr body]
  | _ => throwUnsupportedSyntax

partial def elabLurkBindings : Syntax → TermElabM Lean.Expr
  | `(lurk_bindings| ($bindings*)) => do 
    let bindings ← bindings.mapM elabLurkBinding
    let type ← mkAppM ``Prod #[mkConst ``Lean.Name, mkConst ``Lurk.Syntax.Expr]
    mkListLit type bindings.toList
  | _ => throwUnsupportedSyntax

partial def elabLurkExpr : TSyntax `lurk_expr → TermElabM Lean.Expr
  | `(lurk_expr| $l:lurk_literal) => do
    mkAppM ``Lurk.Syntax.Expr.lit #[← elabLiteral l]
  | `(lurk_expr| $i:ident) => do
    mkAppM ``Lurk.Syntax.Expr.sym #[← mkNameLit i.getId.toString]
  | `(lurk_expr| (if $test $con $alt)) => do
    mkAppM ``Lurk.Syntax.Expr.ifE
      #[← elabLurkExpr test, ← elabLurkExpr con, ← elabLurkExpr alt]
  | `(lurk_expr| (lambda ($formals*) $body)) => do
    let formals ← Array.toList <$> formals.mapM elabLurkIdents
    let formals ← mkListLit (← mkAppM ``List #[mkConst ``Lean.Name]) formals
    let formals ← mkAppM ``List.join #[formals]
    mkAppM ``Lurk.Syntax.Expr.lam #[formals, ← elabLurkExpr body]
  | `(lurk_expr| (let $bind $body)) => do
    mkAppM ``Lurk.Syntax.Expr.letE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (letrec $bind $body)) => do
    mkAppM ``Lurk.Syntax.Expr.letRecE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (mutrec $bind $body)) => do
    mkAppM ``Lurk.Syntax.Expr.mutRecE #[← elabLurkBindings bind, ← elabLurkExpr body]
  | `(lurk_expr| (quote $datum)) => do
    mkAppM ``Lurk.Syntax.Expr.quote #[← SExpr.DSL.elabSExpr datum]
  | `(lurk_expr| ,$datum) => do
    mkAppM ``Lurk.Syntax.Expr.quote #[← SExpr.DSL.elabSExpr datum]
  | `(lurk_expr| ($op:lurk_bin_op $e1 $e2)) => do
    mkAppM ``Lurk.Syntax.Expr.binaryOp
      #[← elabLurkBinOp op, ← elabLurkExpr e1, ← elabLurkExpr e2]
  | `(lurk_expr| (car $e)) => do mkAppM ``Lurk.Syntax.Expr.car #[← elabLurkExpr e]
  | `(lurk_expr| (cdr $e)) => do mkAppM ``Lurk.Syntax.Expr.cdr #[← elabLurkExpr e]
  | `(lurk_expr| (atom $e)) => do mkAppM ``Lurk.Syntax.Expr.atom #[← elabLurkExpr e]
  | `(lurk_expr| (emit $e)) => do mkAppM ``Lurk.Syntax.Expr.emit #[← elabLurkExpr e]
  | `(lurk_expr| (cons $e₁ $e₂)) => do
    mkAppM ``Lurk.Syntax.Expr.cons #[← elabLurkExpr e₁, ← elabLurkExpr e₂]
  | `(lurk_expr| (strcons $e₁ $e₂)) => do
    mkAppM ``Lurk.Syntax.Expr.strcons #[← elabLurkExpr e₁, ← elabLurkExpr e₂]
  | `(lurk_expr| (begin $es*)) => do
    let nilE ← mkConst ``Lurk.Syntax.Expr.mkNil
    match ← es.mapM elabLurkExpr with
    | #[] => mkAppM ``Lurk.Syntax.Expr.begin #[nilE, nilE]
    | #[e] => mkAppM ``Lurk.Syntax.Expr.begin #[nilE, e]
    | es => es.foldlM (init := nilE) fun acc e => mkAppM ``Lurk.Syntax.Expr.begin #[acc, e]
  | `(lurk_expr| current-env) => return mkConst ``Lurk.Syntax.Expr.currEnv
  | `(lurk_expr| ($e*)) => do
    match ← e.mapM elabLurkExpr with
    | ⟨[]⟩    => mkConst ``Lurk.Syntax.Expr.mkNil
    | ⟨e::[]⟩ => mkAppM ``Lurk.Syntax.Expr.mkUnaryApp #[e]
    | ⟨e::es⟩ => es.foldlM (init := e) fun acc e => do
      mkAppM ``Lurk.Syntax.Expr.app #[acc, ← mkAppM ``Option.some #[e]]
  | `(lurk_expr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``Lurk.Syntax.Expr.ToExpr.toExpr #[e]
    else 
      throwUnsupportedSyntax 
end

elab "⟦ " e:lurk_expr " ⟧" : term =>
  elabLurkExpr e

end DSL

namespace SExpr.DSL

def _quote := [sexpr| quote]
def _nil   := [sexpr| nil]
def _cons  := [sexpr| cons]
def _car   := [sexpr| car]
def _cdr   := [sexpr| cdr]
def _begin   := [sexpr| begin]
def _lambda   := [sexpr| lambda]

end SExpr.DSL
end Lurk.Syntax
