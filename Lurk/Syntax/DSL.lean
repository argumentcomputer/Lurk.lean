import Lurk.Syntax.ExprUtils

namespace Lurk.Syntax.DSL

open Lean Elab Meta Term

def mkNameLit (name : String) :=
  mkAppM ``Name.mkSimple #[mkStrLit name]

declare_syntax_cat    lurk_literal
syntax "t"          : lurk_literal
syntax "nil"        : lurk_literal
syntax num          : lurk_literal
-- syntax "-" noWs num : lurk_literal
syntax str          : lurk_literal
syntax char         : lurk_literal

def elabLiteral : Syntax → TermElabM Lean.Expr
  | `(lurk_literal| t)   => return mkConst ``Lurk.Syntax.Literal.t
  | `(lurk_literal| nil) => return mkConst ``Lurk.Syntax.Literal.nil
  -- | `(lurk_literal| -$n) => match n.getNat with
  --   | 0     => do
  --     mkAppM ``Lurk.Syntax.Literal.num #[← mkAppM ``Fin.ofNat #[mkConst ``Nat.zero]]
  --   | n + 1 => do
  --     mkAppM ``Lurk.Syntax.Literal.num #[← mkAppM ``Fin.ofInt #[← mkAppM ``Int.negSucc #[mkNatLit n]]]
  | `(lurk_literal| $n:num) => do
    mkAppM ``Lurk.Syntax.mkNumLit #[mkNatLit n.getNat]
  | `(lurk_literal| $s:str) =>
    mkAppM ``Lurk.Syntax.Literal.str #[mkStrLit s.getString]
  | `(lurk_literal| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Syntax.Literal.char #[c]
  | _ => throwUnsupportedSyntax

declare_syntax_cat           sexpr
syntax lurk_literal        : sexpr
syntax "(" sexpr* ")"      : sexpr
syntax sexpr " . " sexpr   : sexpr

open Lurk SExpr in 
partial def elabSExpr : Syntax → TermElabM Lean.Expr
  | `(sexpr| $l:lurk_literal) => do
    mkAppM ``SExpr.lit #[← elabLiteral l]
  | `(sexpr| ($es*)) => do
    let es ← (es.mapM fun e => elabSExpr e)
    mkAppM ``mkList #[← mkListLit (mkConst ``SExpr) es.toList]
  | `(sexpr| $e1 . $e2) => do
    mkAppM ``SExpr.cons #[← elabSExpr e1, ← elabSExpr e2]
  | `(sexpr| $i) => do 
    if i.raw.isAntiquot then 
      let stx := i.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``ToSExpr.toSExpr #[e]
    else 
      throwUnsupportedSyntax 

elab "[SExpr| " e:sexpr "]" : term =>
  elabSExpr e


declare_syntax_cat  lurk_bin_op
syntax "+ "       : lurk_bin_op
syntax "- "       : lurk_bin_op
syntax "* "       : lurk_bin_op
syntax "/ "       : lurk_bin_op
syntax "= "       : lurk_bin_op
syntax "< "       : lurk_bin_op
syntax "> "       : lurk_bin_op
syntax "<= "      : lurk_bin_op
syntax ">= "      : lurk_bin_op
syntax "eq "      : lurk_bin_op

def elabLurkBinOp : Syntax → TermElabM Lean.Expr
  | `(lurk_bin_op| +)    => return mkConst ``Lurk.Syntax.BinaryOp.sum
  | `(lurk_bin_op| -)    => return mkConst ``Lurk.Syntax.BinaryOp.diff
  | `(lurk_bin_op| *)    => return mkConst ``Lurk.Syntax.BinaryOp.prod
  | `(lurk_bin_op| /)    => return mkConst ``Lurk.Syntax.BinaryOp.quot
  | `(lurk_bin_op| =)    => return mkConst ``Lurk.Syntax.BinaryOp.numEq
  | `(lurk_bin_op| <)    => return mkConst ``Lurk.Syntax.BinaryOp.lt
  | `(lurk_bin_op| >)    => return mkConst ``Lurk.Syntax.BinaryOp.gt
  | `(lurk_bin_op| <=)   => return mkConst ``Lurk.Syntax.BinaryOp.le
  | `(lurk_bin_op| >=)   => return mkConst ``Lurk.Syntax.BinaryOp.ge
  | `(lurk_bin_op| eq)   => return mkConst ``Lurk.Syntax.BinaryOp.eq
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_expr
declare_syntax_cat lurk_binding
declare_syntax_cat lurk_bindings

syntax "(" ident lurk_expr ")" : lurk_binding
syntax  "(" lurk_binding* ")"  : lurk_bindings

syntax lurk_literal                               : lurk_expr
syntax ident                                      : lurk_expr
syntax "(" "if" lurk_expr lurk_expr lurk_expr ")" : lurk_expr
syntax "(" "lambda" "(" ident* ")" lurk_expr ")"  : lurk_expr
syntax "(" "let" lurk_bindings lurk_expr ")"      : lurk_expr
syntax "(" "letrec" lurk_bindings lurk_expr ")"   : lurk_expr
syntax "(" "mutrec" lurk_bindings lurk_expr ")"   : lurk_expr
syntax "(" "quote " sexpr ")"                     : lurk_expr
syntax "," sexpr                                  : lurk_expr
syntax "(" lurk_bin_op lurk_expr lurk_expr ")"    : lurk_expr
syntax "(" "car" lurk_expr ")"                    : lurk_expr
syntax "(" "cdr" lurk_expr ")"                    : lurk_expr
syntax "(" "atom" lurk_expr ")"                   : lurk_expr
syntax "(" "emit" lurk_expr ")"                   : lurk_expr
syntax "(" "cons" lurk_expr lurk_expr ")"         : lurk_expr
syntax "(" "strcons" lurk_expr lurk_expr ")"      : lurk_expr
syntax "(" "begin" lurk_expr*  ")"                : lurk_expr
syntax "current-env"                              : lurk_expr
syntax "(" lurk_expr* ")"                         : lurk_expr

/-- 
There are no type guarentees. 
-/
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
    mkAppM ``Lurk.Syntax.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| ,$datum) => do
    mkAppM ``Lurk.Syntax.Expr.quote #[← elabSExpr datum]
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
    match ← es.mapM elabLurkExpr with
    | #[] => mkAppM ``Lurk.Syntax.Expr.lit #[mkConst ``Lurk.Syntax.Literal.nil]
    | #[e] => return e
    | es =>
      es.foldlM (init := ← mkAppM ``Lurk.Syntax.Expr.lit #[mkConst ``Lurk.Syntax.Literal.nil])
        fun acc e => mkAppM ``Lurk.Syntax.Expr.begin #[acc, e]
  | `(lurk_expr| current-env) => return mkConst ``Lurk.Syntax.Expr.currEnv
  | `(lurk_expr| ($e*)) => do
    match ← e.mapM elabLurkExpr with
    | ⟨[]⟩    => mkAppM ``Lurk.Syntax.Expr.lit #[mkConst ``Lurk.Syntax.Literal.nil]
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

end Lurk.Syntax.DSL

namespace Lurk.Syntax.Expr

/--
Transforms a list of named expressions that were mutually defined into a
"switch" function `S` and a set of projections (named after the original names)
that call `S` with their respective indices.

Important: the resulting expressions must to be bound in a `letrec`.
-/
def mkMutualBlock (mutuals : List (Name × Expr)) : List (Name × Expr) :=
  if mutuals.length == 1 then 
    mutuals 
  else 
    let names := mutuals.map Prod.fst
    let mutualName := names.foldl (init := `__mutual__) fun acc n => acc ++ n
    let fnProjs := names.enum.map fun (i, (n : Name)) => (n, .app ⟦$mutualName⟧ ⟦$i⟧)
    let map := fnProjs.foldl (init := default) fun acc (n, e) => acc.insert n e
    let mutualBlock := mkIfElses (mutuals.enum.map fun (i, _, e) =>
        (⟦(= mutidx $i)⟧, replaceFreeVars map e)
      ) ⟦nil⟧
    (mutualName, ⟦(lambda (mutidx) $mutualBlock)⟧) :: fnProjs

end Lurk.Syntax.Expr
