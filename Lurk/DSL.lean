import Lurk.SExpr
import Lurk.Printer

open Lean Elab Meta

declare_syntax_cat lurk_value 
syntax "t"          : lurk_value
syntax "nil"        : lurk_value
syntax "-" noWs num : lurk_value
syntax num          : lurk_value
syntax ident        : lurk_value
syntax str          : lurk_value
syntax char         : lurk_value

def elabLurkValue : Syntax → MetaM Expr
  | `(lurk_value| t) => return mkConst ``Lurk.Value.t
  | `(lurk_value| nil) => return mkConst ``Lurk.Value.nil
  | `(lurk_value| -$n) => match n.getNat with
    | 0     => do 
      let n ← mkAppM ``Int.ofNat #[mkConst ``Nat.zero]
      let num ← mkAppM ``Lurk.Num.mk #[n, ← mkAppOptM ``none #[mkConst ``Nat]]
      mkAppM ``Lurk.Value.num #[num]
    | n + 1 => do 
      let n ← mkAppM ``Int.negSucc #[mkNatLit n]
      let num ← mkAppM ``Lurk.Num.mk #[n, ← mkAppOptM ``none #[mkConst ``Nat]]
      mkAppM ``Lurk.Value.num #[num]
  | `(lurk_value| $n:num) => do 
    let n ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
    let num ← mkAppM ``Lurk.Num.mk #[n, ← mkAppOptM ``none #[mkConst ``Nat]]
    mkAppM ``Lurk.Value.num #[num]
  | `(lurk_value| $i:ident) => do 
    let s ← mkAppM ``Lurk.Name.mk #[mkStrLit i.getId.toString]
    mkAppM ``Lurk.Value.sym #[s]
  | `(lurk_value| $s:str)   => mkAppM ``Lurk.Value.str #[mkStrLit s.getString]
  | `(lurk_value| $c:char)  => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``Lurk.Value.char #[c]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_num_op 
syntax "+ " : lurk_num_op
syntax "- " : lurk_num_op
syntax "* " : lurk_num_op
syntax "/ " : lurk_num_op

def elabLurkNumOp : Syntax → MetaM Expr
  | `(lurk_num_op| +) => return mkConst ``Lurk.NumOp.sum
  | `(lurk_num_op| -) => return mkConst ``Lurk.NumOp.diff
  | `(lurk_num_op| *) => return mkConst ``Lurk.NumOp.prod
  | `(lurk_num_op| /) => return mkConst ``Lurk.NumOp.quot
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_cons_op 
syntax "car "  : lurk_cons_op
syntax "cdr "  : lurk_cons_op
syntax "atom " : lurk_cons_op
syntax "emit " : lurk_cons_op

def elabLurkConsOp : Syntax → MetaM Expr 
  | `(lurk_cons_op| car) => return mkConst ``Lurk.ConsOp.car
  | `(lurk_cons_op| cdr) => return mkConst ``Lurk.ConsOp.cdr
  | `(lurk_cons_op| atom) => return mkConst ``Lurk.ConsOp.atom
  | `(lurk_cons_op| emit) => return mkConst ``Lurk.ConsOp.emit
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_rel_op 
syntax "= "  : lurk_rel_op
syntax "eq " : lurk_rel_op

def elabLurkRelOp : Syntax → MetaM Expr 
  | `(lurk_rel_op| =) => return mkConst ``Lurk.RelOp.eq
  | `(lurk_rel_op| eq) => return mkConst ``Lurk.RelOp.nEq -- unfortunate clash again
  | _ => throwUnsupportedSyntax

declare_syntax_cat lurk_expr
declare_syntax_cat lurk_bindings

syntax ("(" ident lurk_expr ")")+ : lurk_bindings
syntax  "(" lurk_bindings ")": lurk_bindings

syntax lurk_value                         : lurk_expr
syntax "if" lurk_expr lurk_expr lurk_expr : lurk_expr
syntax "lambda" "(" ident* ")" lurk_expr  : lurk_expr
syntax "let" lurk_bindings lurk_expr      : lurk_expr
syntax "letrec" lurk_bindings lurk_expr   : lurk_expr
syntax "quote" sexpr                      : lurk_expr -- TODO: fixme to use `
syntax "cons" lurk_expr lurk_expr         : lurk_expr
syntax "strcons" lurk_expr lurk_expr      : lurk_expr
syntax  lurk_cons_op lurk_expr            : lurk_expr
syntax  lurk_num_op lurk_expr lurk_expr   : lurk_expr
syntax  lurk_rel_op lurk_expr lurk_expr   : lurk_expr
syntax "emit" lurk_expr                   : lurk_expr
syntax "begin" lurk_expr*                 : lurk_expr
syntax "current-env"                      : lurk_expr
syntax "eval" lurk_expr                   : lurk_expr
syntax "(" lurk_expr ")"                  : lurk_expr

partial def elabLurkExpr : Syntax → MetaM Expr 
  | `(lurk_expr| $v:lurk_value) => do
    mkAppM ``Lurk.Expr.value #[← elabLurkValue v]
  | `(lurk_expr| if $test $con $alt) => do 
    mkAppM ``Lurk.Expr.ifE #[← elabLurkExpr test, ← elabLurkExpr con, ← elabLurkExpr alt]
  | `(lurk_expr| lambda ($formals*) $body) => do 
    let formals ← (formals.mapM fun i => mkAppM ``Lurk.Name.mk #[mkStrLit i.getId.toString])
    let formals := formals.toList 
    let formals ← mkListLit (mkConst ``Lurk.Name) formals
    mkAppM ``Lurk.Expr.lam #[formals, ← elabLurkExpr body] 
  | `(lurk_expr| let $bind $body) => do 
    mkAppM ``Lurk.Expr.letE #[← elabLurkExpr bind, ← elabLurkExpr body]
  | `(lurk_expr| letrec $bind $body) => do 
    mkAppM ``Lurk.Expr.letRecE #[← elabLurkExpr bind, ← elabLurkExpr body]
  | `(lurk_expr| quote $datum) => do 
    mkAppM ``Lurk.Expr.quote #[← elabSExpr datum]
  | `(lurk_expr| cons $a $d) => do 
    mkAppM ``Lurk.Expr.cons #[← elabLurkExpr a, ← elabLurkExpr d]
  | `(lurk_expr| strcons $a $d) => do 
    mkAppM ``Lurk.Expr.strcons #[← elabLurkExpr a, ← elabLurkExpr d]
  | `(lurk_expr| $op:lurk_cons_op $e) => do 
    mkAppM ``Lurk.Expr.consOp #[← elabLurkConsOp op, ← elabLurkExpr e]
  | `(lurk_expr| $op:lurk_num_op $e1 $e2) => do 
    mkAppM ``Lurk.Expr.numOp #[← elabLurkNumOp op, ← elabLurkExpr e1, ← elabLurkExpr e2]
  | `(lurk_expr| $op:lurk_rel_op $e1 $e2) => do 
    mkAppM ``Lurk.Expr.numOp #[← elabLurkRelOp op, ← elabLurkExpr e1, ← elabLurkExpr e2]
  | `(lurk_expr| emit $e) => do 
    mkAppM ``Lurk.Expr.emit #[← elabLurkExpr e]
  | `(lurk_expr| begin $e*) => do 
    let e := (← e.mapM elabLurkExpr).toList 
    let type ← mkAppM ``List #[mkConst ``Lurk.Expr]
    mkAppM ``Lurk.Expr.begin #[← mkListLit type e]
  | `(lurk_expr| current-env) => return mkConst ``Lurk.Expr.currEnv
  | `(lurk_expr| eval $e) => elabLurkExpr e 
  | `(lurk_expr| ($e)) => elabLurkExpr e
  | _ => throwUnsupportedSyntax

-- Tests 

elab "test_elabLurkValue " v:lurk_value : term =>
  elabLurkValue v

#eval test_elabLurkValue 5 -- 5
#eval test_elabLurkValue 0 -- 0
#eval test_elabLurkValue -0 -- 0
#eval test_elabLurkValue -5 -- -5
#eval test_elabLurkValue "" -- ""
#eval test_elabLurkValue "sss" -- "sss"
#eval test_elabLurkValue e


elab "test_elabLurkNumOp " v:lurk_num_op : term =>
  elabLurkNumOp v

#eval test_elabLurkNumOp +
#eval test_elabLurkNumOp -
#eval test_elabLurkNumOp *
#eval test_elabLurkNumOp /


elab "test_elabLurkConsOp " v:lurk_cons_op : term =>
  elabLurkConsOp v

#eval test_elabLurkConsOp car


elab "test_elabLurkRelOp " v:lurk_rel_op : term =>
  elabLurkRelOp v

#eval test_elabLurkRelOp =

elab "[Lurk| " e:lurk_expr "]" : term =>
  elabLurkExpr e

#check [({ data := "n" } : Lurk.Name)]

#eval [Lurk| 
  lambda () n
]
