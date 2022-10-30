import Lean
import Lurk.Syntax2.AST

namespace Lurk.Syntax.DSL

open Lean Elab Meta Term

declare_syntax_cat    sym
scoped syntax ident : sym
scoped syntax "+"   : sym
scoped syntax "*"   : sym
scoped syntax "-"   : sym
scoped syntax "/"   : sym
scoped syntax "="   : sym
scoped syntax "<"   : sym
scoped syntax ">"   : sym
scoped syntax "<="  : sym
scoped syntax ">="  : sym
-- these can't be simple idents because they'd clash with Lean's syntax
scoped syntax "if"  : sym
scoped syntax "let" : sym

def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym|  $i:ident ) => match i.getId.toString.toUpper with
    | "NIL" => return Lean.mkConst ``AST.nil
    | i => mkAppM ``AST.sym #[mkStrLit i]
  | `(sym| +)  => mkAppM ``AST.sym #[mkStrLit "+"]
  | `(sym| *)  => mkAppM ``AST.sym #[mkStrLit "*"]
  | `(sym| -)  => mkAppM ``AST.sym #[mkStrLit "-"]
  | `(sym| /)  => mkAppM ``AST.sym #[mkStrLit "/"]
  | `(sym| =)  => mkAppM ``AST.sym #[mkStrLit "="]
  | `(sym| <)  => mkAppM ``AST.sym #[mkStrLit "<"]
  | `(sym| >)  => mkAppM ``AST.sym #[mkStrLit ">"]
  | `(sym| <=) => mkAppM ``AST.sym #[mkStrLit "<="]
  | `(sym| >=) => mkAppM ``AST.sym #[mkStrLit ">="]
  | `(sym| if) => mkAppM ``AST.sym #[mkStrLit "IF"]
  | `(sym| let) => mkAppM ``AST.sym #[mkStrLit "LET"]
  | _ => throwUnsupportedSyntax

declare_syntax_cat                     ast
scoped syntax num                    : ast
scoped syntax char                   : ast
scoped syntax str                    : ast
scoped syntax sym                    : ast
scoped syntax "(" ast* ")"           : ast
scoped syntax "(" ast+ " . " ast ")" : ast
scoped syntax "," ast                : ast -- quoting
-- symbols separated by a dash (only handles one dash)
scoped syntax sym noWs "-" noWs sym  : ast
scoped syntax sym noWs "-" noWs num  : ast

def mergeSymSym : AST → AST → AST
  | .sym a, .sym b => .sym s!"{a}-{b}"
  | x, _ => x

def mergeSymNat : AST → Nat → AST
  | .sym a, n => .sym s!"{a}-{n}"
  | x, _ => x

mutual

partial def elabASTCons (xs : Array $ TSyntax `ast) (init : Expr) :
    TermElabM Expr := do
  mkAppM ``AST.mkCons #[
    ← mkListLit (mkConst ``AST) (← xs.data.mapM elabAST),
    init
  ]

partial def elabAST : TSyntax `ast → TermElabM Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    mkAppM ``AST.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| $a:sym-$b:sym) => do mkAppM ``mergeSymSym #[← elabSym a, ← elabSym b]
  | `(ast| $a:sym-$n:num) => do mkAppM ``mergeSymNat #[← elabSym a, mkNatLit n.getNat]
  | `(ast| ($xs*)) => elabASTCons xs (mkConst ``AST.nil)
  | `(ast| ($x . $y)) => do mkAppM ``AST.cons #[← elabAST x, ← elabAST y]
  | `(ast| ($xs* . $x)) => do elabASTCons xs (← elabAST x)
  | `(ast| ,$x:ast) => do mkAppM ``AST.mkQuote #[← elabAST x]
  | _ => throwUnsupportedSyntax

end

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

end Lurk.Syntax.DSL
