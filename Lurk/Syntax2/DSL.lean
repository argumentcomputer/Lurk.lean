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
  | `(sym| $i:ident) => mkAppM ``AST.sym #[mkStrLit i.getId.toString.toUpper]
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

mutual

partial def elabASTCons (xs : Array $ TSyntax `ast) : TermElabM Lean.Expr := do
  mkAppM ``AST.mkCons #[← mkListLit (Lean.mkConst ``AST) (← xs.data.mapM elabAST)]

partial def elabAST : TSyntax `ast → TermElabM Lean.Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    mkAppM ``AST.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| ($xs*)) => elabASTCons xs
  | `(ast| ($xs* . $x)) => do mkAppM ``AST.cons #[← elabASTCons xs, ← elabAST x]
  | `(ast| ,$x:ast) => do mkAppM ``AST.mkQuote #[← elabAST x]
  | _ => throwUnsupportedSyntax

end

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

end Lurk.Syntax.DSL
