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
scoped syntax "<="  : sym
scoped syntax ">"   : sym
scoped syntax ">="  : sym

declare_syntax_cat           ast
scoped syntax num          : ast
scoped syntax char         : ast
scoped syntax str          : ast
scoped syntax sym          : ast
scoped syntax "(" ast* ")" : ast

def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) => mkAppM ``AST.sym #[mkStrLit i.getId.toString]
  | `(sym| +) => mkAppM ``AST.sym #[mkStrLit "+"]
  | _ => throwUnsupportedSyntax

partial def elabAST : TSyntax `ast → TermElabM Lean.Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    let c ← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]
    mkAppM ``AST.char #[c]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| ($xs*)) => xs.foldrM (init := Lean.mkConst ``AST.nil) fun x acc => do
    mkAppM ``AST.cons #[← elabAST x, acc]
  | _ => throwUnsupportedSyntax

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

#reduce ⟦(+ a b 1)⟧

end Lurk.Syntax.DSL
