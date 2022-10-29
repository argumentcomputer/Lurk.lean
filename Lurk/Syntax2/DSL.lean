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

def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) => mkAppM ``AST.sym #[mkStrLit i.getId.toString]
  | `(sym| +)  => mkAppM ``AST.sym #[mkStrLit "+"]
  | `(sym| *)  => mkAppM ``AST.sym #[mkStrLit "*"]
  | `(sym| -)  => mkAppM ``AST.sym #[mkStrLit "-"]
  | `(sym| /)  => mkAppM ``AST.sym #[mkStrLit "/"]
  | `(sym| =)  => mkAppM ``AST.sym #[mkStrLit "="]
  | `(sym| <)  => mkAppM ``AST.sym #[mkStrLit "<"]
  | `(sym| >)  => mkAppM ``AST.sym #[mkStrLit ">"]
  | `(sym| <=) => mkAppM ``AST.sym #[mkStrLit "<="]
  | `(sym| >=) => mkAppM ``AST.sym #[mkStrLit ">="]
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

partial def elabASTCons (xs : Array $ TSyntax `ast) : TermElabM Lean.Expr :=
  xs.foldrM (init := Lean.mkConst ``AST.nil)
    fun x acc => do mkAppM ``AST.cons #[← elabAST x, acc]

partial def elabAST : TSyntax `ast → TermElabM Lean.Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    mkAppM ``AST.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| ($xs*)) => elabASTCons xs
  | `(ast| ($xs* . $x)) => do mkAppM ``AST.cons #[← elabASTCons xs, ← elabAST x]
  | `(ast| ,$x:ast) => do
    let quote ← mkAppM ``AST.sym #[mkStrLit "quote"]
    let tail ← mkAppM ``AST.cons #[← elabAST x, Lean.mkConst ``AST.nil]
    mkAppM ``AST.cons #[quote, tail]
  | _ => throwUnsupportedSyntax

end

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

end Lurk.Syntax.DSL
