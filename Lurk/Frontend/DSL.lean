import Lean
import Lurk.Frontend.AST

namespace Lurk.Frontend

open Lean Elab Meta Term

namespace DSL

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
-- a workaround for the dash
scoped syntax "current-env" : sym
scoped syntax "CURRENT-ENV" : sym
-- escaping symbols
scoped syntax "|" sym "|" : sym
-- symbols with a dot followed by a number
scoped syntax ident noWs "." noWs num : sym
scoped syntax "[anonymous]" : sym

def mergeWithDot (s : String) (n : Nat) : String :=
  s!"{s}.{n}"

partial def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) =>
    let i  := i.getId.toString
    let iU := i.toUpper
    if AST.reservedSyms.contains iU then
      mkAppM ``AST.sym #[mkStrLit iU]
    else
      mkAppM ``AST.sym #[mkStrLit i]
  | `(sym| +)  | `(sym| | + |)  => mkAppM ``AST.sym #[mkStrLit "+"]
  | `(sym| *)  | `(sym| | * |)  => mkAppM ``AST.sym #[mkStrLit "*"]
  | `(sym| -)  | `(sym| | - |)  => mkAppM ``AST.sym #[mkStrLit "-"]
  | `(sym| /)  | `(sym| | / |)  => mkAppM ``AST.sym #[mkStrLit "/"]
  | `(sym| =)  | `(sym| | = |)  => mkAppM ``AST.sym #[mkStrLit "="]
  | `(sym| <)  | `(sym| | < |)  => mkAppM ``AST.sym #[mkStrLit "<"]
  | `(sym| >)  | `(sym| | > |)  => mkAppM ``AST.sym #[mkStrLit ">"]
  | `(sym| <=) | `(sym| | <= |) => mkAppM ``AST.sym #[mkStrLit "<="]
  | `(sym| >=) | `(sym| | >= |) => mkAppM ``AST.sym #[mkStrLit ">="]
  | `(sym| CURRENT-ENV)  => mkAppM ``AST.sym #[mkStrLit "CURRENT-ENV"]
  | `(sym| current-env)  => mkAppM ``AST.sym #[mkStrLit "CURRENT-ENV"]
  | `(sym| | current-env |)  => mkAppM ``AST.sym #[mkStrLit "current-env"]
  | `(sym| if)  => mkAppM ``AST.sym #[mkStrLit "IF"]
  | `(sym| let) => mkAppM ``AST.sym #[mkStrLit "LET"]
  | `(sym| | $i:ident |) => mkAppM ``AST.sym #[mkStrLit i.getId.toString]
  | `(sym| | if |)  => mkAppM ``AST.sym #[mkStrLit "if"]
  | `(sym| | let |) => mkAppM ``AST.sym #[mkStrLit "let"]
  | `(sym| $i:ident.$n:num)
  | `(sym| | $i:ident.$n:num |) => do
    let sym ← mkAppM ``mergeWithDot #[mkStrLit i.getId.toString, mkNatLit n.getNat]
    mkAppM ``AST.sym #[sym]
  | `(sym| [anonymous])
  | `(sym| |[anonymous]|) => mkAppM ``AST.sym #[mkStrLit "[anonymous]"]
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

partial def elabASTCons (xs : Array $ TSyntax `ast) (init : Expr) : TermElabM Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``AST.cons #[← elabAST e, acc]

partial def elabAST : TSyntax `ast → TermElabM Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    mkAppM ``AST.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| ()) => pure $ mkConst ``AST.nil
  | `(ast| ($xs*)) => elabASTCons xs (mkConst ``AST.nil)
  | `(ast| ($x . $y)) => do mkAppM ``AST.cons #[← elabAST x, ← elabAST y]
  | `(ast| ($xs* . $x)) => do elabASTCons xs (← elabAST x)
  | `(ast| ,$x:ast) => do mkAppM ``AST.mkQuote #[← elabAST x]
  | _ => throwUnsupportedSyntax

end

elab "⟦" x:ast "⟧" : term =>
  elabAST x

end Lurk.Frontend.DSL
