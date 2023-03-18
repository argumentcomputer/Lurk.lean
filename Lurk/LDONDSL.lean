import Lean
import Lurk.LDON

namespace Lurk.LDON.DSL

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
    if LDON.reservedSyms.contains iU then
      mkAppM ``LDON.sym #[mkStrLit iU]
    else
      mkAppM ``LDON.sym #[mkStrLit i]
  | `(sym| +)  | `(sym| | + |)  => mkAppM ``LDON.sym #[mkStrLit "+"]
  | `(sym| *)  | `(sym| | * |)  => mkAppM ``LDON.sym #[mkStrLit "*"]
  | `(sym| -)  | `(sym| | - |)  => mkAppM ``LDON.sym #[mkStrLit "-"]
  | `(sym| /)  | `(sym| | / |)  => mkAppM ``LDON.sym #[mkStrLit "/"]
  | `(sym| =)  | `(sym| | = |)  => mkAppM ``LDON.sym #[mkStrLit "="]
  | `(sym| <)  | `(sym| | < |)  => mkAppM ``LDON.sym #[mkStrLit "<"]
  | `(sym| >)  | `(sym| | > |)  => mkAppM ``LDON.sym #[mkStrLit ">"]
  | `(sym| <=) | `(sym| | <= |) => mkAppM ``LDON.sym #[mkStrLit "<="]
  | `(sym| >=) | `(sym| | >= |) => mkAppM ``LDON.sym #[mkStrLit ">="]
  | `(sym| CURRENT-ENV)  => mkAppM ``LDON.sym #[mkStrLit "CURRENT-ENV"]
  | `(sym| current-env)  => mkAppM ``LDON.sym #[mkStrLit "CURRENT-ENV"]
  | `(sym| | current-env |)  => mkAppM ``LDON.sym #[mkStrLit "current-env"]
  | `(sym| if)  => mkAppM ``LDON.sym #[mkStrLit "IF"]
  | `(sym| let) => mkAppM ``LDON.sym #[mkStrLit "LET"]
  | `(sym| | $i:ident |) => mkAppM ``LDON.sym #[mkStrLit i.getId.toString]
  | `(sym| | if |)  => mkAppM ``LDON.sym #[mkStrLit "if"]
  | `(sym| | let |) => mkAppM ``LDON.sym #[mkStrLit "let"]
  | `(sym| $i:ident.$n:num)
  | `(sym| | $i:ident.$n:num |) => do
    let sym ← mkAppM ``mergeWithDot #[mkStrLit i.getId.toString, mkNatLit n.getNat]
    mkAppM ``LDON.sym #[sym]
  | `(sym| [anonymous])
  | `(sym| |[anonymous]|) => mkAppM ``LDON.sym #[mkStrLit "[anonymous]"]
  | _ => throwUnsupportedSyntax

declare_syntax_cat                       ldon
scoped syntax num                      : ldon
scoped syntax char                     : ldon
scoped syntax str                      : ldon
scoped syntax sym                      : ldon
scoped syntax "(" ldon* ")"            : ldon
scoped syntax "(" ldon+ " . " ldon ")" : ldon
scoped syntax "," ldon                 : ldon -- quoting

mutual

partial def elabLDONCons (xs : Array $ TSyntax `ldon) (init : Expr) : TermElabM Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``LDON.cons #[← elabLDON e, acc]

partial def elabLDON : TSyntax `ldon → TermElabM Expr
  | `(ldon| $n:num) => do mkAppM ``LDON.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(ldon| $c:char) => do
    mkAppM ``LDON.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ldon| $s:str) => mkAppM ``LDON.str #[mkStrLit s.getString]
  | `(ldon| $s:sym) => elabSym s
  | `(ldon| ()) => pure $ mkConst ``LDON.nil
  | `(ldon| ($xs*)) => elabLDONCons xs (mkConst ``LDON.nil)
  | `(ldon| ($x . $y)) => do mkAppM ``LDON.cons #[← elabLDON x, ← elabLDON y]
  | `(ldon| ($xs* . $x)) => do elabLDONCons xs (← elabLDON x)
  | `(ldon| ,$x:ldon) => do mkAppM ``LDON.mkQuote #[← elabLDON x]
  | _ => throwUnsupportedSyntax

end

scoped elab "⟪" x:ldon "⟫" : term =>
  elabLDON x

end Lurk.LDON.DSL
