import Lean
import Lurk.Field

inductive Symbol
  | root
  | cons : String → Symbol → Symbol
  deriving Ord, BEq, Repr

namespace Symbol

def telescope (acc : List String := []) : Symbol → List String
  | root => acc
  | cons str sym => sym.telescope $ str :: acc

@[inline, match_pattern] def ofString (s : String) : Symbol :=
  .cons s .root

def toString (sym : Symbol) : String :=
  ".".intercalate sym.telescope

instance : ToString Symbol := ⟨Symbol.toString⟩

@[inline] def nil : Symbol :=
  .cons "nil" .root

@[inline] def t : Symbol :=
  .cons "t" .root

end Symbol

inductive LDON
  | num : Lurk.F → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : Symbol → LDON
  | cons : LDON → LDON → LDON
  deriving Ord, BEq, Repr, Inhabited

namespace LDON

@[match_pattern] def nil : LDON := sym .nil
@[match_pattern] def t   : LDON := sym .t

def consWith (xs : List LDON) (init : LDON) : LDON :=
  xs.foldr (init := init) cons

class ToLDON (α : Type _) where
  toLDON : α → LDON

export ToLDON (toLDON)

instance : ToLDON Nat where
  toLDON := .num ∘ .ofNat

instance : ToLDON Char where
  toLDON := .char

instance : ToLDON String where
  toLDON := .str

instance [ToLDON α] : ToLDON (List α) where
  toLDON es := LDON.consWith (es.map toLDON) .nil

instance [ToLDON α] : ToLDON (Array α) where
  toLDON es := LDON.consWith (es.data.map toLDON) .nil

instance : ToLDON LDON := ⟨id⟩

namespace DSL

open Lean Elab Meta Term

declare_syntax_cat    sym
scoped syntax ident : sym
-- these can't be simple idents because they'd clash with Lean's syntax
scoped syntax "if"   : sym
scoped syntax "let"  : sym
scoped syntax "open" : sym
scoped syntax "+"    : sym
scoped syntax "-"    : sym
scoped syntax "*"    : sym
scoped syntax "/"    : sym
scoped syntax "%"    : sym
scoped syntax "="    : sym
scoped syntax "<"    : sym
scoped syntax ">"    : sym
scoped syntax "<="   : sym
scoped syntax ">="   : sym
-- a workaround for the dash
scoped syntax "current-env" : sym
-- escaping symbols
scoped syntax "|" sym "|" : sym

private def mkSym (sym : String) := do
  let sym ← mkAppM ``Symbol.ofString #[mkStrLit sym]
  mkAppM ``LDON.sym #[sym]

partial def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident)    | `(sym| | $i:ident |)    => mkSym i.getId.toString
  | `(sym| current-env) | `(sym| | current-env |) => mkSym "current-env"
  | `(sym| if)          | `(sym| | if |)          => mkSym "if"
  | `(sym| let)         | `(sym| | let |)         => mkSym "let"
  | `(sym| «open»)      | `(sym| | «open» |)      => mkSym "open"
  | `(sym| +)  => mkSym "+"
  | `(sym| -)  => mkSym "-"
  | `(sym| *)  => mkSym "*"
  | `(sym| /)  => mkSym "/"
  | `(sym| %)  => mkSym "%"
  | `(sym| =)  => mkSym "="
  | `(sym| <)  => mkSym "<"
  | `(sym| >)  => mkSym ">"
  | `(sym| <=) => mkSym "<="
  | `(sym| >=) => mkSym ">="
  | _ => throwUnsupportedSyntax

declare_syntax_cat                       ldon
scoped syntax num                      : ldon
scoped syntax char                     : ldon
scoped syntax str                      : ldon
scoped syntax sym                      : ldon
scoped syntax "(" ldon* ")"            : ldon
scoped syntax "(" ldon+ " . " ldon ")" : ldon

mutual

partial def elabLDONCons (xs : Array $ TSyntax `ldon) (init : Lean.Expr) : TermElabM Lean.Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``LDON.cons #[← elabLDON e, acc]

partial def elabLDON : TSyntax `ldon → TermElabM Lean.Expr
  | `(ldon| $n:num) => do mkAppM ``LDON.num #[← mkAppM ``Lurk.F.ofNat #[mkNatLit n.getNat]]
  | `(ldon| $c:char) => do
    mkAppM ``LDON.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ldon| $s:str) => mkAppM ``LDON.str #[mkStrLit s.getString]
  | `(ldon| $s:sym) => elabSym s
  | `(ldon| ()) => pure $ mkConst ``LDON.nil
  | `(ldon| ($xs*)) => elabLDONCons xs (mkConst ``LDON.nil)
  | `(ldon| ($x . $y)) => do mkAppM ``LDON.cons #[← elabLDON x, ← elabLDON y]
  | `(ldon| ($xs* . $x)) => do elabLDONCons xs (← elabLDON x)
  | `(ldon| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``LDON.toLDON #[e]
    else throwUnsupportedSyntax

end

scoped elab "⟪" x:ldon "⟫" : term =>
  elabLDON x

end LDON.DSL
