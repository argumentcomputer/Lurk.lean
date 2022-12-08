import Lurk.Field
import Lurk.Syntax.AST

open Std

namespace Lurk.Evaluation

/-- Basic Lurk primitives -/
inductive Lit
  -- `t` and `nil`
  | t | nil
  -- Numerical values
  | num  : F → Lit
  -- Strings
  | str  : String → Lit
  -- Characters
  | char : Char → Lit
  deriving Repr, BEq

namespace Lit

def toString : Lit → String
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => ToString.toString n
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

def pprint : Lit → Format
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => n.asHex
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Lit where
  format := pprint

def toAST : Lit → Syntax.AST
  | .nil    => .nil
  | .t      => .t
  | .num n  => .num n
  | .str s  => .str s
  | .char c => .char c

end Lit

inductive Op₁
  | atom | car | cdr | emit
  | commit | comm | «open»
  | num | char
  deriving Repr, BEq

open Std Format in
def Op₁.toFormat : Op₁ → Format
| .atom   => "ATOM"
| .car    => "CAR"
| .cdr    => "CDR"
| .emit   => "EMIT"
| .commit => "COMMIT"
| .comm   => "COMM"
| .open   => "OPEN"
| .num    => "NUM"
| .char   => "CHAR"

instance : Std.ToFormat Op₁ := ⟨Op₁.toFormat⟩

inductive Op₂
  | cons | strcons
  | add | sub | mul | div | numEq | lt | gt | le | ge | eq
  | hide
  deriving Repr, BEq

open Std Format in
def Op₂.toFormat : Op₂ → Format
  | .cons    => "CONS"
  | .strcons => "STRCONS"
  | .add     => "+"
  | .sub     => "-"
  | .mul     => "*"
  | .div     => "/"
  | .numEq   => "="
  | .lt      => "<"
  | .gt      => ">"
  | .le      => "<="
  | .ge      => ">="
  | .eq      => "EQ"
  | .hide    => "HIDE"

instance : Std.ToFormat Op₂ := ⟨Op₂.toFormat⟩

inductive Expr
  | lit : Lit → Expr
  | sym : String → Expr
  | env : Expr
  | op₁ : Op₁ → Expr → Expr
  | op₂ : Op₂ → Expr → Expr → Expr
  | begin : Expr → Expr → Expr
  | «if» : Expr → Expr → Expr → Expr
  | app₀ : Expr → Expr
  | app  : Expr → Expr → Expr
  | lambda : String → Expr → Expr
  | «let»  : String → Expr → Expr → Expr
  | letrec : String → Expr → Expr → Expr
  | quote : Syntax.AST → Expr
  deriving Repr, Inhabited, BEq

namespace Expr

/-- Telescopes `(lambda (x₁ x₂ ⋯) body)` into `(#[x₁, x₂, ⋯], body)` -/
def telescopeLam (acc : Array String := #[]) : Expr → (Array String) × Expr
  | .lambda s b => b.telescopeLam (acc.push s)
  | x => (acc, x)

/--
Telescopes `(let/letrec ((n₁ e₁) (n₂ e₂) ⋯) body)` into
`(#[(n₁, e₁), (n₂, e₂), ⋯], body)`
-/
def telescopeLet (acc : Array $ String × Expr := #[]) :
    Expr → (Array $ String × Expr) × Expr
  | .let s v b
  | .letrec s v b => b.telescopeLet (acc.push (s, v))
  | x => (acc, x)

/-- Telescopes `(f a₁ a₂ ⋯)` into `[f, a₁, a₂, ⋯]` -/
def telescopeApp (acc : List Expr) : Expr → List Expr
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

open Std Format Syntax.AST in
partial def toFormat (esc := false) (e : Expr) : Format :=
  let _ : ToFormat Expr := ⟨toFormat⟩
  match e with
  | .lit l => format l
  | .sym s => formatSym s
  | .env => .text "CURRENT-ENV"
  | .op₁ op e =>
    paren <| format op ++ " " ++ e.toFormat esc
  | .op₂ op e₁ e₂ =>
    paren <| format op ++ " " ++ e₁.toFormat esc ++ line ++ e₂.toFormat esc
  | .begin e₁ e₂ =>
    paren <| "BEGIN" ++ line ++ e₁.toFormat esc ++ line ++ e₂.toFormat esc
  | .if cond e₁ e₂ =>
    paren <| "IF " ++ cond.toFormat esc ++ indentD (e₁.toFormat esc ++ line ++ e₂.toFormat esc)
  | .app₀ fn => paren <| fn.toFormat esc
  | .app f a =>
    let as := f.telescopeApp [a] |>.map $ toFormat esc
    paren (joinSep as " ")
  | .lambda s b =>
    let (as, b) := b.telescopeLam #[s]
    let as := as.data.map formatSym
    paren <| "LAMBDA " ++ nest 2 (paren (joinSep as " ")) ++ indentD (b.toFormat esc)
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    let bs := bs.data.map fun (n, e) => paren <| formatSym n ++ indentD (e.toFormat esc)
    paren <| "LET " ++ nest 4 (paren <| joinSep bs line) ++ indentD (b.toFormat esc)
  | .letrec s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    let bs := bs.data.map fun (n, e) => paren <| formatSym n ++ indentD (e.toFormat esc)
    paren <| "LETREC " ++ nest 7 (paren <| joinSep bs line) ++ indentD (b.toFormat esc)
  | .quote datum => paren <| "QUOTE" ++ line ++ format datum
where
  formatSym s := if esc && !reservedSyms.contains s then s!"|{s}|" else s

def toString (esc := false) : Expr → String :=
  ToString.toString ∘ toFormat esc

instance : Std.ToFormat Expr := ⟨toFormat⟩
instance : ToString Expr := ⟨toString⟩

end Expr
end Lurk.Evaluation
