import Lurk.Field

open Std

namespace Lurk.Backend2

/-- Basic Lurk primitives -/
inductive Atom
  -- `t` and `nil`
  | t | nil
  -- Numerical values
  | num : F → Atom
  | u64 : UInt64 → Atom
  -- Strings
  | str : String → Atom
  -- Characters
  | char : Char → Atom
  deriving Repr, BEq

namespace Atom

def toString : Atom → String
  | .nil    => "NIL"
  | .t      => "T"
  | .num  n => ToString.toString n
  | .u64  n => s!"{n}u64"
  | .str  s => s!"\"{s}\""
  | .char c => s!"#\\{c}"

def pprint : Atom → Format
  | .nil    => "NIL"
  | .t      => "T"
  | .num  n => n.asHex
  | .u64  n => s!"{n}u64"
  | .str  s => s!"\"{s}\""
  | .char c => s!"#\\{c}"

instance : ToFormat Atom where
  format := pprint

end Atom

inductive Op₁
  | atom | car | cdr | emit
  | commit | comm | «open»
  | num | u64 | char
  deriving Repr, BEq

def Op₁.toFormat : Op₁ → Format
  | .atom   => "ATOM"
  | .car    => "CAR"
  | .cdr    => "CDR"
  | .emit   => "EMIT"
  | .commit => "COMMIT"
  | .comm   => "COMM"
  | .open   => "OPEN"
  | .num    => "NUM"
  | .u64    => "U64"
  | .char   => "CHAR"

def Op₁.toString := ToString.toString ∘ Op₁.toFormat

instance : Std.ToFormat Op₁ := ⟨Op₁.toFormat⟩

inductive Op₂
  | cons | strcons
  | add | sub | mul | div | mod | numEq | lt | gt | le | ge | eq
  | hide
  deriving Repr, BEq

def Op₂.toFormat : Op₂ → Format
  | .cons    => "CONS"
  | .strcons => "STRCONS"
  | .add     => "+"
  | .sub     => "-"
  | .mul     => "*"
  | .div     => "/"
  | .mod     => "%"
  | .numEq   => "="
  | .lt      => "<"
  | .gt      => ">"
  | .le      => "<="
  | .ge      => ">="
  | .eq      => "EQ"
  | .hide    => "HIDE"

def Op₂.toString := ToString.toString ∘ Op₂.toFormat

instance : Std.ToFormat Op₂ := ⟨Op₂.toFormat⟩

inductive Datum
  | num  : Fin N  → Datum
  | u64  : UInt64 → Datum
  | char : Char   → Datum
  | str  : String → Datum
  | sym  : String → Datum
  | cons : Datum  → Datum → Datum
  deriving Inhabited, BEq

@[match_pattern] def Datum.nil := Datum.sym "NIL"
@[match_pattern] def Datum.t   := Datum.sym "T"

class ToDatum (α : Type _) where
  toDatum : α → Datum

export ToDatum (toDatum)

instance : ToDatum Nat where
  toDatum := .num ∘ .ofNat

instance : ToDatum String where
  toDatum := .str

instance [ToDatum α] : ToDatum (List α) where
  toDatum as := as.foldl (fun acc a => .cons acc (toDatum a)) (.sym "NIL")

instance [ToDatum α] : ToDatum (Array α) := ⟨toDatum ∘ Array.toList⟩

inductive Expr
  | atom : Atom → Expr
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
  | quote : Datum → Expr
  deriving Inhabited, BEq

namespace Expr

class ToExpr (α : Type _) where
  toExpr : α → Expr

export ToExpr (toExpr)

instance : ToExpr Nat where
  toExpr := .atom ∘ .num ∘ .ofNat

instance : ToExpr Char where
  toExpr := .atom ∘ .char

instance : ToExpr String where
  toExpr := .atom ∘ .str

instance : ToExpr Expr := ⟨id⟩

/-- Telescopes `(lambda (x₁ x₂ ⋯) body)` into `(#[x₁, x₂, ⋯], body)` -/
def telescopeLam (acc : Array String := #[]) : Expr → (Array String) × Expr
  | .lambda s b => b.telescopeLam (acc.push s)
  | x => (acc, x)

/--
Telescopes `(let ((n₁ e₁) (n₂ e₂) ⋯) body)` into
`(#[(n₁, e₁), (n₂, e₂), ⋯], body)`
-/
def telescopeLet (acc : Array $ String × Expr := #[]) :
    Expr → (Array $ String × Expr) × Expr
  | .let s v b => b.telescopeLet (acc.push (s, v))
  | x => (acc, x)

/--
Telescopes `(letrec ((n₁ e₁) (n₂ e₂) ⋯) body)` into
`(#[(n₁, e₁), (n₂, e₂), ⋯], body)`
-/
def telescopeLetrec (acc : Array $ String × Expr := #[]) :
    Expr → (Array $ String × Expr) × Expr
  | .letrec s v b => b.telescopeLetrec (acc.push (s, v))
  | x => (acc, x)

/-- Telescopes `(f a₁ a₂ ⋯)` into `[f, a₁, a₂, ⋯]` -/
def telescopeApp (acc : List Expr) : Expr → List Expr
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

def telescopeBegin : Expr → Array Expr
  | .begin e₁ e₂ => e₁.telescopeBegin ++ e₂.telescopeBegin
  | x => #[x]

def telescopeDatumCons (acc : Array Datum := #[]) : Datum → Array Datum × Datum
  | .cons x y => telescopeDatumCons (acc.push x) y
  | x => (acc, x)

open Format

partial def datumFormat : Datum → Format
  | .num x | .sym x => format x
  | .u64 x => s!"{x}u64"
  | .char c => s!"#\\{c}"
  | .str s => s!"\"{s}\""
  | x@(.cons ..) =>
    match telescopeDatumCons #[] x with
    | (xs, .sym "NIL") => paren $ fmtList xs.data
    | (xs, y) => paren $ fmtList xs.data ++ line ++ "." ++ line ++ (datumFormat y)
where
  fmtList : List Datum → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ (datumFormat x)) (datumFormat x)

def datumString : Datum → String :=
  toString ∘ datumFormat

instance : ToFormat Datum := ⟨datumFormat⟩
instance : ToString Datum := ⟨datumString⟩

partial def toFormat (esc := false) (e : Expr) : Format :=
  have : ToFormat Expr := ⟨toFormat⟩
  match e with
  | .atom l => format l
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
    let (bs, b) := b.telescopeLetrec #[(s, v)]
    let bs := bs.data.map fun (n, e) => paren <| formatSym n ++ indentD (e.toFormat esc)
    paren <| "LETREC " ++ nest 7 (paren <| joinSep bs line) ++ indentD (b.toFormat esc)
  | .quote datum => paren <| "QUOTE" ++ line ++ format datum
where
  formatSym s := if esc then s!"|{s}|" else s

def toString (esc := false) : Expr → String :=
  ToString.toString ∘ toFormat esc

instance : ToFormat Expr := ⟨toFormat⟩
instance : ToString Expr := ⟨toString⟩

end Lurk.Backend2.Expr
