import Lean
import Lurk.Hashing.Datatypes

/-!
# Helper DSL for generating test stores
-/

namespace Lurk.Hashing.DSL

open Lean Elab Meta Term Lurk Hashing

declare_syntax_cat                 scalar_ptr
scoped syntax "(nil, " num ")"   : scalar_ptr
scoped syntax "(cons, " num ")"  : scalar_ptr
scoped syntax "(sym, " num ")"   : scalar_ptr
scoped syntax "(fun, " num ")"   : scalar_ptr
scoped syntax "(num, " num ")"   : scalar_ptr
scoped syntax "(thunk, " num ")" : scalar_ptr
scoped syntax "(str, " num ")"   : scalar_ptr
scoped syntax "(char, " char ")" : scalar_ptr
scoped syntax "(comm, " num ")"  : scalar_ptr
scoped syntax "(u64, " num ")"   : scalar_ptr

declare_syntax_cat                                                    scalar_expr
scoped syntax "Cons(" scalar_ptr ", " scalar_ptr ")"                : scalar_expr
scoped syntax "Comm(" num ", " scalar_ptr ")"                       : scalar_expr
scoped syntax "Sym(" scalar_ptr ")"                                 : scalar_expr
scoped syntax "Fun(" scalar_ptr ", " scalar_ptr ", " scalar_ptr ")" : scalar_expr
scoped syntax "Num(" num ")"                                        : scalar_expr
scoped syntax "StrCons(" scalar_ptr ", " scalar_ptr ")"             : scalar_expr
scoped syntax "StrNil"                                              : scalar_expr
scoped syntax "Char(" char ")"                                      : scalar_expr
scoped syntax "UInt(" num ")"                                       : scalar_expr

declare_syntax_cat store_entry
scoped syntax scalar_ptr ": " scalar_expr : store_entry
scoped syntax scalar_ptr ": " "_" : store_entry

declare_syntax_cat lurk_store
scoped syntax "{ " store_entry,*,? " }" : lurk_store

def mkF (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``Lurk.F.ofNat #[mkNatLit n]

def mkScalarPtr (tag : Name) (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``ScalarPtr.mk #[mkConst tag, ← mkF n]

def elabScalarPtr : Syntax → TermElabM Lean.Expr
  | `(scalar_ptr| (nil, $n))     => mkScalarPtr ``Tag.nil   n.getNat
  | `(scalar_ptr| (cons, $n))    => mkScalarPtr ``Tag.cons  n.getNat
  | `(scalar_ptr| (sym, $n))     => mkScalarPtr ``Tag.sym   n.getNat
  | `(scalar_ptr| (fun, $n))     => mkScalarPtr ``Tag.fun   n.getNat
  | `(scalar_ptr| (num, $n:num)) => mkScalarPtr ``Tag.num   n.getNat
  | `(scalar_ptr| (thunk, $n))   => mkScalarPtr ``Tag.thunk n.getNat
  | `(scalar_ptr| (str, $n))     => mkScalarPtr ``Tag.str   n.getNat
  | `(scalar_ptr| (char, $c))    => mkScalarPtr ``Tag.char  c.getChar.toNat
  | `(scalar_ptr| (comm, $n))    => mkScalarPtr ``Tag.comm  n.getNat
  | `(scalar_ptr| (u64, $n))     => mkScalarPtr ``Tag.u64   n.getNat
  | _ => throwUnsupportedSyntax

def elabScalarExpr : Syntax → TermElabM Lean.Expr
  | `(scalar_expr| Cons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.cons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| Comm($n, $p) ) => do
    mkAppM ``ScalarExpr.cons #[← mkF n.getNat, ← elabScalarPtr p]
  | `(scalar_expr| Sym($p) ) => do mkAppM ``ScalarExpr.sym #[← elabScalarPtr p]
  | `(scalar_expr| Fun($p1, $p2, $p3) ) => do
    mkAppM ``ScalarExpr.fun #[← elabScalarPtr p1, ← elabScalarPtr p2, ← elabScalarPtr p3]
  | `(scalar_expr| Num($n) ) => do mkAppM ``ScalarExpr.num #[← mkF n.getNat]
  | `(scalar_expr| StrCons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.strCons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| StrNil ) => return mkConst ``ScalarExpr.strNil
  | `(scalar_expr| Char($c) ) => do
    mkAppM ``ScalarExpr.char #[← mkF c.getChar.toNat]
  | `(scalar_expr| UInt($n) ) => do mkAppM ``ScalarExpr.uInt #[← mkF n.getNat]
  | _ => throwUnsupportedSyntax

elab "[expr| " e:scalar_expr "]" : term =>
  elabScalarExpr e

def someScalarExpr (e : ScalarExpr) : Option ScalarExpr :=
  some e

def noneScalarExpr : Option ScalarExpr :=
  none

def elabStoreEntry : Syntax → TermElabM Lean.Expr
  | `(store_entry| $p:scalar_ptr : $e:scalar_expr ) => do
    let e ← elabScalarExpr e
    let e ← mkAppM ``someScalarExpr #[e]
    mkAppM ``Prod.mk #[← elabScalarPtr p, e]
  | `(store_entry| $p:scalar_ptr : _ ) => do
    mkAppM ``Prod.mk #[← elabScalarPtr p, mkConst ``noneScalarExpr]
  | _ => throwUnsupportedSyntax

elab "[entry| " e:store_entry "]" : term =>
  elabStoreEntry e

open Std in
def elabLurkStore : Syntax → TermElabM Lean.Expr
  | `(lurk_store| { $entries,* } ) => do
    let entries ← entries.getElems.mapM elabStoreEntry
    let optionType ← mkAppM ``Option #[mkConst ``ScalarExpr]
    let type ← mkAppM ``Prod #[mkConst ``ScalarPtr, optionType]
    let entries ← mkListLit type entries.toList
    mkAppM ``ScalarStore.ofList #[entries]
  | _ => throwUnsupportedSyntax

elab "[store| " e:lurk_store "]" : term =>
  elabLurkStore e

end Lurk.Hashing.DSL
