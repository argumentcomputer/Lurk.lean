import Lean
import Lurk.Hashing.Datatypes

/-!
# Helper DSL for generating test stores
-/

namespace Lurk.Hashing.DSL

open Lean Elab Meta Term Lurk Hashing

declare_syntax_cat                           scalar_ptr
scoped syntax "(nil, Scalar(" num "))"     : scalar_ptr
scoped syntax "(cons, Scalar(" num "))"    : scalar_ptr
scoped syntax "(sym, Scalar(" num "))"     : scalar_ptr
scoped syntax "(fun, Scalar(" num "))"     : scalar_ptr
scoped syntax "(num, " num ")"             : scalar_ptr
scoped syntax "(thunk, Scalar(" num "))"   : scalar_ptr
scoped syntax "(str, Scalar(" num "))"     : scalar_ptr
scoped syntax "(strCons, Scalar(" num "))" : scalar_ptr
scoped syntax "(strNil, Scalar(" num "))"  : scalar_ptr
scoped syntax "(char, " char ")"           : scalar_ptr
scoped syntax "(comm, Scalar(" num "))"    : scalar_ptr

declare_syntax_cat                                                    scalar_expr
scoped syntax "Cons(" scalar_ptr ", " scalar_ptr ")"                : scalar_expr
scoped syntax "Comm(" num ", " scalar_ptr ")"                       : scalar_expr
scoped syntax "Sym(" scalar_ptr ")"                                 : scalar_expr
scoped syntax "Fun(" scalar_ptr ", " scalar_ptr ", " scalar_ptr ")" : scalar_expr
scoped syntax "Num(" num ")"                                        : scalar_expr
scoped syntax "Str(" scalar_ptr ")"                                 : scalar_expr
scoped syntax "StrCons(" scalar_ptr ", " scalar_ptr ")"             : scalar_expr
scoped syntax "StrNil"                                              : scalar_expr
scoped syntax "Char(" char ")"                                      : scalar_expr

declare_syntax_cat store_entry
scoped syntax scalar_ptr ": " scalar_expr : store_entry

declare_syntax_cat lurk_store
scoped syntax "scalar_store: { " store_entry,*,? " }" : lurk_store

def mkF (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``Lurk.F.ofNat #[mkNatLit n]

def mkScalarPtr (tag : Name) (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``ScalarPtr.mk #[mkConst tag, ← mkF n]

def elabScalarPtr : Syntax → TermElabM Lean.Expr
  | `(scalar_ptr| (nil, Scalar( $n )))     => mkScalarPtr ``Tag.nil n.getNat
  | `(scalar_ptr| (cons, Scalar( $n )))    => mkScalarPtr ``Tag.cons n.getNat
  | `(scalar_ptr| (sym, Scalar( $n )))     => mkScalarPtr ``Tag.sym n.getNat
  | `(scalar_ptr| (fun, Scalar( $n )))     => mkScalarPtr ``Tag.fun n.getNat
  | `(scalar_ptr| (num, $n:num) )          => mkScalarPtr ``Tag.num n.getNat
  | `(scalar_ptr| (thunk, Scalar( $n )))   => mkScalarPtr ``Tag.thunk n.getNat
  | `(scalar_ptr| (str, Scalar( $n )))     => mkScalarPtr ``Tag.str n.getNat
  | `(scalar_ptr| (strCons, Scalar( $n ))) => mkScalarPtr ``Tag.strCons n.getNat
  | `(scalar_ptr| (strNil, Scalar( $n )))  => mkScalarPtr ``Tag.strNil n.getNat
  | `(scalar_ptr| (char, $c) )             => mkScalarPtr ``Tag.char c.getChar.toNat
  | `(scalar_ptr| (comm, Scalar( $n )))    => mkScalarPtr ``Tag.comm n.getNat
  | _ => throwUnsupportedSyntax

def elabScalarExpr : Syntax → TermElabM Lean.Expr
  | `(scalar_expr| Cons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.cons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| Comm($n, $p) ) => do
    mkAppM ``ScalarExpr.cons #[← mkF n.getNat, ← elabScalarPtr p]
  | `(scalar_expr| Sym($p) ) => do mkAppM ``ScalarExpr.sym #[← elabScalarPtr p]
  | `(scalar_expr| Fun($p1, $p2, $p3) ) => do
    mkAppM ``ScalarExpr.fun #[← elabScalarPtr p1, ← elabScalarPtr p2, ← elabScalarPtr p3]
  | `(scalar_expr| Num($n) ) => do
    mkAppM ``ScalarExpr.num #[← mkF n.getNat]
  | `(scalar_expr| Str($p) ) => do mkAppM ``ScalarExpr.str #[← elabScalarPtr p]
  | `(scalar_expr| StrCons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.strCons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| StrNil ) => return mkConst ``ScalarExpr.strNil
  | `(scalar_expr| Char($c) ) => do mkAppM ``ScalarExpr.char #[← mkF c.getChar.toNat]
  | _ => throwUnsupportedSyntax

elab "[expr| " e:scalar_expr "]" : term =>
  elabScalarExpr e

def elabStoreEntry : Syntax → TermElabM Lean.Expr
  | `(store_entry| $p:scalar_ptr : $e:scalar_expr ) => do
    mkAppM ``Prod.mk #[← elabScalarPtr p, ← elabScalarExpr e]
  | _ => throwUnsupportedSyntax

elab "[entry| " e:store_entry "]" : term =>
  elabStoreEntry e

open Std in
def elabLurkStore : Syntax → TermElabM Lean.Expr
  | `(lurk_store| scalar_store: { $entries,* } ) => do
    let entries ← entries.getElems.mapM elabStoreEntry
    let type ← mkAppM ``Prod #[mkConst ``ScalarPtr, mkConst ``ScalarExpr]
    let entries ← mkListLit type entries.toList
    mkAppM ``ScalarStore.ofList #[entries]
  | _ => throwUnsupportedSyntax

elab "[store| " e:lurk_store "]" : term =>
  elabLurkStore e

end Lurk.Hashing.DSL
