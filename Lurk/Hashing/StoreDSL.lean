import Lean
import Lurk.Hashing.Scalar 

/-!
# Helper DSL for generating test stores

Look below for how to do this -- it's a bit awkward.

**Do not import this file into any other!**.
-/

open Lean Elab Meta Term Lurk Hashing
namespace Lurk.Hashing.DSL
declare_syntax_cat                  scalar_ptr
scoped syntax "(nil, Scalar(" num "))"   : scalar_ptr
scoped syntax "(cons, Scalar(" num "))"  : scalar_ptr
scoped syntax "(sym, Scalar(" num "))"   : scalar_ptr
scoped syntax "(fun, Scalar(" num "))"   : scalar_ptr
scoped syntax "(num, " num ")"           : scalar_ptr
scoped syntax "(thunk, Scalar(" num "))" : scalar_ptr
scoped syntax "(str, Scalar(" num "))"   : scalar_ptr
scoped syntax "(char, " char ")"         : scalar_ptr
scoped syntax "(comm, Scalar(" num "))"  : scalar_ptr

declare_syntax_cat                                             scalar_expr
scoped syntax "Cons(" scalar_ptr ", " scalar_ptr ")"                : scalar_expr
scoped syntax "Comm(" num ", " scalar_ptr ")"                       : scalar_expr
scoped syntax "Sym(" scalar_ptr ")"                                 : scalar_expr
scoped syntax "Fun(" scalar_ptr ", " scalar_ptr ", " scalar_ptr ")" : scalar_expr
scoped syntax "Num(" num ")"                                        : scalar_expr
scoped syntax "StrNil"                                              : scalar_expr
scoped syntax "StrCons(" scalar_ptr ", " scalar_ptr ")"             : scalar_expr
scoped syntax "Char(" char ")"                                      : scalar_expr

declare_syntax_cat store_entry
scoped syntax scalar_ptr ": " scalar_expr : store_entry

declare_syntax_cat lurk_store
scoped syntax "scalar_store: { " store_entry,*,? " }" : lurk_store

def mkF (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``Lurk.Syntax.mkF #[mkNatLit n]

def mkScalarPtr (tag : Name) (n : Nat) : TermElabM Lean.Expr := do
  mkAppM ``ScalarPtr.mk #[mkConst tag, ← mkF n]

def elabScalarPtr : Syntax → TermElabM Lean.Expr 
  | `(scalar_ptr| (nil, Scalar( $n ))) =>
    mkScalarPtr ``Tag.nil n.getNat
  | `(scalar_ptr| (cons, Scalar( $n ))) => 
    mkScalarPtr ``Tag.cons n.getNat
  | `(scalar_ptr| (sym, Scalar( $n ))) =>
    mkScalarPtr ``Tag.sym n.getNat
  | `(scalar_ptr| (fun, Scalar( $n ))) =>
    mkScalarPtr ``Tag.fun n.getNat
  | `(scalar_ptr| (num, $n:num) ) =>
    mkScalarPtr ``Tag.num n.getNat
  | `(scalar_ptr| (thunk, Scalar( $n ))) =>
    mkScalarPtr ``Tag.thunk n.getNat
  | `(scalar_ptr| (str, Scalar( $n ))) =>
    mkScalarPtr ``Tag.str n.getNat
  | `(scalar_ptr| (char, $c) ) =>
    mkScalarPtr ``Tag.char c.getChar.toNat
  | `(scalar_ptr| (comm, Scalar( $n ))) =>
    mkScalarPtr ``Tag.comm n.getNat
  | _ => throwUnsupportedSyntax

def elabScalarExpr : Syntax → TermElabM Lean.Expr 
  | `(scalar_expr| Cons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.cons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| Comm($n, $p) ) => do
    mkAppM ``ScalarExpr.cons #[← mkF n.getNat, ← elabScalarPtr p]
  | `(scalar_expr| Sym($p) ) => do
    mkAppM ``ScalarExpr.sym #[← elabScalarPtr p]
  | `(scalar_expr| Fun($p1, $p2, $p3) ) => do
    mkAppM ``ScalarExpr.fun #[← elabScalarPtr p1, ← elabScalarPtr p2, ← elabScalarPtr p3]
  | `(scalar_expr| Num($n) ) => do
    mkAppM ``ScalarExpr.num #[← mkF n.getNat]
  | `(scalar_expr| StrNil ) => do
    return mkConst ``ScalarExpr.strNil
  | `(scalar_expr| StrCons($p1, $p2) ) => do
    mkAppM ``ScalarExpr.strCons #[← elabScalarPtr p1, ← elabScalarPtr p2]
  | `(scalar_expr| Char($c) ) => do
    mkAppM ``ScalarExpr.char #[← mkF c.getChar.toNat]
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

/-! # Instructions 

1. Add the desired input below
2. Uncomment the last `#eval` line and copy the output directly.
   The output is already structured as valid Lean code. 

## Warning!

We have to do this copy/paste because we have to avoid 
importing this file anywhere. Because of how `declare_syntax_cat` 
works in Lean, the syntax defined in this file pollutes other syntax spaces
and leads to very annoying bugs. 

-/

def out := [store| 
-- BEGIN INPUT BELOW 
scalar_store: {
  (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): Sym((str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (cons, Scalar(0x0540fc0449f56bc7a3d5c3df87c139a09ed8f94fa5801c9664a009b19f766369)): Cons((cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110)), (cons, Scalar(0x350a36ba3d46e278ca108cd94008ffe38d47a1665eb137bd7e724e9f4560e0f1))),
  (cons, Scalar(0x2f54a6df362aeab331aaef0be4860c25002db6a2d06d5adbb2f89b21f435d28f)): Cons((sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)), (cons, Scalar(0x0540fc0449f56bc7a3d5c3df87c139a09ed8f94fa5801c9664a009b19f766369))),
  (cons, Scalar(0x6235f2d4900b2a1ab2cbcfa6a38c4f5768516220c51f7a83158919f67b9c27cf)): Cons((sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)), (cons, Scalar(0x49b8f1a3ab095e3f85518e41aaf4cba9990ea6c9a11d1c4fbdad741ebb2dc7ed))),
  (cons, Scalar(0x49b8f1a3ab095e3f85518e41aaf4cba9990ea6c9a11d1c4fbdad741ebb2dc7ed)): Cons((sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)), (cons, Scalar(0x428c75e9b1613a9a4054c52b18e0fbd5b95d04101b34a0728806aa4ac8014110))),
  (cons, Scalar(0x350a36ba3d46e278ca108cd94008ffe38d47a1665eb137bd7e724e9f4560e0f1)): Cons((cons, Scalar(0x6235f2d4900b2a1ab2cbcfa6a38c4f5768516220c51f7a83158919f67b9c27cf)), (nil, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2))),
  (sym, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): Sym((str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600))),
  (sym, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): Sym((str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc))),
  (sym, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): Sym((str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa))),
  (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000)): StrNil,
  (str, Scalar(0x6ec5d213885296267978e92a3da46608e05b99d10f279dd91ff72c44a1901600)): StrCons((char, 'X'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09)): StrCons((char, 'I'), (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570))),
  (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36)): StrCons((char, 'A'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x18118519a123348a6b31a86f2688156dc236615cff46dfa0f013496f4bc18570)): StrCons((char, 'L'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x02e1314a79caf97ee88842647fe82bb88f5f795845cd3ed258ff172dae38cdb2)): StrCons((char, 'N'), (str, Scalar(0x2a7575c0facca35dc32adee47b9cdf5584f18b6e9d00a8c229b83e8815a4ba09))),
  (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9)): StrCons((char, 'A'), (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1))),
  (str, Scalar(0x4d6ef30d61392956b7c6de65e98b4d1ae39dd60ec21aa51c116a17e9d34f5dd1)): StrCons((char, 'M'), (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da))),
  (str, Scalar(0x71d61cb05f8baceceec13a1565f4fea70316094b632ff5b2a7c2a2be8be099da)): StrCons((char, 'B'), (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe))),
  (str, Scalar(0x09584b74a1bc019ffa64a74fe874135e1443fc6c58fd3fd44c756c56ec34bbdc)): StrCons((char, '+'), (str, Scalar(0x0000000000000000000000000000000000000000000000000000000000000000))),
  (str, Scalar(0x3f1a96056e0c9f204c79a44ebb177feeecac5436e784fa6652d905969db63bfa)): StrCons((char, 'L'), (str, Scalar(0x454cd67d0033680754a96ebb6f8844c35be1332dad1bfedf26f6c3c1256147b9))),
  (str, Scalar(0x6992424b87ef822525fe6564e8b2364b79ddd9b4a6ca84fdc8436d4258b306fe)): StrCons((char, 'D'), (str, Scalar(0x579392079baf4f51f8ad999a9c3a03a53ad27817b7246808f0665211a9109f36))),
}
-- END OF INPUT
]

-- uncomment this line and copy the output directly
#eval IO.println out.repr
