import Lurk.AST
import Lurk.Hashing.Datatypes

namespace Lurk

def hash4 : F → F → F → F → F := sorry

def hashPtrPair (x y : ScalarPtr) : F :=
  hash4 x.kind x.val y.kind y.val

open Std in
structure ScalarStore where
  exprs : RBMap ScalarPtr ScalarExpr compare
  -- conts : RBMap ScalarContPtr ScalarCont compare
  deriving Inhabited

open Std in
structure HashState where
  exprs       : RBMap ScalarPtr ScalarExpr compare
  charCache   : RBMap Char   ScalarPtr compare
  stringCache : RBMap String ScalarPtr compare
  deriving Inhabited

def HashState.store (stt : HashState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev HashM := StateM HashState

def hashChar (c : Char) : HashM ScalarPtr := do
  match (← get).charCache.find? c with
  | some ptr => pure ptr
  | none =>
    let ptr := ⟨Tag.char, .ofNat c.val.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => match s with
    | ⟨[]⟩ => return ⟨Tag.str, F.zero⟩
    | ⟨c :: cs⟩ => do
      let head ← hashChar c
      let tail ← hashString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair head tail⟩
      modifyGet fun stt =>
        (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt =>
    (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def hashExpr : Expr → HashM ScalarPtr
  | .lit .nil => do addToStore ⟨Tag.nil, (← hashString "nil").val⟩ .nil
  | .lit .t => do
    let ptr ← hashString "t"
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .lit (.num n) => addToStore ⟨Tag.num, n⟩ (.num n)
  | .lit (.str ⟨c :: cs⟩) => do
    let headPtr ← hashChar c
    let tailPtr ← hashString ⟨cs⟩
    let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
    let expr := (.str headPtr tailPtr)
    addToStore ptr expr
  | .lit (.char c) => do
    let ptr ← hashChar c
    addToStore ptr (.char ptr.val)
  | .sym name => do
    let ptr ← hashString (name.toString false)
    do addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | .cons car cdr => do
    let carPtr ← hashExpr car
    let cdrPtr ← hashExpr cdr
    let ptr := ⟨Op2.cons, (hashPtrPair carPtr cdrPtr)⟩
    let expr := .cons carPtr cdrPtr
    addToStore ptr expr
  | .strcons car cdr => do
    let carPtr ← hashExpr car
    let cdrPtr ← hashExpr cdr
    let ptr := ⟨Op2.strcons, (hashPtrPair carPtr cdrPtr)⟩
    let expr := .cons carPtr cdrPtr
    addToStore ptr expr
  | .comm expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.comm, ptr.val⟩ (.comm ptr.val ptr)
  | .atom expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.atom, ptr.val⟩ (.comm ptr.val ptr) -- `.comm`?!
  | .car expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.car, ptr.val⟩ (.comm ptr.val ptr) -- `.comm`?!
  | .cdr expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.cdr, ptr.val⟩ (.comm ptr.val ptr) -- `.comm`?!
  | .emit expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.emit, ptr.val⟩ (.comm ptr.val ptr) -- `.comm`?!
  | .commit expr => do
    let ptr ← hashExpr expr
    addToStore ⟨Op1.commit, ptr.val⟩ (.comm ptr.val ptr) -- `.comm`?!
  | .hide secret target => do
    let secretPtr ← hashExpr secret
    let targetPtr ← hashExpr target
    let ptr := ⟨Op2.hide, (hashPtrPair secretPtr targetPtr)⟩
    let expr := .cons secretPtr targetPtr
    addToStore ptr expr
  | .currEnv => do
    let ptr ← hashString "current-env"
    addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
  | _ => sorry

def Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)

end Lurk
