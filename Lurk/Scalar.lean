import Lurk.Tag
import Lurk.AST

namespace Lurk

structure ScalarPtr where
  tag : Tag
  val : F
  deriving Ord

inductive ScalarExpr where
  | nil
  | cons (car : ScalarPtr) (cdr : ScalarPtr)
  | sym (sym : ScalarPtr)
  | num (val : F)
  | str (head : ScalarPtr) (tail : ScalarPtr)
  | char (x : F)

def hash4 : F → F → F → F → F := sorry

def hashPtrPair (x y : ScalarPtr) : F :=
  hash4 x.tag.hash x.val y.tag.hash y.val

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
    let ptr := ⟨.char, .ofNat c.val.toNat⟩
    modifyGet fun stt =>
      (ptr, { stt with charCache := stt.charCache.insert c ptr })

def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => match s with
    | ⟨[]⟩ => return ⟨.str, F.zero⟩
    | ⟨c :: cs⟩ => do
      let head ← hashChar c
      let tail ← hashString ⟨cs⟩
      let ptr := ⟨.str, hashPtrPair head tail⟩
      modifyGet fun stt =>
        (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : HashM ScalarPtr :=
  modifyGet fun stt =>
    (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def hashExpr : Expr → HashM ScalarPtr
  | .lit .nil =>
    -- addToStore ⟨.nil, F.zero⟩ .nil -- I'd like to do this instead
    do addToStore ⟨.nil, (← hashString "nil").val⟩ .nil
  | .lit .t => sorry
  | .lit (.num n) => addToStore ⟨.num, n⟩ (.num n)
  | .lit (.str ⟨c :: cs⟩) => do
    let headPtr ← hashChar c
    let tailPtr ← hashString ⟨cs⟩
    let ptr := ⟨.str, hashPtrPair headPtr tailPtr⟩
    let expr := (.str headPtr tailPtr)
    addToStore ptr expr
  | .lit (.char c) => do
    let ptr ← hashChar c
    addToStore ptr (.char ptr.val)
  | .sym name => do
    let ptr ← hashString (name.toString false)
    do addToStore ⟨.sym, ptr.val⟩ (.sym ptr)
  | .cons car cdr => do
    let carPtr ← hashExpr car
    let cdrPtr ← hashExpr cdr
    let ptr := ⟨.cons, (hashPtrPair carPtr cdrPtr)⟩
    let expr := .cons carPtr cdrPtr
    addToStore ptr expr
  | _ => sorry

def Expr.hash (e : Expr) : ScalarStore × ScalarPtr := Id.run do
  match ← StateT.run (hashExpr e) default with
  | (ptr, stt) => (stt.store, ptr)

end Lurk
