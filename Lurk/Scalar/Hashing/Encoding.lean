import Lurk.Frontend.AST
import Lurk.Scalar.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Scalar

open Frontend (AST)

open Std (RBMap) in
structure EncodeState where
  exprs       : RBMap ScalarPtr   (Option ScalarExpr) compare
  comms       : RBMap F           ScalarPtr           compare
  stringCache : RBMap (List Char) ScalarPtr           compare
  astCache    : RBMap AST         ScalarPtr           compare
  deriving Inhabited

def EncodeState.store (stt : EncodeState) : ScalarStore :=
  ⟨stt.exprs, stt.comms⟩

abbrev EncodeM := StateM EncodeState

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : EncodeM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr (some expr) })

def addCommitment (hash : F) (ptr : ScalarPtr) : EncodeM F :=
  modifyGet fun stt => (hash, { stt with comms := stt.comms.insert hash ptr })

def encodeString (s : List Char) : EncodeM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s with
      | [] => addExprHash ⟨.str, F.zero⟩ .strNil
      | c :: cs =>
        let n := .ofNat c.toNat
        let headPtr ← addExprHash ⟨.char, n⟩ (.char n)
        let tailPtr ← encodeString cs
        addExprHash ⟨.str, hashPtrPair headPtr tailPtr⟩ (.strCons headPtr tailPtr) 
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def encodeAST (x : AST) : EncodeM ScalarPtr := do
  match (← get).astCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil =>
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← encodeString ['N', 'I', 'L']
        addExprHash ⟨.nil, ptr.val⟩ (.sym ptr)
      | .num n => let n := .ofNat n; addExprHash ⟨.num, n⟩ (.num n)
      | .char c => let n := .ofNat c.toNat; addExprHash ⟨.char, n⟩ (.char n)
      | .str s => encodeString s.data
      | .sym s =>
        let ptr ← encodeString s.data
        addExprHash ⟨.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← encodeAST car
        let cdr ← encodeAST cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })
  
def hideAST (secret : F) (x : AST) : EncodeM F := do
  let ptr ← encodeAST x
  addCommitment (hashPtrPair ⟨.comm, secret⟩ ptr ) ptr

end Lurk.Scalar

namespace Lurk.Frontend.AST

open Lurk.Scalar

def encode (x : AST) : ScalarPtr × ScalarStore :=
  match StateT.run (encodeAST x) default with
  | (ptr, stt) => (ptr, stt.store)

def encode' (x : AST) (stt : EncodeState := default) :
    ScalarPtr × EncodeState :=
  StateT.run (encodeAST x) stt

def hide (secret : F) (x : AST) : F × ScalarStore :=
  match StateT.run (hideAST secret x) default with
  | (hash, stt) => (hash, stt.store)

def commit (x : AST) : F × ScalarStore :=
  match StateT.run (hideAST (.ofNat 0) x) default with
  | (hash, stt) => (hash, stt.store)

end Lurk.Frontend.AST
