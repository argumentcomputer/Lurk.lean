import Lurk.Syntax.AST
import Lurk.Hashing.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Hashing

open Std (RBMap) in
structure EncodeState where
  exprs       : RBMap ScalarPtr   ScalarExpr compare
  comms       : RBMap F           ScalarPtr compare
  stringCache : RBMap (List Char) ScalarPtr  compare
  astCache    : RBMap Syntax.AST  ScalarPtr  compare
  deriving Inhabited

def EncodeState.store (stt : EncodeState) : ScalarStore :=
  ⟨stt.exprs, stt.comms⟩

abbrev EncodeM := StateM EncodeState

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : EncodeM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def addCommitment (hash : F) (ptr : ScalarPtr) : EncodeM F :=
  modifyGet fun stt => (hash, { stt with comms := stt.comms.insert hash ptr })

def encodeString (s : List Char) : EncodeM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s with
      | [] => return ⟨.strNil, F.zero⟩
      | c :: cs => do
        let headPtr := ⟨.char, .ofNat c.toNat⟩
        let tailPtr ← encodeString cs
        let ptr := ⟨.strCons, hashPtrPair headPtr tailPtr⟩
        let expr := .strCons headPtr tailPtr
        addExprHash ptr expr
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def encodeAST (x : Syntax.AST) : EncodeM ScalarPtr := do
  match (← get).astCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil =>
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let strConsPtr ← encodeString ['N', 'I', 'L']
        let strPtr ← addExprHash ⟨.str, strConsPtr.val⟩ (.str strConsPtr)
        addExprHash ⟨.nil, strPtr.val⟩ (.sym strPtr)
      | .num n => return ⟨.num, .ofNat n⟩
      | .char c => return ⟨.char, .ofNat c.toNat⟩
      | .str s => do
        let strConsPtr ← encodeString s.data
        addExprHash ⟨.str, strConsPtr.val⟩ (.str strConsPtr)
      | .sym s =>
        let strConsPtr ← encodeString s.data
        let strPtr ← addExprHash ⟨.str, strConsPtr.val⟩ (.str strConsPtr)
        addExprHash ⟨.sym, strPtr.val⟩ (.sym strPtr)
      | .cons car cdr =>
        let car ← encodeAST car
        let cdr ← encodeAST cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })
  
def hideAST (secret : F) (x : Syntax.AST)  : EncodeM F := do
  let ptr ← encodeAST x
  let hash := hashPtrPair ⟨.comm, secret⟩ ptr 
  addCommitment hash ptr

end Lurk.Hashing

namespace Lurk.Syntax.AST

open Lurk.Hashing

def encode (x : Syntax.AST) : ScalarPtr × ScalarStore :=
  match StateT.run (encodeAST x) default with
  | (ptr, stt) => (ptr, stt.store)
  
def hide (secret : F) (x : Syntax.AST) : F × ScalarStore :=
  match StateT.run (hideAST secret x) default with
  | (hash, stt) => (hash, stt.store)

def commit (x : Syntax.AST) : F × ScalarStore :=
  match StateT.run (hideAST (.ofNat 0) x) default with
  | (hash, stt) => (hash, stt.store)

end Lurk.Syntax.AST
