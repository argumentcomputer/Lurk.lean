import Lurk.Syntax2.AST
import Lurk.Hashing2.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Hashing

open Std (RBMap) in
structure EncodeState where
  exprs       : RBMap ScalarPtr  ScalarExpr compare
  comms       : RBMap F          ScalarPtr  compare
  stringCache : RBMap String     ScalarPtr  compare
  astCache    : RBMap Syntax.AST ScalarPtr  compare
  deriving Inhabited

def EncodeState.store (stt : EncodeState) : ScalarStore :=
  ⟨stt.exprs, stt.comms⟩

abbrev EncodeM := StateM EncodeState

def addExprHash (ptr : ScalarPtr) (expr : ScalarExpr) : EncodeM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

def addCommitment (hash : F) (ptr : ScalarPtr) : EncodeM F :=
  modifyGet fun stt => (hash, { stt with comms := stt.comms.insert hash ptr })

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

partial def encodeString (s : String) : EncodeM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s.data with
    | c :: cs => do
      let headPtr := ⟨.char, .ofNat c.toNat⟩
      let tailPtr ← encodeString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
      let expr := .strCons headPtr tailPtr
      addExprHash ptr expr 
    | [] => addExprHash ⟨Tag.str, F.zero⟩ .strNil
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def encodeAST (x : Syntax.AST) : EncodeM ScalarPtr := do
  match (← get).astCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil => do
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← encodeString "NIL"
        addExprHash ⟨.nil, ptr.val⟩ (.sym ptr)
      | .num n => let n := .ofNat n; addExprHash ⟨.num, n⟩ (.num n)
      | .char c => return ⟨.char, .ofNat c.toNat⟩
      | .str s => encodeString s
      | .sym s =>
        let ptr ← encodeString s
        addExprHash ⟨.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← encodeAST car
        let cdr ← encodeAST cdr
        addExprHash ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })


def hidePtr (secret : F) (ptr : ScalarPtr) : EncodeM F := do
  let hash := hashPtrPair ⟨Tag.comm, secret⟩ ptr 
  addCommitment hash ptr

def commitPtr (ptr : ScalarPtr) : EncodeM F := do
  hidePtr (.ofNat 0) ptr
  
def hideAST (secret : F) (x : Syntax.AST)  : EncodeM F := do
  let ptr ← encodeAST x
  hidePtr secret ptr

def commitAST (x : Syntax.AST) : EncodeM F := do
  hideAST (.ofNat 0) x

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
  match StateT.run (commitAST x) default with
  | (hash, stt) => (hash, stt.store)

end Lurk.Syntax.AST