import Lurk.Syntax2.AST
import Lurk.Hashing2.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Hashing

open Std (RBMap) in
structure EncodeState where
  exprs       : RBMap ScalarPtr  ScalarExpr compare
  stringCache : RBMap String     ScalarPtr  compare
  astCache    : RBMap Syntax.AST ScalarPtr  compare
  deriving Inhabited

def EncodeState.store (stt : EncodeState) : ScalarStore :=
  ⟨stt.exprs⟩

abbrev EncodeM := StateM EncodeState

def addToStore (ptr : ScalarPtr) (expr : ScalarExpr) : EncodeM ScalarPtr :=
  modifyGet fun stt => (ptr, { stt with exprs := stt.exprs.insert ptr expr })

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
      addToStore ptr expr 
    | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
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
        addToStore ⟨.nil, ptr.val⟩ (.sym ptr)
      | .num n => let n := .ofNat n; addToStore ⟨.num, n⟩ (.num n)
      | .char c => return ⟨.char, .ofNat c.toNat⟩
      | .str s => encodeString s
      | .sym s =>
        let ptr ← encodeString s
        addToStore ⟨.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← encodeAST car
        let cdr ← encodeAST cdr
        addToStore ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.AST.encode (x : Syntax.AST) : ScalarPtr × ScalarStore :=
  match StateT.run (encodeAST x) default with
  | (ptr, stt) => (ptr, stt.store)
