import Lurk.Hashing2.HashM
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Lurk.Hashing

def hashPtrPair (x y : ScalarPtr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

partial def hashString (s : String) : HashM ScalarPtr := do
  match (← get).stringCache.find? s with
  | some ptr => pure ptr
  | none => 
    let ptr ← match s.data with
    | c :: cs => do
      let headPtr := ⟨.char, .ofNat c.toNat⟩
      let tailPtr ← hashString ⟨cs⟩
      let ptr := ⟨Tag.str, hashPtrPair headPtr tailPtr⟩
      let expr := .strCons headPtr tailPtr
      addToStore ptr expr 
    | [] => addToStore ⟨Tag.str, F.zero⟩ .strNil
    modifyGet fun stt =>
      (ptr, { stt with stringCache := stt.stringCache.insert s ptr })

def hashAST (x : Syntax.AST) : HashM ScalarPtr := do
  match (← get).astCache.find? x with
  | some ptr => pure ptr
  | none =>
    let ptr ← match x with
      | .nil
      | .sym "NIL" => do
        -- `nil` has its own tag instead of `.sym`. Thus we need to manually
        -- hash it as a string and make a `.nil` pointer with it
        let ptr ← hashString "NIL"
        addToStore ⟨Tag.nil, ptr.val⟩ (.sym ptr)
      | .num n => let n := .ofNat n; addToStore ⟨Tag.num, n⟩ (.num n)
      | .str s => hashString s
      | .char c => return ⟨.char, .ofNat c.toNat⟩
      | .sym s =>
        let ptr ← hashString s
        addToStore ⟨Tag.sym, ptr.val⟩ (.sym ptr)
      | .cons car cdr =>
        let car ← hashAST car
        let cdr ← hashAST cdr
        addToStore ⟨.cons, hashPtrPair car cdr⟩ (.cons car cdr)
    modifyGet fun stt =>
      (ptr, { stt with astCache := stt.astCache.insert x ptr })

end Lurk.Hashing

open Lurk.Hashing in
def Lurk.Syntax.AST.hash (x : Syntax.AST) : ScalarPtr × ScalarStore :=
  match StateT.run (hashAST x.upper) default with
  | (ptr, stt) => (ptr, stt.store)
