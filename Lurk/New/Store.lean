import Std.Data.RBMap
import Poseidon.ForLurk
import Lurk.New.Tag
import Lurk.New.LDON

open Lurk (F)

section YoloPlaceholders

def hash2 : F → F → F :=
  fun a b => .ofNat $ (Poseidon.Lurk.hash3 a 8192 b).norm

def hash3 : F → F → F → F :=
  fun a b c => .ofNat $ (Poseidon.Lurk.hash3 a b c).norm

def hash4 : F → F → F → F → F :=
  fun a b c d => .ofNat $ (Poseidon.Lurk.hash4 a b c d).norm
 
def hash6 : F → F → F → F → F → F → F :=
  fun a b c d e f => hash2 (hash3 a b c) (hash3 d e f)

def hash8 : F → F → F → F → F → F → F → F → F :=
  fun a b c d e f g h => hash2 (hash4 a b c d) (hash4 e f g h)

end YoloPlaceholders

structure ExprPtr where
  tag : ExprTag
  val : F
  deriving Ord, BEq

structure ContPtr where
  tag : ContTag
  val : F
  deriving Ord

inductive ExprPtrImg
  | cons : ExprPtr → ExprPtr → ExprPtrImg
  | «fun» : ExprPtr → ExprPtr → ExprPtr → ExprPtrImg
  | comm : F → ExprPtr → ExprPtrImg

inductive ContPtrImg
  | cont0 : ContPtr → ContPtrImg
  | cont1 : ExprPtr → ContPtr → ContPtrImg
  | cont2 : ExprPtr → ExprPtr → ContPtr → ContPtrImg
  | cont3 : ExprPtr → ExprPtr → ExprPtr → ContPtr → ContPtrImg

open Std (RBMap)

structure Store where
  exprData : RBMap ExprPtr ExprPtrImg compare

  charsCache : RBMap (List Char) ExprPtr compare
  stringsCashe : RBMap (List String) ExprPtr compare

  ptrToStr : RBMap ExprPtr String compare
  strToPtr : RBMap String ExprPtr compare

  ptrToSym : RBMap ExprPtr Symbol compare
  symToPtr : RBMap Symbol ExprPtr compare

  contData : RBMap ContPtr ContPtrImg compare
  deriving Inhabited

namespace Store

abbrev StoreM := EStateM String Store

@[inline] def addToExprStore (ptr : ExprPtr) (img : ExprPtrImg) : StoreM ExprPtr :=
  modifyGet fun c => (ptr, { c with exprData := c.exprData.insert ptr img })

@[inline] def addToContStore (ptr : ContPtr) (img : ContPtrImg) : StoreM ContPtr :=
  modifyGet fun c => (ptr, { c with contData := c.contData.insert ptr img })

def putChars (cs : List Char) : StoreM ExprPtr := do
  match (← get).charsCache.find? cs with
  | some ptr => pure ptr
  | none =>
    let ptr ← match cs with
      | [] => pure ⟨.str, F.zero⟩
      | c :: cs =>
        let headPtr := ⟨.char, .ofNat c.toNat⟩
        let tailPtr ← putChars cs
        addToExprStore
          ⟨.str, hash4 headPtr.tag.toF headPtr.val tailPtr.tag.toF tailPtr.val⟩
          (.cons headPtr tailPtr)
    modifyGet fun stt =>
      (ptr, { stt with charsCache := stt.charsCache.insert cs ptr })

def putStrings (ss : List String) : StoreM ExprPtr := do
  match (← get).stringsCashe.find? ss with
  | some ptr => return ptr
  | none =>
    let ptr ← ss.foldrM (init := ⟨.sym, F.zero⟩) fun s acc => do
      let strPtr ← putChars s.data
      addToExprStore
        ⟨.sym, hash4 strPtr.tag.toF strPtr.val acc.tag.toF acc.val⟩
        (.cons strPtr acc)
    modifyGet fun stt =>
      (ptr, { stt with stringsCashe := stt.stringsCashe.insert ss ptr })

def putStr (str : String) : StoreM ExprPtr := do
  match (← get).strToPtr.find? str with
  | some ptr => return ptr
  | none =>
    let ptr ← putChars str.data
    modifyGet fun store => (ptr, { store with
      ptrToStr := store.ptrToStr.insert ptr str
      strToPtr := store.strToPtr.insert str ptr })

def putSym (sym : Symbol) : StoreM ExprPtr := do
  match (← get).symToPtr.find? sym with
  | some ptr => return ptr
  | none =>
    let ptr ← putStrings sym.telescope
    modifyGet fun store => (ptr, { store with
      ptrToSym := store.ptrToSym.insert ptr sym
      symToPtr := store.symToPtr.insert sym ptr })

def hashLDON : LDON → StoreM ExprPtr
  | .num n => pure ⟨.num, n⟩
  | .u64 n => pure ⟨.u64, .ofNat n.val⟩
  | .char n => pure ⟨.char, .ofNat n.toNat⟩
  | .str s => putStr s
  | .sym s => putSym s
  | .cons car cdr => do
    let car ← hashLDON car
    let cdr ← hashLDON cdr
    addToExprStore
      ⟨.cons, hash4 car.tag.toF car.val cdr.tag.toF cdr.val⟩
      (.cons car cdr)

def hideLDON (secret : F) (x : LDON) : StoreM F := do
  let ptr ← hashLDON x
  let hash := hash3 secret ptr.tag.toF ptr.val
  discard $ addToExprStore ⟨.comm, hash⟩ (.comm secret ptr)
  return hash

def getStr (ptr : ExprPtr) : StoreM String := do
  match (← get).ptrToStr.find? ptr with
  | some str => return str
  | none => sorry -- pull from store and then memoize

def getSym (ptr : ExprPtr) : StoreM Symbol := do
  match (← get).ptrToSym.find? ptr with
  | some sym => return sym
  | none => sorry -- pull from store and then memoize

end Store

def ExprPtr.isNil (ptr : ExprPtr) : Store.StoreM Bool :=
  return ptr == (← Store.putSym .nil)
