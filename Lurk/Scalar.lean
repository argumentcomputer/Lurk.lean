import Lurk.Tag

namespace Lurk

structure ScalarPtr where
  tag : Tag
  val : F

inductive ScalarExpr where
  | nil
  | cons (car: ScalarPtr) (cdr: ScalarPtr)
  | num (val: F)
  | char (x : F)
  | str (head : ScalarPtr) (tail : ScalarPtr)

def hash4 : F → F → F → F → F := sorry

def hashPtrPair (x y : ScalarPtr) : F :=
  hash4 x.tag.hash x.val y.tag.hash y.val

open Std in
structure ScalarStore where
  charCache   : RBMap Char   ScalarPtr compare
  stringCache : RBMap String ScalarPtr compare

abbrev HashM := StateT ScalarStore Id

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
      let val := hashPtrPair head tail
      return ⟨.str, val⟩

def ScalarExpr.hash : ScalarExpr → HashM F
  | .nil => sorry
  | .cons car cdr => return hashPtrPair car cdr
  | .num x => return x
  | .char x => sorry
  | .str h t => sorry

end Lurk
