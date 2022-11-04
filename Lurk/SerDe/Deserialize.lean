import Lurk.Hashing.Datatypes

namespace Lurk.SerDe

open Lurk.Hashing

structure DeserializeContext where
  bytes : ByteArray
  size  : Nat
  valid : size = bytes.size

abbrev DeserializeM := ReaderT DeserializeContext $ ExceptT String $ StateM Nat

def deF : DeserializeM F := do
  let idx ← get
  if (← read).size - idx < 32 then
    throw "Not enough data to read a field number"
  let bytes := (← read).bytes.copySlice idx .empty 0 32
  set $ idx + 32
  return .ofBytes bytes

def deTag : DeserializeM Tag := do
  match (← deF).val with
  | 0 => return .nil
  | 1 => return .cons
  | 2 => return .sym
  | 3 => return .fun
  | 4 => return .num
  | 5 => return .thunk
  | 6 => return .str
  | 7 => return .char
  | 8 => return .comm
  | x => throw s!"Invalid data for a tag: {x}"

def dePtr : DeserializeM ScalarPtr :=
  return ⟨← deTag, ← deF⟩

def dePtrExprPair : DeserializeM (ScalarPtr × ScalarExpr) := do
  let ptr ← dePtr
  match ptr.tag with
  | _ => sorry

def deserialize (bytes : ByteArray) :
    Except String ((List ScalarPtr) × ScalarStore) := sorry

end Lurk.SerDe
