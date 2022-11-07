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
  | 0  => return .nil
  | 1  => return .cons
  | 2  => return .sym
  | 3  => return .fun
  | 4  => return .num
  | 5  => return .thunk
  | 6  => return .str
  | 7  => return .strCons
  | 8  => return .strNil
  | 9  => return .char
  | 10 => return .comm
  | x  => throw s!"Invalid data for a tag: {x}"

def dePtr : DeserializeM ScalarPtr :=
  return ⟨← deTag, ← deF⟩

def dePtrExprPair : DeserializeM $ ScalarPtr × ScalarExpr := do
  let ptr ← dePtr
  let expr : ScalarExpr ← match ptr.tag with
  | .nil
  | .sym     => pure $ .sym (← dePtr)
  | .cons    => pure $ .cons (← dePtr) (← dePtr)
  | .fun     => pure $ .fun (← dePtr) (← dePtr) (← dePtr)
  | .num     => pure $ .num (← deF)
  | .thunk   => throw "TODO"
  | .str     => pure $ .str (← dePtr)
  | .strCons => pure $ .strCons (← dePtr) (← dePtr)
  | .strNil  => pure .strNil
  | .char    => pure $ .char (← deF)
  | .comm    => pure $ .comm (← deF) (← dePtr)
  return (ptr, expr)

def deStore : DeserializeM ScalarStore := do
  let mut store := default
  let nExprs := (← deF).val
  for _ in [0 : nExprs] do
    let (ptr, expr) ← dePtrExprPair
    store := { store with exprs := store.exprs.insert ptr expr }
  let nComms := (← deF).val
  for _ in [0 : nComms] do
    store := { store with comms := store.comms.insert (← deF) (← dePtr) }
  return store

def deRoots : DeserializeM $ List ScalarPtr := do
  let nRoots := (← deF).val
  let mut roots := #[]
  for _ in [0 : nRoots] do
    roots := roots.push (← dePtr)
  return roots.data

def deserializeM : DeserializeM $ (List ScalarPtr) × ScalarStore :=
  return (← deRoots, ← deStore)

def deserialize (bytes : ByteArray) :
    Except String ((List ScalarPtr) × ScalarStore) :=
  (StateT.run (ReaderT.run deserializeM ⟨bytes, bytes.size, by eq_refl⟩) 0).1

end Lurk.SerDe
