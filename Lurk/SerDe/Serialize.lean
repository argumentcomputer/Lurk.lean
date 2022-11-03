import Lurk.Hashing.Datatypes
import YatimaStdLib.Nat
import YatimaStdLib.ByteArray

namespace Lurk.SerDe

open Lurk.Hashing

structure SerializeState where
  bytes : ByteArray
  cache : Std.RBMap F ByteArray compare
  deriving Inhabited

abbrev SerializeM := ReaderT ScalarStore $ StateM SerializeState

def writeF (n : F) : SerializeM Unit := do
  match (← get).cache.find? n with
  | some bytes => modify fun stt => { stt with bytes := stt.bytes ++ bytes }
  | none =>
    let bytes := n.toBytes -- this can be a bottleneck so we cache it
    modify fun stt => { stt with
      bytes := stt.bytes ++ bytes
      cache := stt.cache.insert n bytes }

def writePtr (ptr : ScalarPtr) : SerializeM Unit := do
  modify fun stt => { stt with bytes := stt.bytes.push (.ofNat ptr.tag.toNat) }
  writeF ptr.val

def writeExpr : ScalarExpr → SerializeM Unit
  | .cons car cdr => do writePtr car; writePtr cdr
  | .comm n ptr => do writeF n; writePtr ptr
  | .sym ptr => writePtr ptr
  | .fun arg body env => do writePtr arg; writePtr body; writePtr env
  | .num n => writeF n
  | .strNil => writePtr ⟨.str, F.zero⟩
  | .strCons head tail => do writePtr head; writePtr tail
  | .char c => writeF c

def writeStore : SerializeM Unit := do
  let store ← read
  -- writing expressions
  writeF $ .ofNat store.exprs.size
  store.exprs.forM fun ptr expr => do writePtr ptr; writeExpr expr
  -- writing comms
  writeF $ .ofNat store.comms.size
  store.comms.forM fun n ptr => do writeF n; writePtr ptr

def serializeM (roots : List ScalarPtr) : SerializeM Unit := do
  writeF $ .ofNat roots.length
  roots.sort.forM writePtr
  writeStore

def serialize (roots : List ScalarPtr) (store : ScalarStore) : ByteArray :=
  (StateT.run (ReaderT.run (serializeM roots) store) default).2.bytes

end Lurk.SerDe
