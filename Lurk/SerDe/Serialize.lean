import Lurk.Hashing.Datatypes

namespace Lurk.SerDe

open Lurk.Hashing

structure SerializeState where
  bytes : ByteArray
  cache : Std.RBMap F ByteArray compare
  deriving Inhabited

abbrev SerializeM := ReaderT ScalarStore $ StateM SerializeState

def serF (n : F) : SerializeM Unit := do
  match (← get).cache.find? n with
  | some bytes => modify fun stt => { stt with bytes := stt.bytes ++ bytes }
  | none =>
    let bytes := n.toBytes -- this can be a bottleneck so we cache it
    modify fun stt => { stt with
      bytes := stt.bytes ++ bytes
      cache := stt.cache.insert n bytes }

def serPtr (ptr : ScalarPtr) : SerializeM Unit := do
  serF ptr.tag.toF
  serF ptr.val

def serExpr : ScalarExpr → SerializeM Unit
  | .cons car cdr => do serPtr car; serPtr cdr
  | .comm n ptr => do serF n; serPtr ptr
  | .sym ptr => serPtr ptr
  | .fun arg body env => do serPtr arg; serPtr body; serPtr env
  | .num n => serF n
  | .strNil => serPtr ⟨.str, F.zero⟩
  | .strCons head tail => do serPtr head; serPtr tail
  | .char c => serF c

def serStore : SerializeM Unit := do
  let store ← read
  serF $ .ofNat store.exprs.size
  store.exprs.forM fun ptr expr => do serPtr ptr; serExpr expr

def serializeM (roots : List ScalarPtr) : SerializeM Unit := do
  serF $ .ofNat roots.length
  roots.sort.forM serPtr
  serStore

def serialize (roots : List ScalarPtr) (store : ScalarStore) : ByteArray :=
  (StateT.run (ReaderT.run (serializeM roots) store) default).2.bytes

end Lurk.SerDe
