import Lurk.Hashing.Datatypes
import YatimaStdLib.Nat
import YatimaStdLib.ByteArray

namespace Lurk.SerDe

open Lurk.Hashing

abbrev FArray := Array F


-- structure SerializeState where
--   bytes : FArray
--   cache : Std.RBMap F FArray compare
--   deriving Inhabited

-- abbrev SerializeM := ReaderT ScalarStore $ StateM SerializeState

-- def serializePtr (ptr : ScalarPtr) : SerializeM Unit := sorry

-- def serializeIter : SerializeM Unit := sorry

-- def serialize (ptr : ScalarPtr) (store : ScalarStore) : FArray :=
--   (StateT.run (ReaderT.run serializeIter store) default).2.bytes

structure SerializeContext where
  store : ScalarStore
  visit : Std.RBSet ScalarPtr compare
  deriving Inhabited

abbrev SerializeM := ReaderT SerializeContext $ ExceptT String $
  StateM FArray

def withVisiting (ptr : ScalarPtr) : SerializeM α → SerializeM α :=
  withReader fun ctx => { ctx with visit := ctx.visit.insert ptr }

def serializePtr (ptr : ScalarPtr) : SerializeM Unit := sorry

def serialize (ptr : ScalarPtr) (store : ScalarStore) : Except String FArray :=
  match StateT.run (ReaderT.run (serializePtr ptr) ⟨store, default⟩) default with
  | (.error e, _) => .error e
  | (.ok _,  arr) => .ok arr

end Lurk.SerDe
