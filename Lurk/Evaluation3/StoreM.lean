import Lurk.Evaluation3.Datatypes

namespace Lurk.Evaluation
open Lean

abbrev StoreM := EStateM String Store

def numStore.insert (n : F) : StoreM (Ptr × Bool) :=
  modifyGet fun stt => sorry

end Lurk.Evaluation