import LSpec
import Lurk.DSL
import Lurk.Hashing.Scalar

def got := ⟦(cons (+ 1 (* 3 4)) "aa")⟧.hash.1.exprs

open Lurk

def expected : Std.RBMap ScalarPtr ScalarExpr compare := .ofList [
  (⟨Tag.num, .ofNat 1⟩, .num (.ofNat 1)),
  (⟨Tag.num, .ofNat 3⟩, .num (.ofNat 3)),
  (⟨Tag.num, .ofNat 4⟩, .num (.ofNat 4))
]

open LSpec in
def main := do
  -- this should be replaced by a complete equality of RBMaps
  let tSeq : TestSeq := expected.fold (init := .done) fun tSeq ptr expectedExpr =>
    withOptionSome s!"{repr ptr} is found" (got.find? ptr) fun gotExpr =>
      tSeq ++ test s!"Expected ({repr expectedExpr}) equals resulting expression ({repr gotExpr})"
          (expectedExpr == gotExpr)
  lspecIO tSeq
