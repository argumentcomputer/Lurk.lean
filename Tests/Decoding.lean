import LSpec
import Lurk.Syntax.DSL
import Lurk.Syntax.Printing
import Lurk.Hashing.StoreDSL
import Lurk.Hashing.Decoding

open Lurk

open Syntax.DSL Syntax.SExpr.DSL in
def expressions := [
  -- ⟦nil⟧,
  -- ⟦t⟧,
  -- ⟦current-env⟧,
  -- ⟦()⟧,
  ⟦(nil)⟧
  -- ⟦(current-env)⟧,
  -- ⟦(/ (- (+ 1 2) a) (* 4 3))⟧,
  -- ⟦(begin)⟧,
  -- .hide (.sym `a) (.sym `b),
  -- ⟦(lambda (a b c) (begin (cons a b) c))⟧
]

open LSpec in
def main := do
  lspecIO $ expressions.foldl (init := .done)
    fun tSeq (e : Syntax.Expr) =>
      let e := e.toUpper
      let (ptr, store) := e.hash
      -- dbg_trace ptr
      -- dbg_trace "------------------"
      -- dbg_trace store
      withExceptOk s!"Decoding {e.pprint true false} succeeds"
          (Lurk.Hashing.decode ptr store) fun e' =>
        tSeq ++ test
          s!"Expected {e.pprint true false} equals resulting {e'.pprint true false}" (e == e')
