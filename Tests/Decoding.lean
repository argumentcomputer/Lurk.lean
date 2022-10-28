import LSpec
import Lurk.Syntax.DSL
import Lurk.Syntax.Printing
import Lurk.Hashing.Decoding

open Lurk

open Syntax.DSL Syntax.SExpr.DSL in
def expressions := [
  ⟦nil⟧,
  ⟦t⟧,
  ⟦current-env⟧,
  ⟦()⟧,
  ⟦(nil)⟧,
  ⟦(t)⟧,
  ⟦(current-env)⟧,
  ⟦(nil t)⟧,
  ⟦(t nil)⟧,
  ⟦(current-env t nil)⟧,
  ⟦(f)⟧,
  ⟦(f a)⟧,
  ⟦(f 1 q)⟧,
  ⟦(/ (- (+ 1 2) a) (* 4 3))⟧,
  ⟦(begin)⟧,
  ⟦(begin 1)⟧,
  ⟦(begin nil)⟧,
  ⟦(begin 1 2 3)⟧,
  .hide (.sym `a) (.sym `b),
  ⟦(lambda (a b c) (begin (cons a b) c))⟧,
  ⟦(let ((a 1) (b c)) (+ a b))⟧,
  ⟦(quote 1)⟧,
  ⟦(quote x)⟧,
  ⟦(quote (nil))⟧,
  ⟦(quote (nil 1))⟧,
  ⟦(quote (nil . 1))⟧,
  ⟦(quote ((nil . 1) x))⟧
]

open LSpec in
def main := do
  lspecIO $ expressions.foldl (init := .done)
    fun tSeq (e : Syntax.Expr) =>
      let e := e.toUpper
      let (ptr, store) := e.encode
      withExceptOk s!"Decoding {e.pprint true false} succeeds"
          (Lurk.Hashing.decode ptr store) fun e' =>
        tSeq ++ test
          s!"Expected {e.pprint true false} equals {e'.pprint true false}" (e == e')
