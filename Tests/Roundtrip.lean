import LSpec
import Lurk.ExprDSL
import Lurk.Scalar

open Lurk

open DSL in
def exprs := [
  ⟦nil⟧,
  ⟦t⟧,
  ⟦(current-env)⟧,
  ⟦()⟧,
  ⟦(nil)⟧,
  ⟦(t)⟧,
  ⟦(current-env)⟧,
  ⟦(nil t)⟧,
  ⟦(t nil)⟧,
  ⟦((current-env) t nil)⟧,
  ⟦(f)⟧,
  ⟦(f a)⟧,
  ⟦(f 1 q)⟧,
  ⟦(/ (- (+ 1 2) a) (* 4 3))⟧,
  ⟦(begin)⟧,
  ⟦(begin 1)⟧,
  ⟦(begin nil)⟧,
  ⟦(begin 1 2 3)⟧,
  ⟦(hide a b)⟧,
  ⟦(lambda (a b c) (begin (cons a b) c))⟧,
  ⟦(let ((a 1) (b c)) (+ a b))⟧,
  ⟦(quote 1)⟧,
  ⟦(quote x)⟧,
  ⟦(quote (nil))⟧,
  ⟦(quote (nil 1))⟧,
  ⟦(quote (1 . 1))⟧,
  ⟦(quote ((1 . 1) x))⟧,
  ⟦((+ 1 2) (f x) (cons 4 2))⟧
]

open LSpec in
def main :=
  lspecIO $ exprs.foldl (init := .done)
    fun tSeq (e : Expr) =>
      let ldon := e.toLDON
      let (comm, stt) := ldon.commit default
      withExceptOk s!"Openning {comm.asHex} succeeds" (stt.store.open comm) fun ldon' =>
        withExceptOk s!"Converting {ldon'} back to Expr succeeds" ldon'.toExpr fun e' =>
          tSeq ++ test s!"===\n{repr e}\n--\n{repr e'}\n== roundtrips" (e == e')
