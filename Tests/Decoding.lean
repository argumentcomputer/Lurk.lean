import LSpec
import Lurk.Syntax2.DSL
import Lurk.Syntax.Printing
import Lurk.Hashing2.Decoding

open Lurk

open Syntax.DSL in
def asts := [
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
  ⟦(hide a b)⟧,
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
  lspecIO $ asts.foldl (init := .done)
    fun tSeq (x : Lurk.Syntax.AST) =>
      let (ptr, store) := x.hash
      withExceptOk "Decoding {e.pprint true false} succeeds"
          (Lurk.Hashing.decode ptr store) fun x' =>
        tSeq ++ test
          "Expected {repr x} equals {repr x'}" (x == x')
#eval main