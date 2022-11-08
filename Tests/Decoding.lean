import LSpec
import Lurk.Syntax.DSL
import Lurk.Hashing.Encoding
import Lurk.Hashing.Decoding

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
  ⟦(f "abc" . q)⟧,
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
  ⟦(quote ((nil . 1) x))⟧,
  ⟦((+ 1 2) (f x) . (cons 4 2))⟧
]

open LSpec in
def main := do
  lspecIO $ asts.foldl (init := .done)
    fun tSeq (x : Lurk.Syntax.AST) =>
      let (ptr, store) := x.encode
      withExceptOk s!"Decoding {x} succeeds"
          (Lurk.Hashing.decode ptr store) fun x' =>
        tSeq ++ test
          s!"Expected {x} equals {x'}" (x == x')
