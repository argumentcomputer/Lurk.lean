import LSpec
import Lurk.Syntax.Parser
import Lurk.Syntax.DSL

def code := "(begin
    nil
    t
    current-env
    nilbutsym
    (nil.1)
    ()
    (   )
    (nil)
    (t)
    |te._sting|
    (current-env  )
    (nil t)
    (lambda    (x y)     (+ x y))
    (cons 1 2)

    (strcons a b)
    (  f)
    (g x y)
    (let (
        (n1 nil    )   
        (n2 (quote (nil)))
        (n3 (   begin)))
      (current-env))
    (quote    nil)
    (quote 1   \t  )
    (quote (1 2 3)\t)
    (('1) . ' (cons 2 3))
    ((+ 1 2) (f x)  .    (cons 4 2)))"

open Lurk.Syntax.DSL in def expectedAST := ⟦
  (begin
    nil
    t
    current-env
    nilbutsym
    (nil . 1)
    ()
    ()
    (nil)
    (t)
    |te._sting|
    (current-env)
    (nil t)
    (lambda (x y) (+ x y))
    (cons 1 2)
    (strcons a b)
    (f)
    (g x y)
    (let (
        (n1 nil)
        (n2 (quote (nil)))
        (n3 (begin)))
      (current-env))
    (quote nil)
    (quote 1)
    (quote (1 2 3))
    ((,1) . , (cons 2 3))
    ((+ 1 2) (f x) . (cons 4 2)))
⟧

open LSpec in
def main := lspecIO $
  withExceptOk "Parsing succeeds" (Lurk.Syntax.parse code)
    fun resultingAST => test "Parsed correctly" (resultingAST == expectedAST)
