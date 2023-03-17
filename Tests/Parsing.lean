import LSpec
import Lurk.Parser
import Lurk.ExprDSL

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

open Lurk.DSL in def expectedAST := ⟦
  (begin
    nil
    t
    (current-env)
    nilbutsym
    ,(2 . 1)
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
  withExceptOk "Parsing succeeds" (Lurk.Parser.parse code)
    fun resultingAST => 
      test "Parsed correctly" (resultingAST == expectedAST)
