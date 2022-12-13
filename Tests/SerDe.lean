import LSpec
import Lurk.Frontend.DSL
import Lurk.Hashing.Encoding
import Lurk.SerDe.Serialize
import Lurk.SerDe.Deserialize

open Lurk

open Frontend.DSL in def ast := ⟦
  (begin
    nil
    t
    current-env
    ()
    (nil)
    (t)
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
    ((+ 1 2) (f x) . (cons 4 2)))
⟧

open LSpec SerDe in
def main := do
  let (root, store) := ast.encode
  let roots := [root]
  let bytes := serialize roots store
  lspecIO $
    withExceptOk "Deserialization succeeds" (deserialize bytes)
      fun (roots', store') =>
        test "Roots match" (roots == roots') ++
        test "Stores match" (store == store')
