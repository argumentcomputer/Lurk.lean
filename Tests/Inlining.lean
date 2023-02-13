import LSpec
import Lurk.Backend.DSL
import Lurk.Backend.ExprUtils

open Lurk Backend DSL

abbrev Test := Expr × Expr

def inlinesOnBody : Test :=
  (⟦(let ((a 1)) a)⟧, ⟦1⟧)

def inlinesOnBinding : Test :=
  (⟦(let ((a 1) (b a)) c)⟧, ⟦(let ((b 1)) c)⟧)

def inlinesOnBodyWithProperCounting : Test :=
  (⟦(let ((a 1)) (+ a a))⟧, ⟦(let ((a 1)) (+ a a))⟧)

def inlinesOnBindingWithProperCounting : Test :=
  (⟦(let ((a 1) (b (+ a a))) c)⟧, ⟦(let ((a 1) (b (+ a a))) c)⟧)

def inlinesTransitively : Test :=
  (⟦(let ((a 1) (b a)) b)⟧, ⟦1⟧)

def inlinesAfterDeclaration : Test :=
  (⟦(let ((x a) (a 1) (b a)) c)⟧, ⟦(let ((x a) (b 1)) c)⟧)

def inlinesTransitivelyAfterDeclaration : Test :=
  (⟦(let ((x a) (a 1) (b a)) b)⟧, ⟦(let ((x a)) 1)⟧)

def inlinesFreeVarsOnly : Test :=
  (⟦(let ((a 1) (b (lambda (a) a))) (b a))⟧, ⟦((lambda (a) a) 1)⟧)

def cases := [
  inlinesOnBody,
  inlinesOnBinding,
  inlinesOnBodyWithProperCounting,
  inlinesOnBindingWithProperCounting,
  inlinesTransitively,
  inlinesAfterDeclaration,
  inlinesTransitivelyAfterDeclaration,
  inlinesFreeVarsOnly
]

open LSpec

def main := lspecIO $
  cases.foldl (init := .done) fun tSeq (inp, out) =>
    tSeq ++ test s!"inlines {inp} correctly ({inp.inlineBinder})" (inp.inlineBinder == out)

#eval main