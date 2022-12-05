import LSpec
import Lurk.Syntax.DSL
import Lurk.Evaluation.FromAST
import Lurk.Evaluation.Eval

open Lurk Syntax Evaluation DSL

def prog := ⟦
(LETREC
 ((|getelem| (LAMBDA (|xs| |n|) (IF (= |n| 0) (CAR |xs|) (|getelem| (CDR |xs|) (- |n| 1)))))
  (|drop| (LAMBDA (|n| |xs|) (IF (= |n| 0) |xs| (IF |xs| (|drop| (- |n| 1) (CDR |xs|)) |xs|))))
  (|str_mk| (LAMBDA (|cs|) (IF |cs| (STRCONS (CAR |cs|) (|str_mk| (CDR |cs|))) "")))
  (|str_data| (LAMBDA (|s|) (IF (EQ |s| "") NIL (CONS (CAR |s|) (|str_data| (CDR |s|))))))
  (|str_append| (LAMBDA (|xs| |ys|) (IF (EQ "" |xs|) |ys| (STRCONS (CAR |xs|) (|str_append| (CDR |xs|) |ys|)))))
  (|Nat.add| (LAMBDA (|a| |b|) (+ |a| |b|)))
  (|List| (LAMBDA (|α|) (QUOTE ("List" 1 0))))
  (|List.nil| (LAMBDA (|α|) (CONS "List" (CONS 0 (CONS |α| NIL)))))
  (|List.cons| (LAMBDA (|α| |head| |tail|) (CONS "List" (CONS 1 (CONS |α| (CONS |head| (CONS |tail| NIL)))))))
  (|list|
   (LET
    ((|_x.1| 1))
    (LET
     ((|_x.4| 2))
     (LET
      ((|_x.7| 3))
      (LET
       ((|_x.10| 4))
       (LET
        ((|_x.13| 5))
        (LET
         ((|_x.16| 6))
         (LET
          ((|_x.19| (|List.nil| "lcErasedType")))
          (LET
           ((|_x.20| (|List.cons| "lcErasedType" |_x.16| |_x.19|)))
           (LET
            ((|_x.21| (|List.cons| "lcErasedType" |_x.13| |_x.20|)))
            (LET
             ((|_x.22| (|List.cons| "lcErasedType" |_x.10| |_x.21|)))
             (LET
              ((|_x.23| (|List.cons| "lcErasedType" |_x.7| |_x.22|)))
              (LET
               ((|_x.24| (|List.cons| "lcErasedType" |_x.4| |_x.23|)))
               (LET ((|_x.25| (|List.cons| "lcErasedType" |_x.1| |_x.24|))) |_x.25|))))))))))))))
  (|List.map|
   (LAMBDA
    (|α| |β| |f| |x.56|)
    (LET
     ((|_lurk_idx| (|getelem| |x.56| 1)) (|_lurk_args| (|drop| 3 |x.56|)))
     (IF
      (= |_lurk_idx| 0)
      (LET ((|_x.118| (|List.nil| "lcErasedType"))) |_x.118|)
      (IF
       (= |_lurk_idx| 1)
       (LET
        ((|head.67| (|getelem| |_lurk_args| 0)) (|tail.68| (|getelem| |_lurk_args| 1)))
        (LET
         ((|_x.119| (|f| |head.67|)))
         (LET
          ((|_x.120| (|List.map| "lcErasedType" "lcErasedType" |f| |tail.68|)))
          (LET ((|_x.121| (|List.cons| "lcErasedType" |_x.119| |_x.120|))) |_x.121|))))
       NIL)))))
  (|listMap|
   (LET
    ((|_f.33| (LAMBDA (|x|) (LET ((|_x.29| 1)) (LET ((|_x.114| (|Nat.add| |x| |_x.29|))) |_x.114|)))))
    (LET ((|_x.34| |list|)) (LET ((|_x.35| (|List.map| "lcErasedType" "lcErasedType" |_f.33| |_x.34|))) |_x.35|)))))
 |listMap|)
⟧

def progExpected := 
  "(letrec ((|getelem| (lambda (|n| |xs|) (if (= |n| 0) (CAR |xs|) (|getelem| (- |n| 1) (CDR |xs|)))))\n" ++
  "         (|drop| (lambda (|xs| |n|) (if (= |n| 0) |xs| (if |xs| (|drop| (CDR |xs|) (- |n| 1)) |xs|))))\n" ++
  "         (|str_mk| (lambda (|cs|) (if |cs| (STRCONS (CAR |cs|) (|str_mk| (CDR |cs|))) \"\")))\n" ++
  "         (|str_data| (lambda (|s|) (if (eq |s| \"\") NIL (CONS (CAR |s|) (|str_data| (CDR |s|))))))\n" ++
  "         (|str_append| (lambda (|ys| |xs|) (if (eq \"\" |xs|) |ys| (STRCONS (CAR |xs|) (|str_append| |ys| (CDR |xs|))))))\n" ++
  "         (|Nat.add| (lambda (|b| |a|) (+ |a| |b|)))\n" ++
  "         (|List| (lambda (|α|) (quote (\"List\" 1 0))))\n" ++
  "         (|List.nil| (lambda (|α|) (CONS \"List\" (CONS 0 (CONS |α| NIL)))))\n" ++
  "         (|List.cons| (lambda (|tail| |head| |α|) (CONS \"List\" (CONS 1 (CONS |α| (CONS |head| (CONS |tail| NIL)))))))\n" ++
  "         (|list|\n" ++
  "            (let ((|_x.1| 1)\n" ++
  "                  (|_x.4| 2)\n" ++
  "                  (|_x.7| 3)\n" ++
  "                  (|_x.10| 4)\n" ++
  "                  (|_x.13| 5)\n" ++
  "                  (|_x.16| 6)\n" ++
  "                  (|_x.19| (|List.nil| \"lcErasedType\"))\n" ++
  "                  (|_x.20| (|List.cons| |_x.19| |_x.16| \"lcErasedType\"))\n" ++
  "                  (|_x.21| (|List.cons| |_x.20| |_x.13| \"lcErasedType\"))\n" ++
  "                  (|_x.22| (|List.cons| |_x.21| |_x.10| \"lcErasedType\"))\n" ++
  "                  (|_x.23| (|List.cons| |_x.22| |_x.7| \"lcErasedType\"))\n" ++
  "                  (|_x.24| (|List.cons| |_x.23| |_x.4| \"lcErasedType\"))\n" ++
  "                  (|_x.25| (|List.cons| |_x.24| |_x.1| \"lcErasedType\")))\n" ++
  "               |_x.25|))\n" ++
  "         (|List.map|\n" ++
  "            (lambda (|x.56| |f| |β| |α|)\n" ++
  "               (let ((|_lurk_idx| (|getelem| 1 |x.56|)) (|_lurk_args| (|drop| |x.56| 3)))\n" ++
  "                  (if (= |_lurk_idx| 0)\n" ++
  "                     (let ((|_x.118| (|List.nil| \"lcErasedType\"))) |_x.118|)\n" ++
  "                     (if (= |_lurk_idx| 1)\n" ++
  "                        (let ((|head.67| (|getelem| 0 |_lurk_args|))\n" ++
  "                              (|tail.68| (|getelem| 1 |_lurk_args|))\n" ++
  "                              (|_x.119| (|f| |head.67|))\n" ++
  "                              (|_x.120| (|List.map| |tail.68| |f| \"lcErasedType\" \"lcErasedType\"))\n" ++
  "                              (|_x.121| (|List.cons| |_x.120| |_x.119| \"lcErasedType\")))\n" ++
  "                           |_x.121|)\n" ++
  "                        NIL)))))\n" ++
  "         (|listMap|\n" ++
  "            (let ((|_f.33| (lambda (|x|) (let ((|_x.29| 1) (|_x.114| (|Nat.add| |_x.29| |x|))) |_x.114|)))\n" ++
  "                  (|_x.34| |list|)\n" ++
  "                  (|_x.35| (|List.map| |_x.34| |_f.33| \"lcErasedType\" \"lcErasedType\")))\n" ++
  "               |_x.35|)))\n" ++
  "   |listMap|)"

def tests : List (AST × String) := [(prog, progExpected)]

open LSpec in
def main := lspecIO $
  tests.foldl (init := .done) fun tSeq (ast, expected) =>
      tSeq ++ withExceptOk s!"{ast} converts to expression" ast.toExpr fun e =>
        test s!"{e.toString true}\nprints to\n{expected}" (e.toString true == expected)