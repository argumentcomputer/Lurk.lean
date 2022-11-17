import LSpec
import Lurk.Syntax.DSL
import Lurk.Evaluation.FromAST
import Lurk.Evaluation.Eval

open Lurk Syntax Evaluation DSL

abbrev Test := Value × AST

def stringAppend : Test := ("abcdefg", ⟦
(LETREC
 ((|getelem| (LAMBDA (|xs| |n|) (IF (= |n| 0) (CAR |xs|) (|getelem| (CDR |xs|) (- |n| 1)))))
  (|lurk_string_mk| (LAMBDA (|cs|) (IF |cs| (STRCONS (CAR |cs|) (|lurk_string_mk| (CDR |cs|))) "")))
  (|lurk_string_data| (LAMBDA (|s|) (IF (EQ |s| "") NIL (CONS (CAR |s|) (|lurk_string_data| (CDR |s|))))))
  (|HAppend.hAppend| (LAMBDA (|α| |β| |γ| |self|) (|getelem| (|getelem| (CDR (CDR |self|)) 2) 0)))
  (|String| (QUOTE (|String| 0 0)))
  (|HAppend| (LAMBDA (|α| |β| |γ|) (QUOTE (|HAppend| 3 0))))
  (|HAppend.mk|
   (LAMBDA
    (|α| |β| |γ| |hAppend|)
    (CONS
     (QUOTE (|HAppend| 3 0))
     (CONS 0 (CONS (CONS |α| (CONS |β| (CONS |γ| NIL))) (CONS NIL (CONS (CONS |hAppend| NIL) NIL)))))))
  (|HAppend.rec|
   (LAMBDA
    (|α| |β| |γ| |motive| |mk| |t|)
    (IF
     (= (CAR (CDR |t|)) 0)
     (LET
      ((|_lurk_ctor_args| (|getelem| (CDR (CDR |t|)) 2)) (|hAppend| (|getelem| |_lurk_ctor_args| 0)))
      (|mk| |hAppend|))
     NIL)))
  (|Append.append| (LAMBDA (|α| |self|) (|getelem| (|getelem| (CDR (CDR |self|)) 2) 0)))
  (|instHAppend|
   (LAMBDA (|α| |_hyg_.1|) (|HAppend.mk| |α| |α| |α| (LAMBDA (|a| |b|) (|Append.append| |α| |_hyg_.1| |a| |b|)))))
  (|Append| (LAMBDA (|α|) (QUOTE (|Append| 1 0))))
  (|Append.mk|
   (LAMBDA
    (|α| |append|)
    (CONS (QUOTE (|Append| 1 0)) (CONS 0 (CONS (CONS |α| NIL) (CONS NIL (CONS (CONS |append| NIL) NIL)))))))
  (|Append.rec|
   (LAMBDA
    (|α| |motive| |mk| |t|)
    (IF
     (= (CAR (CDR |t|)) 0)
     (LET
      ((|_lurk_ctor_args| (|getelem| (CDR (CDR |t|)) 2)) (|append| (|getelem| |_lurk_ctor_args| 0)))
      (|mk| |append|))
     NIL)))
  (|String.rec| (LAMBDA (|motive| |mk| |_t|) (|mk| (|lurk_string_data| |_t|))))
  (|String.casesOn| (LAMBDA (|motive| |t| |mk|) (|String.rec| |motive| (LAMBDA (|data|) (|mk| |data|)) |t|)))
  (|String.mk| (LAMBDA (|data|) (|lurk_string_mk| |data|)))
  (|String.append.match_1|
   (LAMBDA
    (|motive| |_hyg_.4| |_hyg_.5| |h_1|)
    (|String.casesOn|
     (LAMBDA (|x|) (|motive| |x| |_hyg_.5|))
     |_hyg_.4|
     (LAMBDA
      (|_hyg_.6|)
      (|String.casesOn|
       (LAMBDA (|x|) (|motive| (|String.mk| |_hyg_.6|) |x|))
       |_hyg_.5|
       (LAMBDA (|_hyg_.7|) (|h_1| |_hyg_.6| |_hyg_.7|)))))))
  (|List| (LAMBDA (|_lurk_1|) (QUOTE (|List| 1 0))))
  (|Char| (QUOTE (CHAR 0 0)))
  (|List.rec|
   (LAMBDA
    (|_lurk_1| |motive| |_nil| |_cons| |_t|)
    (IF |_t| (|_cons| (CAR |_t|) (CDR |_t|) (|List.rec| |_lurk_1| |motive| |_nil| |_cons| (CDR |_t|))) |_nil|)))
  (|PProd| (LAMBDA (|α| |β|) (QUOTE (|PProd| 2 0))))
  (|PProd.mk|
   (LAMBDA
    (|α| |β| |fst| |snd|)
    (CONS
     (QUOTE (|PProd| 2 0))
     (CONS 0 (CONS (CONS |α| (CONS |β| NIL)) (CONS NIL (CONS (CONS |fst| (CONS |snd| NIL)) NIL)))))))
  (|PProd.rec|
   (LAMBDA
    (|α| |β| |motive| |mk| |t|)
    (IF
     (= (CAR (CDR |t|)) 0)
     (LET
      ((|_lurk_ctor_args| (|getelem| (CDR (CDR |t|)) 2))
       (|fst| (|getelem| |_lurk_ctor_args| 0))
       (|snd| (|getelem| |_lurk_ctor_args| 1)))
      (|mk| |fst| |snd|))
     NIL)))
  (|PUnit| (QUOTE (|PUnit| 0 0)))
  (|PUnit.unit| (CONS (QUOTE (|PUnit| 0 0)) (CONS 0 NIL)))
  (|PUnit.rec|
   (LAMBDA
    (|motive| |unit| |t|)
    (IF (= (CAR (CDR |t|)) 0) (LET ((|_lurk_ctor_args| (|getelem| (CDR (CDR |t|)) 2))) |unit|) NIL)))
  (|List.below|
   (LAMBDA
    (|α| |motive| |t|)
    (|List.rec|
     |α|
     (LAMBDA (|t|) NIL)
     |PUnit|
     (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| (|motive| |tail|) |tail_ih|) |PUnit|))
     |t|)))
  (|List.nil| (LAMBDA (|_lurk_1|) NIL))
  (|List.cons| (LAMBDA (|_lurk_1| |head| |tail|) (CONS |head| |tail|)))
  (|List.brecOn|
   (LAMBDA
    (|α| |motive| |t| |F_1|)
    (|getelem|
     (|getelem|
      (CDR
       (CDR
        (|List.rec|
         |α|
         (LAMBDA (|t|) (|PProd| (|motive| |t|) (|List.below| |α| |motive| |t|)))
         (|PProd.mk| (|motive| (|List.nil| |α|)) |PUnit| (|F_1| (|List.nil| |α|) |PUnit.unit|) |PUnit.unit|)
         (LAMBDA
          (|head| |tail| |tail_ih|)
          (|PProd.mk|
           (|motive| (|List.cons| |α| |head| |tail|))
           (|PProd| (|PProd| (|motive| |tail|) (|List.below| |α| |motive| |tail|)) |PUnit|)
           (|F_1|
            (|List.cons| |α| |head| |tail|)
            (|PProd.mk| (|PProd| (|motive| |tail|) (|List.below| |α| |motive| |tail|)) |PUnit| |tail_ih| |PUnit.unit|))
           (|PProd.mk| (|PProd| (|motive| |tail|) (|List.below| |α| |motive| |tail|)) |PUnit| |tail_ih| |PUnit.unit|)))
         |t|)))
      2)
     0)))
  (|List.casesOn|
   (LAMBDA
    (|α| |motive| |t| |nil| |cons|)
    (|List.rec| |α| |motive| |nil| (LAMBDA (|head| |tail| |tail_ih|) (|cons| |head| |tail|)) |t|)))
  (|List.reverseAux.match_1|
   (LAMBDA
    (|α| |motive| |_hyg_.10| |_hyg_.11| |h_1| |h_2|)
    (|List.casesOn|
     |α|
     (LAMBDA (|x|) (|motive| |x| |_hyg_.11|))
     |_hyg_.10|
     (|h_1| |_hyg_.11|)
     (LAMBDA (|_hyg_.12| |_hyg_.13|) (|h_2| |_hyg_.12| |_hyg_.13| |_hyg_.11|)))))
  (|PProd.fst| (LAMBDA (|α| |β| |self|) (|getelem| (|getelem| (CDR (CDR |self|)) 2) 0)))
  (|List.append|
   (LAMBDA
    (|α| |_hyg_.8| |_hyg_.9|)
    (|List.brecOn|
     |α|
     (LAMBDA (|_hyg_.8|) NIL)
     |_hyg_.8|
     (LAMBDA
      (|_hyg_.8| |f| |_hyg_.9|)
      (|List.reverseAux.match_1|
       |α|
       (LAMBDA (|_hyg_.14| |_hyg_.15|) NIL)
       |_hyg_.8|
       |_hyg_.9|
       (LAMBDA (|r| |_hyg_.16|) |r|)
       (LAMBDA
        (|a| |l| |r| |_hyg_.16|)
        (|List.cons|
         |α|
         |a|
         (|PProd.fst|
          ((LAMBDA (|_hyg_.8|) NIL) |l|)
          (|List.rec|
           |α|
           (LAMBDA (|t|) NIL)
           |PUnit|
           (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| ((LAMBDA (|_hyg_.8|) NIL) |tail|) |tail_ih|) |PUnit|))
           |l|)
          (|PProd.fst|
           (|PProd|
            ((LAMBDA (|_hyg_.8|) NIL) |l|)
            (|List.rec|
             |α|
             (LAMBDA (|t|) NIL)
             |PUnit|
             (LAMBDA (|head| |tail| |tail_ih|) (|PProd| (|PProd| ((LAMBDA (|_hyg_.8|) NIL) |tail|) |tail_ih|) |PUnit|))
             |l|))
           |PUnit|
           |_hyg_.16|)
          |r|)))
       |f|))
     |_hyg_.9|)))
  (|List.instAppendList| (LAMBDA (|α|) (|Append.mk| (|List| |α|) (|List.append| |α|))))
  (|String.append|
   (LAMBDA
    (|_hyg_.2| |_hyg_.3|)
    (|String.append.match_1|
     (LAMBDA (|_hyg_.4| |_hyg_.5|) |String|)
     |_hyg_.2|
     |_hyg_.3|
     (LAMBDA
      (|a| |b|)
      (|String.mk|
       (|HAppend.hAppend|
        (|List| |Char|)
        (|List| |Char|)
        (|List| |Char|)
        (|instHAppend| (|List| |Char|) (|List.instAppendList| |Char|))
        |a|
        |b|))))))
  (|String.instAppendString| (|Append.mk| |String| |String.append|))
  (|abcd| "abcd")
  (|efg| "efg")
  (|stringAppend|
   (|HAppend.hAppend| |String| |String| |String| (|instHAppend| |String| |String.instAppendString|) |abcd| |efg|)))
 |stringAppend|)
⟧)

def pairs : List Test := [
  -- stringAppend
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq pair =>
    let (expect, ast) := (pair : Test)
    tSeq ++ withExceptOk "Converts to expression" (AST.toExpr ast) fun e =>
      withExceptOk "Evaluation succeeds" e.eval
        fun res => test s!"Resulting {res} equals {expect}" (res == expect)
