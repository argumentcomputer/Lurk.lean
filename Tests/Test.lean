import LSpec
import Lurk.Backend.DSL
import Lurk.Backend.Eval
import Lurk.Backend.ExprUtils

open Lurk.Backend DSL

def prog := ⟦
(LETREC ((lneq (LAMBDA (x y) (IF (EQ x y) NIL T)))
         (List_nil (LAMBDA (x) NIL))
         (List_cons (LAMBDA (x head tail) (CONS head tail)))
         (list
            (LET ((_uniq_7 (List_nil "lcErased"))
                  (_uniq_8 (List_cons "lcErased" 6 _uniq_7))
                  (_uniq_9 (List_cons "lcErased" 5 _uniq_8))
                  (_uniq_10 (List_cons "lcErased" 4 _uniq_9))
                  (_uniq_11 (List_cons "lcErased" 3 _uniq_10))
                  (_uniq_12 (List_cons "lcErased" 2 _uniq_11))
                  (_uniq_13 (List_cons "lcErased" 1 _uniq_12)))
               _uniq_13))
         (Nat_add (LAMBDA (a b) (+ a b)))
         (List_map__at__listMap_spec_0
            (LAMBDA (_uniq_1)
               (IF (EQ _uniq_1 NIL)
                  _uniq_1
                  (IF (lneq _uniq_1 NIL)
                     (LET ((_uniq_2 (CAR _uniq_1))
                           (_uniq_3 (CDR _uniq_1))
                           (_uniq_5 (Nat_add _uniq_2 1))
                           (_uniq_6 (List_map__at__listMap_spec_0 _uniq_3))
                           (_uniq_7 (List_cons "lcErased" _uniq_5 _uniq_6)))
                        _uniq_7)
                     NIL))))
         (listMap (LET ((_uniq_2 (List_map__at__listMap_spec_0 list))) _uniq_2)))
   listMap)
⟧

#eval Expr.mutualize $ Array.data $ Prod.fst $ prog.telescopeLetrec