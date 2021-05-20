; call: cvc4 --lang=sygus2 smt_demo/synth4bool.smt2
; returns instantly
;    unsat
;    (define-fun func ((x Bool) (y Bool) (z Bool)) Int (ite z (ite y (ite x 4 2) 1) (ite y (ite x 3 2) 3)))
;
;
; call: ~/asp/cvc5/bin/cvc5 --lang=sygus2 --sygus-stream smt_demo/synth4bool.smt2
; returns in about 3 seconds an optimal answer:
;   (define-fun func ((x Bool) (y Bool) (z Bool)) Int (ite y (ite x (ite z 4 3) 2) (ite z 1 3)))
;
; call:  ~/asp/cvc5/bin/cvc5 --lang=sygus2 --sygus-stream --sygus-pbe smt_demo/synth4bool.smt2
; returns instantly  an answer:
;   (define-fun func ((x Bool) (y Bool) (z Bool)) Int (ite z (ite y (ite x 4 2) 1) (ite y (ite x 3 2) 3)))
; and hangs
;
(set-logic  UFDTLIA)

(synth-fun func ((x Bool) (y Bool) (z Bool)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (1
                 2
                 3
                 4
                 (ite StartBool Start Start)))
     (StartBool Bool (x
                      y
                      z
                      ))
     ))


(constraint (= 4 (func true true true)))
(constraint (= 2 (func false true true)))
(constraint (= 1 (func true false true)))
(constraint (= 3 (func true true false)))
(constraint (= 1 (func false false true)))
(constraint (= 2 (func false true false)))
(constraint (= 3 (func true false false)))
(constraint (= 3 (func false false false)))


(check-synth)
