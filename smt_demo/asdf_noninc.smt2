; execute as
;   cvc4 -L smt2.6 --no-incremental --no-type-checking --no-interactive --finite-model-find --decision=internal asdf_noninc.smt2 -m

; Preamble  --------------
(set-logic  UFDTLIA)


;(declare-datatype bool ((T) (F)))
(declare-datatypes ((bool 0)) (((T) (F))) )
(declare-datatypes ((unit 0)) (((U))) )
;(declare-datatype unit ((U)))


;match ... with
;| pair (nil, _) -> 10
;| pair (_, nil) -> 20
;| pair (cons (_, _), cons (_, _)) -> 30
;(declare-datatype list ( (Nil) (Cons (h unit) (tl list))))
(declare-datatypes ((list 0)) (( (Nil) (Cons (h Int) (tl list)))) )


(declare-fun func2 (list list) Int)
(assert
  (= 10 (func2 Nil Nil)))
(assert
  (forall ((x Int))
  (= 20 (func2 (Cons x Nil) Nil))) )
(assert (forall ((x Int) )
  (= 10 (func2 Nil (Cons x Nil) ))) )
(assert (forall ((x Int) (y Int))
  (= 30 (func2 (Cons x Nil) (Cons x Nil) ))) )

(check-sat)
;(get-model)
;(get-info :reason-unknown)
