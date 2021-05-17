; execute as
;    cvc4 -m asdf.smt2 --incremental

; Preamble  --------------
(set-logic UFDTLIA)

(declare-datatype bool ((T) (F)))
(declare-datatype unit ((U)))

(push)

(declare-fun func ( bool bool bool) Int)
(assert (= 4 (func T T T)))
(assert (= 2 (func F T T)))
(assert (= 1 (func T F T)))
(assert (= 3 (func T T F)))
(assert (= 1 (func F F T)))
(assert (= 2 (func F T F)))
(assert (= 3 (func T F F)))
(assert (= 3 (func F F F)))
(check-sat)
(get-model)
(pop)


(push)
;match ... with
;| pair (nil, _) -> 10
;| pair (_, nil) -> 20
;| pair (cons (_, _), cons (_, _)) -> 30
(declare-datatype list ( (Nil) (Cons (h unit) (tl list))))
(declare-fun func2 (list list) Int)
(assert
  (= 10 (func2 Nil Nil)))
(assert
  ;(forall ((x unit))
  (= 20 (func2 (Cons U Nil) Nil))) ;)
(assert ;(forall ((x unit) )
  (= 10 (func2 Nil (Cons U Nil) ))) ;)
(assert ;(forall ((x unit) (y unit))
  (= 30 (func2 (Cons U Nil) (Cons U Nil) ))) ;)

(check-sat)
(get-model)
(pop)


(push)
;match ... with
;| pair (nil, _) -> 10
;| pair (_, nil) -> 20
;| pair (cons (_, _), cons (_, _)) -> 30
(declare-datatype list ( (Nil) (Cons (h unit) (tl list))))
(declare-fun func2 (list list) Int)
(assert
  (= 10 (func2 Nil Nil)))
(assert
  (forall ((x unit))
  (= 20 (func2 (Cons x Nil) Nil))) )
(assert (forall ((x unit) )
  (= 10 (func2 Nil (Cons x Nil) ))) )
(assert (forall ((x unit) (y unit))
  (= 30 (func2 (Cons x Nil) (Cons x Nil) ))) )

(check-sat)
(get-model)
(pop)
