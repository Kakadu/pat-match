; https://www.starexec.org/starexec/secure/details/benchmark.jsp?id=4785727

(set-logic  UFDTLIA)

(declare-datatypes ((unit 0)) (((U))) )
(declare-datatypes ((list 0)) (( (Nil) (Cons (h Int) (tl list)))) )
(declare-var x Int)
(declare-var y Int)

(synth-fun func2 ((x list) (y list)) Int
    ((Start Int) (StartList list) (StartBool Bool))
    ((Start Int (10
                 20
                 30
                 (ite StartBool Start Start)))
     (StartList list (x
                      y
                      (tl StartList)
                      Nil
                      (Cons Start StartList)
                      ))
     (StartBool Bool ((and StartBool StartBool)
                      ;(or  StartBool StartBool)
                      ;(not StartBool)
                      ;(<=  Start Start)
                      ;(=   Start Start)
                      ;(= StartList StartList)
                      ((_ is Nil) StartList)
                      ((_ is Cons) StartList)                    
                      ))))



(constraint
  (= 10 (func2 Nil Nil)))
(constraint
  (= 20 (func2 (Cons x Nil) Nil)))
(constraint
  (= 10 (func2 Nil (Cons x Nil) )))
(constraint
  (= 30 (func2 (Cons x Nil) (Cons x Nil) )))
(check-synth)
