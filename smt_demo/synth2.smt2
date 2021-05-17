; https://www.starexec.org/starexec/secure/details/benchmark.jsp?id=4785727

(set-logic  UFDTLIA)


(declare-datatypes ((bool 0)) (((T) (F))) )
(declare-datatypes ((unit 0)) (((U))) )
(declare-datatypes ((list 0)) (( (Nil) (Cons (h Int) (tl list)))) )
(declare-var x Int)
(declare-var y Int)

(synth-fun func2 ((x list) (y list)) Int
    ((Start Int ((h StartList)
                 10
                 20
                 30
                 ;(+ Start Start)
                 ;(- Start Start)
                 (ite StartBool Start Start)))
     (StartList list (x y (tl StartList) Nil (Cons Start StartList)) )
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      ;(<=  Start Start)
                      (=   Start Start)
                      (= StartList StartList)
                      ;(>=  Start Start)
                      ))))



(constraint
  (= 10 (func2 Nil Nil)))

(check-synth)
