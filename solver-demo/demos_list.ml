let demo1 = "
  (declare-const x Int)
  (declare-const y Int)
  (assert (= (- x y) (+ x (- y) 1)))
  (check-sat)
  "
