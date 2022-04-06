(set-logic UFDT)
; run with: vampire -sa fmb -av off --input_syntax smtlib2 -fmbes smt -fmbss 2 -fmbswo diagonal -stat none pattern-matching-compile.smt2

(declare-datatypes
  ((Bol 0) (Var 0) (Branch 0))
	(((F) (T))             ; names of constructors
	 ((x) (y) (z))         ; number of variables in scrutinee tuple
	 ((c1) (c2) (c3) (c4)) ; number of rhs
   ))

; Output language
(declare-sort Code 0) ; Code ~= IR
(declare-fun ret (Branch) Code)
(declare-fun switch (
  Var ; matchable
  Code ; on_false
  Code ; on_true
  )
  Code ; result
  )
(declare-fun nondet () Code)
(assert (forall ((b1 Branch) (b2 Branch))
  (=> (distinct b1 b2) (distinct (ret b1) (ret b2))))) ; different arguments => diffrent ADT values
(assert (forall ((b Branch))
  (distinct (ret b) nondet)
))
(assert (forall ((b Branch) (v Var) (fcase Code) (tcase Code))
  (distinct (ret b) (switch v fcase tcase)))) ; switch =/= ret
; switch=/=nondet is omitted intentionally
; </Output language>

(declare-fun m (Bol Bol Bol) Branch)
(assert (= (m F F T) c1))
(assert (= (m T F T) c1))
(assert (= (m F T F) c2))
(assert (= (m F T T) c2))
(assert (= (m F F F) c3))
(assert (= (m T F F) c3))
(assert (= (m T T F) c3))
(assert (= (m T T T) c4))

;
(declare-fun eval (Code Bol Bol Bol Branch) Bool)
(assert (forall ((b Branch) (b1 Bol) (b2 Bol) (b3 Bol))
  (eval nondet b1 b2 b3 b))) ;

; eval is a deterministic unless it evaluates nondet
(assert (forall ((c1 Code) (r1 Branch) (r2 Branch) (x1 Bol) (x2 Bol) (x3 Bol))
	(=> (and (eval c1 x1 x2 x3 r1) (eval c1 x1 x2 x3 r2)) (or (= r1 r2) (= c1 nondet)))))
; evaluating return is easy
(assert (forall ((br Branch) (b1 Bol) (b2 Bol) (b3 Bol))
  (eval (ret br) b1 b2 b3 br)))

(assert (forall ((v Var) (fcase Code) (tcase Code) (b1 Bol) (b2 Bol) (b3 Bol) (b Branch))
	(=> (or (and (= v x) (= b1 F))
			    (and (= v y) (= b2 F))
			    (and (= v z) (= b3 F)))
        ; env: [ (x,b1); (y,b2); (z,b3) ]
		(=> (eval fcase b1 b2 b3 b)
        (eval (switch v fcase tcase) b1 b2 b3 b)))))
(assert (forall ((v Var) (fcase Code) (tcase Code) (b1 Bol) (b2 Bol) (b3 Bol) (b Branch))
	(=> (or (and (= v x) (= b1 T))
		      (and (= v y) (= b2 T))
			    (and (= v z) (= b3 T)))
		(=> (eval tcase b1 b2 b3 b)
        (eval (switch v fcase tcase) b1 b2 b3 b)))))

; size constraints
(declare-fun lt (Code Code) Bool)
(assert (forall ((v Var) (fcase Code) (tcase Code))
  (lt fcase (switch v fcase tcase))))
(assert (forall ((v Var) (fcase Code) (tcase Code))
  (lt tcase (switch v fcase tcase))))
(assert (forall ((v Var) (x Code) (y Code) (tcase Code))
  (=> (lt x y)
  (lt x (switch v y tcase)))))
(assert (forall ((v Var) (x Code) (y Code) (fcase Code))
  (=> (lt x y)
      (lt x (switch v fcase y)))))
(define-fun le ((c1 Code) (c2 Code)) Bool
	(or (= c1 c2) (lt c1 c2)))

; shallow correctness of IR
(define-fun normal ((c Code)) Bool
   (and (distinct c nondet)
   		(or (exists ((b Branch)) (= c (ret b)))
	       	(exists ((v2 Var) (fcase2 Code) (tcase2 Code))
            (= c (switch v2 fcase2 tcase2))))))
; normal switch has only normal branches
(assert (forall ((c Code) (v1 Var) (fcase1 Code) (tcase1 Code))
	(=> (and (distinct c nondet)
           (= c (switch v1 fcase1 tcase1)))
      (and (normal fcase1)
           (normal tcase1)))))

;;; Heuristics to make speedup synthesis
(declare-fun query () Code)
; for any input synthesized code fits the spec `m`
(assert (forall ((b1 Bol) (b2 Bol) (b3 Bol))
  (eval query b1 b2 b3 (m b1 b2 b3))))
(assert (distinct query nondet))
(assert (exists ((v Var) (fcase Code) (tcase Code))
	(and (= query (switch v fcase tcase))
       (forall ((stc Code) (fcase1 Code) (tcase1 Code))
         (=> (and (= stc (switch v fcase1 tcase1)) (lt stc query)) false))
  )))
; Magic to prevent cycling
(assert (forall ((stc Code))
  (=> (and (le stc query) (lt stc stc)) false)))



; match x,y,z with
; | _,F,T -> c1
; | F,T,_ -> c2
; | _,_,F -> c3
; | _,_,T -> c4

; solution: (if y (if x (if z c4 c3) c2) (if z c1 c3))
; (declare-fun c5 () Code)
; (declare-fun c6 () Code)
; (declare-fun c7 () Code)
; (declare-fun c8 () Code)
; (assert (= c5 (switch z (ret c4) (ret c3))))
; (assert (= c6 (switch x c5 (ret c2))))
; (assert (= c7 (switch z (ret c1) (ret c3))))
; (assert (= c8 (switch y c6 c7)))
; (assert (= query c8))

; from `tff(function_ret,axiom,
;           ret(c1) = fmb_'Code()'_9
;         & ret(c2) = fmb_'Code()'_5
;         & ret(c3) = fmb_'Code()'_6
;         & ret(c4) = fmb_'Code()'_8).`

; $6 = c3
; $9 = c1
; $5 = c2
; $8 = c4

; from `& switch(y,fmb_'Code()'_3,fmb_'Code()'_4) = query` get
; s y $3 $4
; from `& switch(x,fmb_'Code()'_5,fmb_'Code()'_7) = fmb_'Code()'_4`
; s x $5 $7 === $4
; from `& switch(z,fmb_'Code()'_6,fmb_'Code()'_8) = fmb_'Code()'_7`
; s z $6 $8 === $7
; from `switch(z,fmb_'Code()'_6,fmb_'Code()'_9) = fmb_'Code()'_3` get
; s z $6 $9 === $3


; vampire solution: (s y (s z c3 c1) (s x c2 (s z c3 c4)))

(check-sat)
