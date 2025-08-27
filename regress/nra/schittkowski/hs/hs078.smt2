(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0) (^ x3 2.0) (^ x4 2.0)) 10.0))
(assert (= (- (* x1 x2) (* (* 5.0 x3) x4)) 0.0))
(assert (= (+ (^ x0 3.0) (^ x1 3.0)) (- 1.0)))

(minimize
	(* (* (* (* x0 x1) x2) x3) x4)
)
(check-sat)
(get-objectives)
(exit)

