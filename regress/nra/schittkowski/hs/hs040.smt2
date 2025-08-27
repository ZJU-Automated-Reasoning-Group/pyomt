(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)

(assert (= (+ (^ x0 3.0) (^ x1 2.0)) 1.0))
(assert (= (+ (* (- 1.0) x3) (* (^ x0 2.0) x2)) 0.0))
(assert (= (+ (* (- 1.0) x1) (^ x2 2.0)) 0.0))

(minimize
	(- (* (* (* x0 x1) x3) x2))
)
(check-sat)
(get-objectives)
(exit)

