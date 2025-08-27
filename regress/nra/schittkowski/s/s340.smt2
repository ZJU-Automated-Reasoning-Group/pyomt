(declare-const x0 Real)
(declare-const x1 Real)
(assert (<= x1 1.0))
(declare-const x2 Real)

(assert (<= (- 1.800000) (+ (* (- 1.0) x0) (* (- 2.0) x1) (* (- 2.0) x2))))

(minimize
	(- (* (* x0 x1) x2))
)
(check-sat)
(get-objectives)
(exit)

