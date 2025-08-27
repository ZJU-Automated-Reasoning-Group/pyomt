(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (<= (+ (^ x0 2.0) (* 2.0 (^ x1 2.0)) (* 4.0 (^ x2 2.0))) 48.0))

(minimize
	(- (* (* x0 x1) x2))
)
(check-sat)
(get-objectives)
(exit)

