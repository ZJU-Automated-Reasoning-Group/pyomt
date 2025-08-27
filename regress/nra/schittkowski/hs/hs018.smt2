(declare-const x0 Real)
(assert (<= 2.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 25.0 (* x0 x1)))
(assert (<= 25.0 (+ (^ x0 2.0) (^ x1 2.0))))

(minimize
	(+ (* 0.010000 (^ x0 2.0)) (^ x1 2.0))
)
(check-sat)
(get-objectives)
(exit)

