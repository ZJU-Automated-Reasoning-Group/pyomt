(declare-const x0 Real)
(assert (<= 1.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))


(minimize
	(+ (* 1.0 x1) (* 0.333333 (^ (+ 1.0 x0) 3.0)))
)
(check-sat)
(get-objectives)
(exit)

