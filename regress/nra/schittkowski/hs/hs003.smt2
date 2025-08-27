(declare-const x0 Real)
(declare-const x1 Real)
(assert (<= 0.0 x1))


(minimize
	(+ (* 1.0 x1) (* 0.000010 (^ (- x1 x0) 2.0)))
)
(check-sat)
(get-objectives)
(exit)

