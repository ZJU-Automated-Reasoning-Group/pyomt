(declare-const x0 Real)
(declare-const x1 Real)
(assert (<= (- 1.500000) x1))


(minimize
	(+ (* 100.0 (^ (- x1 (^ x0 2.0)) 2.0)) (^ (- 1.0 x0) 2.0))
)
(check-sat)
(get-objectives)
(exit)

