(declare-const x0 Real)
(assert (<= (- 1.500000) x0))
(declare-const x1 Real)
(assert (<= (- 3.0) x1))


(minimize
	(+ (* (- 1.500000) x0) (* 2.500000 x1) (+ (sin (+ x0 x1)) (^ (- x0 x1) 2.0) 1.0))
)
(check-sat)
(get-objectives)
(exit)

