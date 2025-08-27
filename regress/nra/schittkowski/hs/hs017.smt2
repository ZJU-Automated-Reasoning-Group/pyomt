(declare-const x0 Real)
(assert (<= (- 0.500000) x0))
(declare-const x1 Real)
(assert (<= x1 1.0))

(assert (<= 0.0 (+ (* (- 1.0) x0) (^ x1 2.0))))
(assert (<= 0.0 (+ (* (- 1.0) x1) (^ x0 2.0))))

(minimize
	(+ (* 100.0 (^ (- x1 (^ x0 2.0)) 2.0)) (^ (- 1.0 x0) 2.0))
)
(check-sat)
(get-objectives)
(exit)

