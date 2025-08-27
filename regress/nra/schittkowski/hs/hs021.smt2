(declare-const x0 Real)
(assert (<= 2.0 x0))
(declare-const x1 Real)
(assert (<= (- 50.0) x1))

(assert (<= 10.0 (+ (* 10.0 x0) (* (- 1.0) x1))))

(minimize
	(+ (* 0.010000 (^ x0 2.0)) (^ x1 2.0) (- 100.0))
)
(check-sat)
(get-objectives)
(exit)

