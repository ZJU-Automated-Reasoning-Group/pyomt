(declare-const x0 Real)
(declare-const x1 Real)

(assert (<= (+ (* 4.0 (^ x0 2.0)) (^ x1 2.0)) 25.0))

(minimize
	(+ (* (- 7.0) x0) (* (- 7.0) x1) (+ (* 0.500000 (^ x0 2.0)) (^ x1 2.0) (- (* x0 x1))))
)
(check-sat)
(get-objectives)
(exit)

