(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= (- 18.0) (+ (* (- 1.0) x0) (* (- 3.0) x1))))
(assert (<= (- 8.0) (+ (* (- 1.0) x0) (* (- 1.0) x1))))

(minimize
	(+ (* (- 48.0) x0) (* (- 40.0) x1) (+ (* 2.0 (^ x0 2.0)) (^ x1 2.0)))
)
(check-sat)
(get-objectives)
(exit)

