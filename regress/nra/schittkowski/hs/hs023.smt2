(declare-const x0 Real)
(assert (<= (- 50.0) x0))
(declare-const x1 Real)
(assert (<= (- 50.0) x1))

(assert (<= 1.0 (+ (^ x0 2.0) (^ x1 2.0))))
(assert (<= 9.0 (+ (* 9.0 (^ x0 2.0)) (^ x1 2.0))))
(assert (<= 0.0 (+ (* (- 1.0) x1) (^ x0 2.0))))
(assert (<= 0.0 (+ (* (- 1.0) x0) (^ x1 2.0))))
(assert (<= 1.0 (+ (* 1.0 x0) (* 1.0 x1))))

(minimize
	(+ (^ x0 2.0) (^ x1 2.0))
)
(check-sat)
(get-objectives)
(exit)

