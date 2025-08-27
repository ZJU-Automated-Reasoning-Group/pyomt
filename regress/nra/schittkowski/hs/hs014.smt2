(declare-const x0 Real)
(declare-const x1 Real)

(assert (<= (+ (* 0.250000 (^ x0 2.0)) (^ x1 2.0)) 1.0))
(assert (= (+ (* 1.0 x0) (* (- 2.0) x1)) (- 1.0)))

(minimize
	(+ (^ (+ (- 2.0) x0) 2.0) (^ (+ (- 1.0) x1) 2.0))
)
(check-sat)
(get-objectives)
(exit)

