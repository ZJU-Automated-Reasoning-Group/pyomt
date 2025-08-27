(declare-const x0 Real)
(declare-const x1 Real)

(assert (<= (+ (* (- 1.0) x1) (^ x0 2.0)) 0.0))

(minimize
	(+ (^ (+ (- 5.0) x0) 2.0) (^ x1 2.0) (- 25.0))
)
(check-sat)
(get-objectives)
(exit)

