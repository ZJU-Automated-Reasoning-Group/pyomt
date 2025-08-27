(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (* 0.010000 (^ x0 2.0)) (* 0.010000 (^ x1 2.0))) 1.0))

(minimize
	(+ (^ (+ (- 20.0) x0) 2.0) (^ (+ 20.0 x1) 2.0))
)
(check-sat)
(get-objectives)
(exit)

