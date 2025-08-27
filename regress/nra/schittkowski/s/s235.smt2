(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (* 1.0 x1) (^ x0 2.0)) (- 1.0)))

(minimize
	(+ (* 0.010000 (^ (+ (- 1.0) x1) 2.0)) (^ (- x2 (^ x1 2.0)) 2.0))
)
(check-sat)
(get-objectives)
(exit)

