(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (* (- 2.0) x1) (* x0 (+ (- 4.0) x0))) (- 12.0)))

(minimize
	(+ (* 100.0 (^ (- (^ x0 2.0) x1) 2.0)) (^ (+ (- 1.0) x0) 2.0))
)
(check-sat)
(get-objectives)
(exit)

