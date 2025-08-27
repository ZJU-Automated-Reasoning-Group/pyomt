(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)


(minimize
	(+ (* 100.0 (^ (- (^ x0 2.0) x1) 2.0)) (^ (+ (- 1.0) x0) 2.0) (* 90.0 (^ (- (^ x2 2.0) x3) 2.0)) (^ (+ (- 1.0) x2) 2.0) (* 10.100000 (^ (+ (- 1.0) x1) 2.0)) (* 10.100000 (^ (+ (- 1.0) x3) 2.0)) (* (* 19.800000 (+ (- 1.0) x0)) (+ (- 1.0) x3)))
)
(check-sat)
(get-objectives)
(exit)

