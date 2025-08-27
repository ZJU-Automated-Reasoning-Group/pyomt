(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (= (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0)) 25.0))
(assert (= (+ (* 8.0 x0) (* 14.0 x1) (* 7.0 x2)) 56.0))

(minimize
	(- (+ (^ x0 2.0) (- (* (- 2.0) (^ x1 2.0))) (^ x2 2.0) (* x0 x1) (* x0 x2) (- 1000.0)))
)
(check-sat)
(get-objectives)
(exit)

