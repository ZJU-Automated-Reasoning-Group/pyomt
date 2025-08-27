(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (^ x0 2.0) (* 0.666667 (^ x1 2.0)) (* 0.250000 (^ x2 2.0))) 4.0))
(assert (= (+ (* 0.500000 x0) (* 1.0 x1) (* 1.0 x2)) 1.0))

(minimize
	(- (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0)))
)
(check-sat)
(get-objectives)
(exit)

