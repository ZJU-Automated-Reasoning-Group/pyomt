(declare-const x0 Real)
(assert (<= 0.001000 x0))
(declare-const x1 Real)
(assert (<= 0.001000 x1))
(declare-const x2 Real)
(assert (<= 0.001000 x2))
(declare-const x3 Real)
(assert (<= 0.001000 x3))

(assert (<= (+ (/ 4.0 x0) (/ 2.250000 x1) (/ 1.0 x2) (/ 0.250000 x3)) 0.040100))
(assert (<= (+ (/ 0.160000 x0) (/ 0.360000 x1) (/ 0.640000 x2) (/ 0.640000 x3)) 0.010085))

(minimize
	(+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2) (* 1.0 x3) 1.0)
)
(check-sat)
(get-objectives)
(exit)

