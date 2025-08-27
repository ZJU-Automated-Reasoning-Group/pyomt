(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (= (+ (* 1.0 x0) (* 1.0 x1)) 1.0))
(assert (= (+ (* 1.0 x2) (* 1.0 x3)) 1.0))

(minimize
	(- (+ (exp (* (* (- 10.0) x0) (exp (- x2)))) (exp (* (* (- 10.0) x1) (exp (- x3)))) (- 2.0)))
)
(check-sat)
(get-objectives)
(exit)

