(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))
(declare-const x4 Real)
(assert (<= 0.0 x4))
(declare-const x5 Real)
(assert (<= 0.0 x5))

(assert (<= 2.070000 (* 0.001000 (* (* (* (* (* x0 x1) x2) x3) x4) x5))))
(assert (<= (+ (* (* (* (* 0.000620 x0) x3) (^ x4 2.0)) (+ x0 x1 x2)) (* (* (* (* 0.000580 x1) x2) (^ x5 2.0)) (+ x0 (* 1.570000 x1) x3))) 1.0))

(minimize
	(+ (* (* (* 0.020400 x0) x3) (+ x0 x1 x2)) (* (* (* 0.018700 x1) x2) (+ x0 (* 1.570000 x1) x3)) (* (* (* (* 0.060700 x0) x3) (^ x4 2.0)) (+ x0 x1 x2)) (* (* (* (* 0.043700 x1) x2) (^ x5 2.0)) (+ x0 (* 1.570000 x1) x3)))
)
(check-sat)
(get-objectives)
(exit)

