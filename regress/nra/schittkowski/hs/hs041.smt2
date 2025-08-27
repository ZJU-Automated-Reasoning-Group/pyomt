(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (= (+ (* 1.0 x0) (* 2.0 x1) (* 2.0 x2) (* (- 1.0) x3)) 0.0))

(minimize
	(- 2.0 (* (* x0 x1) x2))
)
(check-sat)
(get-objectives)
(exit)

