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


(minimize
	(+ (* (- 0.008333) (* (* (* (* x0 x1) x2) x3) x4)) 2.0)
)
(check-sat)
(get-objectives)
(exit)

