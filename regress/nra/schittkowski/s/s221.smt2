(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 0.0 (+ (* (- 1.0) x1) (^ (- 1.0 x0) 3.0))))

(minimize
	 (* (- 1.0) x0)
)
(check-sat)
(get-objectives)
(exit)

