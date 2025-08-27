(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (<= 0.0 (+ (* 1.0 x1) (- (exp x0)))))
(assert (<= 0.0 (+ (* 1.0 x2) (- (exp x1)))))

(minimize
	 (* (- 1.0) x0)
)
(check-sat)
(get-objectives)
(exit)

