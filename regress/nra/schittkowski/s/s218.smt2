(declare-const x0 Real)
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 0.0 (+ (* 1.0 x1) (- (^ x0 2.0)))))

(minimize
	 (* 1.0 x1)
)
(check-sat)
(get-objectives)
(exit)

