(declare-const x0 Real)
(declare-const x1 Real)

(assert (<= (- 1.0) (+ (* (- 3.0) (^ x0 2.0)) (* (* 2.0 x0) x1) (- (^ x1 2.0)))))

(minimize
	(+ (* 1.0 x0) (* (- 1.0) x1))
)
(check-sat)
(get-objectives)
(exit)

