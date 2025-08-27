(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (<= (- 48.0) (+ (- (^ x0 2.0)) (* (- 2.0) (^ x1 2.0)) (* (- 4.0) (^ x2 2.0)))))

(minimize
	(- (* (* x0 x1) x2))
)
(check-sat)
(get-objectives)
(exit)

