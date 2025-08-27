(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (<= (- 10.0) (- (- (* x0 x1)) (* (* 2.0 x0) x2))))

(minimize
	(+ (/ 0.200000 (* (* x0 x1) x2)) (/ 4.0 x0) (/ 3.0 x2))
)
(check-sat)
(get-objectives)
(exit)

