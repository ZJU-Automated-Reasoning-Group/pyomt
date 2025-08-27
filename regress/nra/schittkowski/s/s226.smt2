(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 0.0 (+ (^ x0 2.0) (^ x1 2.0))))
(assert (<= (- 1.0) (- (- (^ x1 2.0)) (^ x0 2.0))))

(minimize
	(- (* x0 x1))
)
(check-sat)
(get-objectives)
(exit)

