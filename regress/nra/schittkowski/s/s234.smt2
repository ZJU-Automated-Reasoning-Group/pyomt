(declare-const x0 Real)
(assert (<= 0.200000 x0))
(declare-const x1 Real)
(assert (<= 0.200000 x1))

(assert (<= (- 1.0) (- (- (^ x1 2.0)) (^ x0 2.0))))

(minimize
	(+ (* 1.0 x0) (+ (^ (- x1 x0) 4.0) (- 1.0)))
)
(check-sat)
(get-objectives)
(exit)

