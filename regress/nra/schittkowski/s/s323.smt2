(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 1.0 (+ (* 1.0 x1) (- (^ x0 2.0)))))
(assert (<= (- 2.0) (+ (* 1.0 x0) (* (- 1.0) x1))))

(minimize
	(+ (* (- 4.0) x0) (+ (^ x0 2.0) (^ x1 2.0) 4.0))
)
(check-sat)
(get-objectives)
(exit)

