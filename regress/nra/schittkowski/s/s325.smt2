(declare-const x0 Real)
(declare-const x1 Real)

(assert (<= (- 1.0) (+ (* (- 1.0) x0) (- (^ x1 2.0)))))
(assert (= (+ (^ x0 2.0) (^ x1 2.0)) 9.0))
(assert (<= (- 1.0) (+ (* (- 1.0) x0) (* (- 1.0) x1))))

(minimize
	(+ (* 1.0 x1) (^ x0 2.0))
)
(check-sat)
(get-objectives)
(exit)

