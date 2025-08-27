(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= (- 11.0) (+ (* 6.0 x0) (* (- 4.0) x1) (- (^ x0 2.0)))))
(assert (<= (- 1.0) (+ (* (- 3.0) x1) (- (* x0 x1) (exp (+ (- 3.0) x0))))))

(minimize
	(+ (* (- 16.0) x0) (* (- 10.0) x1) (+ (^ x0 2.0) (^ x1 2.0)))
)
(check-sat)
(get-objectives)
(exit)

