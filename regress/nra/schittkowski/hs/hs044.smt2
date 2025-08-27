(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (<= (+ (* 1.0 x0) (* 2.0 x1)) 8.0))
(assert (<= (+ (* 4.0 x0) (* 1.0 x1)) 12.0))
(assert (<= (+ (* 3.0 x0) (* 4.0 x1)) 12.0))
(assert (<= (+ (* 2.0 x2) (* 1.0 x3)) 8.0))
(assert (<= (+ (* 1.0 x2) (* 2.0 x3)) 8.0))
(assert (<= (+ (* 1.0 x2) (* 1.0 x3)) 5.0))

(minimize
	(+ (* 1.0 x0) (* (- 1.0) x1) (* (- 1.0) x2) (+ (- (* x0 x2)) (* x0 x3) (* x1 x2) (- (* x1 x3))))
)
(check-sat)
(get-objectives)
(exit)

