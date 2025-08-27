(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (<= (+ (* 1.0 x0) (* 2.0 x1) (* 1.0 x2) (* 1.0 x3)) 5.0))
(assert (<= (+ (* 3.0 x0) (* 1.0 x1) (* 2.0 x2) (* (- 1.0) x3)) 4.0))
(assert (<= 1.500000 (+ (* 1.0 x1) (* 4.0 x2))))

(minimize
	(+ (* (- 1.0) x0) (* (- 3.0) x1) (* 1.0 x2) (* (- 1.0) x3) (+ (^ x0 2.0) (* 0.500000 (^ x1 2.0)) (^ x2 2.0) (* 0.500000 (^ x3 2.0)) (- (* x0 x2)) (* x2 x3)))
)
(check-sat)
(get-objectives)
(exit)

