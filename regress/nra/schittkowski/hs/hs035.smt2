(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (<= (+ (* 1.0 x0) (* 1.0 x1) (* 2.0 x2)) 3.0))

(minimize
	(+ (* (- 8.0) x0) (* (- 6.0) x1) (* (- 4.0) x2) (+ (* 2.0 (^ x0 2.0)) (* 2.0 (^ x1 2.0)) (^ x2 2.0) (* (* 2.0 x0) x1) (* (* 2.0 x0) x2) 9.0))
)
(check-sat)
(get-objectives)
(exit)

