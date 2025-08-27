(declare-const x0 Real)
(assert (<= 1.0 x0))
(declare-const x1 Real)
(assert (<= 1.0 x1))


(minimize
	(+ (* 0.100000 (^ x0 2.0)) (* 0.100000 (/ (+ 1.0 (^ x1 2.0)) (^ x0 2.0))) (* 0.100000 (/ (+ 100.0 (* (^ x0 2.0) (^ x1 2.0))) (* (^ x0 4.0) (^ x1 4.0)))) 1.200000)
)
(check-sat)
(get-objectives)
(exit)

