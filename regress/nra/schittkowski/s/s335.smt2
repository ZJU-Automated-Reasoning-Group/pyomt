(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (* (- 1.0) x2) (+ (* 1000.0 (^ x0 2.0)) (* 100.0 (^ x1 2.0)))) 0.0))
(assert (= (+ (* 1.0 x2) (+ (* 100.0 (^ x0 2.0)) (* 400.0 (^ x1 2.0)))) 0.010000))

(minimize
	(+ (* (- 0.001000) x0) (* (- 1.0) x1))
)
(check-sat)
(get-objectives)
(exit)

