(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= (- 1.0) (* (- 8.620000) (/ (^ x1 3.0) x0))))

(minimize
	(+ (* 0.044000 (/ (^ x0 3.0) (^ x1 2.0))) (/ 1.0 x0) (* 0.059200 (/ x0 (^ x1 3.0))))
)
(check-sat)
(get-objectives)
(exit)

