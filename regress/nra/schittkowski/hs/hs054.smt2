(declare-const x0 Real)
(assert (<= (- 1.250000) x0))
(declare-const x1 Real)
(assert (<= (- 11.0) x1))
(declare-const x2 Real)
(assert (<= (- 0.285714) x2))
(declare-const x3 Real)
(assert (<= (- 0.200000) x3))
(declare-const x4 Real)
(assert (<= (- 20.020000) x4))
(declare-const x5 Real)
(assert (<= (- 0.200000) x5))

(assert (= (+ (* 1.0 x0) (* 0.500000 x1)) 0.450000))

(minimize
	(+ (* 1.041667 (^ x0 2.0)) (* 1.041667 (* (* 0.400000 x0) x1)) (* 1.041667 (^ x1 2.0)) (^ x2 2.0) (^ x3 2.0) (^ x4 2.0) (^ x5 2.0))
)
(check-sat)
(get-objectives)
(exit)

