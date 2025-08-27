(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (<= 2.083333 (+ (* 1.0 x0) (* 0.500000 x1) (* 0.333333 x2) (* 0.250000 x3))))
(assert (<= 1.283333 (+ (* 0.500000 x0) (* 0.333333 x1) (* 0.250000 x2) (* 0.200000 x3))))
(assert (<= 0.950000 (+ (* 0.333333 x0) (* 0.250000 x1) (* 0.200000 x2) (* 0.166667 x3))))
(assert (<= 0.759524 (+ (* 0.250000 x0) (* 0.200000 x1) (* 0.166667 x2) (* 0.142857 x3))))

(minimize
	(+ (* 2.083333 x0) (* 1.283333 x1) (* 0.950000 x2) (* 0.759524 x3))
)
(check-sat)
(get-objectives)
(exit)

