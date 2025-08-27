(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (<= 21.0 (+ (* 12.0 x0) (* 11.900000 x1) (* 41.800000 x2) (* 52.100000 x3) (* (- 1.645000) (sqrt (+ (* 0.280000 (^ x0 2.0)) (* 0.190000 (^ x1 2.0)) (* 20.500000 (^ x2 2.0)) (* 0.620000 (^ x3 2.0))))))))
(assert (<= 5.0 (+ (* 2.300000 x0) (* 5.600000 x1) (* 11.100000 x2) (* 1.300000 x3))))
(assert (= (+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2) (* 1.0 x3)) 1.0))

(minimize
	(+ (* 24.550000 x0) (* 26.750000 x1) (* 39.0 x2) (* 40.500000 x3))
)
(check-sat)
(get-objectives)
(exit)

