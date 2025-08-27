(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (= (+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2)) 1.0))

(minimize
	(+ (* (- 8204.370000) (log (/ (+ 0.030000 x0 x1 x2) (+ 0.030000 (* 0.090000 x0) x1 x2)))) (* (- 9008.720000) (log (/ (+ 0.030000 x1 x2) (+ 0.030000 (* 0.070000 x1) x2)))) (* (- 9330.460000) (log (/ (+ 0.030000 x2) (+ 0.030000 (* 0.130000 x2))))))
)
(check-sat)
(get-objectives)
(exit)

