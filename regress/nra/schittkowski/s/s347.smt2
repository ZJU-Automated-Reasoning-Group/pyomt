(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)

(assert (= (+ (* 1.0 x3) (- (/ (+ 0.030000 x0 x1 x2) (+ 0.030000 (* 0.090000 x0) x1 x2)))) 0.0))
(assert (= (+ (* 1.0 x4) (- (/ (+ 0.030000 x1 x2) (+ 0.030000 (* 0.070000 x1) x2)))) 0.0))
(assert (= (+ (* 1.0 x5) (- (/ (+ 0.030000 x2) (+ 0.030000 (* 0.130000 x2))))) 0.0))
(assert (= (+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2)) 1.0))

(minimize
	(+ (* 8204.370000 (log x3)) (* 9008.720000 (log x4)) (* 9330.460000 (log x5)))
)
(check-sat)
(get-objectives)
(exit)

