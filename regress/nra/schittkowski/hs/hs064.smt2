(declare-const x0 Real)
(assert (<= 0.000010 x0))
(declare-const x1 Real)
(assert (<= 0.000010 x1))
(declare-const x2 Real)
(assert (<= 0.000010 x2))

(assert (<= (+ (/ 4.0 x0) (/ 32.0 x1) (/ 120.0 x2)) 1.0))

(minimize
	(+ (* 5.0 x0) (* 20.0 x1) (* 10.0 x2) (+ (/ 50000.0 x0) (/ 72000.0 x1) (/ 144000.0 x2)))
)
(check-sat)
(get-objectives)
(exit)

