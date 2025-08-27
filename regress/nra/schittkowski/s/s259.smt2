(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert (<= x3 1.0))


(minimize
	(+ (* 100.0 (^ (- x1 (^ x0 2.0)) 2.0)) (^ (- 1.0 x0) 2.0) (* 90.0 (^ (- x3 (^ x2 2.0)) 2.0)) (^ (- 1.0 x2) 3.0) (* 10.100000 (^ (+ (- 1.0) x1) 2.0)) (^ (+ (- 1.0) x3) 2.0) (* (* 19.800000 (+ (- 1.0) x1)) (+ (- 1.0) x3)))
)
(check-sat)
(get-objectives)
(exit)

