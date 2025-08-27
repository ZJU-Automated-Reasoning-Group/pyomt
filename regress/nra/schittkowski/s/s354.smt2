(declare-const x0 Real)
(assert (<= x0 20.0))
(declare-const x1 Real)
(assert (<= x1 20.0))
(declare-const x2 Real)
(assert (<= x2 20.0))
(declare-const x3 Real)
(assert (<= x3 20.0))

(assert (<= 1.0 (+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2) (* 1.0 x3))))

(minimize
	(+ (^ (+ x0 (* 10.0 x1)) 2.0) (* 5.0 (^ (- x2 x3) 2.0)) (^ (+ x1 (* (- 2.0) x2)) 4.0) (* 10.0 (^ (- x0 x3) 4.0)))
)
(check-sat)
(get-objectives)
(exit)

