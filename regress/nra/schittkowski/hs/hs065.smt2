(declare-const x0 Real)
(assert (<= (- 4.500000) x0))
(declare-const x1 Real)
(assert (<= (- 4.500000) x1))
(declare-const x2 Real)
(assert (<= (- 5.0) x2))

(assert (<= (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0)) 48.0))

(minimize
	(+ (^ (- x0 x1) 2.0) (* 0.111111 (^ (+ (- 10.0) (+ x0 x1)) 2.0)) (^ (+ (- 5.0) x2) 2.0))
)
(check-sat)
(get-objectives)
(exit)

