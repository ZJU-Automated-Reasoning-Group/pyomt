(declare-const x0 Real)
(assert (<= (- 10.0) x0))
(declare-const x1 Real)
(assert (<= (- 10.0) x1))
(declare-const x2 Real)
(assert (<= (- 10.0) x2))

(assert (= (+ (* x0 (+ 1.0 (^ x1 2.0))) (^ x2 4.0)) 8.242641))

(minimize
	(+ (^ (+ (- 1.0) x0) 2.0) (^ (- x0 x1) 2.0) (^ (- x1 x2) 4.0))
)
(check-sat)
(get-objectives)
(exit)

