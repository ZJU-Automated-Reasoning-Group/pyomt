(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (= (+ (^ x0 2.0) (^ x1 2.0)) 2.0))

(minimize
	(+ (^ (+ (- 2.0) x2) 2.0) (^ (+ (- 3.0) x0) 2.0) (^ (+ (- 4.0) x1) 2.0) 1.0)
)
(check-sat)
(get-objectives)
(exit)

