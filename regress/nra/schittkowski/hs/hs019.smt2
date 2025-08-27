(declare-const x0 Real)
(assert (<= 13.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 100.0 (+ (^ (+ (- 5.0) x0) 2.0) (^ (+ (- 5.0) x1) 2.0))))
(assert (<= (+ (^ (+ (- 5.0) x1) 2.0) (^ (+ (- 6.0) x0) 2.0)) 82.810000))

(minimize
	(+ (^ (+ (- 10.0) x0) 3.0) (^ (+ (- 20.0) x1) 3.0))
)
(check-sat)
(get-objectives)
(exit)

