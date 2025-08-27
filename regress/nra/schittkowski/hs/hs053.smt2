(declare-const x0 Real)
(assert (<= (- 10.0) x0))
(declare-const x1 Real)
(assert (<= (- 10.0) x1))
(declare-const x2 Real)
(assert (<= (- 10.0) x2))
(declare-const x3 Real)
(assert (<= (- 10.0) x3))
(declare-const x4 Real)
(assert (<= (- 10.0) x4))

(assert (= (+ (* 1.0 x0) (* 3.0 x1)) 0.0))
(assert (= (+ (* 1.0 x2) (* 1.0 x3) (* (- 2.0) x4)) 0.0))
(assert (= (+ (* 1.0 x1) (* (- 1.0) x4)) 0.0))

(minimize
	(+ (^ (- x0 x1) 2.0) (^ (+ (- 2.0) (+ x1 x2)) 2.0) (^ (+ (- 1.0) x3) 2.0) (^ (+ (- 1.0) x4) 2.0))
)
(check-sat)
(get-objectives)
(exit)

