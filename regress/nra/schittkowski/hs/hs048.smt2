(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (* 1.0 x0) (* 1.0 x1) (* 1.0 x2) (* 1.0 x3) (* 1.0 x4)) 5.0))
(assert (= (+ (* 1.0 x2) (* (- 2.0) x3) (* (- 2.0) x4)) (- 3.0)))

(minimize
	(+ (^ (+ (- 1.0) x0) 2.0) (^ (- x1 x2) 2.0) (^ (- x3 x4) 2.0))
)
(check-sat)
(get-objectives)
(exit)

