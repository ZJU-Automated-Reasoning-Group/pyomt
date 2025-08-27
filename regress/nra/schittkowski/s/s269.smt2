(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (* 1.0 x0) (* 3.0 x1)) 0.0))
(assert (= (+ (* 1.0 x2) (* 1.0 x3) (* (- 2.0) x4)) 0.0))
(assert (= (+ (* 1.0 x1) (* (- 1.0) x4)) 0.0))

(minimize
	(+ (^ (- x0 x1) 2.0) (^ (+ (- 2.0) (+ x1 x2)) 2.0) (^ (+ (- 1.0) x3) 2.0) (^ (+ (- 1.0) x4) 2.0))
)
(check-sat)
(get-objectives)
(exit)

