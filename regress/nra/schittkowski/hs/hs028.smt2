(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (* 1.0 x0) (* 2.0 x1) (* 3.0 x2)) 1.0))

(minimize
	(+ (^ (+ x0 x1) 2.0) (^ (+ x1 x2) 2.0))
)
(check-sat)
(get-objectives)
(exit)

