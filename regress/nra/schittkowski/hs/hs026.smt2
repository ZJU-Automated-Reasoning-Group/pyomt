(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (* (+ 1.0 (^ x1 2.0)) x0) (^ x2 4.0)) 3.0))

(minimize
	(+ (^ (- x0 x1) 2.0) (^ (- x1 x2) 4.0))
)
(check-sat)
(get-objectives)
(exit)

