(declare-const x0 Real)
(assert (<= 1.0 x0))
(declare-const x1 Real)
(assert (<= 1.0 x1))
(declare-const x2 Real)
(assert (<= 1.0 x2))
(declare-const x3 Real)
(assert (<= 1.0 x3))

(assert (<= 25.0 (* (* (* x0 x1) x2) x3)))
(assert (= (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0) (^ x3 2.0)) 40.0))

(minimize
	(+ (* 1.0 x2) (* (* x0 x3) (+ x0 x1 x2)))
)
(check-sat)
(get-objectives)
(exit)

