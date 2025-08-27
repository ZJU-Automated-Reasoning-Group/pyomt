(declare-const x0 Real)
(assert (<= (- 2.300000) x0))
(declare-const x1 Real)
(assert (<= (- 2.300000) x1))
(declare-const x2 Real)
(assert (<= (- 3.200000) x2))
(declare-const x3 Real)
(assert (<= (- 3.200000) x3))
(declare-const x4 Real)
(assert (<= (- 3.200000) x4))

(assert (= (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0) (^ x3 2.0) (^ x4 2.0)) 10.0))
(assert (= (- (* x1 x2) (* (* 5.0 x3) x4)) 0.0))
(assert (= (+ (^ x0 3.0) (^ x1 3.0)) (- 1.0)))

(minimize
	(exp (* (* (* (* x0 x1) x2) x3) x4))
)
(check-sat)
(get-objectives)
(exit)

