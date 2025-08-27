(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (* 1.0 x2) (* x0 (- 1.0 x1))) 1.500000))
(assert (= (+ (* 1.0 x3) (* x0 (- 1.0 (^ x1 2.0)))) 2.250000))
(assert (= (+ (* 1.0 x4) (* x0 (- 1.0 (^ x1 3.0)))) 2.625000))

(minimize
	(+ (^ x2 2.0) (^ x3 2.0) (^ x4 2.0))
)
(check-sat)
(get-objectives)
(exit)

