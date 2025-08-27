(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (^ x0 2.0) (^ x1 2.0)) 25.0))
(assert (= (* x0 x1) 9.0))

(minimize
	(- 1.0)
)
(check-sat)
(get-objectives)
(exit)

