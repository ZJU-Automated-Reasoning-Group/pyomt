(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (* 10.0 x1) (* (- 10.0) (^ x0 2.0))) 0.0))

(minimize
	(^ (- 1.0 x0) 2.0)
)
(check-sat)
(get-objectives)
(exit)

