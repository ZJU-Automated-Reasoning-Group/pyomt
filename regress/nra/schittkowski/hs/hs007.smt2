(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (^ (+ 1.0 (^ x0 2.0)) 2.0) (^ x1 2.0)) 4.0))

(minimize
	(+ (* (- 1.0) x1) (log (+ 1.0 (^ x0 2.0))))
)
(check-sat)
(get-objectives)
(exit)

