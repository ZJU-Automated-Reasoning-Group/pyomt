(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)

(assert (= (+ (* 1.0 x3) (- (- (^ x1 2.0)) (^ x0 3.0))) 0.0))
(assert (= (+ (* (- 1.0) x3) (- (^ x0 2.0) (^ x2 2.0))) 0.0))

(minimize
	 (* (- 1.0) x0)
)
(check-sat)
(get-objectives)
(exit)

