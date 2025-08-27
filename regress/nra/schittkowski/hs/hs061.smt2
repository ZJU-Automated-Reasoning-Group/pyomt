(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (* 3.0 x2) (* (- 2.0) (^ x0 2.0))) 7.0))
(assert (= (+ (* 4.0 x2) (- (^ x1 2.0))) 11.0))

(minimize
	(+ (* 16.0 x0) (* (- 24.0) x1) (* (- 33.0) x2) (+ (* 4.0 (^ x2 2.0)) (* 2.0 (^ x0 2.0)) (* 2.0 (^ x1 2.0))))
)
(check-sat)
(get-objectives)
(exit)

