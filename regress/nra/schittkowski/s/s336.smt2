(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (^ x0 2.0) (* 2.0 (^ x1 2.0)) (* 3.0 (^ x2 2.0))) 1.0))
(assert (= (+ (* 5.0 x0) (* 5.0 x1) (* (- 3.0) x2)) 6.0))

(minimize
	(+ (* 7.0 x0) (* (- 6.0) x1) (* 4.0 x2))
)
(check-sat)
(get-objectives)
(exit)

