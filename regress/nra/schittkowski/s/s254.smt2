(declare-const x0 Real)
(assert (<= 1.0 x0))
(declare-const x1 Real)
(declare-const x2 Real)

(assert (= (+ (^ x2 2.0) (^ x0 2.0)) 4.0))
(assert (= (+ (* 1.0 x0) (- (^ x1 2.0))) 1.0))

(minimize
	(+ (* (- 1.0) x2) (log x0))
)
(check-sat)
(get-objectives)
(exit)

