(declare-const x0 Real)
(assert (<= 0.100000 x0))
(declare-const x1 Real)
(assert (<= 0.100000 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (= (+ (^ (+ (- (* x0 x3)) (- (* x1 x3)) (* x2 x3) 11.0) 2.0) (^ (+ (* 1.0 x0) (* 10.0 x1) (* (- 1.0) x2) (* 1.0 x3) (* (* x1 x3) (- x2 x0))) 2.0) (- (^ (+ (- (* (* 4.0 x0) x3)) (- (* (* 4.0 x1) x3)) (* x2 x3) 11.0) 2.0)) (- (^ (+ (* 2.0 x0) (* 20.0 x1) (* (- 0.500000) x2) (* 2.0 x3) (* (* (* 2.0 x1) x3) (+ x2 (* (- 4.0) x0)))) 2.0))) 0.0))

(minimize
	(+ (^ (+ (- (* x0 x3)) (- (* x1 x3)) (* x2 x3) 11.0) 2.0) (^ (+ (* 1.0 x0) (* 10.0 x1) (* (- 1.0) x2) (* 1.0 x3) (* (* x1 x3) (- x2 x0))) 2.0))
)
(check-sat)
(get-objectives)
(exit)

