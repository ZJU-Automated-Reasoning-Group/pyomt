(declare-const x0 Real)
(assert (<= 0.100000 x0))
(declare-const x1 Real)
(declare-const x2 Real)
(assert (<= (- 2.500000) x2))
(declare-const x3 Real)

(assert (= (+ (* 1.0 x3) (- (ite (> x0 0.0) (* 0.159160 (atan (/ x1 x0))) (+ 0.500000 (* 0.159160 (atan (/ x1 x0))))))) 0.0))

(minimize
	(+ (* 100.0 (^ (+ x2 (* (- 10.0) x3)) 2.0)) (* 100.0 (^ (+ (- 1.0) (sqrt (+ (^ x0 2.0) (^ x1 2.0)))) 2.0)) (^ x2 2.0))
)
(check-sat)
(get-objectives)
(exit)

