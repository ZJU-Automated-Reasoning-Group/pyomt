(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (* (^ x0 2.0) x2) (sin (- x2 x3))) 1.0))
(assert (= (+ (* 1.0 x4) (* (^ x1 4.0) (^ x2 2.0))) 2.0))

(minimize
	(+ (^ (- x0 x4) 2.0) (^ (+ (- 1.0) x1) 2.0) (^ (+ (- 1.0) x2) 4.0) (^ (+ (- 1.0) x3) 6.0))
)
(check-sat)
(get-objectives)
(exit)

