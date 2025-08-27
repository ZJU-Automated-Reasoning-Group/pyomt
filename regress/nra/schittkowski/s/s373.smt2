(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(declare-const x6 Real)
(declare-const x7 Real)
(declare-const x8 Real)

(assert (= (+ (* 1.0 x2) (* 1.0 x8) (* x0 (exp (* (- 5.0) x1)))) 127.0))
(assert (= (+ (* 1.0 x3) (* 1.0 x8) (* x0 (exp (* (- 3.0) x1)))) 151.0))
(assert (= (+ (* 1.0 x4) (* 1.0 x8) (* x0 (exp (- x1)))) 379.0))
(assert (= (+ (* 1.0 x5) (* 1.0 x8) (* x0 (exp x1))) 421.0))
(assert (= (+ (* 1.0 x6) (* 1.0 x8) (* x0 (exp (* 3.0 x1)))) 460.0))
(assert (= (+ (* 1.0 x7) (* 1.0 x8) (* x0 (exp (* 5.0 x1)))) 426.0))

(minimize
	(+ (^ x2 2.0) (^ x3 2.0) (^ x4 2.0) (^ x5 2.0) (^ x6 2.0) (^ x7 2.0))
)
(check-sat)
(get-objectives)
(exit)

