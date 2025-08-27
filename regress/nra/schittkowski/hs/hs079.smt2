(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)

(assert (= (+ (* 1.0 x0) (+ (^ x1 2.0) (^ x2 3.0))) 6.242641))
(assert (= (+ (* 1.0 x1) (* 1.0 x4) (- (^ x2 2.0))) 0.828427))
(assert (= (* x0 x3) 2.0))

(minimize
	(+ (^ (+ (- 1.0) x0) 2.0) (^ (- x0 x1) 2.0) (^ (- x1 x2) 2.0) (^ (- x2 x4) 4.0) (^ (- x4 x3) 4.0))
)
(check-sat)
(get-objectives)
(exit)

