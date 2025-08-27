(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(declare-const x6 Real)
(declare-const x7 Real)

(assert (= (+ (* 1.0 x3) (- (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0)))) (- 1.0)))
(assert (= (+ (* 1.0 x4) (- (+ (^ x0 2.0) (^ x1 2.0) (^ (+ (- 2.0) x2) 2.0)))) (- 1.0)))
(assert (= (+ (* 1.0 x7) (+ (- (^ x0 3.0)) (* (- 3.0) (^ x1 2.0)) (- (^ (+ 1.0 (- (* 5.0 x2) x0)) 2.0)))) (- 36.0)))
(assert (= (+ (* (- 1.0) x0) (* (- 1.0) x1) (* (- 1.0) x2) (* 1.0 x5)) (- 1.0)))
(assert (= (+ (* (- 1.0) x0) (* (- 1.0) x1) (* 1.0 x2) (* 1.0 x6)) 1.0))

(minimize
	(+ (^ x3 2.0) (^ x4 2.0) (^ x5 2.0) (^ x6 2.0) (^ x7 2.0))
)
(check-sat)
(get-objectives)
(exit)

