(declare-const x0 Real)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(declare-const x4 Real)
(declare-const x5 Real)
(declare-const x6 Real)

(assert (<= (+ (* 1.0 x2) (* 5.0 x5) (+ (* 2.0 (^ x0 2.0)) (* 3.0 (^ x1 4.0)) (* 4.0 (^ x3 2.0)))) 127.0))
(assert (<= (+ (* 7.0 x0) (* 3.0 x1) (* 1.0 x3) (* (- 1.0) x5) (* 10.0 (^ x2 2.0))) 282.0))
(assert (<= (+ (* 23.0 x0) (* (- 8.0) x6) (+ (^ x1 2.0) (* 6.0 (^ x4 2.0)))) 196.0))
(assert (<= 0.0 (+ (* (- 5.0) x4) (* 11.0 x6) (+ (* (- 4.0) (^ x0 2.0)) (- (^ x1 2.0)) (* (* 3.0 x0) x1) (* (- 2.0) (^ x2 2.0))))))

(minimize
	(+ (* (- 10.0) x4) (* (- 8.0) x6) (+ (^ (+ (- 10.0) x0) 2.0) (* 5.0 (^ (+ (- 12.0) x1) 2.0)) (^ x2 4.0) (* 3.0 (^ (+ (- 11.0) x3) 2.0)) (* 10.0 (^ x5 6.0)) (* 7.0 (^ x4 2.0)) (^ x6 4.0) (- (* (* 4.0 x4) x6))))
)
(check-sat)
(get-objectives)
(exit)

