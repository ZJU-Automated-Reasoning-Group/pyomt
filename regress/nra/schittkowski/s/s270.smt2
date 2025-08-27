(declare-const x0 Real)
(assert (<= 1.0 x0))
(declare-const x1 Real)
(assert (<= 2.0 x1))
(declare-const x2 Real)
(assert (<= 3.0 x2))
(declare-const x3 Real)
(assert (<= 4.0 x3))
(declare-const x4 Real)

(assert (<= (- 34.0) (- (+ (^ x0 2.0) (^ x1 2.0) (^ x2 2.0) (^ x3 2.0) (^ x4 2.0)))))

(minimize
	(+ (* (- 24.0) x0) (* (- 12.0) x1) (* (- 8.0) x2) (* (- 6.0) x3) (+ (* (* (* x0 x1) x2) x3) (- (* (* (* 3.0 x0) x1) x3)) (- (* (* (* 4.0 x0) x1) x2)) (* (* 12.0 x0) x1) (- (* (* x1 x2) x3)) (* (* 3.0 x1) x3) (* (* 4.0 x1) x2) (- (* (* (* 2.0 x0) x2) x3)) (* (* 6.0 x0) x3) (* (* 8.0 x0) x2) (* (* 2.0 x2) x3) (* 1.500000 (^ x4 4.0)) (* (- 5.750000) (^ x4 3.0)) (* 5.250000 (^ x4 2.0)) 24.0))
)
(check-sat)
(get-objectives)
(exit)

