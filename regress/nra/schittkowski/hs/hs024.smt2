(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))

(assert (<= 0.0 (+ (* 0.577350 x0) (* (- 1.0) x1))))
(assert (<= (- 6.0) (+ (* (- 1.0) x0) (* (- 1.732051) x1))))

(minimize
	(* 0.021383 (* (+ (- 9.0) (^ (+ (- 3.0) x0) 2.0)) (^ x1 3.0)))
)
(check-sat)
(get-objectives)
(exit)

