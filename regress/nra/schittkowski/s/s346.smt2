(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))

(assert (<= (- 675.0) (- (* (^ x0 2.0) x1))))
(assert (<= (- 0.419000) (- (* (* 0.000000 (^ x0 2.0)) (^ x2 2.0)))))

(minimize
	(* 0.000000 (* (* (* (- 0.020100) (^ x0 4.0)) x1) (^ x2 2.0)))
)
(check-sat)
(get-objectives)
(exit)

