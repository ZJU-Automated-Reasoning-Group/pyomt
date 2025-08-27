(declare-const x0 Real)
(declare-const x1 Real)

(assert (= (+ (* 4.0 x0) (* (- 3.0) x1)) 0.0))

(minimize
	(* (sin (* 0.261799 x0)) (cos (* 0.196349 x1)))
)
(check-sat)
(get-objectives)
(exit)

