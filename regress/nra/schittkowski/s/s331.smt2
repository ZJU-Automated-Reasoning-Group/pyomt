(declare-const x0 Real)
(assert (<= 0.000100 x0))
(declare-const x1 Real)
(assert (<= 0.000100 x1))

(assert (<= (- 1.0) (+ (* (- 1.0) x0) (* (- 1.0) x1))))

(minimize
	(* (/ 1.0 x0) (log (/ (* 2.0 (log x1)) (log (+ x0 x1)))))
)
(check-sat)
(get-objectives)
(exit)

