(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 1.200000 x1))
(declare-const x2 Real)
(assert (<= 20.0 x2))
(declare-const x3 Real)
(assert (<= 9.0 x3))
(declare-const x4 Real)
(assert (<= 6.500000 x4))

(assert (<= 0.0 (* (+ (- 326669.510400) (* 7390.684120 x1) (* (- 27.898698) x2) (* 16643.076000 x3) (* 30988.146000 x4)) x0)))
(assert (<= (- 277200.0) (- (* (+ (- 326669.510400) (* 7390.684120 x1) (* (- 27.898698) x2) (* 16643.076000 x3) (* 30988.146000 x4)) x0))))

(minimize
	(+ (* (+ 8720288.849000 (* (- 150512.525300) x1) (* 156.695032 x2) (* (- 476470.322200) x3) (* (- 729482.827100) x4)) x0) 24345.0)
)
(check-sat)
(get-objectives)
(exit)

