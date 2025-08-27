(declare-const x0 Real)
(assert (<= (- 0.480000) x0))
(declare-const x1 Real)
(assert (<= (- 0.480000) x1))
(declare-const x2 Real)
(assert (<= 0.0 x2))
(declare-const x3 Real)
(assert (<= 0.0 x3))

(assert (= (+ (* 1.0 x2) (+ (* (- 1000.0) (sin (+ (- 0.250000) (- x0)))) (* (- 1000.0) (sin (+ (- 0.250000) (- x1)))))) 894.800000))
(assert (= (+ (* 1.0 x3) (+ (* (- 1000.0) (sin (+ (- 0.250000) x0))) (* (- 1000.0) (sin (+ (- 0.250000) (- x0 x1)))))) 894.800000))
(assert (= (+ (* 1000.0 (sin (+ (- 0.250000) x1))) (* 1000.0 (sin (+ (- 0.250000) (- x1 x0))))) (- 1294.800000)))
(assert (let ((.def_0 (+ (* (- 1.0) x0) (* 1.0 x1)))) (and (<= (- 0.480000) .def_0)(<= .def_0 0.480000))))

(minimize
	(+ (* 3.0 x2) (* 2.0 x3) (+ (* 0.000001 (^ x2 3.0)) (* 0.000001 (^ x3 3.0))))
)
(check-sat)
(get-objectives)
(exit)

