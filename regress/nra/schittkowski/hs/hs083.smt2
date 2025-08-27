(declare-const x0 Real)
(assert (<= 78.0 x0))
(declare-const x1 Real)
(assert (<= 27.0 x1))
(declare-const x2 Real)
(assert (<= 27.0 x2))
(declare-const x3 Real)
(assert (<= 33.0 x3))
(declare-const x4 Real)
(assert (<= 27.0 x4))

(assert (let ((.def_0 (+ (* (* 0.005686 x3) x2) (* (* 0.000626 x0) x4) (- (* (* 0.002205 x1) x2))))) (and (<= (- 85.334407) .def_0)(<= .def_0 6.665593))))
(assert (let ((.def_0 (+ (* (* 0.007132 x3) x2) (* (* 0.002995 x0) x3) (* 0.002181 (^ x1 2.0))))) (and (<= 9.487510 .def_0)(<= .def_0 29.487510))))
(assert (let ((.def_0 (+ (* (* 0.004703 x1) x2) (* (* 0.001255 x0) x1) (* (* 0.001909 x1) x4)))) (and (<= 10.699039 .def_0)(<= .def_0 15.699039))))

(minimize
	(+ (* 37.293239 x0) (+ (* 5.357855 (^ x1 2.0)) (* (* 0.835689 x0) x2) (- 40792.141000)))
)
(check-sat)
(get-objectives)
(exit)

