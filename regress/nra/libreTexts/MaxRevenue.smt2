; https://math.libretexts.org/Courses/Mount_Royal_University/MATH_1200%3A_Calculus_for_Scientists_I/3%3A_Applications_of_Derivatives/3.6%3A_Applied_Optimization_Problems -> 3.6.6
(declare-fun x () Real)
(assert (>= x 50))
(assert (<= x 200))
(maximize (+ (* (- 5) x x) (* 1000 x)))
(check-sat)
(get-objectives)
(exit)
