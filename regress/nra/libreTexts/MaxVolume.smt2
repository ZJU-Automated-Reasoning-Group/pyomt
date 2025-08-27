; https://math.libretexts.org/Courses/Mount_Royal_University/MATH_1200%3A_Calculus_for_Scientists_I/3%3A_Applications_of_Derivatives/3.6%3A_Applied_Optimization_Problems -> 3.6.4
(declare-fun x () Real)
(assert (> x 0))
(assert (< x 12))
(maximize (+ (* 4 x x x) (* (- 120) x x) (* 864 x)))
(check-sat)
(get-objectives)
(exit)
