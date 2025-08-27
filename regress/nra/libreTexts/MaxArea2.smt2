; https://math.libretexts.org/Courses/Mount_Royal_University/MATH_1200%3A_Calculus_for_Scientists_I/3%3A_Applications_of_Derivatives/3.6%3A_Applied_Optimization_Problems -> 3.6.2
(declare-fun x () Real)
(assert (>= x 0))
(assert (<= x 50))
(maximize (+ (* 50 x) (* (- (/ 1 2)) x x)))
(check-sat)
(get-objectives)
(exit)
