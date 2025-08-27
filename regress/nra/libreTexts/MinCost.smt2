; https://math.libretexts.org/Courses/Mount_Royal_University/MATH_1200%3A_Calculus_for_Scientists_I/3%3A_Applications_of_Derivatives/3.6%3A_Applied_Optimization_Problems -> 3.6.1
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= x 0))
(assert (<= x 5000))
(assert (> y 0))
(assert (> (- y (* 50 (- 5000 x))) 0)) ; note that this condition is must ... for square may lose +/-
(assert (=  (* (- y (* 50 (- 5000 x))) (- y (* 50 (- 5000 x)))) (* (* 130 130) (+ (* x x) (* 1000 1000)))))
(minimize y)
(check-sat)
(get-objectives)
(exit)
