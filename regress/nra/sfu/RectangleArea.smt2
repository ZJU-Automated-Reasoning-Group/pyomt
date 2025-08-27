; https://www.sfu.ca/math-coursenotes/Math%20157%20Course%20Notes/sec_Optimization.html -> 5.8.7
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0))
(assert (= (+ (* 2 x x) 200 (- (* x y))) 0))
(minimize y)
(check-sat)
(get-objectives)
(exit)
