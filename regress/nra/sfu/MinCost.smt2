; https://www.sfu.ca/math-coursenotes/Math%20157%20Course%20Notes/sec_Optimization.html -> 5.8.2
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ (* 0.0001 x x x) (- (* 0.08 x x)) (* 65 x) 5000 (- (* x y))) 0)) 
(assert (> x 0))
(minimize y)
(check-sat)
(get-objectives)
(exit)
