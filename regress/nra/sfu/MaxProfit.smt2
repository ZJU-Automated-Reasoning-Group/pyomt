; https://www.sfu.ca/math-coursenotes/Math%20157%20Course%20Notes/sec_Optimization.html -> 5.8.1
(declare-fun x () Real)
(assert (> x 0))
(maximize (+ (* (- 10000) x x) (* 25000 x) (- 12000)))
(check-sat)
(get-objectives)
(exit)
