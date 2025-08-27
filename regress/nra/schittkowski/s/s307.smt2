(declare-const x0 Real)
(assert (<= 0.0 x0))
(declare-const x1 Real)
(assert (<= 0.0 x1))


(minimize
	(+ (^ (- 4.0 (+ (exp x0) (exp x1))) 2.0) (^ (- 6.0 (+ (exp (* 2.0 x0)) (exp (* 2.0 x1)))) 2.0) (^ (- 8.0 (+ (exp (* 3.0 x0)) (exp (* 3.0 x1)))) 2.0) (^ (- 10.0 (+ (exp (* 4.0 x0)) (exp (* 4.0 x1)))) 2.0) (^ (- 12.0 (+ (exp (* 5.0 x0)) (exp (* 5.0 x1)))) 2.0) (^ (- 14.0 (+ (exp (* 6.0 x0)) (exp (* 6.0 x1)))) 2.0) (^ (- 16.0 (+ (exp (* 7.0 x0)) (exp (* 7.0 x1)))) 2.0) (^ (- 18.0 (+ (exp (* 8.0 x0)) (exp (* 8.0 x1)))) 2.0) (^ (- 20.0 (+ (exp (* 9.0 x0)) (exp (* 9.0 x1)))) 2.0) (^ (- 22.0 (+ (exp (* 10.0 x0)) (exp (* 10.0 x1)))) 2.0))
)
(check-sat)
(get-objectives)
(exit)

