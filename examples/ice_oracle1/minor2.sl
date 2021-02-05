(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(define-fun pre-f ((x Int) (y Int)) Bool
    (and (> y 0) (= x 0)))
(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (or (and (>= x y) (and (= x! x) (= y! y))) (and (< x y) (and (= x! (+ x 1)) (= y! y)))))
(define-fun post-f ((x Int) (y Int)) Bool
    (=> (>= x y) (= x y)))

(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)

