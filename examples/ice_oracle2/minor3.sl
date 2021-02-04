(set-logic LIA)

(declare-var x Int)
(declare-var x! Int)
(declare-var y Int)
(declare-var y! Int)

(synth-inv inv-f ((x Int) (y Int)))

(define-fun pre-f ((x Int) (y Int)) Bool
    (and (<= x 5) (>= x 4) (<= y 5) (>= y 4)))
(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (or (and (= x! (- x 1)) (= y! y) (>= x 0) (>= y 0)) (and (= x! x) (= y! (- y 1)) (< x 0) (>= y 0)) (and (= x! (+ x 1)) (= y! (- y 1)) (< y 0))))
(define-fun post-f ((x Int) (y Int)) Bool
    (<= y 5))

(constraint (=> (pre-f x y)(inv-f x y)))
(constraint (=> (and (inv-f x y)(trans-f x y x! y!))(inv-f x! y!)))
(constraint (=> (inv-f x y)(post-f x y)))


(check-synth)

