(set-logic LIA)

(synth-fun inv-f ((x Int) (y Int)) Bool)

(declare-var x Int)
(declare-var y Int)
(declare-var x! Int)
(declare-var y! Int)


(define-fun pre-f ((x Int) (y Int)) Bool
    (and (<= x 1) (>= x 0) (= y (- 3))))
(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (or (and (= x! (- x 1)) (= y! (+ y 2)) (< (- x y) 2)) (and (= x! x) (= y! (+ y 1)) (>= (- x y) 2))))
(define-fun post-f ((x Int) (y Int)) Bool
    (and (<= x 1) (>= y (- 3))))

(constraint (=> (pre-f x y)(inv-f x y)))

(check-synth)

