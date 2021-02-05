(declare-fun x () Int)
(declare-fun x! () Int)
(declare-fun y () Int)
(declare-fun y! () Int)
(define-fun trans-f (( parameter0 Int)( parameter1 Int)( parameter2 Int)( parameter3 Int))
 Bool (or (and (= x! (- x 1)) (= y! (+ y 2)) (< (- x y) 2)) (and (= x! x) (= y! (+ y 1)) (>= (- x y) 2))))
(define-fun inv-f (( parameter0 Int)( parameter1 Int))
 Bool (> parameter1 (ite (> parameter0 1) parameter1 (- 4))))

(assert (and (inv-f x y)(trans-f x y x! y!)(not (inv-f x! y!))))
(check-sat)
(get-model)
