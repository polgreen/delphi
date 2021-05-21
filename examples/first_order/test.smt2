
(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) 
(bvadd x (_ bv10 32)))

(declare-fun x ()(_ BitVec 32))

(declare-oracle-fun rand rand32 ((_ BitVec 32)) (_ BitVec 32))
(declare-oracle-fun reffunction
 add10
((_ BitVec 32)) (_ BitVec 32))


(assert (= (f (rand x)) (reffunction (rand x))))

(check-sat)
(get-model)