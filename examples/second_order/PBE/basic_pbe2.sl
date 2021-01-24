(set-logic BV)

(declare-oracle-fun rand rand ((_ BitVec 32)) (_ BitVec 32))
(declare-oracle-fun reffunction reffunction ((_ BitVec 32)) (_ BitVec 32))

(synth-fun synthfun ((x (_ BitVec 32))) (_ BitVec 32))

(constraint (= (synthfun (rand (_ bv1 32))) (reffunction (rand (_ bv1 32)))))
(constraint (= (synthfun (rand (_ bv2 32))) (reffunction (rand (_ bv2 32)))))
(constraint (= (synthfun (rand (_ bv3 32))) (reffunction (rand (_ bv3 32)))))
(constraint (= (synthfun (rand (_ bv4 32))) (reffunction (rand (_ bv4 32)))))
(constraint (= (synthfun (rand (_ bv5 32))) (reffunction (rand (_ bv5 32)))))
(constraint (= (synthfun (rand (_ bv6 32))) (reffunction (rand (_ bv6 32)))))
(constraint (= (synthfun (rand (_ bv7 32))) (reffunction (rand (_ bv7 32)))))
(constraint (= (synthfun (rand (_ bv8 32))) (reffunction (rand (_ bv8 32)))))
(constraint (= (synthfun (rand (_ bv9 32))) (reffunction (rand (_ bv9 32)))))
(constraint (= (synthfun (rand (_ bv10 32))) (reffunction (rand (_ bv10 32)))))

(check-synth)