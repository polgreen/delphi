(set-logic BV)
(declare-var x (_ BitVec 32))

(declare-oracle-fun rand rand ((x (_ BitVec 32))) (_ BitVec 32))
(declare-oracle-fun reffunction reffunction ((x (_ BitVec 32))) (_ BitVec 32))

(synth-fun synthfun ((x (_ BitVec 32))) (_ BitVec 32))

(constraint (=> (and (< 0 x)(>= 10 x))(= (synthfun (rand x)) (reffun (rand x)))))
(check-synth)