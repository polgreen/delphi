(set-logic BV)

; parameter 'x' is not used
(synth-fun my_constant ((x (_ BitVec 8))) (_ BitVec 8))

(declare-oracle-fun myoracle ./constant_oracle ((_ BitVec 8)) Bool)

(constraint (bvult (my_constant (_ bv0 8)) (_ bv10 8)))
(constraint (myoracle (my_constant (_ bv0 8))))

(check-synth)
