(set-logic BV)

(synth-fun invar ((index1 (_ BitVec 32)) (data1 (_ BitVec 32)) (index2 (_ BitVec 32)) (data2 (_ BitVec 32))) Bool)

(declare-oracle-fun array_oracle ./array_oracle ((_ BitVec 32)) (_ BitVec 32))

(declare-var index1 (_ BitVec 32))
(declare-var index2 (_ BitVec 32))

; enforce bounds
(constraint (bvult index1 (_ bv100 32)))
(constraint (bvult index2 (_ bv100 32)))

; invariant must be true for all index1/index2 (within bounds)
(constraint (invar index1 (array_oracle index1) index2 (array_oracle index2)))

(check-synth)
