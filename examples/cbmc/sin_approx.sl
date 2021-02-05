(set-logic BV)

(synth-fun mysin ((x (_ BitVec 4))) (_ BitVec 4))

(declare-var x (_ BitVec 4))
(declare-oracle-fun sin_oracle sin_oracle ((_ BitVec 4)) (_ BitVec 4))

(constraint (= (mysin x) (sin_oracle x)))

(check-synth)
