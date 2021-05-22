(set-logic BV)

(synth-fun mysin ((x (_ BitVec 8))) (_ BitVec 8))

(declare-var x (_ BitVec 8))
(declare-oracle-fun sin_oracle ./sin_oracle8bits ((_ BitVec 8)) (_ BitVec 8))

(constraint (= (mysin x) (sin_oracle x)))

(check-synth)
