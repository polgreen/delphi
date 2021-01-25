(set-logic BV)

(synth-fun max ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32))

(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-oracle-fun myoracle max-corr ((-> (_ BitVec 32) (_ BitVec 32) (_ BitVec 32))) Bool)

(constraint (bvuge (max x y) x))
(constraint (bvuge (max x y) y))
(constraint (myoracle max))

(oracle-constraint max-pos () ((x (_ BitVec 32))(y (_ BitVec 32))(z (_ BitVec 32)))
(= (max x y) z)
)


(check-synth)
