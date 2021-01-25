(set-logic BV)

(synth-fun max ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32))

(declare-var x (_ BitVec 32))
(declare-var y (_ BitVec 32))
(declare-oracle-fun myoracle max-io ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(constraint (bvuge (max x y) x))
(constraint (bvuge (max x y) y))
(constraint (= (max (_ bv10 32) (_ bv5 32)) (myoracle (_ bv10 32) (_ bv5 32))))
(constraint (= (max (_ bv7 32) (_ bv9 32))(myoracle (_ bv7 32) (_ bv9 32))))



(check-synth)

