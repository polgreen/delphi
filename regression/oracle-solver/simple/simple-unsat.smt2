(set-logic BV)

(declare-fun x () (_ BitVec 8))

(declare-oracle-fun add  ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8) ../../../examples/first_order/add8bitsbinary)

(assert (not (=> (bvult x (_ bv20 8)) (= (add x (_ bv0 8)) x))))
(check-sat)
