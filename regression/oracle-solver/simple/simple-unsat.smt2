(set-logic BV)

(declare-fun x () (_ BitVec 8))

(declare-oracle-fun add ../../../examples/first_order/add8bitsbinary ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))

(assert (not (= (add x (_ bv0 8)) x)))
(check-sat)
