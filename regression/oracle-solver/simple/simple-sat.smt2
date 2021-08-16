(set-logic BV)

(declare-fun x () (_ BitVec 8))

(declare-oracle-fun add  ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8) ../../../examples/first_order/add8bitsbinary)

(assert (not (= (add x (_ bv0 8)) (_ bv20 8))))
(check-sat)
(get-model)
