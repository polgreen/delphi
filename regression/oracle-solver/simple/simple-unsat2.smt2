(set-logic BV)

(declare-fun x () (_ BitVec 8))

(declare-oracle-fun add  ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8) ../../../examples/first_order/add8bitsbinary)

(assert (bvugt x (_ bv250 8)))
(assert (not (= (add x (_ bv0 8)) x)))
(assert (not (= (add (bvadd x (_ bv1 8)) (_ bv0 8)) (bvadd x (_ bv1 8)))))
(check-sat)
