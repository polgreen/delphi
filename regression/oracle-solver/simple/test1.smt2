(set-logic BV)

(declare-fun x () (_ BitVec 8))

(define-fun add ((x(_ BitVec 8))(y (_ BitVec 8))) (_ BitVec 8)
(bvadd x y)
)

(assert  (= (add x (_ bv0 8)) (_ bv20 8)))
(check-sat)
(get-model)