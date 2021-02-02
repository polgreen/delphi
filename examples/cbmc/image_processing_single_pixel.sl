(set-logic BV)

(synth-fun tweak ((pixel (_ BitVec 8))) (_ BitVec 8))

(declare-oracle-fun pixel_average ./pixel_average.sh ((-> (_ BitVec 8) (_ BitVec 8))) (_ BitVec 8))

(constraint (= (pixel_average tweak) (_ bv120 8)))

(constraint (= (tweak (_ bv0 8)) (_ bv20 8)))
(constraint (= (tweak (_ bv10 8)) (_ bv30 8)))

(check-synth)
