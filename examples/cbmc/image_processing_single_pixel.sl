(set-logic BV)

(synth-fun tweak ((pixel (_ BitVec 8))) (_ BitVec 8))

(oracle-constraint ./image_processing_single_pixel
  ((tweak (-> (_ BitVec 8) (_ BitVec 8))))
  ((correct Bool) (input (_ BitVec 8)) (expected_output (_ BitVec 8)))
  (=> (not correct) (= (tweak input) expected_output)))

(check-synth)
