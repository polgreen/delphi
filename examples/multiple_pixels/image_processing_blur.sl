(set-logic BV)

(synth-fun tweak ((p00 (_ BitVec 8))(p01 (_ BitVec 8))) (_ BitVec 8))

; abusing pixel_oracle.sh both for 'correctness' and 'hints'

; correctness (verification)
(declare-oracle-fun pixel_correct ./pixel_oracle_blur.sh ((-> (_ BitVec 8)(_ BitVec 8) (_ BitVec 8))) Bool)

(constraint (pixel_correct tweak))

; hints (synthesis)
(oracle-constraint
  ./pixel_oracle_blur.sh
  ((tweak (-> (_ BitVec 8)(_ BitVec 8)(_ BitVec 8))))
  ((correct Bool) (p00 (_ BitVec 8))(p01 (_ BitVec 8))(pixelOut (_ BitVec 8)))
  (=> (not correct) (= (tweak p00 p01 ) pixelOut)))

(check-synth)
