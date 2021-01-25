(set-logic LIA)

(synth-fun max ((x Int) (y Int)) Int
    ((Start Int (x
                 y
                 0
                 1
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))

(declare-var x Int)
(declare-var y Int)
(declare-oracle-fun myoracle max-corr ((-> Int Int Int)) Bool)

(constraint (>= (max x y) x))
(constraint (>= (max x y) y))
(constraint (myoracle max))

(oracle-constraint max-pos () ((x Int)(y Int)(z Int))
(= (max x y) z)
)


(check-synth)

