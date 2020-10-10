; org.apache.commons.lang3.StringUtils
; public static String chomp(final String str)

; inputs
(declare-var |str.size| Int)
(declare-var |str| (Array Int Int))

; helper
(define-fun ends_on_cr_or_lf
  (
    (|str| (Array Int Int))
    (|str.size| Int)

  ) Bool
  (or
    (and (>= |str.size| 1) (= (select |str| (- |str.size| 1)) 13))
    (and (>= |str.size| 1) (= (select |str| (- |str.size| 1)) 10))
  )
)

(define-fun ends_on_crlf
  (
    (|str| (Array Int Int))
    (|str.size| Int)

  ) Bool
  (and
    (>= |str.size| 2)
    (= (select |str| (- |str.size| 2)) 13)
    (= (select |str| (- |str.size| 1)) 10)
  )
)

; sketch
; (synth-fun |hole-char|
;   (
;     (|i| Int)
;     (|str.size| Int)
;     (|str| (Array Int Int))
;   )
;   Int)

; (define-fun |return|
;   (
;     (|i| Int)
;     (|str.size| Int)
;     (|str| (Array Int Int))
;   )
;   Int
;   (|hole-char| |i| |str.size| |str|))

(synth-fun |hole-size|
  (
    (|str.size| Int)
    (|str| (Array Int Int))
  )
  Int)
; ((I Int) (B Bool)(C Bool))
; ((I Int (0 2 1 (ite B I I)
; (- I)
; (+ I I)
; str.size 
; (select str str.size)
; (select str 0)
; (select str 1)
; ))
; (B Bool ((ends_on_cr_or_lf str str.size) (ends_on_crlf str str.size)
;   (and B B) (or B B) (not B) (and C C) (or C C)))
; (C Bool ((= I I) (<= I I) (>= I I)
; ))
; )) 



(define-fun |return.size|
  (
    (|str.size| Int)
    (|str| (Array Int Int))
  )
  Int
  (|hole-size| |str.size| |str|))

; precondition
(define-fun pre 
  (
    (|str.size| Int)
    (|str| (Array Int Int))
  )
  Bool
  true)


; postcondition when string ends on newline

; (constraint (=>
;   (and (pre |str.size| |str| ) (ends_on_cr_or_lf |str| |str.size|))
;   (= (|return.size| |str.size| |str|)
;     (- |str.size|
;       (ite (ends_on_crlf  |str| |str.size|) 2 1)
;     ))))


(constraint (ite (ends_on_crlf  |str| |str.size|)
(= (|return.size| |str.size| |str|) (- |str.size| 2))
(= (|return.size| |str.size| |str|)(- |str.size| 1))

))

; (constraint (=>
;   (and (pre |str.size| |str|) (ends_on_cr_or_lf |str| |str.size|))
;   (forall ((index Int))
;     (=>
;       (and (>= index 0) (< index (|return.size| |str.size| |str|)))
;       (= (|return| index |str.size| |str|) (select |str| index))
;     )
;   ))
; )

; postcondition when string does not end on newline

; (constraint (=>
;   (and (pre |str.size| |str| ) (not (ends_on_cr_or_lf |str| |str.size|)))
;   (= (|return.size| |str.size| |str|) |str.size|)))

; (constraint (=>
;   (and (pre |str.size| |str| ) (not (ends_on_cr_or_lf |str| |str.size|)))
;   (forall ((index Int)) (= (|return| index |str.size| |str|) (select |str| index)))))

(check-synth)
