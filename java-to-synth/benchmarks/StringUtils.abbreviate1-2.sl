; org.apache.commons.lang3.StringUtils
; public static String abbreviate(final String str, final int maxWidth)

; inputs
(declare-var |str.size| Int)
(declare-var |str| (Array Int Int))
(declare-var |maxWidth| Int)
(declare-var index Int)

; sketch
; (synth-fun |hole-char|
;   (
;     (|i| Int)
;     (|str.size| Int)
;     (|str| (Array Int Int))
;     (|maxWidth| Int)
;   )
;   Int)

; (define-fun |return|
;   (
;     (|i| Int)
;     (|str.size| Int)
;     (|str| (Array Int Int))
;     (|maxWidth| Int)
;   )
;   Int
;   (|hole-char| |i| |str.size| |str| |maxWidth|))

(synth-fun |hole-size|
  (
    (|str.size| Int)
    (|str| (Array Int Int))
    (|maxWidth| Int)
  )
  Int)


; precondition
(define-fun pre 
  (
    (|str.size| Int)
    (|str| (Array Int Int))
    (|maxWidth| Int)
  )
  Bool
  (>= |maxWidth| 4))

; postcondition when string is short

(constraint (=>
  (and (pre |str.size| |str| |maxWidth|) (<= |str.size| |maxWidth|))
  (= (|hole-size| |str.size| |str| |maxWidth|) |str.size|)))



; postcondition when string is long

(constraint (=>
  (and (pre |str.size| |str| |maxWidth|) (> |str.size| |maxWidth|))
  (= (|hole-size| |str.size| |str| |maxWidth|) |maxWidth|)))

; (constraint (=>
;   (and (pre |str.size| |str| |maxWidth|) 
;     (<= |str.size| |maxWidth|))
;     (ite (<= index (- |str.size| 4)) 
;       (= (|return| index |str.size| |str| |maxWidth|)(select |str| index) )
;       (= (|return| index |str.size| |str| |maxWidth|) 46))))



(check-synth)
