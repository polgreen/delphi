; org.apache.commons.lang3.StringUtils
; static String appendIfMissing(final String str, final CharSequence suffix)

; inputs
(declare-var strSize Int)
(declare-var |str| (Array Int Int))
(declare-var suffixSize Int)
(declare-var |suffix| (Array Int Int))
(declare-var index Int)

; helper
(define-fun append
  (
    (strSize Int)
    (|str| (Array Int Int))
    (suffixSize Int)
    (|suffix| (Array Int Int))
  )
  Bool
  (exists ((i Int)) 
    (not (= (select |str| (+ (- strSize suffixSize) i)) (select |suffix| i)))
  ))


; (synth-fun |hole-size|
;   (
;     (strSize Int)
;     (|str| (Array Int Int))
;     (suffixSize Int)
;     (|suffix| (Array Int Int))
;   )
;   Int
;   ((I Int) (B Bool))
;   ((I Int ( 
;     strSize (+ strSize suffixSize)
;     (select str 0)
;     (select str 1)
;     (select str suffixSize)
;     (select str strSize)
;     (select suffix suffixSize)
;     (select suffix strSize)
;     (ite B I I)))
;     (B Bool ((append strSize str suffixSize suffix)))
;   ))



; sketch
(synth-fun |hole-char|
  (
    (index Int)
    (strSize Int)
    (|str| (Array Int Int))
    (suffixSize Int)
    (|suffix| (Array Int Int))
  )
  Int
  )

; postcondition when suffix is appended

; (constraint (ite 
;   (append strSize |str| suffixSize|suffix|)
;   (= (|hole-size| strSize |str| suffixSize|suffix|) (+ strSize suffixSize))
;   (= (|hole-size| strSize |str| suffixSize |suffix|) strSize)))


(constraint (ite
  (and (append strSize |str| suffixSize|suffix|) (<= index strSize)) 
    (= (|hole-char| index strSize |str| suffixSize|suffix|)
    (select |str| index)) 
    (ite (<= index strSize)
    (= (|hole-char| index strSize |str| suffixSize|suffix|)(select |suffix| (- index strSize)))
    (= 1 1))))



  ; (forall ((index Int)) (= (|return| index strSize |str| suffixSize|suffix|)
  ;   (select |str| index)))

; postcondition when suffix is not appended



; (constraint (=>
;   (and (pre strSize |str| |maxWidth|) (not (append strSize |str| suffixSize|suffix|)))
;   (forall ((index Int)) (= (|return| index strSize |str| suffixSize|suffix|)
;     (select |str| index)))))

(check-synth)
