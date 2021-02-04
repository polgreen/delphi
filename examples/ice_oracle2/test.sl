(set-logic ALL)
(synth-fun inv-f (( parameter0 Int)( parameter1 Int))
 Bool
(( NTbool Bool)(NTnonbool Int)(NTbool Bool))
((NTbool Bool((and NTbool NTbool)(or NTbool NTbool)(not NTbool)(= NTnonbool NTnonbool)(>= NTnonbool NTnonbool)(> NTnonbool NTnonbool)))
(NTnonbool Int(parameter0 parameter1 0 1 2 3 (Constant Int)(+ NTnonbool NTnonbool)(- NTnonbool NTnonbool)(- NTnonbool)(ite NTbool NTnonbool NTnonbool)))

(NTbool Bool((and NTbool NTbool)(or NTbool NTbool)(not NTbool)(= NTnonbool NTnonbool)(>= NTnonbool NTnonbool)(> NTnonbool NTnonbool)))

)
)

(check-synth)
