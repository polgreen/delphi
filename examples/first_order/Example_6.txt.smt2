(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
  Christoph Erkinger, "Rotating Workforce Scheduling as Satisfiability Modulo
  Theories", Master's Thesis, Technische Universitaet Wien, 2013
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun shift0 () (_ BitVec 49))
(declare-fun shift1 () (_ BitVec 49))
(declare-fun shift2 () (_ BitVec 49))
(declare-fun shift3 () (_ BitVec 49))
(assert (and (= (bvand shift0 shift1) (_ bv0 49)) (= (bvand shift0 shift2) (_ bv0 49)) (= (bvand shift0 shift3) (_ bv0 49)) (= (bvand shift1 shift2) (_ bv0 49)) (= (bvand shift1 shift3) (_ bv0 49)) (= (bvand shift2 shift3) (_ bv0 49)) ))
(assert (= (bvnot (_ bv0 49)) (bvor shift0  (bvor shift1  (bvor shift2  shift3 ) ) ) ))
; ==== Temporal Requirements ====
;
;
(declare-oracle-fun bitsumhelper bitsumhelperbinary7 ((_ BitVec 7)) (_ BitVec 7))
;(define-fun bitsumhelper ((x (_ BitVec 7))) (_ BitVec 7) (bvand x (bvsub x (_ bv1 7))))
;
(assert (= (_ bv0 7)  (concat ((_ extract 0 0) shift1)  (concat ((_ extract 7 7) shift1)  (concat ((_ extract 14 14) shift1)  (concat ((_ extract 21 21) shift1)  (concat ((_ extract 28 28) shift1)  (concat ((_ extract 35 35) shift1)  ((_ extract 42 42) shift1)  ) ) ) ) ) ) ))
; =========================
(assert (= (_ bv0 7)  (concat ((_ extract 0 0) shift2)  (concat ((_ extract 7 7) shift2)  (concat ((_ extract 14 14) shift2)  (concat ((_ extract 21 21) shift2)  (concat ((_ extract 28 28) shift2)  (concat ((_ extract 35 35) shift2)  ((_ extract 42 42) shift2)  ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 0 0) shift3)  (concat ((_ extract 7 7) shift3)  (concat ((_ extract 14 14) shift3)  (concat ((_ extract 21 21) shift3)  (concat ((_ extract 28 28) shift3)  (concat ((_ extract 35 35) shift3)  ((_ extract 42 42) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 0 0) shift3)  (concat ((_ extract 7 7) shift3)  (concat ((_ extract 14 14) shift3)  (concat ((_ extract 21 21) shift3)  (concat ((_ extract 28 28) shift3)  (concat ((_ extract 35 35) shift3)  ((_ extract 42 42) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 1 1) shift1)  (concat ((_ extract 8 8) shift1)  (concat ((_ extract 15 15) shift1)  (concat ((_ extract 22 22) shift1)  (concat ((_ extract 29 29) shift1)  (concat ((_ extract 36 36) shift1)  ((_ extract 43 43) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift1)  (concat ((_ extract 8 8) shift1)  (concat ((_ extract 15 15) shift1)  (concat ((_ extract 22 22) shift1)  (concat ((_ extract 29 29) shift1)  (concat ((_ extract 36 36) shift1)  ((_ extract 43 43) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 1 1) shift2)  (concat ((_ extract 8 8) shift2)  (concat ((_ extract 15 15) shift2)  (concat ((_ extract 22 22) shift2)  (concat ((_ extract 29 29) shift2)  (concat ((_ extract 36 36) shift2)  ((_ extract 43 43) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift2)  (concat ((_ extract 8 8) shift2)  (concat ((_ extract 15 15) shift2)  (concat ((_ extract 22 22) shift2)  (concat ((_ extract 29 29) shift2)  (concat ((_ extract 36 36) shift2)  ((_ extract 43 43) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (= (_ bv0 7)  (concat ((_ extract 1 1) shift3)  (concat ((_ extract 8 8) shift3)  (concat ((_ extract 15 15) shift3)  (concat ((_ extract 22 22) shift3)  (concat ((_ extract 29 29) shift3)  (concat ((_ extract 36 36) shift3)  ((_ extract 43 43) shift3)  ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 2 2) shift1)  (concat ((_ extract 9 9) shift1)  (concat ((_ extract 16 16) shift1)  (concat ((_ extract 23 23) shift1)  (concat ((_ extract 30 30) shift1)  (concat ((_ extract 37 37) shift1)  ((_ extract 44 44) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift1)  (concat ((_ extract 9 9) shift1)  (concat ((_ extract 16 16) shift1)  (concat ((_ extract 23 23) shift1)  (concat ((_ extract 30 30) shift1)  (concat ((_ extract 37 37) shift1)  ((_ extract 44 44) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 2 2) shift2)  (concat ((_ extract 9 9) shift2)  (concat ((_ extract 16 16) shift2)  (concat ((_ extract 23 23) shift2)  (concat ((_ extract 30 30) shift2)  (concat ((_ extract 37 37) shift2)  ((_ extract 44 44) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift2)  (concat ((_ extract 9 9) shift2)  (concat ((_ extract 16 16) shift2)  (concat ((_ extract 23 23) shift2)  (concat ((_ extract 30 30) shift2)  (concat ((_ extract 37 37) shift2)  ((_ extract 44 44) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 2 2) shift3)  (concat ((_ extract 9 9) shift3)  (concat ((_ extract 16 16) shift3)  (concat ((_ extract 23 23) shift3)  (concat ((_ extract 30 30) shift3)  (concat ((_ extract 37 37) shift3)  ((_ extract 44 44) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift3)  (concat ((_ extract 9 9) shift3)  (concat ((_ extract 16 16) shift3)  (concat ((_ extract 23 23) shift3)  (concat ((_ extract 30 30) shift3)  (concat ((_ extract 37 37) shift3)  ((_ extract 44 44) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 3 3) shift1)  (concat ((_ extract 10 10) shift1)  (concat ((_ extract 17 17) shift1)  (concat ((_ extract 24 24) shift1)  (concat ((_ extract 31 31) shift1)  (concat ((_ extract 38 38) shift1)  ((_ extract 45 45) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift1)  (concat ((_ extract 10 10) shift1)  (concat ((_ extract 17 17) shift1)  (concat ((_ extract 24 24) shift1)  (concat ((_ extract 31 31) shift1)  (concat ((_ extract 38 38) shift1)  ((_ extract 45 45) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 3 3) shift2)  (concat ((_ extract 10 10) shift2)  (concat ((_ extract 17 17) shift2)  (concat ((_ extract 24 24) shift2)  (concat ((_ extract 31 31) shift2)  (concat ((_ extract 38 38) shift2)  ((_ extract 45 45) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift2)  (concat ((_ extract 10 10) shift2)  (concat ((_ extract 17 17) shift2)  (concat ((_ extract 24 24) shift2)  (concat ((_ extract 31 31) shift2)  (concat ((_ extract 38 38) shift2)  ((_ extract 45 45) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 3 3) shift3)  (concat ((_ extract 10 10) shift3)  (concat ((_ extract 17 17) shift3)  (concat ((_ extract 24 24) shift3)  (concat ((_ extract 31 31) shift3)  (concat ((_ extract 38 38) shift3)  ((_ extract 45 45) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift3)  (concat ((_ extract 10 10) shift3)  (concat ((_ extract 17 17) shift3)  (concat ((_ extract 24 24) shift3)  (concat ((_ extract 31 31) shift3)  (concat ((_ extract 38 38) shift3)  ((_ extract 45 45) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 4 4) shift1)  (concat ((_ extract 11 11) shift1)  (concat ((_ extract 18 18) shift1)  (concat ((_ extract 25 25) shift1)  (concat ((_ extract 32 32) shift1)  (concat ((_ extract 39 39) shift1)  ((_ extract 46 46) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift1)  (concat ((_ extract 11 11) shift1)  (concat ((_ extract 18 18) shift1)  (concat ((_ extract 25 25) shift1)  (concat ((_ extract 32 32) shift1)  (concat ((_ extract 39 39) shift1)  ((_ extract 46 46) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 4 4) shift2)  (concat ((_ extract 11 11) shift2)  (concat ((_ extract 18 18) shift2)  (concat ((_ extract 25 25) shift2)  (concat ((_ extract 32 32) shift2)  (concat ((_ extract 39 39) shift2)  ((_ extract 46 46) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift2)  (concat ((_ extract 11 11) shift2)  (concat ((_ extract 18 18) shift2)  (concat ((_ extract 25 25) shift2)  (concat ((_ extract 32 32) shift2)  (concat ((_ extract 39 39) shift2)  ((_ extract 46 46) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 4 4) shift3)  (concat ((_ extract 11 11) shift3)  (concat ((_ extract 18 18) shift3)  (concat ((_ extract 25 25) shift3)  (concat ((_ extract 32 32) shift3)  (concat ((_ extract 39 39) shift3)  ((_ extract 46 46) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift3)  (concat ((_ extract 11 11) shift3)  (concat ((_ extract 18 18) shift3)  (concat ((_ extract 25 25) shift3)  (concat ((_ extract 32 32) shift3)  (concat ((_ extract 39 39) shift3)  ((_ extract 46 46) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 5 5) shift1)  (concat ((_ extract 12 12) shift1)  (concat ((_ extract 19 19) shift1)  (concat ((_ extract 26 26) shift1)  (concat ((_ extract 33 33) shift1)  (concat ((_ extract 40 40) shift1)  ((_ extract 47 47) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift1)  (concat ((_ extract 12 12) shift1)  (concat ((_ extract 19 19) shift1)  (concat ((_ extract 26 26) shift1)  (concat ((_ extract 33 33) shift1)  (concat ((_ extract 40 40) shift1)  ((_ extract 47 47) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 5 5) shift2)  (concat ((_ extract 12 12) shift2)  (concat ((_ extract 19 19) shift2)  (concat ((_ extract 26 26) shift2)  (concat ((_ extract 33 33) shift2)  (concat ((_ extract 40 40) shift2)  ((_ extract 47 47) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift2)  (concat ((_ extract 12 12) shift2)  (concat ((_ extract 19 19) shift2)  (concat ((_ extract 26 26) shift2)  (concat ((_ extract 33 33) shift2)  (concat ((_ extract 40 40) shift2)  ((_ extract 47 47) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 5 5) shift3)  (concat ((_ extract 12 12) shift3)  (concat ((_ extract 19 19) shift3)  (concat ((_ extract 26 26) shift3)  (concat ((_ extract 33 33) shift3)  (concat ((_ extract 40 40) shift3)  ((_ extract 47 47) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift3)  (concat ((_ extract 12 12) shift3)  (concat ((_ extract 19 19) shift3)  (concat ((_ extract 26 26) shift3)  (concat ((_ extract 33 33) shift3)  (concat ((_ extract 40 40) shift3)  ((_ extract 47 47) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 6 6) shift1)  (concat ((_ extract 13 13) shift1)  (concat ((_ extract 20 20) shift1)  (concat ((_ extract 27 27) shift1)  (concat ((_ extract 34 34) shift1)  (concat ((_ extract 41 41) shift1)  ((_ extract 48 48) shift1)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift1)  (concat ((_ extract 13 13) shift1)  (concat ((_ extract 20 20) shift1)  (concat ((_ extract 27 27) shift1)  (concat ((_ extract 34 34) shift1)  (concat ((_ extract 41 41) shift1)  ((_ extract 48 48) shift1)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 6 6) shift2)  (concat ((_ extract 13 13) shift2)  (concat ((_ extract 20 20) shift2)  (concat ((_ extract 27 27) shift2)  (concat ((_ extract 34 34) shift2)  (concat ((_ extract 41 41) shift2)  ((_ extract 48 48) shift2)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift2)  (concat ((_ extract 13 13) shift2)  (concat ((_ extract 20 20) shift2)  (concat ((_ extract 27 27) shift2)  (concat ((_ extract 34 34) shift2)  (concat ((_ extract 41 41) shift2)  ((_ extract 48 48) shift2)  ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 7)  (bitsumhelper  (concat ((_ extract 6 6) shift3)  (concat ((_ extract 13 13) shift3)  (concat ((_ extract 20 20) shift3)  (concat ((_ extract 27 27) shift3)  (concat ((_ extract 34 34) shift3)  (concat ((_ extract 41 41) shift3)  ((_ extract 48 48) shift3)  ) ) ) ) ) ) ) )))
(assert (= (_ bv0 7)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift3)  (concat ((_ extract 13 13) shift3)  (concat ((_ extract 20 20) shift3)  (concat ((_ extract 27 27) shift3)  (concat ((_ extract 34 34) shift3)  (concat ((_ extract 41 41) shift3)  ((_ extract 48 48) shift3)  ) ) ) ) ) ) ) ) ))
; =========================
; ==== Length of workblocks ====
;
(declare-fun noncyclic_workblocks () (_ BitVec 98))
(declare-fun workblocks_justTrailingOnes () (_ BitVec 49))
(declare-fun workblocks_withoutTrailingOnes () (_ BitVec 49))
(declare-fun workblock_helper () (_ BitVec 98))
(assert (= workblocks_justTrailingOnes (bvnot (bvneg (bvxor shift0 (bvand shift0 (bvsub shift0 (_ bv1 49)))))) ))
(assert (= workblocks_withoutTrailingOnes (bvxor (bvnot shift0) (bvnot (bvneg (bvxor shift0 (bvand shift0 (bvsub shift0 (_ bv1 49))))))) ))
(assert (= noncyclic_workblocks (concat workblocks_justTrailingOnes workblocks_withoutTrailingOnes )))
(assert (= workblock_helper (bvand noncyclic_workblocks  (bvand (bvlshr noncyclic_workblocks (_ bv1 98)) (bvand (bvlshr noncyclic_workblocks (_ bv2 98)) (bvlshr noncyclic_workblocks (_ bv3 98)) ) ) )))
(assert (= noncyclic_workblocks (bvor workblock_helper  (bvor (bvshl workblock_helper (_ bv1 98)) (bvor (bvshl workblock_helper (_ bv2 98)) (bvshl workblock_helper (_ bv3 98)) ) ) )))
(assert (= (bvand noncyclic_workblocks  (bvand (bvlshr noncyclic_workblocks (_ bv1 98)) (bvand (bvlshr noncyclic_workblocks (_ bv2 98)) (bvand (bvlshr noncyclic_workblocks (_ bv3 98)) (bvand (bvlshr noncyclic_workblocks (_ bv4 98)) (bvand (bvlshr noncyclic_workblocks (_ bv5 98)) (bvand (bvlshr noncyclic_workblocks (_ bv6 98)) (bvlshr noncyclic_workblocks (_ bv7 98)) ) ) ) ) ) ) )(_ bv0 98)))
; ==== length of blocks of consecutive shifts ====
;
(assert (= (bvand (concat shift0 shift0)  (bvand (bvlshr (concat shift0 shift0) (_ bv1 98)) (bvand (bvlshr (concat shift0 shift0) (_ bv2 98)) (bvand (bvlshr (concat shift0 shift0) (_ bv3 98)) (bvlshr (concat shift0 shift0) (_ bv4 98)) ) ) ) )(_ bv0 98)))
(declare-fun noncyclic_shift1 () (_ BitVec 98))
(declare-fun shift1_justTrailingOnes () (_ BitVec 49))
(declare-fun shift1_withoutTrailingOnes () (_ BitVec 49))
(assert (= shift1_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift1) (bvand (bvnot shift1) (bvsub (bvnot shift1) (_ bv1 49)))))) ))
(assert (= shift1_withoutTrailingOnes (bvxor shift1 (bvnot (bvneg (bvxor (bvnot shift1) (bvand (bvnot shift1) (bvsub (bvnot shift1) (_ bv1 49))))))) ))
(assert (= noncyclic_shift1 (concat shift1_justTrailingOnes shift1_withoutTrailingOnes )))
(declare-fun shift1_helper () (_ BitVec 98))
(assert (= shift1_helper (bvand noncyclic_shift1  (bvlshr noncyclic_shift1 (_ bv1 98)) )))
(assert (= noncyclic_shift1 (bvor shift1_helper  (bvshl shift1_helper (_ bv1 98)) )))
(assert (= (bvand (concat shift1 shift1)  (bvand (bvlshr (concat shift1 shift1) (_ bv1 98)) (bvand (bvlshr (concat shift1 shift1) (_ bv2 98)) (bvand (bvlshr (concat shift1 shift1) (_ bv3 98)) (bvand (bvlshr (concat shift1 shift1) (_ bv4 98)) (bvand (bvlshr (concat shift1 shift1) (_ bv5 98)) (bvlshr (concat shift1 shift1) (_ bv6 98)) ) ) ) ) ) )(_ bv0 98)))
(declare-fun noncyclic_shift2 () (_ BitVec 98))
(declare-fun shift2_justTrailingOnes () (_ BitVec 49))
(declare-fun shift2_withoutTrailingOnes () (_ BitVec 49))
(assert (= shift2_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift2) (bvand (bvnot shift2) (bvsub (bvnot shift2) (_ bv1 49)))))) ))
(assert (= shift2_withoutTrailingOnes (bvxor shift2 (bvnot (bvneg (bvxor (bvnot shift2) (bvand (bvnot shift2) (bvsub (bvnot shift2) (_ bv1 49))))))) ))
(assert (= noncyclic_shift2 (concat shift2_justTrailingOnes shift2_withoutTrailingOnes )))
(declare-fun shift2_helper () (_ BitVec 98))
(assert (= shift2_helper (bvand noncyclic_shift2  (bvlshr noncyclic_shift2 (_ bv1 98)) )))
(assert (= noncyclic_shift2 (bvor shift2_helper  (bvshl shift2_helper (_ bv1 98)) )))
(assert (= (bvand (concat shift2 shift2)  (bvand (bvlshr (concat shift2 shift2) (_ bv1 98)) (bvand (bvlshr (concat shift2 shift2) (_ bv2 98)) (bvand (bvlshr (concat shift2 shift2) (_ bv3 98)) (bvand (bvlshr (concat shift2 shift2) (_ bv4 98)) (bvand (bvlshr (concat shift2 shift2) (_ bv5 98)) (bvlshr (concat shift2 shift2) (_ bv6 98)) ) ) ) ) ) )(_ bv0 98)))
(declare-fun noncyclic_shift3 () (_ BitVec 98))
(declare-fun shift3_justTrailingOnes () (_ BitVec 49))
(declare-fun shift3_withoutTrailingOnes () (_ BitVec 49))
(assert (= shift3_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift3) (bvand (bvnot shift3) (bvsub (bvnot shift3) (_ bv1 49)))))) ))
(assert (= shift3_withoutTrailingOnes (bvxor shift3 (bvnot (bvneg (bvxor (bvnot shift3) (bvand (bvnot shift3) (bvsub (bvnot shift3) (_ bv1 49))))))) ))
(assert (= noncyclic_shift3 (concat shift3_justTrailingOnes shift3_withoutTrailingOnes )))
(declare-fun shift3_helper () (_ BitVec 98))
(assert (= shift3_helper (bvand noncyclic_shift3  (bvlshr noncyclic_shift3 (_ bv1 98)) )))
(assert (= noncyclic_shift3 (bvor shift3_helper  (bvshl shift3_helper (_ bv1 98)) )))
(assert (= (bvand (concat shift3 shift3)  (bvand (bvlshr (concat shift3 shift3) (_ bv1 98)) (bvand (bvlshr (concat shift3 shift3) (_ bv2 98)) (bvand (bvlshr (concat shift3 shift3) (_ bv3 98)) (bvand (bvlshr (concat shift3 shift3) (_ bv4 98)) (bvand (bvlshr (concat shift3 shift3) (_ bv5 98)) (bvlshr (concat shift3 shift3) (_ bv6 98)) ) ) ) ) ) )(_ bv0 98)))
; ==== not allowed shift sequences ====
;
(assert (= (_ bv0 49) (bvand ((_ rotate_right 1) shift3) shift1)))
(assert (= (_ bv0 49) (bvand ((_ rotate_right 1) shift3) shift2)))
(assert (= (_ bv0 49) (bvand ((_ rotate_right 1) shift2) shift1)))
(assert (= (_ bv0 49) (bvand shift3 ((_ rotate_right 1) (bvand ((_ rotate_right 1) shift3) shift0)))))
(assert (= (_ bv0 49) (bvand shift1 ((_ rotate_right 1) (bvand ((_ rotate_right 1) shift2) shift0)))))
(assert (= (_ bv0 49) (bvand shift2 ((_ rotate_right 1) (bvand ((_ rotate_right 1) shift3) shift0)))))
(assert (= (_ bv0 49) (bvand shift1 ((_ rotate_right 1) (bvand ((_ rotate_right 1) shift3) shift0)))))
(check-sat)
(exit)
