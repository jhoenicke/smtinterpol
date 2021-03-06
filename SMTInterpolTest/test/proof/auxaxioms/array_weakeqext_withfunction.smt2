(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :interactive-mode true)

(set-logic QF_AUFLIA)
(declare-sort U 0)
(declare-fun i1 () U)
(declare-fun i2 () U)
(declare-fun i3 () U)
(declare-fun v1 () U)
(declare-fun v2 () U)
(declare-fun v3 () U)
(declare-fun f (U) U)
(declare-fun a () (Array U U))
(declare-fun b () (Array U U))
(declare-fun c () (Array U U))
(declare-fun d () (Array U U))
(assert (= b (store a i1 v1)))
(assert (= c (store b (f i2) v2)))
(assert (= d (store c (f i3) v3)))
(assert (= (select a i1) (select d i1)))
(assert (= (select a (f i2)) (select d (f i2))))
(assert (= i2 i3))
(assert (not (= a d)))
(check-sat)
(set-option :print-terms-cse false)
(get-proof)