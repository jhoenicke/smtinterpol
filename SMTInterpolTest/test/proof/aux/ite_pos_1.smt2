(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)

(set-logic QF_UF)
(declare-sort U 0)
(declare-fun c1 () Bool)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (not q))
(assert p)
(push 1)
(assert (or q (and p (ite c1 a b))))
(assert (not a))
(assert c1)
;(@tautology (! (or (not (! (ite c1 a b) :quoted)) (not c1) a) :ite+1))

(check-sat)
(set-option :print-terms-cse false)
(get-proof)