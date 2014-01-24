(set-option :produce-proofs true)
(set-option :print-success false)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (! (= y 0) :named IP_0))
(assert (! (= x 0) :named IP_1))
(assert (! (= x 1) :named IP_2))
(check-sat)
(get-proof)
(exit)
