(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (and a b))
(assert (or c d))
(assert (not (or c (and a b d))))
(check-sat)
(exit)
