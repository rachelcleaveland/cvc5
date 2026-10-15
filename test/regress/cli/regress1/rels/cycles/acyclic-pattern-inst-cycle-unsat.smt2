; Regression test for InstCycle-Patt (TheorySetsRels::applyInstCyclePatternRule),
; the first inference rule for the fixed-length rel.cyclic-pattern predicate:
; (rel.cyclic-pattern (lambda ((t1 T) ... (tl T)) P) R) holds iff some
; closed walk w1,...,wl over R (l = the arity of the lambda) satisfies
; P[w1/t1,...,wl/tl].
;
; This file asserts it with P identically false and l = 2: InstCycle-Patt
; must derive (w1,w2) in R, (w2,w1) in R, and P[w1/t1,w2/t2] -- the last of
; which is immediately contradictory since P is always false, so the only
; possible answer is unsat regardless of what R is.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (rel.cyclic-pattern (lambda ((t1 Atom) (t2 Atom)) false) R))
(check-sat)
