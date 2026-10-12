; Regression test for InstCycle-Patt (TheorySetsRels::applyInstCyclePatternRule),
; the first inference rule for the fixed-length rel.cyclic-pattern predicate:
; (rel.cyclic-pattern ((t1 T) ... (tl T)) R P) is a closure that holds iff
; some closed walk w1,...,wl over R (l = the bound variable list's length)
; satisfies P[w1/t1,...,wl/tl].
;
; This file asserts it with P identically false and l = 2: InstCycle-Patt
; must derive (w1,w2) in R, (w2,w1) in R, and P[w1/t1,w2/t2] -- the last of
; which is immediately contradictory since P is always false, so the only
; possible answer is unsat regardless of what R is.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (rel.cyclic-pattern ((t1 Atom) (t2 Atom)) R false))
(check-sat)
