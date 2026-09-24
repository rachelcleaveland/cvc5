; Regression test for InstCycle-Pred (TheorySetsRels::applyInstCyclePatternRule),
; the first inference rule for the fixed-length rel.acyclic-pattern
; predicate: (rel.acyclic-pattern ((t1 T) ... (tl T)) (tuple R1 ... Rk) P)
; is a closure that holds iff no closed walk w1,...,wl over
; R1 U ... U Rk (l = the bound variable list's length) with w1,...,wl
; pairwise distinct satisfies P[w1/t1,...,wl/tl].
;
; This file asserts the negation with P identically false and l = 2:
; InstCycle-Pred must derive (w1,w2) in R, (w2,w1) in R, distinct(w1,w2),
; and P[w1/t1,w2/t2] -- the last of which is immediately contradictory
; since P is always false, so the only possible answer is unsat regardless
; of what R is.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (not (rel.acyclic-pattern ((t1 Atom) (t2 Atom)) (tuple R) false)))
(check-sat)
