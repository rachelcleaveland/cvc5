; Regression test for AcyclicDown-Patt (TheorySetsRels::checkAcyclicPatternDown
; / searchAcyclicPatternWalks / fireAcyclicPatternDown): the second
; inference rule for rel.cyclic-pattern, which searches a known-false
; (not (rel.cyclic-pattern ((t1 T) (t2 T)) R P)) atom's relation for closed
; walks of length l = 2 and fires NOT P[w1/t1,w2/t2] for each one found.
;
; R is pinned to two disjoint, concrete 2-cycles: a<->b and c<->d. P is true
; only for a walk starting at c, so it is only the c<->d cycle that
; contradicts the (not (rel.cyclic-pattern ...)) assertion -- this exercises
; that the search correctly considers every starting node in the graph (not
; just the first one it happens to try), and that the specific pair found is
; substituted for t1,t2, not some other pair.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun d () Atom)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (distinct a b c d))
(assert (= R (set.union (set.singleton (tuple a b))
             (set.union (set.singleton (tuple b a))
             (set.union (set.singleton (tuple c d))
                        (set.singleton (tuple d c)))))))
(assert (not (rel.cyclic-pattern ((t1 Atom) (t2 Atom)) R (= t1 c))))
(check-sat)
