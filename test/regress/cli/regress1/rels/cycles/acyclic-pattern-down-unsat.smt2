; Regression test for AcyclicDown-Pred (TheorySetsRels::checkAcyclicPatternDown
; / searchAcyclicPatternWalks / fireAcyclicPatternDown): the second
; inference rule for rel.acyclic-pattern, which searches a known-true
; (rel.acyclic-pattern ((t1 T) (t2 T)) (tuple R) P) atom's relation for
; closed walks of length l = 2 and fires NOT P[w1/t1,w2/t2] for each one
; found.
;
; R is pinned to two disjoint, concrete 2-cycles: a<->b and c<->d. P is true
; only for a walk starting at c, so it is only the c<->d cycle that
; contradicts the acyclic-pattern assertion -- this exercises that the
; search correctly considers every starting node in the graph (not just the
; first one it happens to try), and that the specific pair found is
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
(assert (rel.acyclic-pattern ((t1 Atom) (t2 Atom)) (tuple R) (= t1 c)))
(check-sat)
