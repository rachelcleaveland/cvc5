; Companion to acyclic-pattern-inst-cycle-unsat.smt2: same InstCycle-Patt
; derivation (l = 2), but P refers to a relation S that is not part of R,
; and R is pinned to two disjoint 2-cycles a<->b and c<->d rather than left
; unconstrained -- exercises that InstCycle-Patt picks its witness pair from
; R to satisfy the edge conjuncts, while P's truth is entirely independent
; of R, driven by S.
;
; DISABLE-TESTER: model
; rel.cyclic-pattern has no ground-model evaluation yet (see
; acyclic-pattern-inst-cycle-sat.smt2's comment for the same, pre-existing
; gap).
(set-logic ALL)
(set-info :status sat)
(declare-sort Atom 0)
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun c () Atom)
(declare-fun d () Atom)
(declare-fun e () Atom)
(declare-fun R () (Set (Tuple Atom Atom)))
(declare-fun S () (Set (Tuple Atom Atom)))
(assert (distinct a b c d e))
(assert (= R (set.union (set.singleton (tuple a b))
             (set.union (set.singleton (tuple b a))
             (set.union (set.singleton (tuple c d))
                        (set.singleton (tuple d c)))))))
(assert (rel.cyclic-pattern ((t1 Atom) (t2 Atom)) R (set.member (tuple t1 t2) S)))
(check-sat)
