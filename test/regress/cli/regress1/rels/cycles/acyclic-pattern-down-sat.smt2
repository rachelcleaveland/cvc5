; Companion to acyclic-pattern-down-unsat.smt2: same two disjoint 2-cycles
; a<->b and c<->d, but P is true only for a walk starting at e, an atom not
; part of either cycle. Neither cycle satisfies P, so AcyclicDown-Pred finds
; no contradiction and the acyclic-pattern assertion is satisfiable --
; confirms the search does not produce false positives for cycles that do
; not actually satisfy P.
;
; DISABLE-TESTER: model
; rel.acyclic-pattern has no ground-model evaluation yet (see
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
(assert (distinct a b c d e))
(assert (= R (set.union (set.singleton (tuple a b))
             (set.union (set.singleton (tuple b a))
             (set.union (set.singleton (tuple c d))
                        (set.singleton (tuple d c)))))))
(assert (rel.acyclic-pattern ((t1 Atom) (t2 Atom)) (tuple R) (= t1 e)))
(check-sat)
