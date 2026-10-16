; The predicate of rel.cyclic-pattern may be a declared function instead of a
; lambda. AcyclicDown-Patt then concludes the negated application
; (not (P w1 w2)) for each closed walk w1, w2 over R; here the walk a, b
; contradicts (P a b).
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun a () Atom)
(declare-fun b () Atom)
(declare-fun P (Atom Atom) Bool)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (distinct a b))
(assert (= R (set.union (set.singleton (tuple a b))
                        (set.singleton (tuple b a)))))
(assert (P a b))
(assert (not (rel.cyclic-pattern P R)))
(check-sat)
