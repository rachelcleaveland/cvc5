; The predicate of rel.cyclic-pattern may be a declared function instead of a
; lambda. InstCycle-Patt then concludes the application (P w1 w2) for fresh
; w1, w2, which contradicts the quantified formula.
(set-logic HO_ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-fun P (Atom Atom) Bool)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (rel.cyclic-pattern P R))
(assert (forall ((x Atom) (y Atom)) (not (P x y))))
(check-sat)
