; A closed walk may revisit an element: over R = {(a, a)}, a -> a -> a is a
; closed walk of length 2, and it satisfies (= t1 t2). So the pattern holds
; and its negation is unsat. AcyclicDown-Patt used to search only walks with
; distinct elements and accepted a model here.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-const a Atom)
(declare-const R (Relation Atom Atom))
(assert (= R (set.singleton (tuple a a))))
(assert (not (rel.cyclic-pattern ((t1 Atom) (t2 Atom)) R (= t1 t2))))
(check-sat)
