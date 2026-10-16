; Over R = {(a, b), (b, a), (b, b)} with a != b, the closed walk a -> b -> b -> a
; has length 3 and revisits b. It satisfies (= t1 a), so the negated pattern
; is unsat. The walks of length 3 with distinct elements do not exist here.
(set-logic ALL)
(set-info :status unsat)
(declare-sort Atom 0)
(declare-const a Atom)
(declare-const b Atom)
(declare-const R (Relation Atom Atom))
(assert (distinct a b))
(assert (= R (set.insert (tuple a b) (tuple b a) (set.singleton (tuple b b)))))
(assert (not (rel.cyclic-pattern ((t1 Atom) (t2 Atom) (t3 Atom)) R (= t1 a))))
(check-sat)
