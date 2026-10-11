; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: unsat
; With a, b, c, d distinct, (a, c) in A;B is refuted by the grounding conflict.
(set-logic ALL)
(declare-sort U 0)
(declare-const A (Relation U U))
(declare-const B (Relation U U))
(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(assert (= A (set.singleton (tuple a b))))
(assert (= B (set.singleton (tuple d c))))
(assert (set.member (tuple a c) (rel.join A B)))
(assert (distinct a b c d))
(check-sat)
