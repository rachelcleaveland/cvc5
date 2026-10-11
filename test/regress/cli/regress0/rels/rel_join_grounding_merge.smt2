; REQUIRES: no-safe-mode
; REQUIRES: no-stable-mode
; COMMAND-LINE: --rels-acyclic-hammer
; EXPECT: sat
; The join grounding conflict must not refute (a, c) in A;B: b = d justifies it.
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
(check-sat)
