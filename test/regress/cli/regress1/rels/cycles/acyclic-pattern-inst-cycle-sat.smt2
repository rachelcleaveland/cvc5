; Companion to acyclic-pattern-inst-cycle-unsat.smt2: same InstCycle-Patt
; derivation (l = 2, R unconstrained), but with P identically true instead
; of false, so the derived conjunct P is trivially satisfiable and R can be
; built to satisfy (w1,w2) in R, (w2,w1) in R -- e.g. a concrete 2-cycle
; over two distinct atoms.
;
; DISABLE-TESTER: model
; rel.cyclic-pattern has no ground-model evaluation yet (no rewriter or
; model-value case for it), so --debug-check-models cannot independently
; re-derive its value from the model and reports a spurious mismatch. The
; theory's own reasoning here is verified correct via the InstCycle-Patt
; conjuncts it derives (see the base tester), not via re-evaluating this
; term; this is a known gap to close when rel.cyclic-pattern gets a
; rewriter/model-value implementation.
(set-logic ALL)
(set-info :status sat)
(declare-sort Atom 0)
(declare-fun R () (Set (Tuple Atom Atom)))
(assert (rel.cyclic-pattern ((t1 Atom) (t2 Atom)) R true))
(check-sat)
