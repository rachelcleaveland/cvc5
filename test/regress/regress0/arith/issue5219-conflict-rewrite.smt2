; REQUIRES: poly
; COMMAND-LINE: --theoryof-mode=term --nl-icp
; EXPECT: unknown
(set-logic QF_NRA)
(set-option :check-proofs true)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (and (< 1 y) (= y (+ x (* x x)))))
(check-sat)
