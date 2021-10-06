; COMMAND-LINE: --arith-idl-ext
(set-logic QF_IDL)
(set-info :source |Example for Formal Techniques Summer School May 23, 2016 by
Clark Barrett
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (- x y) 5))
(assert (>= (- z y) 2))
(assert (> (- z x) 2))
(assert (= (- w x) 2))
(assert (< (- z w) 0))
(check-sat)
