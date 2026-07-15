(certificate vampire-megalodon 1
  (problem "native-cert-v1-cnf-clause-primitive-contract-missing-bad")
  (step_extra c1 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=cnf_clause"
     "conclusion_unit=c1"))
  (formula_input f1 (source axiom "literal_axiom")
    (pos (AP (TMH "p") (TMH "a"))))
  (cnf_literal c1
    (parent f1)
    (result
      (clause
        (pos (AP (TMH "p") (TMH "a"))))))
  (formula_input f2 (source negated_conjecture "literal_goal")
    (neg (AP (TMH "p") (TMH "a"))))
  (cnf_literal c2
    (parent f2)
    (result
      (clause
        (neg (AP (TMH "p") (TMH "a"))))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
