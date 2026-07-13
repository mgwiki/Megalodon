(certificate vampire-megalodon 1
  (problem "native-cert-v1-cnf-literal-valid")
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
