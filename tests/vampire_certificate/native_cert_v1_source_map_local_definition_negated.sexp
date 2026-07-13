(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-local-definition-negated")
  (formula_input c1 (source negated_conjecture "ldef")
    (pos (TMH "p")))
  (cnf_literal c2
    (parent c1)
    (result
      (clause
        (pos (TMH "p")))))
  (input c3 (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
