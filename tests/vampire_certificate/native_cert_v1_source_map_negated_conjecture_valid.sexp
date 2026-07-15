(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-negated-conjecture-valid")
  (formula_input c1 (source negated_conjecture "ng")
    (neg (TMH "p")))
  (cnf_literal c2
    (parent c1)
    (result
      (clause
        (neg (TMH "p")))))
  (input c3 (source axiom "p_ax")
    (clause
      (pos (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
