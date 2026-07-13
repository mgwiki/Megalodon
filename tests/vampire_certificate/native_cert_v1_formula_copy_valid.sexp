(certificate vampire-megalodon 1
  (problem "native-cert-v1-formula-copy-valid")
  (formula_term_input c1 (source negated_conjecture "neg")
    (formula
      (IMP (TMH "p") (TMH "vampire_false"))))
  (formula_copy c2
    (parent c1)
    (result
      (neg (TMH "p"))))
  (input c3 (source axiom "p")
    (clause
      (pos (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
