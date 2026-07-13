(certificate vampire-megalodon 1
  (problem "native-cert-v1-skolem-bogus-shape-bad")
  (formula_term_input f0 (source axiom "exists_p")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (AP
          (TMH "vLAM")
          (AP (TMH "p") (TMH "X0"))))))
  (skolem_formula f1
    (parent f0)
    (subst ("X0" (TMH "sk")))
    (result
      (formula
        (AP (TMH "q") (TMH "sk")))))
  (cnf_formula_clause c1
    (parent f1)
    (index 0)
    (result
      (clause
        (pos (AP (TMH "q") (TMH "sk"))))))
  (input c2 (source axiom "neg_q")
    (clause
      (neg (AP (TMH "q") (TMH "sk")))))
  (resolve r1
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction done r1))
