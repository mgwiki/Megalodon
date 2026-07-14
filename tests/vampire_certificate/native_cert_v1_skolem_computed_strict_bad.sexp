(certificate vampire-megalodon 1
  (problem "native-cert-v1-skolem-computed-strict-bad")
  (formula_term_input f0 (source axiom "exists_eq")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (LAM
          (SET)
          (AP
            (AP
              (TMH "=")
              (AP (TMH "g") (TMH "X0")))
            (TMH "y"))))))
  (skolem_formula_computed f1
    (parent f0)
    (subst ("X0" (TMH "sk"))))
  (cnf_formula_clause c1
    (parent f1)
    (index 0)
    (result
      (clause
        (pos
          (AP
            (AP
              (TMH "=")
              (TMH "y"))
            (AP (TMH "g") (TMH "sk")))))))
  (input c2 (source axiom "neg_eq")
    (clause
      (neg
        (AP
          (AP
            (TMH "=")
            (TMH "y"))
          (AP (TMH "g") (TMH "sk"))))))
  (resolve r1
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction done r1))
