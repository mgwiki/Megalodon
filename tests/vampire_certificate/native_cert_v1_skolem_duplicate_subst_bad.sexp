(certificate vampire-megalodon 1
  (problem "native-cert-v1-skolem-duplicate-subst-bad")
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
  (skolem_formula f1
    (parent f0)
    (subst
      ("X0" (TMH "sk1"))
      ("X0" (TMH "sk2")))
    (result
      (formula
        (AP
          (AP
            (TMH "=")
            (TMH "y"))
          (AP (TMH "g") (TMH "sk1"))))))
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
            (AP (TMH "g") (TMH "sk1")))))))
  (input c2 (source axiom "neg_eq")
    (clause
      (neg
        (AP
          (AP
            (TMH "=")
            (TMH "y"))
          (AP (TMH "g") (TMH "sk1"))))))
  (resolve r1
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction done r1))
