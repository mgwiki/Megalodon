(certificate vampire-megalodon 1
  (problem "native-cert-v1-skolem-application-valid")
  (formula_term_input f0 (source axiom "exists_applied_head")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (LAM
          (AR (SET) (SET))
          (ALL
            (SET)
            (AP
              (AP
                (TMH "=")
                (AP (TMH "X0") (TMH "X1")))
              (TMH "f__true")))))))
  (skolem_formula f1
    (parent f0)
    (subst ("X0" (TMH "sk")))
    (result
      (formula
        (ALL
          (SET)
          (AP
            (AP
              (TMH "=")
              (AP (TMH "sk") (TMH "X1")))
            (TMH "f__true"))))))
  (cnf_formula_clause c1
    (parent f1)
    (index 0)
    (result
      (clause
        (pos
          (AP
            (AP
              (TMH "=")
              (AP (TMH "sk") (TMH "X1")))
            (TMH "f__true"))))))
  (input c2 (source axiom "neg_applied_head")
    (clause
      (neg
        (AP
          (AP
            (TMH "=")
            (AP (TMH "sk") (TMH "X1")))
          (TMH "f__true")))))
  (resolve r1
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction done r1))
