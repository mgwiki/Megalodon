(certificate vampire-megalodon 1
  (problem "native-cert-v1-formula-cnf-vampire-order-valid")
  (formula_term_input f0 (source axiom "dist")
    (formula
      (AP
        (AP
          (TMH "vampire_or")
          (AP
            (AP (TMH "vampire_and") (TMH "a"))
            (TMH "b")))
        (AP
          (AP (TMH "vampire_and") (TMH "c"))
          (TMH "d")))))
  (cnf_formula_clause c1
    (parent f0)
    (index 1)
    (result
      (clause
        (pos (TMH "b"))
        (pos (TMH "c")))))
  (input nb (source axiom "not_b")
    (clause
      (neg (TMH "b"))))
  (resolve r1
    (parents c1 nb)
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "c")))))
  (input nc (source axiom "not_c")
    (clause
      (neg (TMH "c"))))
  (resolve r2
    (parents r1 nc)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r2))
