(certificate vampire-megalodon 1
  (problem "native-cert-v1-formula-cnf-valid")
  (formula_term_input f0 (source axiom "imp")
    (formula
      (IMP
        (TMH "p")
        (TMH "q"))))
  (fool_formula f1
    (parent f0)
    (result
      (formula
        (IMP
          (AP (AP (TMH "=") (TMH "p")) (TMH "f__true"))
          (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (ennf_formula f2
    (parent f1)
    (result
      (formula
        (AP
          (AP
            (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "p")) (TMH "f__true"))
              (TMH "vampire_false")))
          (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (cnf_formula_clause c1
    (parent f2)
    (index 0)
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "p")) (TMH "f__true")))
        (pos (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (input p1 (source axiom "p_true")
    (clause
      (pos (AP (AP (TMH "=") (TMH "p")) (TMH "f__true")))))
  (resolve r1
    (parents c1 p1)
    (pivot 0 0)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (input q1 (source axiom "q_false")
    (clause
      (neg (AP (AP (TMH "=") (TMH "q")) (TMH "f__true")))))
  (resolve r2
    (parents r1 q1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r2))
