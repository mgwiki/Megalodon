(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-lambda-not-valid")
  (formula_term_input f0 (source axiom "lambda_not")
    (formula
      (AP
        (AP
          (TMH "=")
          (TMH "infinite"))
        (LAMV "X0" (SET)
          (IMP
            (AP (TMH "finite") (TMH "X0"))
            (TMH "vampire_false"))))))
  (fool_formula f1
    (parent f0)
    (result
      (formula
        (AP
          (AP
            (TMH "=")
            (TMH "infinite"))
          (AP
            (TMH "vLAM")
            (AP
              (TMH "vNOT")
              (AP (TMH "finite") (TMH "db0"))))))))
  (cnf_literal c1
    (parent f1)
    (result
      (clause
        (pos
          (AP
            (AP
              (TMH "=")
              (TMH "infinite"))
            (AP
              (TMH "vLAM")
              (AP
                (TMH "vNOT")
                (AP (TMH "finite") (TMH "db0")))))))))
  (input n1 (source axiom "not_lambda_not")
    (clause
      (neg
        (AP
          (AP
            (TMH "=")
            (TMH "infinite"))
          (AP
            (TMH "vLAM")
            (AP
              (TMH "vNOT")
              (AP (TMH "finite") (TMH "db0"))))))))
  (resolve r1
    (parents c1 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r1))
