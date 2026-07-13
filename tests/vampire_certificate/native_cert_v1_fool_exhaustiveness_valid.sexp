(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-exhaustiveness-valid")
  (fool_exhaustiveness b1
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "f__true")) (TMH "X0")))
        (pos (AP (AP (TMH "=") (TMH "f__false")) (TMH "X0"))))))
  (input n1 (source axiom "not_true")
    (clause
      (neg (AP (AP (TMH "=") (TMH "f__true")) (TMH "X0")))))
  (resolve c1
    (parents b1 n1)
    (pivot 0 0)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "f__false")) (TMH "X0"))))))
  (input n2 (source axiom "not_false")
    (clause
      (neg (AP (AP (TMH "=") (TMH "f__false")) (TMH "X0")))))
  (resolve c2
    (parents c1 n2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c3 c2))
