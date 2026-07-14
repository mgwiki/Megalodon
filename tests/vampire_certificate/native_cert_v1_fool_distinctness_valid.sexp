(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-distinctness-valid")
  (input p1 (source axiom "true_eq_false")
    (clause
      (pos (AP (AP (TMH "=") (TMH "f__true")) (TMH "f__false")))))
  (fool_distinctness d1
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "f__true")) (TMH "f__false"))))))
  (resolve c1
    (parents p1 d1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 c1))
