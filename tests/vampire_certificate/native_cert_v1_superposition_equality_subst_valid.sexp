(certificate vampire-megalodon 1
  (problem "native-cert-v1-superposition-equality-subst-valid")
  (fool_exhaustiveness b1
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "f__true")) (TMH "X0")))
        (pos (AP (AP (TMH "=") (TMH "f__false")) (TMH "X0"))))))
  (input t1 (source axiom "target")
    (clause
      (neg
        (AP
          (AP (TMH "=") (AP (AP (TMH "In") (TMH "X1")) (TMH "omega")))
          (TMH "f__true")))))
  (superposition c2
    (target t1 0)
    (equality b1 0)
    (subst)
    (subst ("X0" (AP (AP (TMH "In") (TMH "X1")) (TMH "omega"))))
    (position 0 1)
    (from (AP (AP (TMH "In") (TMH "X1")) (TMH "omega")))
    (to (TMH "f__true"))
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "f__true")) (TMH "f__true")))
        (pos (AP (AP (TMH "=") (AP (AP (TMH "In") (TMH "X1")) (TMH "omega"))) (TMH "f__false"))))))
  (equality_resolution c3
    (parent c2)
    (literal 0)
    (result
      (clause
        (pos (AP (AP (TMH "=") (AP (AP (TMH "In") (TMH "X1")) (TMH "omega"))) (TMH "f__false"))))))
  (input n1 (source axiom "neg_result")
    (clause
      (neg (AP (AP (TMH "=") (AP (AP (TMH "In") (TMH "X1")) (TMH "omega"))) (TMH "f__false")))))
  (resolve c4
    (parents c3 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
