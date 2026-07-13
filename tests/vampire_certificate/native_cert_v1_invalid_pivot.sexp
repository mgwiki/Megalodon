(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-pivot")
  (input c1 (source axiom "a1")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "a2")
    (clause
      (pos (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause))))
