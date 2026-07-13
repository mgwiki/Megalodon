(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-definition-valid")
  (input c1 (source definition "d1")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
