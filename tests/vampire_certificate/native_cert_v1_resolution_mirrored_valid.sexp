(certificate vampire-megalodon 1
  (problem "native-cert-v1-resolution-mirrored-valid")
  (input c1 (source axiom "p")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "not-p-or-q")
    (clause
      (neg (TMH "p"))
      (pos (TMH "q"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "q")))))
  (input c4 (source axiom "not-q")
    (clause
      (neg (TMH "q"))))
  (resolve c5
    (parents c3 c4)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c6 c5))
