(certificate vampire-megalodon 1
  (problem "native-cert-v1-substitute-prop-changed-unsupported")
  (input c1 (source axiom "x")
    (clause
      (pos (TMH "X0"))))
  (substitute c2
    (parent c1)
    (subst ("X0" (TMH "p")))
    (result
      (clause
        (pos (TMH "p")))))
  (input c3 (source axiom "not-p")
    (clause
      (neg (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
