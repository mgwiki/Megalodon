(certificate vampire-megalodon 1
  (problem "native-cert-v1-substitute-prop-noop-valid")
  (input c1 (source axiom "p")
    (clause
      (pos (TMH "p"))))
  (substitute c2
    (parent c1)
    (subst)
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
