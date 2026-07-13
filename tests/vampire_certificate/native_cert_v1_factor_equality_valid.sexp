(certificate vampire-megalodon 1
  (problem "native-cert-v1-factor-equality-valid")
  (input c1 (source axiom "dup")
    (clause
      (pos (TMH "p"))
      (pos (TMH "p"))
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "a")))))
  (factor c2
    (parent c1)
    (literals 0 1)
    (result
      (clause
        (pos (TMH "p"))
        (neg (AP (AP (TMH "=") (TMH "a")) (TMH "a"))))))
  (equality_resolution c3
    (parent c2)
    (literal 1)
    (result
      (clause
        (pos (TMH "p"))))))
