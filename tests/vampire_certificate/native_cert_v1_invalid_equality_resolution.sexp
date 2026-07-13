(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-equality-resolution")
  (input c1 (source axiom "neq")
    (clause
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "b")))))
  (equality_resolution c2
    (parent c1)
    (literal 0)
    (result
      (clause))))
