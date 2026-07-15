(certificate vampire-megalodon 1
  (problem "native-cert-v1-equality-factoring-primitive-valid")
  (input "u1" (source axiom "two_equalities")
    (clause
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b")))
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "c")))))
  (equality_factoring "u2"
    (parent "u1")
    (selected 0)
    (other 1)
    (subst)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "a")) (TMH "c")))
        (neg (AP (AP (TMH "=") (TMH "b")) (TMH "c")))))))
