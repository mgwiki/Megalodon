(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-paramod-position")
  (input c1 (source axiom "eq")
    (clause
      (pos (AP (AP (TMH "=") (AP (TMH "f") (TMH "a"))) (TMH "b")))))
  (input c2 (source axiom "pa")
    (clause
      (pos (AP (TMH "p") (AP (TMH "g") (TMH "a"))))))
  (paramodulate c3
    (equality c1 0)
    (target c2 0)
    (position 1)
    (from (AP (TMH "f") (TMH "a")))
    (to (TMH "b"))
    (result
      (clause
        (pos (AP (TMH "p") (TMH "b")))))))
