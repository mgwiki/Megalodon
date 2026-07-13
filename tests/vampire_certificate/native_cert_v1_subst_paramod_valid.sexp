(certificate vampire-megalodon 1
  (problem "native-cert-v1-subst-paramod-valid")
  (input c1 (source axiom "eq")
    (clause
      (pos (AP (AP (TMH "=") (AP (TMH "f") (TMH "X"))) (TMH "b")))))
  (input c2 (source axiom "pa")
    (clause
      (pos (AP (TMH "p") (AP (TMH "f") (TMH "a"))))))
  (input c3 (source axiom "nb")
    (clause
      (neg (AP (TMH "p") (TMH "b")))))
  (substitute c4
    (parent c1)
    (subst
      ("X" (TMH "a")))
    (result
      (clause
        (pos (AP (AP (TMH "=") (AP (TMH "f") (TMH "a"))) (TMH "b"))))))
  (paramodulate c5
    (equality c4 0)
    (target c2 0)
    (position 1)
    (from (AP (TMH "f") (TMH "a")))
    (to (TMH "b"))
    (result
      (clause
        (pos (AP (TMH "p") (TMH "b"))))))
  (resolve c6
    (parents c5 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c7 c6))
