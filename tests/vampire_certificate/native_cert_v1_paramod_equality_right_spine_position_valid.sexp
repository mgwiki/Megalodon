(certificate vampire-megalodon 1
  (problem "native-cert-v1-paramod-equality-right-spine-position-valid")
  (input c1 (source axiom "eq")
    (clause
      (pos (AP (AP (TMH "=") (AP (TMH "f") (TMH "a"))) (TMH "b")))))
  (input c2 (source axiom "target")
    (clause
      (pos
        (AP
          (AP (TMH "=") (AP (TMH "g") (TMH "x")))
          (AP (AP (TMH "f") (TMH "a")) (TMH "x"))))))
  (paramodulate c3
    (equality c1 0)
    (target c2 0)
    (position 0 1 0)
    (from (AP (TMH "f") (TMH "a")))
    (to (TMH "b"))
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (AP (TMH "g") (TMH "x")))
            (AP (TMH "b") (TMH "x")))))))
  (input c4 (source axiom "neg_target")
    (clause
      (neg
        (AP
          (AP (TMH "=") (AP (TMH "g") (TMH "x")))
          (AP (TMH "b") (TMH "x"))))))
  (resolve c5
    (parents c3 c4)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c6 c5))
