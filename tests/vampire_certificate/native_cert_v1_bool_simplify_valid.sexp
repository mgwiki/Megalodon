(certificate vampire-megalodon 1
  (problem "native-cert-v1-bool-simplify-valid")
  (input c1 (source axiom "bool_simplify_target")
    (clause
      (neg
        (AP
          (AP (TMH "=")
            (AP (AP (TMH "vOR") (TMH "f__false")) (TMH "x")))
          (TMH "x")))))
  (bool_simplify c2
    (parent c1)
    (literal 0)
    (position 0 1)
    (from (AP (AP (TMH "vOR") (TMH "f__false")) (TMH "x")))
    (to (TMH "x"))
    (result
      (clause
        (neg
          (AP
            (AP (TMH "=") (TMH "x"))
            (TMH "x"))))))
  (equality_resolution c3
    (parent c2)
    (literal 0)
    (result
      (clause)))
  (contradiction c4 c3))
