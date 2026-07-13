(certificate vampire-megalodon 1
  (problem "native-cert-v1-superposition-simultaneous-selected-literal-valid")
  (input eq (source axiom "eq")
    (clause
      (pos (AP (AP (TMH "=") (AP (TMH "f") (TMH "a"))) (TMH "b")))))
  (input target (source axiom "target")
    (clause
      (pos
        (AP
          (AP (TMH "=") (AP (TMH "h") (AP (TMH "f") (TMH "a"))))
          (AP (TMH "k") (AP (TMH "f") (TMH "a")))))))
  (superposition step
    (target target 0)
    (equality eq 0)
    (subst)
    (subst)
    (position 0 1 1)
    (from (AP (TMH "f") (TMH "a")))
    (to (TMH "b"))
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (AP (TMH "h") (TMH "b")))
            (AP (TMH "k") (TMH "b")))))))
  (input neg_target (source axiom "neg_target")
    (clause
      (neg
        (AP
          (AP (TMH "=") (AP (TMH "h") (TMH "b")))
          (AP (TMH "k") (TMH "b"))))))
  (resolve r1
    (parents step neg_target)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c1 r1))
