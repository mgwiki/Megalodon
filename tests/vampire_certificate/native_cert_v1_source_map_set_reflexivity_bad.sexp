(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-set-reflexivity-bad")
  (input c1 (source axiom "set_eq")
    (clause
      (pos
        (AP
          (AP (TMH "=") (TMH "a"))
          (TMH "b")))))
  (input c2 (source axiom "not_set_eq")
    (clause
      (neg
        (AP
          (AP (TMH "=") (TMH "a"))
          (TMH "b")))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
