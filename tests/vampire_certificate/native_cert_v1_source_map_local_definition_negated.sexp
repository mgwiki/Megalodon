(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-local-definition-negated")
  (formula_input c1 (source negated_conjecture "ldef")
    (pos
      (AP
        (AP (TMH "=") (TMH "d"))
        (TMH "body"))))
  (cnf_literal c2
    (parent c1)
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (TMH "d"))
            (TMH "body"))))))
  (input c3 (source axiom "a2")
    (clause
      (neg
        (AP
          (AP (TMH "=") (TMH "d"))
          (TMH "body")))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
