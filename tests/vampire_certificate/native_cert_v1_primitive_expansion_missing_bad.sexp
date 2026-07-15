(certificate vampire-megalodon 1
  (problem "native-cert-v1-primitive-expansion-missing-bad")
  (step_extra c3 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=unit_resulting_resolution"))
  (input c1 (source axiom "a1")
    (clause
      (pos (TMH "p"))
      (pos (TMH "q"))))
  (input c2 (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "q")))))
  (input c4 (source axiom "a3")
    (clause
      (neg (TMH "q"))))
  (resolve c5
    (parents c3 c4)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c6 c5))
