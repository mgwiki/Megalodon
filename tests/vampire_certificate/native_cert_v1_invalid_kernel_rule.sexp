(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-kernel-rule")
  (step_extra "c3" "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=bogus_macro_rule"
     "conclusion_unit=c3"))
  (input c1 (source axiom "p")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "not-p")
    (clause
      (neg (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
