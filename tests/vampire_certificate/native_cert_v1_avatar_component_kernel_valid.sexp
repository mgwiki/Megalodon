(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-component-kernel-valid")
  (step_extra c0 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_component"
     "result_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "literal_count=1"
     "literal_0=(pos (TMH \"p\"))"
     "split_0_level=0"
     "split_0_var=1"
     "split_0_positive=1"
     "split_count=1"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=c0"
     "primitive_expansion_requires=avatar_component"
     "conclusion_unit=c0"
     "conclusion_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "result_literal_count=2"
     "result_literal_0=(pos (TMH \"p\"))"
     "result_literal_1=(neg (TMH \"split_1\"))"
     "parent_count=0"))
  (avatar_component c0
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (input s1 (source axiom "split_1_active")
    (clause
      (pos (TMH "split_1"))))
  (resolve r1
    (parents c0 s1)
    (pivot 1 0)
    (result
      (clause
        (pos (TMH "p")))))
  (input np (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (resolve r2
    (parents r1 np)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c1 r2))
