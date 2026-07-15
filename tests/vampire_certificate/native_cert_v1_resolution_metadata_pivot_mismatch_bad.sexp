(certificate vampire-megalodon 1
  (problem "native-cert-v1-resolution-metadata-pivot-mismatch-bad")
  (step_extra c3 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=resolution"
     "conclusion_unit=c3"
     "selected=(pos (TMH \"p\"))"
     "selected_substituted=(pos (TMH \"p\"))"
     "selected_parent_index=0"
     "selected_literal_index=1"
     "selected_parent_unit=c1"
     "other=(neg (TMH \"p\"))"
     "other_substituted=(neg (TMH \"p\"))"
     "other_parent_index=1"
     "other_literal_index=0"
     "other_parent_unit=c2"
     "primitive_parent_0_substitution=(subst)"
     "primitive_parent_1_substitution=(subst)"
     "result_clause=(clause (pos (TMH \"q\")))"
     "conclusion_clause=(clause (pos (TMH \"q\")))"
     "result_literal_count=1"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=c3"
     "primitive_expansion_requires=resolve"))
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
