(certificate vampire-megalodon 1
  (problem "native-cert-v1-factoring-kernel-missing-other-bad")
  (input "u1" (source axiom "dup_p")
    (clause
      (pos (TMH "p"))
      (pos (TMH "p"))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=factoring" "primitive_expansion=prefix" "primitive_expansion_prefix=u2" "primitive_expansion_requires=factor" "conclusion_unit=u2" "selected=(pos (TMH \"p\"))" "selected_substituted=(pos (TMH \"p\"))" "selected_parent_index=0" "selected_literal_index=0" "selected_parent_unit=u1" "other_substituted=(pos (TMH \"p\"))" "other_parent_index=0" "other_literal_index=1" "other_parent_unit=u1" "primitive_parent_0_substitution=(subst)" "result_clause=(clause (pos (TMH \"p\")))" "conclusion_clause=(clause (pos (TMH \"p\")))" "result_literal_count=1"))
  (factor "u2"
    (parent "u1")
    (literals 0 1)
    (result
      (clause
        (pos (TMH "p")))))
  (input "u3" (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u5" "u4"))
