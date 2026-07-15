(certificate vampire-megalodon 1
  (problem "native-cert-v1-equality-resolution-kernel-valid")
  (input "u1" (source axiom "not-refl")
    (clause
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "a")))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=equality_resolution" "selected=(neg (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"a\")))" "selected_parent_index=0" "selected_literal_index=0" "selected_parent_unit=u1" "selected_substituted=(neg (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"a\")))" "primitive_expansion=prefix" "primitive_expansion_prefix=u2" "primitive_expansion_requires=equality_resolution" "conclusion_unit=u2" "vampire_rule=trivial inequality removal" "conclusion_clause=(clause)" "result_clause=(clause)" "result_literal_count=0" "parent_count=1" "parent_0_unit=u1" "parent_0_clause=(clause (neg (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"a\"))))" "parent_0_literal_count=1" "parent_0_literal_0=(neg (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"a\")))"))
  (equality_resolution "u2"
    (parent "u1")
    (literal 0)
    (result
      (clause)))
  (contradiction "u3" "u2"))
