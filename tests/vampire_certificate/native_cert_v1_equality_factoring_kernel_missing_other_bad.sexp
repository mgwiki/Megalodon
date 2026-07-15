(certificate vampire-megalodon 1
  (problem "native-cert-v1-equality-factoring-kernel-missing-other-bad")
  (input "u1" (source axiom "two_equalities")
    (clause
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b")))
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "c")))))
  (equality_factoring "u2"
    (parent "u1")
    (selected 0)
    (other 1)
    (subst)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "a")) (TMH "c")))
        (neg (AP (AP (TMH "=") (TMH "b")) (TMH "c"))))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=equality_factoring" "primitive_expansion=prefix" "primitive_expansion_prefix=u2" "primitive_expansion_requires=equality_factoring" "conclusion_unit=u2" "selected=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))" "selected_substituted=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))" "selected_parent_index=0" "selected_literal_index=0" "selected_parent_unit=u1" "other_substituted=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"c\")))" "other_parent_index=0" "other_literal_index=1" "other_parent_unit=u1" "primitive_parent_0_substitution=(subst)" "result_clause=(clause (pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"c\"))) (neg (AP (AP (TMH \"=\") (TMH \"b\")) (TMH \"c\"))))" "conclusion_clause=(clause (pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"c\"))) (neg (AP (AP (TMH \"=\") (TMH \"b\")) (TMH \"c\"))))" "result_literal_count=2"))
  (input "u3" (source axiom "not_a_eq_c")
    (clause
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "c")))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "b")) (TMH "c"))))))
  (input "u5" (source axiom "b_eq_c")
    (clause
      (pos (AP (AP (TMH "=") (TMH "b")) (TMH "c")))))
  (resolve "u6"
    (parents "u4" "u5")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u7" "u6")
)
