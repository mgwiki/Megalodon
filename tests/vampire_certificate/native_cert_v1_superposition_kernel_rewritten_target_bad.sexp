(certificate vampire-megalodon 1
  (problem "native-cert-v1-superposition-kernel-rewritten-target-bad")
  (step_extra step "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=superposition"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=step"
     "primitive_expansion_requires=paramodulate"
     "conclusion_unit=step"
     "selected=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "selected_substituted=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "selected_parent_index=0"
     "selected_literal_index=0"
     "selected_parent_unit=target"
     "other=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))"
     "other_substituted=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))"
     "other_parent_index=1"
     "other_literal_index=0"
     "other_parent_unit=eq"
     "target_substituted=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "equality_substituted=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))"
     "target_parent_index=0"
     "target_literal_index=0"
     "equality_parent_index=1"
     "equality_literal_index=0"
     "rewrite_position=(position 0 1 1)"
     "from=(TMH \"a\")"
     "to=(TMH \"b\")"
     "rewritten_target=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "primitive_parent_0_substitution=(subst)"
     "primitive_parent_1_substitution=(subst)"
     "parent_count=2"
     "parent_0_unit=target"
     "parent_1_unit=eq"
     "result_clause=(clause (pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"b\"))) (TMH \"c\"))))"
     "conclusion_clause=(clause (pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"b\"))) (TMH \"c\"))))"
     "result_literal_count=1"))
  (definition_input eq
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b"))))))
  (definition_input target
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (AP (TMH "h") (TMH "a")))
            (TMH "c"))))))
  (superposition step
    (target target 0)
    (equality eq 0)
    (subst)
    (subst)
    (position 0 1 1)
    (from (TMH "a"))
    (to (TMH "b"))
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (AP (TMH "h") (TMH "b")))
            (TMH "c")))))))
