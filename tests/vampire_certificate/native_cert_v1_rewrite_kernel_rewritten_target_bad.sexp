(certificate vampire-megalodon 1
  (problem "native-cert-v1-rewrite-kernel-rewritten-target-bad")
  (step_extra step "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=rewrite"
     "rule_lhs=(TMH \"a\")"
     "redex=(TMH \"a\")"
     "rule_rhs=(TMH \"b\")"
     "replacement=(TMH \"b\")"
     "replay_rule_lhs=(TMH \"a\")"
     "replay_rule_rhs=(TMH \"b\")"
     "replay_redex=(TMH \"a\")"
     "replay_replacement=(TMH \"b\")"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=step"
     "primitive_expansion_requires=paramodulate"
     "conclusion_unit=step"
     "equality_substituted=(pos (AP (AP (TMH \"=\") (TMH \"a\")) (TMH \"b\")))"
     "equality_parent_index=1"
     "equality_literal_index=0"
     "from=(TMH \"a\")"
     "to=(TMH \"b\")"
     "target_parent_index=0"
     "target_literal_index=0"
     "rewrite_position=(position 0 1 1)"
     "target_substituted=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "rewritten_target=(pos (AP (AP (TMH \"=\") (AP (TMH \"h\") (TMH \"a\"))) (TMH \"c\")))"
     "parent_count=2"
     "parent_0_unit=target"
     "parent_0_substitution=(subst)"
     "parent_1_unit=eq"
     "parent_1_substitution=(subst)"
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
  (paramodulate step
    (equality eq 0)
    (target target 0)
    (position 0 1 1)
    (from (TMH "a"))
    (to (TMH "b"))
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (AP (TMH "h") (TMH "b")))
            (TMH "c")))))))
