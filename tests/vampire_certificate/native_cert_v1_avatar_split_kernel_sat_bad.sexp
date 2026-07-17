(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-split-kernel-sat-bad")
  (step_extra s0 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_split"
     "source_unit=a0"
     "source_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_2\")))"
     "parent_0_unit=a0"
     "parent_0_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_2\")))"
     "previous_split_count=0"
     "sat_literal_0_var=99"
     "sat_literal_0_positive=1"
     "sat_literal_count=1"
     "component_parent_ref_0_unit=d0"
     "component_parent_ref_0_split_level=0"
     "component_parent_ref_0_split_var=2"
     "component_parent_ref_0_split_positive=1"
     "component_parent_ref_0_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_2\")))"
     "component_parent_ref_count=1"
     "component_parent_count=1"
     "literal_class_0_literal_count=1"
     "literal_class_0_literal_0=p"
     "literal_class_0_matched_split_level=0"
     "literal_class_count=1"
     "parent_var_binding_count=0"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=s0"
     "primitive_expansion_requires=avatar_split"
     "conclusion_unit=s0"
     "vampire_rule=avatar split clause"
     "parent_count=1"))
  (avatar_component a0
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_2")))))
  (avatar_definition d0
    (split 2 true)
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_2")))))
  (avatar_split s0
    (parents a0 d0)
    (result
      (clause
        (pos (TMH "split_1")))))
  (avatar_contradiction k0
    (parents s0)
    (result
      (clause
        (neg (TMH "split_1")))))
  (avatar_refutation r0
    (parents s0 k0)
    (sat_clauses
      (sat_clause (lit 1 true))
      (sat_clause (lit 1 false)))
    (sat_proof
      (sat_input 1 (sat_clause (lit 1 true)))
      (sat_input 2 (sat_clause (lit 1 false)))
      (sat_rup 3
        (parents 1 2)
        (result
          (sat_clause))))
    (result
      (clause)))
  (contradiction c0 r0))
