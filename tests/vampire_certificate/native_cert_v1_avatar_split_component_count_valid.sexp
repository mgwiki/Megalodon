(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-split-component-count-valid")
  (step_extra s0 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_split"
     "source_unit=a0"
     "source_clause=(clause (neg (TMH \"p\")) (neg (TMH \"q\")))"
     "parent_0_unit=a0"
     "parent_0_clause=(clause (neg (TMH \"p\")) (neg (TMH \"q\")))"
     "result_clause=(clause (neg (TMH \"split_1\")) (neg (TMH \"split_2\")))"
     "previous_split_count=0"
     "sat_literal_0_var=1"
     "sat_literal_0_positive=0"
     "sat_literal_1_var=2"
     "sat_literal_1_positive=0"
     "sat_literal_count=2"
     "component_parent_count=2"
     "component_parent_ref_count=0"
     "literal_class_0_literal_count=1"
     "literal_class_0_literal_0=p"
     "literal_class_0_matched_split_level=0"
     "literal_class_1_literal_count=1"
     "literal_class_1_literal_0=q"
     "literal_class_1_matched_split_level=0"
     "literal_class_count=2"
     "parent_var_binding_count=0"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=s0"
     "primitive_expansion_requires=avatar_split"
     "conclusion_unit=s0"
     "vampire_rule=avatar split clause"
     "parent_count=1"
     "parent_0_unit=a0"
     "parent_0_literal_count=2"
     "parent_0_literal_0=(neg (TMH \"p\"))"
     "parent_0_literal_1=(neg (TMH \"q\"))"))
  (input a0 (source axiom "not_p_or_not_q")
    (clause
      (neg (TMH "p"))
      (neg (TMH "q"))))
  (avatar_split s0
    (parents a0)
    (result
      (clause
        (neg (TMH "split_1"))
        (neg (TMH "split_2")))))
  (input s1 (source axiom "split_1_active")
    (clause
      (pos (TMH "split_1"))))
  (input s2 (source axiom "split_2_active")
    (clause
      (pos (TMH "split_2"))))
  (avatar_refutation r0
    (parents s0 s1 s2)
    (sat_clauses
      (sat_clause (lit 1 false) (lit 2 false))
      (sat_clause (lit 1 true))
      (sat_clause (lit 2 true)))
    (sat_proof
      (sat_input 1 (sat_clause (lit 1 false) (lit 2 false)))
      (sat_input 2 (sat_clause (lit 1 true)))
      (sat_input 3 (sat_clause (lit 2 true)))
      (sat_rup 4
        (parents 1 3 2)
        (result
          (sat_clause))))
    (result
      (clause)))
  (contradiction c0 r0))
