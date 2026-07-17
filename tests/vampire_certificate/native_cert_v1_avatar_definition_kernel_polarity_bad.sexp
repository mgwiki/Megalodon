(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-definition-kernel-polarity-bad")
  (step_extra d0 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_definition"
     "component_split_level=0"
     "component_split_var=1"
     "component_split_positive=0"
     "component_clause=(p) \\/ ((split_1) -> vampire_false)"
     "component_clause_sexpr=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "component_clause_variable_sort_count=0"
     "component_clause_db_sort_count=0"
     "result_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=d0"
     "primitive_expansion_requires=avatar_definition"
     "conclusion_unit=d0"
     "vampire_rule=avatar definition"
     "parent_count=0"))
  (avatar_definition d0
    (split 1 true)
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (avatar_split s0
    (parents d0)
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
