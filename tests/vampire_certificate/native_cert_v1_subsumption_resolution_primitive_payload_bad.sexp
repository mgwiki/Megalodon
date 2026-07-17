(certificate vampire-megalodon 1
  (problem "native-cert-v1-subsumption-resolution-primitive-payload-bad")
  (input "u1" (source axiom "pq")
    (clause
      (pos (TMH "p"))
      (pos (TMH "q"))))
  (input "u2" (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (step_extra "u3" "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=subsumption_resolution"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=u3"
     "primitive_expansion_requires=resolve"
     "primitive_expansion_final_result_clause=(clause (pos (TMH \"q\")))"
     "primitive_expansion_step_count=1"
     "primitive_expansion_step_0_rule=resolve"
     "primitive_expansion_step_0_id=u3_resolve_0"
     "primitive_expansion_step_0_parent_count=2"
     "primitive_expansion_step_0_parent_0_id=u1"
     "primitive_expansion_step_0_parent_1_id=u2"
     "primitive_expansion_step_0_result_clause=(clause (pos (TMH \"q\")))"
     "primitive_expansion_step_0_pivot_left=1"
     "primitive_expansion_step_0_pivot_right=0"
     "primitive_expansion_requires_count=1"
     "primitive_expansion_requires_0=resolve"
     "conclusion_unit=u3"
     "selected=(pos (TMH \"p\"))"
     "selected_substituted=(pos (TMH \"p\"))"
     "selected_parent_index=0"
     "selected_literal_index=0"
     "selected_parent_unit=u1"
     "main_parent_index=0"
     "side_parent_index=1"
     "side_substitution=(subst)"
     "side_pivot=(neg (TMH \"p\"))"
     "side_pivot_substituted=(neg (TMH \"p\"))"
     "side_pivot_parent_index=1"
     "side_pivot_literal_index=0"
     "side_pivot_parent_unit=u2"
     "parent_count=2"
     "parent_0_unit=u1"
     "parent_1_unit=u2"
     "result_clause=(clause (pos (TMH \"q\")))"
     "conclusion_clause=(clause (pos (TMH \"q\")))"
     "result_literal_count=1"))
  (resolve "u3_resolve_0"
    (parents "u1" "u2")
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "q")))))
  (subsumption_resolution "u3"
    (parents "u1" "u2")
    (selected (pos (TMH "p")))
    (side_pivot (neg (TMH "p")))
    (subst)
    (result
      (clause
        (pos (TMH "q")))))
  (input "u4" (source axiom "not_q")
    (clause
      (neg (TMH "q"))))
  (resolve "u5"
    (parents "u3" "u4")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u6" "u5"))
