(certificate vampire-megalodon 1
  (problem "native-cert-v1-urr-primitive-chain-final-bad")
  (step_extra c3 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=unit_resulting_resolution"
     "conclusion_unit=c3"
     "result_clause=(clause (pos (TMH \"q\")))"
     "conclusion_clause=(clause (pos (TMH \"q\")))"
     "trace_main_parent_unit=c1"
     "trace_step_count=1"
     "trace_step_0_unit_parent=c2"
     "trace_step_0_selected=(pos (TMH \"p\"))"
     "trace_step_0_selected_substituted=(pos (TMH \"p\"))"
     "trace_step_0_unit_substituted=(neg (TMH \"p\"))"
     "trace_step_0_remaining_after=(clause (pos (TMH \"q\")))"
     "trace_remaining=(clause (pos (TMH \"q\")))"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=c3"
     "primitive_expansion_requires=resolve"
     "primitive_expansion_final_result_clause=(clause (pos (TMH \"q\")))"
     "primitive_expansion_step_count=1"
     "primitive_expansion_step_0_rule=resolve"
     "primitive_expansion_step_0_id=c3_resolve"
     "primitive_expansion_step_0_parent_count=2"
     "primitive_expansion_step_0_parent_0_id=c1"
     "primitive_expansion_step_0_parent_1_id=c2"
     "primitive_expansion_step_0_result_clause=(clause (pos (TMH \"q\")))"
     "primitive_expansion_requires_count=1"
     "primitive_expansion_requires_0=resolve"))
  (input c1 (source axiom "a1")
    (clause
      (pos (TMH "p"))
      (pos (TMH "q"))))
  (input c2 (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve c3_resolve
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "q")))))
  (substitute c3
    (parent c3_resolve)
    (subst)
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
