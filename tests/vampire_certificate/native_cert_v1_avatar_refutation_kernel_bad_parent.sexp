(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-refutation-kernel-bad-parent")
  (step_extra "r0" "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_refutation"
     "result_clause=(clause)"
     "sat_refutation_clause=(sat_clause)"
     "sat_input_0_clause=(sat_clause (lit 1 true))"
     "sat_input_0_origin_unit=s0"
     "sat_input_1_clause=(sat_clause (lit 1 false))"
     "sat_input_1_origin_unit=k0"
     "sat_input_count=2"
     "sat_proof_step_count=3"
     "sat_proof_step_0_id=1"
     "sat_proof_step_0_clause=(sat_clause (lit 1 true))"
     "sat_proof_step_0_kind=input"
     "sat_proof_step_0_origin_unit=s0"
     "sat_proof_step_1_id=2"
     "sat_proof_step_1_clause=(sat_clause (lit 1 false))"
     "sat_proof_step_1_kind=input"
     "sat_proof_step_1_origin_unit=k0"
     "sat_proof_step_2_id=3"
     "sat_proof_step_2_clause=(sat_clause)"
     "sat_proof_step_2_kind=rup"
     "sat_proof_step_2_parent_0_id=1"
     "sat_proof_step_2_parent_0_clause=(sat_clause (lit 1 true))"
     "sat_proof_step_2_parent_1_id=99"
     "sat_proof_step_2_parent_1_clause=(sat_clause (lit 1 false))"
     "sat_proof_step_2_parent_count=2"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=r0"
     "primitive_expansion_requires=avatar_refutation"
     "conclusion_unit=r0"))
  (avatar_component a0
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_2")))))
  (avatar_split s0
    (parents a0)
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
