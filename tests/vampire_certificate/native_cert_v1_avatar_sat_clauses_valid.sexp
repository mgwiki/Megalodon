(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-sat-clauses-valid")
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
