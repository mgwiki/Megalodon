(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-split-refutation-pf-valid")
  (input p1 (source axiom "split_1_active")
    (clause
      (pos (TMH "split_1"))))
  (avatar_split s0
    (parents p1)
    (result
      (clause
        (pos (TMH "split_1")))))
  (input n1 (source axiom "split_1_inactive")
    (clause
      (neg (TMH "split_1"))))
  (avatar_refutation r0
    (parents s0 n1)
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
