(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-refutation-sat-resolution-pf-valid")
  (input s12 (source axiom "split_1_or_split_2")
    (clause
      (pos (TMH "split_1"))
      (pos (TMH "split_2"))))
  (input n1 (source axiom "not_split_1")
    (clause
      (neg (TMH "split_1"))))
  (input n2 (source axiom "not_split_2")
    (clause
      (neg (TMH "split_2"))))
  (avatar_refutation r0
    (parents s12 n1 n2)
    (sat_clauses
      (sat_clause (lit 1 true) (lit 2 true))
      (sat_clause (lit 1 false))
      (sat_clause (lit 2 false)))
    (sat_proof
      (sat_input 1 (sat_clause (lit 1 true) (lit 2 true)))
      (sat_input 2 (sat_clause (lit 1 false)))
      (sat_rup 3
        (parents 1 2)
        (result
          (sat_clause (lit 2 true))))
      (sat_input 4 (sat_clause (lit 2 false)))
      (sat_rup 5
        (parents 3 4)
        (result
          (sat_clause))))
    (result
      (clause)))
  (contradiction c0 r0))
