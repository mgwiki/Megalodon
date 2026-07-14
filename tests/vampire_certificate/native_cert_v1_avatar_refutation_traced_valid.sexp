(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-refutation-traced-valid")
  (avatar_refutation r0
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
