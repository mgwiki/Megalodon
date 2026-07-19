(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-split-multi-var-pf-valid")
  (symbol_declaration "Variable p:set->prop.")
  (symbol_declaration "Variable q:prop.")
  (step_variable_sorts src ("X:set" "Y:set"))
  (input src (source axiom "xy_source")
    (clause
      (pos (AP (TMH "p") (TMH "X")))
      (pos (AP (TMH "p") (TMH "Y")))))
  (step_variable_sorts d1 ("X:set" "Y:set"))
  (avatar_definition d1
    (split 1 true)
    (result
      (clause
        (pos (AP (TMH "p") (TMH "X")))
        (pos (AP (TMH "p") (TMH "Y")))
        (neg (TMH "split_1")))))
  (avatar_definition d2
    (split 2 true)
    (result
      (clause
        (pos (TMH "q"))
        (neg (TMH "split_2")))))
  (avatar_split s0
    (parents src d1 d2)
    (result
      (clause
        (pos (TMH "split_1"))
        (pos (TMH "split_2")))))
  (input n1 (source axiom "not_split_1")
    (clause
      (neg (TMH "split_1"))))
  (input n2 (source axiom "not_split_2")
    (clause
      (neg (TMH "split_2"))))
  (avatar_refutation r0
    (parents s0 n1 n2)
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
