(certificate vampire-megalodon 1
  (problem "native-cert-v1-open-dropped-parent-bad")
  (step_variable_sorts "u1" ("X0:set"))
  (step_variable_sorts "u2" ("X0:set"))
  (symbol_declaration "Variable p:set->prop.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (AP (TMH "p") (TMH "X0")))))
  (input "u2" (source axiom "a2")
    (clause
      (neg (AP (TMH "p") (TMH "X0")))))
  (resolve "u3"
    (parents "u1" "u2")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u4" "u3"))
