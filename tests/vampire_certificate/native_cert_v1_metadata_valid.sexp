(certificate vampire-megalodon 1
  (problem "native-cert-v1-metadata-valid")
  (symbol_declaration "Variable p:prop.")
  (step_proposition "c1" "p")
  (step_variable_sorts "c1" ("X0:set"))
  (step_extra "c1" "fool" ("rule=fool elimination" "source=p" "target=vampire_eq_prop p vampire_true"))
  (input c1 (source axiom "p")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "not-p")
    (clause
      (neg (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
