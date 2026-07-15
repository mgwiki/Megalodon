(certificate vampire-megalodon 1
  (problem "vampire-native-certificate-substituted-subsumption-resolution")
  (step_variable_sorts "u2" ("X0:prop"))
  (symbol_declaration "Variable q:prop.")
  (symbol_declaration "Variable r:prop.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (TMH "q"))
      (pos (TMH "r"))))
  (input "u2" (source axiom "a2")
    (clause
      (neg (TMH "X0"))))
  (subsumption_resolution "u3"
    (parents "u1" "u2")
    (selected (pos (TMH "q")))
    (side_pivot (neg (TMH "X0")))
    (subst ("X0" (TMH "q")))
    (result
      (clause
        (pos (TMH "r")))))
  (input "u4" (source axiom "a3")
    (clause
      (neg (TMH "r"))))
  (resolve "u5"
    (parents "u3" "u4")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u6" "u5")
)
