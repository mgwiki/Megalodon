(certificate vampire-megalodon 1
  (problem "vampire-native-certificate-preprocess-formula-copy")
  (step_proposition "u1" "q")
  (step_proposition "u2" "q")
  (step_proposition "u3" "(q) -> vampire_false")
  (step_proposition "u4" "vampire_false")
  (step_proposition "u5" "vampire_false")
  (symbol_declaration "Variable q:prop.")
  (formula_term_input "u1" (source axiom "a1")
    (formula (TMH "q")))
  (formula_copy "u2"
    (parent "u1")
    (result
      (pos (TMH "q"))))
  (input "u3" (source axiom "a2")
    (clause
      (neg (TMH "q"))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u5" "u4")
)
