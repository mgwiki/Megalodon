(certificate vampire-megalodon 1
  (problem "vampire-native-certificate-preprocess-formula-identity-rectify")
  (step_proposition "u1" "q")
  (step_proposition "u2" "q")
  (step_proposition "u3" "q")
  (step_proposition "u4" "q")
  (step_proposition "u5" "(q) -> vampire_false")
  (step_proposition "u6" "vampire_false")
  (step_proposition "u7" "vampire_false")
  (symbol_declaration "Variable q:prop.")
  (formula_term_input "u1" (source axiom "a1")
    (formula (TMH "q")))
  (formula_term_copy "u2"
    (parent "u1")
    (result (formula (TMH "q"))))
  (rectify_formula "u3"
    (parent "u2")
    (result (formula (TMH "q"))))
  (formula_copy "u4"
    (parent "u3")
    (result
      (pos (TMH "q"))))
  (input "u5" (source axiom "a2")
    (clause
      (neg (TMH "q"))))
  (resolve "u6"
    (parents "u4" "u5")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u7" "u6")
)
