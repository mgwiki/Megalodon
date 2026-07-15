(certificate vampire-megalodon 1
  (problem "core-equality-symmetry-negative")
  (step_proposition "u1" "(a = b) -> vampire_false")
  (step_proposition "u2" "(b = a) -> vampire_false")
  (step_proposition "u3" "b = a")
  (step_proposition "u4" "vampire_false")
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable b:set.")
  (input "u1" (source axiom "a1")
    (clause
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "b")))))
  (equality_symmetry "u2" (parent "u1") (literal 0)
    (result
      (clause
        (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "a"))))))
  (input "u3" (source axiom "a2")
    (clause
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "a")))))
  (resolve "u4" (parents "u2" "u3") (pivot 0 0) (result (clause)))
  (contradiction "u5" "u4")
)
