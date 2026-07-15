(certificate vampire-megalodon 1
  (problem "core-paramodulation-negative-target")
  (step_proposition "u1" "a = b")
  (step_proposition "u2" "(a = c) -> vampire_false")
  (step_proposition "u3" "(b = c) -> vampire_false")
  (step_proposition "u4" "b = c")
  (step_proposition "u5" "vampire_false")
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable b:set.")
  (symbol_declaration "Variable c:set.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "b")))))
  (input "u2" (source axiom "a2")
    (clause
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "c")))))
  (paramodulate "u3" (equality "u1" 0) (target "u2" 0) (position 0 1) (from (TMH "a")) (to (TMH "b"))
    (result
      (clause
        (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "c"))))))
  (input "u4" (source axiom "a3")
    (clause
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "c")))))
  (resolve "u5" (parents "u3" "u4") (pivot 0 0) (result (clause)))
  (contradiction "u6" "u5")
)
