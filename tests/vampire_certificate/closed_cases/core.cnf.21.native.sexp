(certificate vampire-megalodon 1
  (problem "core-paramodulation-binary-target")
  (step_proposition "u1" "a = b")
  (step_proposition "u2" "vampire_or (p) (a = c)")
  (step_proposition "u3" "vampire_or (p) (b = c)")
  (step_proposition "u4" "(p) -> vampire_false")
  (step_proposition "u5" "b = c")
  (step_proposition "u6" "(b = c) -> vampire_false")
  (step_proposition "u7" "vampire_false")
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable b:set.")
  (symbol_declaration "Variable c:set.")
  (symbol_declaration "Variable p:prop.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "b")))))
  (input "u2" (source axiom "a2")
    (clause
      (pos (TMH "p"))
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "a")) (TMH "c")))))
  (paramodulate "u3" (equality "u1" 0) (target "u2" 1) (position 0 1) (from (TMH "a")) (to (TMH "b"))
    (result
      (clause
        (pos (TMH "p"))
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "c"))))))
  (input "u4" (source axiom "a3") (clause (neg (TMH "p"))))
  (resolve "u5" (parents "u3" "u4") (pivot 0 0)
    (result
      (clause
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "c"))))))
  (input "u6" (source axiom "a4")
    (clause
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (SET)) (TMH "b")) (TMH "c")))))
  (resolve "u7" (parents "u5" "u6") (pivot 0 0) (result (clause)))
  (contradiction "u8" "u7")
)
