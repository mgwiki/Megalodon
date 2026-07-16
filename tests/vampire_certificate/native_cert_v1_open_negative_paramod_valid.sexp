(certificate vampire-megalodon 1
  (problem "native-cert-v1-open-negative-paramod-valid")
  (step_variable_sorts "u2" ("X0:set"))
  (step_variable_sorts "u3" ("X0:set"))
  (step_variable_sorts "u4" ("X0:set"))
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable p:set->prop.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "a"))))))
  (input "u2" (source axiom "a2")
    (clause
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (AP (TMH "p") (TMH "a"))) (TMH "f__true")))
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "X0"))))))
  (paramodulate "u3"
    (equality "u1" 0)
    (target "u2" 0)
    (position 1)
    (from (AP (TMH "p") (TMH "a")))
    (to (TMH "f__true"))
    (result
      (clause
        (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (TMH "f__true")))
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "X0")))))))
  (equality_resolution "u4"
    (parent "u3")
    (literal 0)
    (result
      (clause
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "X0")))))))
  (input "u5" (source axiom "a3")
    (clause
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "a"))))))
  (substitute "u6" (parent "u4")
    (subst ("X0" (TMH "a")))
    (result
      (clause
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (TMH "f__true")) (AP (TMH "p") (TMH "a")))))))
  (resolve "u7"
    (parents "u6" "u5")
    (pivot 0 0)
    (result (clause)))
  (contradiction "u8" "u7"))
