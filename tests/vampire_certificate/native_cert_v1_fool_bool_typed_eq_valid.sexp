(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-bool-typed-eq-valid")
  (formula_input f1 (source axiom "bool_axiom")
    (pos (AP (TMH "p") (TMH "a"))))
  (formula_copy f2
    (parent f1)
    (result (pos (AP (TMH "p") (TMH "a")))))
  (fool_bool f3
    (parent f2)
    (result
      (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (AP (TMH "p") (TMH "a"))) (TMH "f__true")))))
  (cnf_literal c1
    (parent f3)
    (result
      (clause
        (pos (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (AP (TMH "p") (TMH "a"))) (TMH "f__true"))))))
  (formula_input g1 (source negated_conjecture "bool_goal")
    (neg (AP (TMH "p") (TMH "a"))))
  (fool_bool g2
    (parent g1)
    (result
      (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (AP (TMH "p") (TMH "a"))) (TMH "f__true")))))
  (cnf_literal c2
    (parent g2)
    (result
      (clause
        (neg (AP (AP (TPAP (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a") (PROP)) (AP (TMH "p") (TMH "a"))) (TMH "f__true"))))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
