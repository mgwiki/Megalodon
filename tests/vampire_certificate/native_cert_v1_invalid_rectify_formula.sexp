(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-rectify-formula")
  (formula_term_input c1 (source axiom "not_a_rectification")
    (formula
      (ALL (SET)
        (AP (AP (TMH "p") (TMH "X0")) (TMH "a")))))
  (rectify_formula c2
    (parent c1)
    (result
      (formula
        (ALL (SET)
          (AP (AP (TMH "q") (TMH "X1")) (TMH "a"))))))
  (contradiction c3 c2))
