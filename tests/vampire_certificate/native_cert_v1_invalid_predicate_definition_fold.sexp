(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-predicate-definition-fold")
  (predicate_definition d1
    (symbol "pdef")
    (result
      (formula
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))
              (TMH "vampire_false")))
          (TMH "q")))))
  (formula_term_input d2
    (source axiom "source_formula")
    (formula
      (AP (AP (TMH "vampire_and") (TMH "r")) (TMH "q"))))
  (predicate_definition_fold d3
    (source d2)
    (definition d1)
    (result
      (formula
        (AP (AP (TMH "vampire_and") (TMH "r")) (TMH "bad"))))))
