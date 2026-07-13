(certificate vampire-megalodon 1
  (problem "native-cert-v1-predicate-definition-fold-valid")
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
        (AP
          (AP (TMH "vampire_and") (TMH "r"))
          (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))))))
  (formula_copy d4
    (parent d3)
    (result
      (pos
        (AP
          (AP (TMH "vampire_and") (TMH "r"))
          (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))))))
  (input d5
    (source axiom "not_folded")
    (clause
      (neg
        (AP
          (AP (TMH "vampire_and") (TMH "r"))
          (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))))))
  (resolve d6
    (parents d4 d5)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction d7 d6))
