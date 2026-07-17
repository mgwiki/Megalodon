(certificate vampire-megalodon 1
  (problem "native-cert-v1-predicate-definition-fold-chain-valid")
  (symbol_declaration "Variable r:prop.")
  (symbol_declaration "Variable q:prop.")
  (symbol_declaration "Variable pdef:prop.")
  (symbol_declaration "Variable qdef:prop.")
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
  (predicate_definition d2
    (symbol "qdef")
    (result
      (formula
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "qdef"))
              (TMH "vampire_false")))
          (AP
            (AP (TMH "vampire_and") (TMH "r"))
            (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef")))))))
  (formula_term_input d3
    (source axiom "source_formula")
    (formula
      (AP (AP (TMH "vampire_and") (TMH "r")) (TMH "q"))))
  (predicate_definition_fold_chain d4
    (source d3)
    (definitions d1 d2)
    (result
      (formula
        (AP (AP (TMH "=") (TMH "f__true")) (TMH "qdef")))))
  (formula_copy d5
    (parent d4)
    (result
      (pos
        (AP (AP (TMH "=") (TMH "f__true")) (TMH "qdef")))))
  (input d6
    (source axiom "not_folded")
    (clause
      (neg
        (AP (AP (TMH "=") (TMH "f__true")) (TMH "qdef")))))
  (resolve d7
    (parents d5 d6)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction d8 d7))
