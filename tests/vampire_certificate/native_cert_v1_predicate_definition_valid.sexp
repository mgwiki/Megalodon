(certificate vampire-megalodon 1
  (problem "native-cert-v1-predicate-definition-valid")
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
  (formula_copy d2
    (parent d1)
    (result
      (pos
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))
              (TMH "vampire_false")))
          (TMH "q")))))
  (input d3
    (source axiom "not_definition")
    (clause
      (neg
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))
              (TMH "vampire_false")))
          (TMH "q")))))
  (resolve d4
    (parents d2 d3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction d5 d4))
