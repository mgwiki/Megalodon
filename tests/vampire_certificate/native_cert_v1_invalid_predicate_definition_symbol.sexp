(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-predicate-definition-symbol")
  (predicate_definition d1
    (symbol "wrong")
    (result
      (formula
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))
              (TMH "vampire_false")))
          (TMH "q"))))))
