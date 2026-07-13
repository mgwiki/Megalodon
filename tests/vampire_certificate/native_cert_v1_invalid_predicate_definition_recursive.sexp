(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-predicate-definition-recursive")
  (predicate_definition d1
    (symbol "pdef")
    (result
      (formula
        (AP
          (AP (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "f__true")) (TMH "pdef"))
              (TMH "vampire_false")))
          (AP (TMH "r") (TMH "pdef")))))))
