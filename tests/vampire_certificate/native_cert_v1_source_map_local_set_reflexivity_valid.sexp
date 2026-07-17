(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-map-local-set-reflexivity-valid")
  (symbol_declaration "Variable a:set.")
  (input c1 (source axiom "local_set_eq")
    (clause
      (pos
        (AP
          (AP (TMH "=") (TMH "a"))
          (TMH "a")))))
  (input c2 (source axiom "not_local_set_eq")
    (clause
      (neg
        (AP
          (AP (TMH "=") (TMH "a"))
          (TMH "a")))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
