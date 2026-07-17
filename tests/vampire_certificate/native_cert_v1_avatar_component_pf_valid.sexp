(certificate vampire-megalodon 1
  (problem "native-cert-v1-avatar-component-pf-valid")
  (symbol_declaration "Variable p:prop.")
  (avatar_definition d0
    (split 1 true)
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (avatar_component c0
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (input s1 (source axiom "split_1_active")
    (clause
      (pos (TMH "split_1"))))
  (resolve r1
    (parents c0 s1)
    (pivot 1 0)
    (result
      (clause
        (pos (TMH "p")))))
  (input np (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (resolve r2
    (parents r1 np)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c1 r2))
