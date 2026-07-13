(certificate vampire-megalodon 1
  (problem "native-cert-v1-definition-input-valid")
  (definition_input d1
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b"))))))
  (input n1 (source axiom "definition_contradictor")
    (clause
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "b")))))
  (resolve c1
    (parents d1 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 c1))
