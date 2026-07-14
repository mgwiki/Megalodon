(certificate vampire-megalodon 1
  (problem "native-cert-v1-source-name-mangled-valid")
  (input c1 (source axiom "c_Foo_5Fbar")
    (clause
      (pos (TMH "p"))))
  (input c2 (source axiom "c_Not_2Fp")
    (clause
      (neg (TMH "p"))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
