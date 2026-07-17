(certificate vampire-megalodon 1
  (problem "native-cert-v1-resolve-left-last-pivot-valid")
  (symbol_declaration "Variable a:prop.")
  (symbol_declaration "Variable b:prop.")
  (symbol_declaration "Variable q:prop.")
  (input "u2" (source axiom "a1")
    (clause
      (pos (TMH "q"))
      (pos (TMH "b"))))
  (input "u1" (source axiom "a2")
    (clause
      (pos (TMH "a"))
      (neg (TMH "q"))))
  (resolve "u3"
    (parents "u1" "u2")
    (pivot 1 0)
    (result
      (clause
        (pos (TMH "a"))
        (pos (TMH "b")))))
  (input "u4" (source axiom "a3")
    (clause
      (neg (TMH "a"))))
  (resolve "u5"
    (parents "u3" "u4")
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "b")))))
  (input "u6" (source axiom "a4")
    (clause
      (neg (TMH "b"))))
  (resolve "u7"
    (parents "u5" "u6")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u8" "u7"))
