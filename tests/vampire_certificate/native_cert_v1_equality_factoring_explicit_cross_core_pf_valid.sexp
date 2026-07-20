(certificate vampire-megalodon 1
  (problem "native-cert-v1-equality-factoring-explicit-cross-core-pf-valid")
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable b:set.")
  (symbol_declaration "Variable c:set.")
  (input "u1" (source axiom "two_equalities")
    (clause
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b")))
      (pos (AP (AP (TMH "=") (TMH "c")) (TMH "a")))))
  (equality_factoring "u2"
    (parent "u1")
    (selected 0)
    (other 1)
    (selected_lhs (TMH "a"))
    (other_rhs (TMH "c"))
    (subst)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "c")) (TMH "a")))
        (neg (AP (AP (TMH "=") (TMH "b")) (TMH "c"))))))
  (input "u3" (source axiom "not_c_a")
    (clause
      (neg (AP (AP (TMH "=") (TMH "c")) (TMH "a")))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "b")) (TMH "c"))))))
  (input "u5" (source axiom "b_c")
    (clause
      (pos (AP (AP (TMH "=") (TMH "b")) (TMH "c")))))
  (resolve "u6"
    (parents "u4" "u5")
    (pivot 0 0)
    (result (clause))))
