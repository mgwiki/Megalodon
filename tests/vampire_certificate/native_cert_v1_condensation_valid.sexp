(certificate vampire-megalodon 1
  (problem "native-cert-v1-condensation-valid")
  (input p0 (source axiom "dup_after_subst")
    (clause
      (pos (AP (TMH "p") (TMH "X0")))
      (pos (AP (TMH "p") (TMH "a")))))
  (condensation c0
    (parent p0)
    (subst ("X0" (TMH "a")))
    (result
      (clause
        (pos (AP (TMH "p") (TMH "a"))))))
  (input n0 (source axiom "not_p_a")
    (clause
      (neg (AP (TMH "p") (TMH "a")))))
  (resolve r0
    (parents c0 n0)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c1 r0))
