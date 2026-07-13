(certificate vampire-megalodon 1
  (problem "native-cert-v1-equality-symmetry-valid")
  (input p1 (source axiom "eq_forward")
    (clause
      (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b")))))
  (equality_symmetry p2
    (parent p1)
    (literal 0)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "b")) (TMH "a"))))))
  (input n1 (source axiom "eq_backward_negated")
    (clause
      (neg (AP (AP (TMH "=") (TMH "b")) (TMH "a")))))
  (resolve c1
    (parents p2 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 c1))
