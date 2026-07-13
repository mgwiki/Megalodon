(certificate vampire-megalodon 1
  (problem "native-cert-v1-truth-conflict-valid")
  (input c1 (source axiom "truth-conflict")
    (clause
      (pos (TMH "p"))
      (pos (AP (AP (TMH "=") (TMH "f__true")) (TMH "f__false")))))
  (truth_conflict c2
    (parent c1)
    (literal 1)
    (result
      (clause
        (pos (TMH "p")))))
  (input c3 (source axiom "not-p")
    (clause
      (neg (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
