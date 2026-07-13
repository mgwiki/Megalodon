(certificate vampire-megalodon 1
  (problem "native-cert-v1-invalid-truth-conflict")
  (input c1 (source axiom "not-conflict")
    (clause
      (pos (TMH "p"))
      (pos (AP (AP (TMH "=") (TMH "f__true")) (TMH "f__true")))))
  (truth_conflict c2
    (parent c1)
    (literal 1)
    (result
      (clause
        (pos (TMH "p"))))))
