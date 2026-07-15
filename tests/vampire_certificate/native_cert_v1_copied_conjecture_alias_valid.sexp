(certificate vampire-megalodon 1
  (problem "native-cert-v1-copied-conjecture-alias-valid")
  (step_proposition "c1" "p")
  (step_proposition "c2" "p")
  (formula_input c1
    (source conjecture "conj_c__2Fproject_2Ftmp_2Fcopied_5Fcorpus_2Fhammer_5F10656_5F24")
    (pos (TMH "p")))
  (cnf_literal c2
    (parent c1)
    (result
      (clause
        (pos (TMH "p")))))
  (input c3 (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve c4
    (parents c2 c3)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c5 c4))
