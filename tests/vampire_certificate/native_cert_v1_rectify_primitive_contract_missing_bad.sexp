(certificate vampire-megalodon 1
  (problem "native-cert-v1-rectify-primitive-contract-missing-bad")
  (step_extra c2 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=rectify_formula"
     "conclusion_unit=c2"))
  (formula_term_input c1 (source negated_conjecture "negated_variable_literal")
    (formula
      (IMP
        (AP (TMH "p") (TMH "X0"))
        (TMH "vampire_false"))))
  (rectify_formula c2
    (parent c1)
    (result
      (formula
        (IMP
          (AP (TMH "p") (TMH "X1"))
          (TMH "vampire_false")))))
  (formula_copy c3
    (parent c2)
    (result
      (neg (AP (TMH "p") (TMH "X1")))))
  (input c4 (source axiom "positive_variable_literal")
    (clause
      (pos (AP (TMH "p") (TMH "X1")))))
  (resolve c5
    (parents c3 c4)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c6 c5))
