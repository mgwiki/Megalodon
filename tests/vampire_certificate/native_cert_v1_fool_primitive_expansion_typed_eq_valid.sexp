(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-primitive-expansion-typed-eq-valid")
  (step_extra f1 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=fool_formula"
     "conclusion_unit=f1"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=f1"
     "primitive_expansion_requires=fool_atom_lift"))
  (formula_term_input p1 (source axiom "a1")
    (formula (TMH "p")))
  (fool_atom_lift f1_fool_atom_0
    (source (formula (TMH "p")))
    (target
      (formula
        (AP
          (AP
            (TPAP
              (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a")
              (PROP))
            (TMH "p"))
          (TMH "f__true"))))
    (path "root"))
  (fool_formula f1
    (parent p1)
    (result
      (formula
        (AP
          (AP
            (TPAP
              (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a")
              (PROP))
            (TMH "p"))
          (TMH "f__true")))))
  (formula_copy c1
    (parent f1)
    (result
      (pos
        (AP
          (AP
            (TPAP
              (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a")
              (PROP))
            (TMH "p"))
          (TMH "f__true")))))
  (input n1 (source axiom "a2")
    (clause
      (neg
        (AP
          (AP
            (TPAP
              (TMH "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a")
              (PROP))
            (TMH "p"))
          (TMH "f__true")))))
  (resolve r1
    (parents c1 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r1))
