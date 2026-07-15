(certificate vampire-megalodon 1
  (problem "native-cert-v1-kernel-skolemize-valid")
  (formula_term_input "u0" (source axiom "exists_applied_head")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (LAM
          (AR (SET) (SET))
          (ALL
            (SET)
            (AP
              (AP
                (TMH "=")
                (AP (TMH "X0") (TMH "X1")))
              (TMH "f__true")))))))
  (skolem_formula "u1"
    (parent "u0")
    (source
      (formula
        (AP
          (TMH "vampire_exists_prop")
          (LAM
            (AR (SET) (SET))
            (ALL
              (SET)
              (AP
                (AP
                  (TMH "=")
                  (AP (TMH "X0") (TMH "X1")))
                (TMH "f__true")))))))
    (subst ("X0" (TMH "sk")))
    (introduced
      (symbol
        (name "sk")
        (replaced_var "X0")
        (declaration "Variable sk:set->set.")))
    (result
      (formula
        (ALL
          (SET)
          (AP
            (AP
              (TMH "=")
              (AP (TMH "sk") (TMH "X1")))
            (TMH "f__true"))))))
  (step_extra "u1" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=skolemize" "primitive_expansion=prefix" "primitive_expansion_prefix=u1" "primitive_expansion_requires=skolem_formula" "conclusion_unit=u1" "proof_parent_count=1" "parent_count=0" "parent_0_unit=u0" "source_unit=u0" "source_formula=(AP (TMH \"vampire_exists_prop\") (LAM (AR (SET) (SET)) (ALL (SET) (AP (AP (TMH \"=\") (AP (TMH \"X0\") (TMH \"X1\"))) (TMH \"f__true\")))))" "parent_0_formula=(AP (TMH \"vampire_exists_prop\") (LAM (AR (SET) (SET)) (ALL (SET) (AP (AP (TMH \"=\") (AP (TMH \"X0\") (TMH \"X1\"))) (TMH \"f__true\")))))" "result_formula=(ALL (SET) (AP (AP (TMH \"=\") (AP (TMH \"sk\") (TMH \"X1\"))) (TMH \"f__true\")))" "conclusion_formula=(ALL (SET) (AP (AP (TMH \"=\") (AP (TMH \"sk\") (TMH \"X1\"))) (TMH \"f__true\")))" "introduced_count=1" "introduced_0_kind=0" "introduced_0_raw_symbol=1" "introduced_0_symbol=sk" "introduced_0_replaced_var=X0" "introduced_0_declaration=Variable sk:set->set."))
  (cnf_formula_clause "c1"
    (parent "u1")
    (index 0)
    (result
      (clause
        (pos
          (AP
            (AP
              (TMH "=")
              (AP (TMH "sk") (TMH "X1")))
            (TMH "f__true"))))))
  (input "c2" (source axiom "neg_applied_head")
    (clause
      (neg
        (AP
          (AP
            (TMH "=")
            (AP (TMH "sk") (TMH "X1")))
          (TMH "f__true")))))
  (resolve "r1"
    (parents "c1" "c2")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "done" "r1"))
