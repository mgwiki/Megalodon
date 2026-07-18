(certificate vampire-megalodon 1
  (problem "native-cert-v1-kernel-skolemize-dependency-count-bad")
  (symbol_declaration "Variable p:set->prop.")
  (formula_term_input "u0" (source axiom "exists_p")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (LAM
          (SET)
          (AP (TMH "p") (TMH "X0"))))))
  (skolem_formula "u1"
    (parent "u0")
    (source
      (formula
        (AP
          (TMH "vampire_exists_prop")
          (LAM
            (SET)
            (AP (TMH "p") (TMH "X0"))))))
    (subst ("X0" (TMH "sk")))
    (introduced
      (symbol
        (name "sk")
        (replaced_var "X0")
        (declaration "Variable sk:set.")))
    (result
      (formula
        (AP (TMH "p") (TMH "sk")))))
  (step_extra "u1" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=skolemize" "primitive_expansion=prefix" "primitive_expansion_prefix=u1" "primitive_expansion_requires=skolem_formula" "conclusion_unit=u1" "proof_parent_count=2" "parent_count=0" "parent_0_unit=u0" "parent_1_unit=u1_parent_1" "source_unit=u0" "source_formula=(AP (TMH \"vampire_exists_prop\") (LAM (SET) (AP (TMH \"p\") (TMH \"X0\"))))" "parent_0_formula=(AP (TMH \"vampire_exists_prop\") (LAM (SET) (AP (TMH \"p\") (TMH \"X0\"))))" "parent_1_formula=(IMP (AP (TMH \"vampire_exists_prop\") (LAM (SET) (AP (TMH \"p\") (TMH \"X0\")))) (AP (TMH \"p\") (TMH \"sk\")))" "result_formula=(AP (TMH \"p\") (TMH \"sk\"))" "conclusion_formula=(AP (TMH \"p\") (TMH \"sk\"))" "introduced_count=1" "introduced_0_kind=0" "introduced_0_raw_symbol=1" "introduced_0_symbol=sk" "introduced_0_replaced_var=X0" "introduced_0_declaration=Variable sk:set." "introduced_0_witness_term=(TMH \"sk\")" "introduced_0_dependency_count=1" "introduced_0_choice_principle=classical_choice"))
  (cnf_formula_clause "c1"
    (parent "u1")
    (index 0)
    (result
      (clause
        (pos (AP (TMH "p") (TMH "sk"))))))
  (input "c2" (source axiom "not_p_sk")
    (clause
      (neg (AP (TMH "p") (TMH "sk")))))
  (resolve "r1"
    (parents "c1" "c2")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "done" "r1"))
