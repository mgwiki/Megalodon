(certificate vampire-megalodon 1
  (problem "native-cert-v1-cnf-clause-kernel-count-mismatch-bad")
  (symbol_declaration "Variable p:prop.")
  (symbol_declaration "Variable q:prop.")
  (step_extra c1 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=cnf_clause"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=c1"
     "primitive_expansion_requires=cnf_formula_clause"
     "conclusion_unit=c1"
     "proof_parent_count=1"
     "source_kind=formula"
     "source_unit=f1"
     "parent_0_unit=f1"
     "source_formula=(AP (AP (TMH \"vampire_or\") (TMH \"p\")) (TMH \"q\"))"
     "parent_0_formula=(AP (AP (TMH \"vampire_or\") (TMH \"p\")) (TMH \"q\"))"
     "result_clause=(clause (pos (TMH \"p\")) (pos (TMH \"q\")))"
     "conclusion_clause=(clause (pos (TMH \"p\")) (pos (TMH \"q\")))"
     "result_literal_count=2"
     "clause_parent_unit=f1"
     "clause_index=0"
     "clause_count=2"
     "parent_clause_count=2"))
  (formula_term_input f1 (source axiom "p_or_q")
    (formula
      (AP
        (AP
          (TMH "vampire_or")
          (TMH "p"))
        (TMH "q"))))
  (cnf_formula_clause c1
    (parent f1)
    (index 0)
    (count 1)
    (result
      (clause
        (pos (TMH "p"))
        (pos (TMH "q")))))
  (input np (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (resolve c2
    (parents c1 np)
    (pivot 0 0)
    (result
      (clause
        (pos (TMH "q")))))
  (input nq (source negated_conjecture "not_q")
    (clause
      (neg (TMH "q"))))
  (resolve c3
    (parents c2 nq)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
