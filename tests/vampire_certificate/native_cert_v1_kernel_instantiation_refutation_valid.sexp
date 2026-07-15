(certificate vampire-megalodon 1
  (problem "native-cert-v1-kernel-instantiation-refutation-valid")
  (step_variable_sorts "u1" ("X0:prop"))
  (symbol_declaration "Variable p:prop.")
  (input "u1" (source axiom "a1")
    (clause
      (pos (TMH "X0"))))
  (substitute "u2" (parent "u1")
    (subst ("X0" (TMH "p")))
    (result
      (clause
        (pos (TMH "p")))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=instantiation" "conclusion_unit=u2" "result_clause=(clause (pos (TMH \"p\")))" "conclusion_clause=(clause (pos (TMH \"p\")))" "substitution=(subst (\"X0\" (TMH \"p\")))" "result_literal_count=1" "result_literal_0=(pos (TMH \"p\"))" "parent_count=1" "parent_0_unit=u1" "parent_0_clause=(clause (pos (TMH \"X0\")))" "parent_0_literal_count=1" "parent_0_literal_0=(pos (TMH \"X0\"))" "parent_0_substitution=(subst (\"X0\" (TMH \"p\")))" "parent_0_substituted_literal_count=1" "parent_0_substituted_literal_0=(pos (TMH \"p\"))"))
  (input "u3" (source axiom "a2")
    (clause
      (neg (TMH "p"))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u5" "u4")
)
