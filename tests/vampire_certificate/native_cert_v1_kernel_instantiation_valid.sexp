(certificate vampire-megalodon 1
  (problem "native-cert-v1-kernel-instantiation-valid")
  (input "u1" (source axiom "a1")
    (clause
      (pos (AP (TMH "p") (TMH "X0")))))
  (substitute "u2" (parent "u1")
    (subst ("X0" (TMH "a")))
    (result
      (clause
        (pos (AP (TMH "p") (TMH "a"))))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=instantiation" "primitive_expansion=prefix" "primitive_expansion_prefix=u2" "primitive_expansion_requires=substitute" "conclusion_unit=u2" "result_clause=(clause (pos (AP (TMH \"p\") (TMH \"a\"))))" "conclusion_clause=(clause (pos (AP (TMH \"p\") (TMH \"a\"))))" "substitution=(subst (\"X0\" (TMH \"a\")))" "result_literal_count=1" "result_literal_0=(pos (AP (TMH \"p\") (TMH \"a\")))" "parent_count=1" "parent_0_unit=u1" "parent_0_clause=(clause (pos (AP (TMH \"p\") (TMH \"X0\"))))" "parent_0_literal_count=1" "parent_0_literal_0=(pos (AP (TMH \"p\") (TMH \"X0\")))" "parent_0_substitution=(subst (\"X0\" (TMH \"a\")))" "parent_0_substituted_literal_count=1" "parent_0_substituted_literal_0=(pos (AP (TMH \"p\") (TMH \"a\")))"))
)
