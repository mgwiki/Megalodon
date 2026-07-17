(certificate vampire-megalodon 1
  (problem "native-cert-v1-open-derived-resolve-valid")
  (step_variable_sorts "u1" ("X0:set"))
  (step_variable_sorts "u2" ("X0:set"))
  (step_variable_sorts "u4" ("X0:set"))
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable p:set->prop.")
  (symbol_declaration "Variable q:prop.")
  (input "u1" (source axiom "a1")
    (clause
      (neg (TMH "q"))
      (pos (AP (TMH "p") (TMH "X0")))
      (pos (AP (TMH "p") (TMH "X0")))))
  (step_extra "u2" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=factoring" "primitive_expansion=prefix" "primitive_expansion_prefix=u2" "primitive_expansion_requires=factor" "conclusion_unit=u2" "selected=(pos (AP (TMH \"p\") (TMH \"X0\")))" "selected_substituted=(pos (AP (TMH \"p\") (TMH \"X0\")))" "selected_parent_index=0" "selected_literal_index=1" "selected_parent_unit=u1" "other=(pos (AP (TMH \"p\") (TMH \"X0\")))" "other_substituted=(pos (AP (TMH \"p\") (TMH \"X0\")))" "other_parent_index=0" "other_literal_index=2" "other_parent_unit=u1" "primitive_parent_0_substitution=(subst)" "result_clause=(clause (neg (TMH \"q\")) (pos (AP (TMH \"p\") (TMH \"X0\"))))" "conclusion_clause=(clause (neg (TMH \"q\")) (pos (AP (TMH \"p\") (TMH \"X0\"))))" "result_literal_count=2" "result_literal_0=(neg (TMH \"q\"))" "result_literal_1=(pos (AP (TMH \"p\") (TMH \"X0\")))" "parent_count=1" "parent_0_unit=u1" "parent_0_clause=(clause (neg (TMH \"q\")) (pos (AP (TMH \"p\") (TMH \"X0\"))) (pos (AP (TMH \"p\") (TMH \"X0\"))))" "parent_0_literal_count=3" "parent_0_literal_0=(neg (TMH \"q\"))" "parent_0_literal_1=(pos (AP (TMH \"p\") (TMH \"X0\")))" "parent_0_literal_2=(pos (AP (TMH \"p\") (TMH \"X0\")))"))
  (factor "u2"
    (parent "u1")
    (literals 1 2)
    (result
      (clause
        (neg (TMH "q"))
        (pos (AP (TMH "p") (TMH "X0"))))))
  (input "u3" (source axiom "a2")
    (clause
      (pos (TMH "q"))))
  (resolve "u4"
    (parents "u2" "u3")
    (pivot 0 0)
    (result
      (clause
        (pos (AP (TMH "p") (TMH "X0"))))))
  (step_extra "u5" "kernel_v1" ("schema=prover9-small-kernel-v1" "rule=instantiation" "primitive_expansion=prefix" "primitive_expansion_prefix=u5" "primitive_expansion_requires=substitute" "conclusion_unit=u5" "result_clause=(clause (pos (AP (TMH \"p\") (TMH \"a\"))))" "conclusion_clause=(clause (pos (AP (TMH \"p\") (TMH \"a\"))))" "substitution=(subst (\"X0\" (TMH \"a\")))" "result_literal_count=1" "result_literal_0=(pos (AP (TMH \"p\") (TMH \"a\")))" "parent_count=1" "parent_0_unit=u4" "parent_0_clause=(clause (pos (AP (TMH \"p\") (TMH \"X0\"))))" "parent_0_literal_count=1" "parent_0_literal_0=(pos (AP (TMH \"p\") (TMH \"X0\")))" "parent_0_substitution=(subst (\"X0\" (TMH \"a\")))" "parent_0_substituted_literal_count=1" "parent_0_substituted_literal_0=(pos (AP (TMH \"p\") (TMH \"a\")))"))
  (substitute "u5"
    (parent "u4")
    (subst ("X0" (TMH "a")))
    (result
      (clause
        (pos (AP (TMH "p") (TMH "a"))))))
  (input "u6" (source axiom "a3")
    (clause
      (neg (AP (TMH "p") (TMH "a")))))
  (resolve "u7"
    (parents "u5" "u6")
    (pivot 0 0)
    (result
      (clause)))
  (contradiction "u8" "u7"))
