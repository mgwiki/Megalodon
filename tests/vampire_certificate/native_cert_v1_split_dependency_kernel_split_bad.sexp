(certificate vampire-megalodon 1
  (problem "native-cert-v1-split-dependency-kernel-split-bad")
  (step_extra c0 "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=split_dependency"
     "dependency_0_split_level=0"
     "dependency_0_split_var=2"
     "dependency_0_split_positive=1"
     "dependency_0_component_clause=p \\/ ((split_1) -> vampire_false)"
     "dependency_0_component_clause_sexpr=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "dependency_0_component_clause_variable_sort_count=0"
     "dependency_0_component_clause_db_sort_count=0"
     "dependency_count=1"
     "result_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=c0"
     "primitive_expansion_requires=split_dependency"
     "conclusion_unit=c0"
     "conclusion_clause=(clause (pos (TMH \"p\")) (neg (TMH \"split_1\")))"
     "result_literal_count=2"
     "result_literal_0=(pos (TMH \"p\"))"
     "result_literal_1=(neg (TMH \"split_1\"))"
     "parent_count=0"))
  (avatar_component c0
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (split_dependency c0_split_dependency
    (owner c0)
    (dependencies
      (dependency 1 true
        (component
          (clause
            (pos (TMH "p"))
            (neg (TMH "split_1"))))))
    (result
      (clause
        (pos (TMH "p"))
        (neg (TMH "split_1")))))
  (input s1 (source axiom "split_1_active")
    (clause
      (pos (TMH "split_1"))))
  (resolve r1
    (parents c0_split_dependency s1)
    (pivot 1 0)
    (result
      (clause
        (pos (TMH "p")))))
  (input np (source axiom "not_p")
    (clause
      (neg (TMH "p"))))
  (resolve r2
    (parents r1 np)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c1 r2))
