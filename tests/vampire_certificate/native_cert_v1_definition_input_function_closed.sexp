(certificate vampire-megalodon 1
  (problem "native-cert-v1-definition-input-function-closed")
  (step_proposition "d1" "a = b")
  (step_extra "d1" "function_definition" ("introduced_symbol=b" "sort=set" "equality_sort=set" "lhs=a" "rhs=b" "proposition=a = b"))
  (symbol_declaration "Variable a:set.")
  (symbol_declaration "Variable b:set.")
  (definition_input d1
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "a")) (TMH "b"))))))
  (input n1 (source axiom "not_definition")
    (clause
      (neg (AP (AP (TMH "=") (TMH "a")) (TMH "b")))))
  (resolve c1
    (parents d1 n1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 c1))
