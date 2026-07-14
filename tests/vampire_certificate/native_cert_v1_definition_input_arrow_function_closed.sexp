(certificate vampire-megalodon 1
  (problem "native-cert-v1-definition-input-arrow-function-closed")
  (step_proposition "d1" "vampire_eq_set_to_set f g")
  (step_extra "d1" "function_definition" ("introduced_symbol=g" "sort=set->set" "equality_sort=set->set" "lhs=f" "rhs=g" "proposition=vampire_eq_set_to_set f g"))
  (symbol_declaration "Variable f:set->set.")
  (symbol_declaration "Variable g:set->set.")
  (symbol_declaration "Variable a:set.")
  (definition_input d1
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "f")) (TMH "g"))))))
  (input n1 (source axiom "not_definition")
    (clause
      (neg (AP (AP (TMH "=") (AP (TMH "f") (TMH "a"))) (AP (TMH "g") (TMH "a"))))))
  (paramodulate p1
    (equality d1 0)
    (target n1 0)
    (position 0 0)
    (from (TMH "f"))
    (to (TMH "g"))
    (result
      (clause
        (neg (AP (AP (TMH "=") (AP (TMH "g") (TMH "a"))) (AP (TMH "g") (TMH "a")))))))
  (equality_resolution c1
    (parent p1)
    (literal 0)
    (result
      (clause)))
  (contradiction c2 c1))
