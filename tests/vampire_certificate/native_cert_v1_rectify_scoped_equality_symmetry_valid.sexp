(certificate vampire-megalodon 1
  (problem "native-cert-v1-rectify-scoped-equality-symmetry-valid")
  (step_proposition "f1" "forall X1:prop, forall X0:prop, vampire_eq_prop (X0) (X1)")
  (step_variable_sorts "f1" ("X0:prop" "X1:prop"))
  (step_proposition "f2" "forall X2:prop, forall X1:prop, vampire_eq_prop (X1) (X2)")
  (step_variable_sorts "f2" ("X1:prop" "X2:prop"))
  (step_proposition "c1" "forall X1:prop, forall X2:prop, vampire_eq_prop (X1) (X2)")
  (step_variable_sorts "c1" ("X1:prop" "X2:prop"))
  (step_proposition "c2" "forall X1:prop, forall X2:prop, vampire_eq_prop (X1) (X2) -> False")
  (step_variable_sorts "c2" ("X1:prop" "X2:prop"))
  (formula_term_input f1 (source axiom "a1")
    (formula
      (ALL (PROP)
        (AP (AP (TMH "=") (TMH "X0")) (TMH "X1")))))
  (rectify_formula f2
    (parent f1)
    (renamings
      (renaming
        (source
          (formula
            (ALL (PROP)
              (AP (AP (TMH "=") (TMH "X0")) (TMH "X1")))))
        (subst)
        (target
          (formula
            (ALL (PROP)
              (AP (AP (TMH "=") (TMH "X1")) (TMH "X2")))))))
    (result
      (formula
        (ALL (PROP)
          (AP (AP (TMH "=") (TMH "X1")) (TMH "X2"))))))
  (cnf_literal c1
    (parent f2)
    (result
      (clause
        (pos
          (ALL (PROP)
            (AP (AP (TMH "=") (TMH "X1")) (TMH "X2")))))))
  (input c2 (source axiom "a2")
    (clause
      (neg
        (ALL (PROP)
          (AP (AP (TMH "=") (TMH "X1")) (TMH "X2"))))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
