(certificate vampire-megalodon 1
  (problem "native-cert-v1-formula-cnf-valid")
  (symbol_declaration "Variable p:prop.")
  (symbol_declaration "Variable q:prop.")
  (step_proposition "f0" "p -> q")
  (step_proposition "f1" "vampire_eq_prop (p) (vampire_true) -> vampire_eq_prop (q) (vampire_true)")
  (step_extra "f1" "fool" ("rule=fool elimination" "source=p -> q" "target=vampire_eq_prop (p) (vampire_true) -> vampire_eq_prop (q) (vampire_true)"))
  (step_proposition "f2" "(vampire_eq_prop (p) (vampire_true) -> vampire_false) \\/ vampire_eq_prop (q) (vampire_true)")
  (step_extra "f2" "normal_form" ("rule=ennf transformation" "source=vampire_eq_prop (p) (vampire_true) -> vampire_eq_prop (q) (vampire_true)" "target=(vampire_eq_prop (p) (vampire_true) -> vampire_false) \\/ vampire_eq_prop (q) (vampire_true)"))
  (step_proposition "c1" "(vampire_eq_prop (p) (vampire_true) -> False) \\/ vampire_eq_prop (q) (vampire_true)")
  (step_extra "c1" "cnf" ("rule=cnf transformation" "source=(vampire_eq_prop (p) (vampire_true) -> vampire_false) \\/ vampire_eq_prop (q) (vampire_true)" "target=(vampire_eq_prop (p) (vampire_true) -> False) \\/ vampire_eq_prop (q) (vampire_true)"))
  (step_proposition "p1" "vampire_eq_prop (p) (vampire_true)")
  (step_proposition "r1" "vampire_eq_prop (q) (vampire_true)")
  (step_proposition "q1" "vampire_eq_prop (q) (vampire_true) -> False")
  (step_proposition "r2" "False")
  (formula_term_input f0 (source axiom "imp")
    (formula
      (IMP
        (TMH "p")
        (TMH "q"))))
  (fool_formula f1
    (parent f0)
    (result
      (formula
        (IMP
          (AP (AP (TMH "=") (TMH "p")) (TMH "f__true"))
          (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (ennf_formula f2
    (parent f1)
    (result
      (formula
        (AP
          (AP
            (TMH "vampire_or")
            (IMP
              (AP (AP (TMH "=") (TMH "p")) (TMH "f__true"))
              (TMH "vampire_false")))
          (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (cnf_formula_clause c1
    (parent f2)
    (index 0)
    (count 1)
    (result
      (clause
        (neg (AP (AP (TMH "=") (TMH "p")) (TMH "f__true")))
        (pos (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (input p1 (source axiom "p_true")
    (clause
      (pos (AP (AP (TMH "=") (TMH "p")) (TMH "f__true")))))
  (resolve r1
    (parents c1 p1)
    (pivot 0 0)
    (result
      (clause
        (pos (AP (AP (TMH "=") (TMH "q")) (TMH "f__true"))))))
  (input q1 (source axiom "q_false")
    (clause
      (neg (AP (AP (TMH "=") (TMH "q")) (TMH "f__true")))))
  (resolve r2
    (parents r1 q1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r2))
