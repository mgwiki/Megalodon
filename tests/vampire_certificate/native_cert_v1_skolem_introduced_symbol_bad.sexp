(certificate vampire-megalodon 1
  (problem "native-cert-v1-skolem-introduced-symbol-bad")
  (formula_term_input f0 (source axiom "exists_applied_head")
    (formula
      (AP
        (TMH "vampire_exists_prop")
        (LAM
          (AR (SET) (SET))
          (ALL
            (SET)
            (AP
              (AP
                (TMH "=")
                (AP (TMH "X0") (TMH "X1")))
              (TMH "f__true")))))))
  (skolem_formula f1
    (parent f0)
    (source
      (formula
        (AP
          (TMH "vampire_exists_prop")
          (LAM
            (AR (SET) (SET))
            (ALL
              (SET)
              (AP
                (AP
                  (TMH "=")
                  (AP (TMH "X0") (TMH "X1")))
                (TMH "f__true")))))))
    (subst ("X0" (TMH "sk")))
    (introduced
      (symbol
        (name "bad_sk")
        (replaced_var "X0")
        (declaration "Variable bad_sk:set->set.")))
    (result
      (formula
        (ALL
          (SET)
          (AP
            (AP
              (TMH "=")
              (AP (TMH "sk") (TMH "X1")))
            (TMH "f__true")))))))
