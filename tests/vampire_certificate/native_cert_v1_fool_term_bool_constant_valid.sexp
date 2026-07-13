(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-term-bool-constant-valid")
  (formula_term_input f0 (source axiom "descr_bool")
    (formula
      (AP
        (AP (TMH "=") (TMH "default"))
        (AP
          (TMH "Descr_ii")
          (LAMV "X0" (SET) (TMH "vampire_true"))))))
  (fool_formula f1
    (parent f0)
    (result
      (formula
        (AP
          (AP (TMH "=") (TMH "default"))
          (AP
            (TMH "Descr_ii")
            (AP (TMH "vLAM") (TMH "f__true")))))))
  (cnf_literal c1
    (parent f1)
    (result
      (clause
        (pos
          (AP
            (AP (TMH "=") (TMH "default"))
            (AP
              (TMH "Descr_ii")
              (AP (TMH "vLAM") (TMH "f__true"))))))))
  (input c2 (source axiom "not_descr_bool")
    (clause
      (neg
        (AP
          (AP (TMH "=") (TMH "default"))
          (AP
            (TMH "Descr_ii")
            (AP (TMH "vLAM") (TMH "f__true")))))))
  (resolve c3
    (parents c1 c2)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c4 c3))
