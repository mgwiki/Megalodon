(certificate vampire-megalodon 1
  (problem "native-cert-v1-fool-formula-equality-orientation-valid")
  (formula_term_input p1 (source axiom "negated_goal")
    (formula
      (IMP
        (AP
          (AP
            (TMH "=")
            (AP
              (AP
                (TMH "Pi_SNo")
                (LAMV "X0" (SET) (TMH "Empty")))
              (TMH "Empty")))
          (TMH "n"))
        (TMH "vampire_false"))))
  (fool_formula f1
    (parent p1)
    (result
      (formula
        (IMP
          (AP
            (AP
              (TMH "=")
              (TMH "n"))
            (AP
              (AP
                (TMH "Pi_SNo")
                (AP (TMH "vLAM") (TMH "Empty")))
              (TMH "Empty")))
          (TMH "vampire_false")))))
  (formula_copy c1
    (parent f1)
    (result
      (neg
        (AP
          (AP
            (TMH "=")
            (TMH "n"))
          (AP
            (AP
              (TMH "Pi_SNo")
              (AP (TMH "vLAM") (TMH "Empty")))
            (TMH "Empty"))))))
  (input p2 (source axiom "positive_goal")
    (clause
      (pos
        (AP
          (AP
            (TMH "=")
            (TMH "n"))
          (AP
            (AP
              (TMH "Pi_SNo")
              (AP (TMH "vLAM") (TMH "Empty")))
            (TMH "Empty"))))))
  (resolve r1
    (parents p2 c1)
    (pivot 0 0)
    (result
      (clause)))
  (contradiction c2 r1))
