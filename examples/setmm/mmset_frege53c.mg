Parameter wsbc : ((set -> prop) -> ((set -> prop) -> prop)).
Parameter wceq : ((set -> prop) -> ((set -> prop) -> prop)).
Axiom ax_mp: (forall ph:prop, (forall ps:prop, ph -> (wi ph ps) -> ps)).
Axiom ax_frege52c: (forall ph:(set -> prop), (forall A2:(set -> (set -> prop)), (forall B2:(set -> (set -> prop)), (forall x3:set, (wi (wceq (A2 x3) (B2 x3)) (wi (wsbc (fun x3:set => (ph x3)) (A2 x3)) (wsbc (fun x3:set => (ph x3)) (B2 x3)))))))).
Axiom ax_frege8: (forall ph:prop, (forall ps:prop, (forall ch:prop, (wi (wi ph (wi ps ch)) (wi ps (wi ph ch)))))).
Theorem frege53c: (forall ph:(set -> prop), (forall A2:(set -> (set -> prop)), (forall B2:(set -> (set -> prop)), (forall x3:set, (wi (wsbc (fun x3:set => (ph x3)) (A2 x3)) (wi (wceq (A2 x3) (B2 x3)) (wsbc (fun x3:set => (ph x3)) (B2 x3)))))))).
let ph:(set -> prop).
let A2:(set -> (set -> prop)).
let B2:(set -> (set -> prop)).
let x3:set.
exact (ax_mp (wi (wceq (A2 x3) (B2 x3)) (wi (wsbc (fun x3:set => (ph x3)) (A2 x3)) (wsbc (fun x3:set => (ph x3)) (B2 x3)))) (wi (wsbc (fun x3:set => (ph x3)) (A2 x3)) (wi (wceq (A2 x3) (B2 x3)) (wsbc (fun x3:set => (ph x3)) (B2 x3)))) (ax_frege52c (fun x3:set => (ph x3)) (fun x3:set => (A2 x3)) (fun x3:set => (B2 x3)) x3) (ax_frege8 (wceq (A2 x3) (B2 x3)) (wsbc (fun x3:set => (ph x3)) (A2 x3)) (wsbc (fun x3:set => (ph x3)) (B2 x3)))).
Qed.
