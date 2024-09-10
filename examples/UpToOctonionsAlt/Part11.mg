(** Part 11: Cayley Dickson **)

Section Alg.

Variable extension_tag:set.
Let ctag : set -> set := fun alpha => SetAdjoin alpha extension_tag.
Postfix '' 100 := ctag.
Definition pair_tag : set -> set -> set := fun x y => x :\/: {u ''|u :e y}.

Variable F:set -> prop.

Hypothesis extension_tag_fresh: forall x, F x -> forall u :e x, extension_tag /:e u.

Theorem ctagged_notin_F : forall x y, F x -> (y '') /:e x.
let x y.
assume Hx: F x.
assume H1: y '' :e x.
apply extension_tag_fresh x Hx (y '') H1.
prove extension_tag :e y ''.
prove extension_tag :e y :\/: {extension_tag}.
apply binunionI2.
apply SingI.
Qed.

Theorem ctagged_eqE_Subq : forall x y, F x -> forall u :e x, forall v, u '' = v '' -> u c= v.
let x y. assume Hx. let u. assume Hu. let v. assume Huv.
let w. assume Hw: w :e u.
claim L1: w :e v ''.
{ rewrite <- Huv.
  prove w :e u :\/: {extension_tag}.
  apply binunionI1. exact Hw.
}
apply binunionE v {extension_tag} w L1.
- assume H1: w :e v. exact H1.
- assume H1: w :e {extension_tag}. prove False.
  claim L2: w = extension_tag.
  { exact SingE extension_tag w H1. }
  apply extension_tag_fresh x Hx u Hu.
  prove extension_tag :e u.
  rewrite <- L2. exact Hw.
Qed.

Theorem ctagged_eqE_eq : forall x y, F x -> F y -> forall u :e x, forall v :e y, u '' = v '' -> u = v.
let x y. assume Hx Hy. let u. assume Hu. let v. assume Hv Huv.
apply set_ext.
- exact ctagged_eqE_Subq x y Hx u Hu v Huv.
- apply ctagged_eqE_Subq y x Hy v Hv u. symmetry. exact Huv.
Qed.

Theorem pair_tag_prop_1_Subq : forall x1 y1 x2 y2, F x1 -> pair_tag x1 y1 = pair_tag x2 y2 -> x1 c= x2.
let x1 y1 x2 y2.
assume Hx1.
assume H1: pair_tag x1 y1 = pair_tag x2 y2.
let v. assume Hv: v :e x1.
claim L1: v :e pair_tag x2 y2.
{ rewrite <- H1.
  prove v :e x1 :\/: {u ''|u :e y1}.
  apply binunionI1.
  exact Hv.
}
apply binunionE x2 {u ''|u :e y2} v L1.
- assume H2: v :e x2. exact H2.
- assume H2: v :e {u ''|u :e y2}. prove False.
  apply ReplE_impred y2 (fun u => u '') v H2.
  let u. assume Hu: u :e y2.
  assume Hvu: v = u ''.
  apply ctagged_notin_F x1 u Hx1.
  prove u '' :e x1.
  rewrite <- Hvu. exact Hv.
Qed.

Theorem pair_tag_prop_1 : forall x1 y1 x2 y2, F x1 -> F x2 -> pair_tag x1 y1 = pair_tag x2 y2 -> x1 = x2.
let x1 y1 x2 y2.
assume Hx1 Hx2.
assume H1: pair_tag x1 y1 = pair_tag x2 y2.
apply set_ext.
- exact pair_tag_prop_1_Subq x1 y1 x2 y2 Hx1 H1.
- apply pair_tag_prop_1_Subq x2 y2 x1 y1 Hx2.
  symmetry. exact H1.
Qed.

Theorem pair_tag_prop_2_Subq : forall x1 y1 x2 y2, F y1 -> F x2 -> F y2 -> pair_tag x1 y1 = pair_tag x2 y2 -> y1 c= y2.
let x1 y1 x2 y2.
assume Hy1 Hx2 Hy2.
assume H1: pair_tag x1 y1 = pair_tag x2 y2.
let v. assume Hv: v :e y1.
claim L1: v '' :e pair_tag x2 y2.
{ rewrite <- H1.
  prove v '' :e x1 :\/: {u ''|u :e y1}.
  apply binunionI2.
  prove v '' :e {u ''|u :e y1}.
  exact ReplI y1 (fun u => u '') v Hv.
}
apply binunionE x2 {u ''|u :e y2} (v '') L1.
- assume H2: v '' :e x2. prove False.
  exact ctagged_notin_F x2 v Hx2 H2.
- assume H2: v '' :e {u ''|u :e y2}.
  apply ReplE_impred y2 (fun u => u '') (v '') H2.
  let u. assume Hu: u :e y2.
  assume Hvu: v '' = u ''.
  claim L2: v = u.
  { exact ctagged_eqE_eq y1 y2 Hy1 Hy2 v Hv u Hu Hvu. }
  prove v :e y2. rewrite L2. exact Hu.
Qed.

Theorem pair_tag_prop_2 : forall x1 y1 x2 y2, F x1 -> F y1 -> F x2 -> F y2 -> pair_tag x1 y1 = pair_tag x2 y2 -> y1 = y2.
let x1 y1 x2 y2.
assume Hx1 Hy1 Hx2 Hy2.
assume H1: pair_tag x1 y1 = pair_tag x2 y2.
apply set_ext.
- exact pair_tag_prop_2_Subq x1 y1 x2 y2 Hy1 Hx2 Hy2 H1.
- apply pair_tag_prop_2_Subq x2 y2 x1 y1 Hy2 Hx1 Hy1.
  symmetry. exact H1.
Qed.

Theorem pair_tag_0 : forall x, pair_tag x 0 = x.
let x.
prove x :\/: {u ''| u :e 0} = x.
rewrite Repl_Empty (fun u => u '').
prove x :\/: 0 = x.
exact binunion_idr x.
Qed.

Definition CD_carr: set -> prop := fun z => exists x, F x /\ exists y, F y /\ z = pair_tag x y.

Theorem CD_carr_I: forall x y, F x -> F y -> CD_carr (pair_tag x y).
let x y. assume Hx Hy.
prove exists x', F x' /\ exists y', F y' /\ pair_tag x y = pair_tag x' y'.
witness x. apply andI.
- exact Hx.
- witness y. apply andI.
  + exact Hy.
  + reflexivity.
Qed.

Theorem CD_carr_E: forall z, CD_carr z ->
  forall p:set -> prop,
      (forall x y, F x -> F y -> z = pair_tag x y -> p (pair_tag x y))
    -> p z.
let z. assume Hz. let p. assume Hp.
apply Hz.
let x. assume H1. apply H1.
assume Hx. assume H1. apply H1.
let y. assume H1. apply H1.
assume Hy Hzxy.
rewrite Hzxy.
exact Hp x y Hx Hy Hzxy.
Qed.

Theorem CD_carr_0ext: F 0 -> forall x, F x -> CD_carr x.
assume H0.
let x. assume Hx.
prove exists x', F x' /\ exists y, F y /\ x = pair_tag x' y.
witness x. apply andI.
- exact Hx.
- witness 0. apply andI.
  + exact H0.
  + symmetry. exact pair_tag_0 x.
Qed.

Definition CD_proj0 : set -> set := fun z => Eps_i (fun x => F x /\ exists y, F y /\ z = pair_tag x y).
Definition CD_proj1 : set -> set := fun z => Eps_i (fun y => F y /\ z = pair_tag (CD_proj0 z) y).

Let proj0 := CD_proj0.
Let proj1 := CD_proj1.
Let pa : set -> set -> set := pair_tag.

Theorem CD_proj0_1: forall z, CD_carr z -> F (proj0 z) /\ exists y, F y /\ z = pa (proj0 z) y.
let z. assume Hz.
apply Eps_i_ex (fun x => F x /\ exists y, F y /\ z = pa x y).
prove exists x, F x /\ exists y, F y /\ z = pa x y.
exact Hz.
Qed.

Theorem CD_proj0_2: forall x y, F x -> F y -> proj0 (pa x y) = x.
let x y. assume Hx Hy.
apply CD_proj0_1 (pa x y) (CD_carr_I x y Hx Hy).
assume H1: F (proj0 (pa x y)).
assume H2: exists y', F y' /\ pa x y = pa (proj0 (pa x y)) y'.
apply H2.
let y'. assume H3. apply H3.
assume Hy': F y'.
assume H4: pa x y = pa (proj0 (pa x y)) y'.
symmetry.
exact pair_tag_prop_1 x y (proj0 (pa x y)) y' Hx H1 H4.
Qed.

Theorem CD_proj1_1: forall z, CD_carr z -> F (proj1 z) /\ z = pa (proj0 z) (proj1 z).
let z. assume Hz.
apply Eps_i_ex (fun y => F y /\ z = pa (proj0 z) y).
prove exists y, F y /\ z = pa (proj0 z) y.
apply CD_carr_E z Hz.
let x y. assume Hx Hy.
assume Hzxy: z = pa x y.
witness y. apply andI.
- exact Hy.
- prove pa x y = pa (proj0 (pa x y)) y.
  apply CD_proj0_2 x y Hx Hy (fun u v => pa x y = pa v y).
  prove pa x y = pa x y.
  reflexivity.
Qed.

Theorem CD_proj1_2: forall x y, F x -> F y -> proj1 (pa x y) = y.
let x y. assume Hx Hy.
symmetry.
apply CD_proj1_1 (pa x y) (CD_carr_I x y Hx Hy).
assume H1: F (proj1 (pa x y)).
apply CD_proj0_2 x y Hx Hy (fun u v => pa x y = pa v (proj1 (pa x y)) -> y = proj1 (pa x y)).
assume H2: pa x y = pa x (proj1 (pa x y)).
exact pair_tag_prop_2 x y x (proj1 (pa x y)) Hx Hy Hx H1 H2.
Qed.

Theorem CD_proj0R: forall z, CD_carr z -> F (proj0 z).
let z. assume Hz. apply CD_proj0_1 z Hz. exact (fun H _ => H).
Qed.

Theorem CD_proj1R: forall z, CD_carr z -> F (proj1 z).
let z. assume Hz. apply CD_proj1_1 z Hz. exact (fun H _ => H).
Qed.

Theorem CD_proj0proj1_eta: forall z, CD_carr z -> z = pa (proj0 z) (proj1 z).
let z. assume Hz. apply CD_proj1_1 z Hz. exact (fun _ H => H).
Qed.

Theorem CD_proj0proj1_split: forall z w, CD_carr z -> CD_carr w -> proj0 z = proj0 w -> proj1 z = proj1 w -> z = w.
let z w. assume Hz Hw.
assume H1 H2.
transitivity (pa (proj0 z) (proj1 z)).
- exact CD_proj0proj1_eta z Hz.
- transitivity (pa (proj0 w) (proj1 w)).
  + rewrite H1. rewrite H2. reflexivity.
  + symmetry. exact CD_proj0proj1_eta w Hw.
Qed.

Theorem CD_proj0_F: F 0 -> forall x, F x -> CD_proj0 x = x.
assume H0.
let x. assume Hx.
rewrite <- pair_tag_0 x at 1.
prove CD_proj0 (pair_tag x 0) = x.
exact CD_proj0_2 x 0 Hx H0.
Qed.

Theorem CD_proj1_F: F 0 -> forall x, F x -> CD_proj1 x = 0.
assume H0.
let x. assume Hx.
rewrite <- pair_tag_0 x at 1.
prove CD_proj1 (pair_tag x 0) = 0.
exact CD_proj1_2 x 0 Hx H0.
Qed.

Section CD_minus_conj.

Variable minus:set -> set.
Prefix - 358 := minus.

Definition CD_minus : set -> set := fun z => pa (- proj0 z) (- proj1 z).

Prefix :-: 358 := CD_minus.


Variable conj:set -> set.
Definition CD_conj : set -> set := fun z => pa (conj (proj0 z)) (- proj1 z).

End CD_minus_conj.

Section CD_add.

Variable add:set -> set -> set.
Infix + 360 right := add.

Definition CD_add : set -> set -> set := fun z w => pa (proj0 z + proj0 w) (proj1 z + proj1 w).

End CD_add.

Section CD_mul.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.

Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Definition CD_mul : set -> set -> set := fun z w => pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
Infix :*: 355 right := CD_mul.

Definition CD_exp_nat : set -> set -> set := fun z m => nat_primrec 1 (fun _ r => z :*: r) m.

End CD_mul.

Section CD_minus_conj_clos.

Variable minus:set -> set.
Prefix - 358 := minus.
Prefix :-: 358 := CD_minus minus.

Hypothesis F_minus: forall x, F x -> F (- x).

Theorem CD_minus_CD: forall z, CD_carr z -> CD_carr (:-: z).
let z. assume Hz.
prove CD_carr (pa (- proj0 z) (- proj1 z)).
apply CD_carr_I.
- apply F_minus. apply CD_proj0R. exact Hz.
- apply F_minus. apply CD_proj1R. exact Hz.
Qed.

Theorem CD_minus_proj0: forall z, CD_carr z -> proj0 (:-: z) = - proj0 z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove proj0 (pa (- proj0 z) (- proj1 z)) = - proj0 z.
exact CD_proj0_2 (- proj0 z) (- proj1 z) ?? ??.
Qed.

Theorem CD_minus_proj1: forall z, CD_carr z -> proj1 (:-: z) = - proj1 z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove proj1 (pa (- proj0 z) (- proj1 z)) = - proj1 z.
exact CD_proj1_2 (- proj0 z) (- proj1 z) ?? ??.
Qed.

Variable conj:set -> set.
Postfix ' 100 := CD_conj minus conj.

Hypothesis F_conj: forall x, F x -> F (conj x).

Theorem CD_conj_CD: forall z, CD_carr z -> CD_carr (z ').
let z. assume Hz.
prove CD_carr (pa (conj (proj0 z)) (- proj1 z)).
apply CD_carr_I.
- apply F_conj. apply CD_proj0R. exact Hz.
- apply F_minus. apply CD_proj1R. exact Hz.
Qed.

Theorem CD_conj_proj0: forall z, CD_carr z -> proj0 (z ') = conj (proj0 z).
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove proj0 (pa (conj (proj0 z)) (- proj1 z)) = conj (proj0 z).
exact CD_proj0_2 (conj (proj0 z)) (- proj1 z) ?? ??.
Qed.

Theorem CD_conj_proj1: forall z, CD_carr z -> proj1 (z ') = - proj1 z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove proj1 (pa (conj (proj0 z)) (- proj1 z)) = - proj1 z.
exact CD_proj1_2 (conj (proj0 z)) (- proj1 z) ?? ??.
Qed.

End CD_minus_conj_clos.

Section CD_add_clos.

Variable add:set -> set -> set.
Infix + 360 right := add.
Infix :+: 360 right := CD_add add.

Hypothesis F_add: forall x y, F x -> F y -> F (x + y).

Theorem CD_add_CD: forall z w, CD_carr z -> CD_carr w -> CD_carr (z :+: w).
let z w. assume Hz Hw.
prove CD_carr (pa (proj0 z + proj0 w) (proj1 z + proj1 w)).
apply CD_carr_I.
- apply F_add.
  + apply CD_proj0R. exact Hz.
  + apply CD_proj0R. exact Hw.
- apply F_add.
  + apply CD_proj1R. exact Hz.
  + apply CD_proj1R. exact Hw.
Qed.

Theorem CD_add_proj0: forall z w, CD_carr z -> CD_carr w -> proj0 (z :+: w) = proj0 z + proj0 w.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
exact CD_proj0_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
Qed.

Theorem CD_add_proj1: forall z w, CD_carr z -> CD_carr w -> proj1 (z :+: w) = proj1 z + proj1 w.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
exact CD_proj1_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
Qed.

End CD_add_clos.

Section CD_mul_clos.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.

Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).

Theorem CD_mul_CD: forall z w, CD_carr z -> CD_carr w -> CD_carr (z :*: w).
let z w. assume Hz Hw.
prove CD_carr (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w))).
apply CD_carr_I.
- apply F_add.
  + apply F_mul.
    * apply CD_proj0R. exact Hz.
    * apply CD_proj0R. exact Hw.
  + apply F_minus.
    apply F_mul.
    * apply F_conj. apply CD_proj1R. exact Hw.
    * apply CD_proj1R. exact Hz.
- apply F_add.
  + apply F_mul.
    * apply CD_proj1R. exact Hw.
    * apply CD_proj0R. exact Hz.
  + apply F_mul.
    * apply CD_proj1R. exact Hz.
    * apply F_conj. apply CD_proj0R. exact Hw.
Qed.

Theorem CD_mul_proj0: forall z w, CD_carr z -> CD_carr w -> proj0 (z :*: w) = proj0 z * proj0 w + - conj (proj1 w) * proj1 z.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact ??. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact ??. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim LzwL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzwR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
exact CD_proj0_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                 (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                 ?? ??.
Qed.

Theorem CD_mul_proj1: forall z w, CD_carr z -> CD_carr w -> proj1 (z :*: w) = proj1 w * proj0 z + proj1 z * conj (proj0 w).
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact ??. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact ??. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim LzwL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzwR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
exact CD_proj1_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                 (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                 ?? ??.
Qed.

End CD_mul_clos.

Section CD_minus_conj_F.

Variable minus:set -> set.
Prefix - 358 := minus.
Prefix :-: 358 := CD_minus minus.

Hypothesis F_0 : F 0.
Hypothesis F_minus_0: - 0 = 0.

Theorem CD_minus_F_eq: forall x, F x -> :-: x = - x.
let x. assume Hx.
prove pa (- proj0 x) (- proj1 x) = - x.
rewrite CD_proj0_F F_0 x Hx.
rewrite CD_proj1_F F_0 x Hx.
rewrite F_minus_0.
prove pa (- x) 0 = - x.
exact pair_tag_0 (- x).
Qed.

Variable conj:set -> set.
Postfix ' 100 := CD_conj minus conj.

Theorem CD_conj_F_eq: forall x, F x -> x ' = conj x.
let x. assume Hx.
prove pa (conj (proj0 x)) (- proj1 x) = conj x.
rewrite CD_proj0_F F_0 x Hx.
rewrite CD_proj1_F F_0 x Hx.
rewrite F_minus_0.
prove pa (conj x) 0 = conj x.
exact pair_tag_0 (conj x).
Qed.

End CD_minus_conj_F.

Section CD_add_F.

Variable add:set -> set -> set.
Infix + 360 right := add.

Infix :+: 360 right := CD_add add.

Hypothesis F_0 : F 0.
Hypothesis F_add_0_0: 0 + 0 = 0.

Theorem CD_add_F_eq: forall x y, F x -> F y -> x :+: y = x + y.
let x y. assume Hx Hy.
prove pa (proj0 x + proj0 y) (proj1 x + proj1 y) = x + y.
rewrite CD_proj0_F F_0 x Hx.
rewrite CD_proj1_F F_0 x Hx.
rewrite CD_proj0_F F_0 y Hy.
rewrite CD_proj1_F F_0 y Hy.
rewrite F_add_0_0.
prove pa (x + y) 0 = x + y.
exact pair_tag_0 (x + y).
Qed.

End CD_add_F.

Section CD_mul_F.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.

Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_0 : F 0.
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_add_0R: forall x, F x -> x + 0 = x.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_0R: forall x, F x -> x * 0 = 0.

Theorem CD_mul_F_eq: forall x y, F x -> F y -> x :*: y = x * y.
let x y. assume Hx Hy.
prove pa (proj0 x * proj0 y + - conj (proj1 y) * proj1 x) (proj1 y * proj0 x + proj1 x * conj (proj0 y)) = x * y.
rewrite CD_proj0_F F_0 x Hx.
rewrite CD_proj1_F F_0 x Hx.
rewrite CD_proj0_F F_0 y Hy.
rewrite CD_proj1_F F_0 y Hy.
prove pa (x * y + - conj 0 * 0) (0 * x + 0 * conj y) = x * y.
rewrite F_mul_0R (conj 0) (F_conj 0 F_0).
rewrite F_mul_0L x Hx.
rewrite F_mul_0L (conj y) (F_conj y Hy).
rewrite F_minus_0.
rewrite F_add_0R 0 F_0.
rewrite F_add_0R (x * y) (F_mul x y Hx Hy).
prove pa (x * y) 0 = x * y.
exact pair_tag_0 (x * y).
Qed.

End CD_mul_F.

Section CD_minus_invol.

Variable minus:set -> set.
Prefix - 358 := minus.
Prefix :-: 358 := CD_minus minus.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_minus_invol: forall x, F x -> - - x = x.

Theorem CD_minus_invol: forall z, CD_carr z -> :-: :-: z = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove pa (- proj0 (pa (- proj0 z) (- proj1 z))) (- proj1 (pa (- proj0 z) (- proj1 z))) = z.
rewrite CD_proj0_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite CD_proj1_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite F_minus_invol (proj0 z) Lp0z.
rewrite F_minus_invol (proj1 z) Lp1z.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_minus_invol.

Section CD_conj_invol.

Variable minus:set -> set.
Variable conj:set -> set.

Prefix - 358 := minus.
Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_minus_invol: forall x, F x -> - - x = x.
Hypothesis F_conj_invol: forall x, F x -> conj (conj x) = x.

Theorem CD_conj_invol: forall z, CD_carr z -> z ' ' = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove pa (conj (proj0 (pa (conj (proj0 z)) (- proj1 z)))) (- proj1 (pa (conj (proj0 z)) (- proj1 z))) = z.
rewrite CD_proj0_2 (conj (proj0 z)) (- proj1 z) Lcp0z Lmp1z.
rewrite CD_proj1_2 (conj (proj0 z)) (- proj1 z) Lcp0z Lmp1z.
rewrite F_conj_invol (proj0 z) Lp0z.
rewrite F_minus_invol (proj1 z) Lp1z.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_conj_invol.

Section CD_conj_minus.

Variable minus:set -> set.
Variable conj:set -> set.
Prefix - 358 := minus.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_conj_minus: forall x, F x -> conj (- x) = - conj x.

Theorem CD_conj_minus: forall z, CD_carr z -> (:-: z) ' = :-: (z ').
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lcmp0z: F (conj (- proj0 z)).
{ apply F_conj. exact Lmp0z. }
prove pa (conj (proj0 (pa (- (proj0 z)) (- (proj1 z)))))
         (- proj1 (pa (- (proj0 z)) (- (proj1 z))))
    = pa (- proj0 (pa (conj (proj0 z)) (- proj1 z)))
         (- proj1 (pa (conj (proj0 z)) (- proj1 z))).
f_equal.
- prove conj (proj0 (pa (- (proj0 z)) (- (proj1 z))))
      = - proj0 (pa (conj (proj0 z)) (- proj1 z)).
  rewrite CD_proj0_2 (- proj0 z) (- proj1 z) ?? ??.
  rewrite CD_proj0_2 (conj (proj0 z)) (- proj1 z) ?? ??.
  prove conj (- proj0 z) = - conj (proj0 z).
  exact F_conj_minus (proj0 z) ??.
- prove - proj1 (pa (- (proj0 z)) (- (proj1 z)))
      = - proj1 (pa (conj (proj0 z)) (- proj1 z)).
  f_equal.
  rewrite CD_proj1_2 (conj (proj0 z)) (- (proj1 z)) ?? ??.
  exact CD_proj1_2 (- (proj0 z)) (- (proj1 z)) ?? ??.
Qed.

End CD_conj_minus.

Section CD_minus_add.

Variable minus:set -> set.
Variable add:set -> set -> set.

Prefix - 358 := minus.
Infix + 360 right := add.

Prefix :-: 358 := CD_minus minus.
Infix :+: 360 right := CD_add add.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.

Theorem CD_minus_add: forall z w, CD_carr z -> CD_carr w -> :-: (z :+: w) = :-: z :+: :-: w.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lmp0w: F (- proj0 w).
{ apply F_minus. exact Lp0w. }
claim Lmp1w: F (- proj1 w).
{ apply F_minus. exact Lp1w. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
prove pa (- proj0 (pa (proj0 z + proj0 w) (proj1 z + proj1 w)))
         (- proj1 (pa (proj0 z + proj0 w) (proj1 z + proj1 w)))
    = pa (proj0 (pa (- proj0 z) (- proj1 z)) + proj0 (pa (- proj0 w) (- proj1 w)))
         (proj1 (pa (- proj0 z) (- proj1 z)) + proj1 (pa (- proj0 w) (- proj1 w))).
rewrite CD_proj0_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj1_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj0_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite CD_proj1_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite CD_proj0_2 (- proj0 w) (- proj1 w) Lmp0w Lmp1w.
rewrite CD_proj1_2 (- proj0 w) (- proj1 w) Lmp0w Lmp1w.
f_equal.
- apply F_minus_add.
  + exact ??.
  + exact ??.
- apply F_minus_add.
  + exact ??.
  + exact ??.
Qed.

End CD_minus_add.

Section CD_conj_add.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.

Prefix - 358 := minus.
Infix + 360 right := add.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_conj_add: forall x y, F x -> F y -> conj (x + y) = conj x + conj y.

Theorem CD_conj_add: forall z w, CD_carr z -> CD_carr w -> (z :+: w) ' = z ' :+: w '.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact Lp0w. }
claim Lmp1w: F (- proj1 w).
{ apply F_minus. exact Lp1w. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
prove pa (conj (proj0 (pa (proj0 z + proj0 w) (proj1 z + proj1 w))))
         (- proj1 (pa (proj0 z + proj0 w) (proj1 z + proj1 w)))
    = pa (proj0 (pa (conj (proj0 z)) (- proj1 z)) + proj0 (pa (conj (proj0 w)) (- proj1 w)))
         (proj1 (pa (conj (proj0 z)) (- proj1 z)) + proj1 (pa (conj (proj0 w)) (- proj1 w))).
rewrite CD_proj0_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj1_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj0_2 (conj (proj0 z)) (- proj1 z) Lcp0z Lmp1z.
rewrite CD_proj1_2 (conj (proj0 z)) (- proj1 z) Lcp0z Lmp1z.
rewrite CD_proj0_2 (conj (proj0 w)) (- proj1 w) Lcp0w Lmp1w.
rewrite CD_proj1_2 (conj (proj0 w)) (- proj1 w) Lcp0w Lmp1w.
f_equal.
- apply F_conj_add.
  + exact ??.
  + exact ??.
- apply F_minus_add.
  + exact ??.
  + exact ??.
Qed.

End CD_conj_add.

Section CD_add_com.

Variable add:set -> set -> set.
Infix + 360 right := add.
Infix :+: 360 right := CD_add add.

Hypothesis F_add_com: forall x y, F x -> F y -> x + y = y + x.

Theorem CD_add_com: forall z w, CD_carr z -> CD_carr w -> z :+: w = w :+: z.
let z w.
assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
prove pa (proj0 z + proj0 w) (proj1 z + proj1 w)
    = pa (proj0 w + proj0 z) (proj1 w + proj1 z).
f_equal.
- apply F_add_com.
  + exact ??.
  + exact ??.
- apply F_add_com.
  + exact ??.
  + exact ??.
Qed.

End CD_add_com.

Section CD_add_assoc.

Variable add:set -> set -> set.
Infix + 360 right := add.
Infix :+: 360 right := CD_add add.

Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_add_assoc: forall x y z, F x -> F y -> F z -> (x + y) + z = x + (y + z).

Theorem CD_add_assoc: forall z w u, CD_carr z -> CD_carr w -> CD_carr u -> (z :+: w) :+: u = z :+: (w :+: u).
let z w u.
assume Hz Hw Hu.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lp0u: F (proj0 u).
{ exact CD_proj0R u Hu. }
claim Lp1u: F (proj1 u).
{ exact CD_proj1R u Hu. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp0wu: F (proj0 w + proj0 u).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wu: F (proj1 w + proj1 u).
{ apply F_add.
  - exact ??.
  - exact ??.
}
set zw := pa (proj0 z + proj0 w) (proj1 z + proj1 w).
set wu := pa (proj0 w + proj0 u) (proj1 w + proj1 u).
prove pa (proj0 zw + proj0 u) (proj1 zw + proj1 u)
    = pa (proj0 z + proj0 wu) (proj1 z + proj1 wu).
rewrite CD_proj0_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj1_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj0_2 (proj0 w + proj0 u) (proj1 w + proj1 u) ?? ??.
rewrite CD_proj1_2 (proj0 w + proj0 u) (proj1 w + proj1 u) ?? ??.
f_equal.
- apply F_add_assoc.
  + exact ??.
  + exact ??.
  + exact ??.
- apply F_add_assoc.
  + exact ??.
  + exact ??.
  + exact ??.
Qed.

End CD_add_assoc.

Section CD_add_0R.

Variable add:set -> set -> set.
Infix + 360 right := add.
Infix :+: 360 right := CD_add add.

Hypothesis F_0: F 0.
Hypothesis F_add_0R: forall x, F x -> x + 0 = x.

Theorem CD_add_0R: forall z, CD_carr z -> z :+: 0 = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
prove pa (proj0 z + proj0 0) (proj1 z + proj1 0) = z.
rewrite CD_proj0_F F_0 0 F_0.
rewrite CD_proj1_F F_0 0 F_0.
rewrite F_add_0R (proj0 z) ??.
rewrite F_add_0R (proj1 z) ??.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_add_0R.

Section CD_add_0L.

Variable add:set -> set -> set.
Infix + 360 right := add.
Infix :+: 360 right := CD_add add.

Hypothesis F_0: F 0.
Hypothesis F_add_0L: forall x, F x -> 0 + x = x.

Theorem CD_add_0L: forall z, CD_carr z -> 0 :+: z = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
prove pa (proj0 0 + proj0 z) (proj1 0 + proj1 z) = z.
rewrite CD_proj0_F F_0 0 F_0.
rewrite CD_proj1_F F_0 0 F_0.
rewrite F_add_0L (proj0 z) ??.
rewrite F_add_0L (proj1 z) ??.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_add_0L.

Section CD_add_minus_linv.

Variable minus:set -> set.
Variable add:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Prefix :-: 358 := CD_minus minus.
Infix :+: 360 right := CD_add add.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_add_minus_linv: forall x, F x -> - x + x = 0.

Theorem CD_add_minus_linv : forall z, CD_carr z -> :-: z :+: z = 0.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove :-: z :+: z = 0.
prove pa (proj0 (pa (- proj0 z) (- proj1 z)) + proj0 z)
         (proj1 (pa (- proj0 z) (- proj1 z)) + proj1 z)
    = 0.
rewrite CD_proj0_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite CD_proj1_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite F_add_minus_linv (proj0 z) Lp0z.
rewrite F_add_minus_linv (proj1 z) Lp1z.
prove pa 0 0 = 0.
exact pair_tag_0 0.
Qed.

End CD_add_minus_linv.

Section CD_add_minus_rinv.

Variable minus:set -> set.
Variable add:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Prefix :-: 358 := CD_minus minus.
Infix :+: 360 right := CD_add add.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_add_minus_rinv: forall x, F x -> x + - x = 0.

Theorem CD_add_minus_rinv : forall z, CD_carr z -> z :+: :-: z = 0.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact Lp0z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
prove pa (proj0 z + proj0 (pa (- proj0 z) (- proj1 z)))
         (proj1 z + proj1 (pa (- proj0 z) (- proj1 z)))
    = 0.
rewrite CD_proj0_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite CD_proj1_2 (- proj0 z) (- proj1 z) Lmp0z Lmp1z.
rewrite F_add_minus_rinv (proj0 z) Lp0z.
rewrite F_add_minus_rinv (proj1 z) Lp1z.
prove pa 0 0 = 0.
exact pair_tag_0 0.
Qed.

End CD_add_minus_rinv.

Section CD_mul_0R.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_0: F 0.
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_conj_0: conj 0 = 0.
Hypothesis F_add_0_0: 0 + 0 = 0.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_0R: forall x, F x -> x * 0 = 0.

Theorem CD_mul_0R: forall z, CD_carr z -> z :*: 0 = 0.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
prove pa (proj0 z * proj0 0 + - conj (proj1 0) * proj1 z)
         (proj1 0 * proj0 z + proj1 z * conj (proj0 0))
    = 0.
rewrite CD_proj0_F F_0 0 F_0.
rewrite CD_proj1_F F_0 0 F_0.
prove pa (proj0 z * 0 + - conj 0 * proj1 z)
         (0 * proj0 z + proj1 z * conj 0)
    = 0.
rewrite F_conj_0.
prove pa (proj0 z * 0 + - 0 * proj1 z)
         (0 * proj0 z + proj1 z * 0)
    = 0.
rewrite F_mul_0L (proj0 z) ??.
rewrite F_mul_0L (proj1 z) ??.
rewrite F_mul_0R (proj0 z) ??.
rewrite F_mul_0R (proj1 z) ??.
rewrite F_minus_0.
prove pa (0 + 0) (0 + 0) = 0.
rewrite F_add_0_0.
prove pa 0 0 = 0.
exact pair_tag_0 0.
Qed.

End CD_mul_0R.

Section CD_mul_0L.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_0: F 0.
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_add_0_0: 0 + 0 = 0.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_0R: forall x, F x -> x * 0 = 0.

Theorem CD_mul_0L: forall z, CD_carr z -> 0 :*: z = 0.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lcp1z: F (conj (proj1 z)).
{ apply F_conj. exact Lp1z. }
prove pa (proj0 0 * proj0 z + - conj (proj1 z) * proj1 0)
         (proj1 z * proj0 0 + proj1 0 * conj (proj0 z))
    = 0.
rewrite CD_proj0_F F_0 0 F_0.
rewrite CD_proj1_F F_0 0 F_0.
prove pa (0 * proj0 z + - conj (proj1 z) * 0)
         (proj1 z * 0 + 0 * conj (proj0 z))
    = 0.
rewrite F_mul_0L (proj0 z) ??.
rewrite F_mul_0L (conj (proj0 z)) ??.
rewrite F_mul_0R (conj (proj1 z)) ??.
rewrite F_mul_0R (proj1 z) ??.
rewrite F_minus_0.
prove pa (0 + 0) (0 + 0) = 0.
rewrite F_add_0_0.
prove pa 0 0 = 0.
exact pair_tag_0 0.
Qed.

End CD_mul_0L.

Section CD_mul_1R.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_0: F 0.
Hypothesis F_1: F 1.
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_conj_0: conj 0 = 0.
Hypothesis F_conj_1: conj 1 = 1.
Hypothesis F_add_0L: forall x, F x -> 0 + x = x.
Hypothesis F_add_0R: forall x, F x -> x + 0 = x.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_1R: forall x, F x -> x * 1 = x.

Theorem CD_mul_1R: forall z, CD_carr z -> z :*: 1 = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
prove pa (proj0 z * proj0 1 + - conj (proj1 1) * proj1 z)
         (proj1 1 * proj0 z + proj1 z * conj (proj0 1))
    = z.
rewrite CD_proj0_F F_0 1 F_1.
prove pa (proj0 z * 1 + - conj (proj1 1) * proj1 z)
         (proj1 1 * proj0 z + proj1 z * conj 1)
    = z.
rewrite CD_proj1_F F_0 1 F_1.
prove pa (proj0 z * 1 + - conj 0 * proj1 z)
         (0 * proj0 z + proj1 z * conj 1)
    = z.
rewrite F_conj_0.
rewrite F_conj_1.
prove pa (proj0 z * 1 + - 0 * proj1 z)
         (0 * proj0 z + proj1 z * 1)
    = z.
rewrite F_mul_1R (proj0 z) ??.
rewrite F_mul_1R (proj1 z) ??.
rewrite F_mul_0L (proj0 z) ??.
rewrite F_mul_0L (proj1 z) ??.
prove pa (proj0 z + - 0) (0 + proj1 z) = z.
rewrite F_minus_0.
prove pa (proj0 z + 0) (0 + proj1 z) = z.
rewrite F_add_0L (proj1 z) ??.
rewrite F_add_0R (proj0 z) ??.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_mul_1R.

Section CD_mul_1L.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_0: F 0.
Hypothesis F_1: F 1.
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_add_0R: forall x, F x -> x + 0 = x.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_0R: forall x, F x -> x * 0 = 0.
Hypothesis F_mul_1L: forall x, F x -> 1 * x = x.
Hypothesis F_mul_1R: forall x, F x -> x * 1 = x.

Theorem CD_mul_1L: forall z, CD_carr z -> 1 :*: z = z.
let z. assume Hz.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lcp1z: F (conj (proj1 z)).
{ apply F_conj. exact Lp1z. }
prove pa (proj0 1 * proj0 z + - conj (proj1 z) * proj1 1)
         (proj1 z * proj0 1 + proj1 1 * conj (proj0 z))
    = z.
rewrite CD_proj0_F F_0 1 F_1.
rewrite CD_proj1_F F_0 1 F_1.
prove pa (1 * proj0 z + - conj (proj1 z) * 0)
         (proj1 z * 1 + 0 * conj (proj0 z))
    = z.
rewrite F_mul_1L (proj0 z) ??.
rewrite F_mul_1R (proj1 z) ??.
rewrite F_mul_0L (conj (proj0 z)) ??.
rewrite F_mul_0R (conj (proj1 z)) ??.
prove pa (proj0 z + - 0) (proj1 z + 0) = z.
rewrite F_minus_0.
rewrite F_add_0R (proj0 z) ??.
rewrite F_add_0R (proj1 z) ??.
prove pa (proj0 z) (proj1 z) = z.
symmetry.
exact CD_proj0proj1_eta z Hz.
Qed.

End CD_mul_1L.

Section CD_conj_mul.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_minus_invol: forall x, F x -> - - x = x.
Hypothesis F_conj_invol: forall x, F x -> conj (conj x) = x.
Hypothesis F_conj_minus: forall x, F x -> conj (- x) = - conj x.
Hypothesis F_conj_add: forall x y, F x -> F y -> conj (x + y) = conj x + conj y.
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_add_com: forall x y, F x -> F y -> x + y = y + x.
Hypothesis F_conj_mul: forall x y, F x -> F y -> conj (x * y) = conj y * conj x.
Hypothesis F_minus_mul_distrR: forall x y, F x -> F y -> x * (- y) = - (x * y).
Hypothesis F_minus_mul_distrL: forall x y, F x -> F y -> (- x) * y = - (x * y).

Theorem CD_conj_mul: forall z w, CD_carr z -> CD_carr w -> (z :*: w) ' = w ' :*: z '.
let z w. assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lcp0z: F (conj (proj0 z)).
{ apply F_conj. exact Lp0z. }
claim Lcp1z: F (conj (proj1 z)).
{ apply F_conj. exact Lp1z. }
claim Lmcp1z: F (- conj (proj1 z)).
{ apply F_minus. exact Lcp1z. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact Lp1z. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact Lp0w. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact Lp1w. }
claim Lmp1w: F (- proj1 w).
{ apply F_minus. exact Lp1w. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim LzwL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzwR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
set w' := pa (conj (proj0 w)) (- proj1 w).
set z' := pa (conj (proj0 z)) (- proj1 z).
claim Lp0w': F (proj0 w').
{ exact CD_proj0R (CD_conj minus conj w) (CD_conj_CD minus F_minus conj F_conj w Hw). }
claim Lp1w': F (proj1 w').
{ exact CD_proj1R (CD_conj minus conj w) (CD_conj_CD minus F_minus conj F_conj w Hw). }
claim Lp0z': F (proj0 z').
{ exact CD_proj0R (CD_conj minus conj z) (CD_conj_CD minus F_minus conj F_conj z Hz). }
claim Lp1z': F (proj1 z').
{ exact CD_proj1R (CD_conj minus conj z) (CD_conj_CD minus F_minus conj F_conj z Hz). }
claim Lcp0z': F (conj (proj0 z')).
{ apply F_conj. exact ??. }
claim Lcp1z': F (conj (proj1 z')).
{ apply F_conj. exact ??. }
claim Lp0w'p0z': F (proj0 w' * proj0 z').
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1z'p1w': F (conj (proj1 z') * proj1 w').
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1z'p1w': F (- conj (proj1 z') * proj1 w').
{ apply F_minus. exact ??. }
claim Lw'z'L: F (proj0 w' * proj0 z' + - conj (proj1 z') * proj1 w').
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1z'p0w': F (proj1 z' * proj0 w').
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1w'cp0z': F (proj1 w' * conj (proj0 z')).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lw'z'R: F (proj1 z' * proj0 w' + proj1 w' * conj (proj0 z')).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lcp1zp1w: F (conj (proj1 z) * proj1 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lmp1zcp0w: F ((- proj1 z) * (conj (proj0 w))).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lmp1wp0z: F ((- proj1 w) * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
prove pa (conj (proj0 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)))))
         (- (proj1 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)))))
    = pa (proj0 w' * proj0 z' + - conj (proj1 z') * proj1 w') (proj1 z' * proj0 w' + proj1 w' * conj (proj0 z')).
rewrite CD_proj0_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)) ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)) ?? ??.
prove pa (conj (proj0 z * proj0 w + - conj (proj1 w) * proj1 z))
         (- (proj1 w * proj0 z + proj1 z * conj (proj0 w)))
    = pa (proj0 w' * proj0 z' + - conj (proj1 z') * proj1 w') (proj1 z' * proj0 w' + proj1 w' * conj (proj0 z')).
rewrite CD_proj0_2 (conj (proj0 w)) (- proj1 w) ?? ??.
rewrite CD_proj1_2 (conj (proj0 w)) (- proj1 w) ?? ??.
rewrite CD_proj0_2 (conj (proj0 z)) (- proj1 z) ?? ??.
rewrite CD_proj1_2 (conj (proj0 z)) (- proj1 z) ?? ??.
prove pa (conj (proj0 z * proj0 w + - conj (proj1 w) * proj1 z))
         (- (proj1 w * proj0 z + proj1 z * conj (proj0 w)))
    = pa (conj (proj0 w) * conj (proj0 z) + - conj (- proj1 z) * (- proj1 w))
         ((- proj1 z) * (conj (proj0 w)) + (- proj1 w) * conj (conj (proj0 z))).
f_equal.
- prove conj (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
      = conj (proj0 w) * conj (proj0 z) + - conj (- proj1 z) * (- proj1 w).
  rewrite F_conj_add (proj0 z * proj0 w) (- conj (proj1 w) * proj1 z) ?? ??.
  prove conj (proj0 z * proj0 w) + conj (- conj (proj1 w) * proj1 z)
      = conj (proj0 w) * conj (proj0 z) + - conj (- proj1 z) * (- proj1 w).
  f_equal.
  + prove conj (proj0 z * proj0 w) = conj (proj0 w) * conj (proj0 z).
    exact F_conj_mul (proj0 z) (proj0 w) ?? ??.
  + prove conj (- conj (proj1 w) * proj1 z) = - conj (- proj1 z) * (- proj1 w).
    rewrite F_conj_minus (conj (proj1 w) * proj1 z) ??.
    f_equal.
    prove conj (conj (proj1 w) * proj1 z) = conj (- proj1 z) * (- proj1 w).
    rewrite F_conj_mul (conj (proj1 w)) (proj1 z) ?? ??.
    prove conj (proj1 z) * (conj (conj (proj1 w))) = conj (- proj1 z) * (- proj1 w).
    rewrite F_conj_invol (proj1 w) ??.
    prove conj (proj1 z) * proj1 w = conj (- proj1 z) * (- proj1 w).
    rewrite F_conj_minus (proj1 z) ??.
    prove conj (proj1 z) * proj1 w = (- conj (proj1 z)) * (- proj1 w).
    rewrite F_minus_mul_distrR (- conj (proj1 z)) (proj1 w) ?? ??.
    rewrite F_minus_mul_distrL (conj (proj1 z)) (proj1 w) ?? ??.
    symmetry.
    apply F_minus_invol (conj (proj1 z) * proj1 w) ??.
- prove - (proj1 w * proj0 z + proj1 z * conj (proj0 w))
      = (- proj1 z) * (conj (proj0 w)) + (- proj1 w) * conj (conj (proj0 z)).
  rewrite F_conj_invol (proj0 z) ??.
  rewrite F_minus_add (proj1 w * proj0 z) (proj1 z * conj (proj0 w)) ?? ??.
  rewrite F_add_com ((- proj1 z) * (conj (proj0 w))) ((- proj1 w) * proj0 z) ?? ??.
  f_equal.
  + prove - proj1 w * proj0 z = (- proj1 w) * proj0 z.
    symmetry.
    exact F_minus_mul_distrL (proj1 w) (proj0 z) ?? ??.
  + prove - proj1 z * conj (proj0 w) = (- proj1 z) * (conj (proj0 w)).
    symmetry.
    exact F_minus_mul_distrL (proj1 z) (conj (proj0 w)) ?? ??.
Qed.

End CD_conj_mul.

Section CD_add_mul_distrR.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_add_assoc: forall x y z, F x -> F y -> F z -> (x + y) + z = x + (y + z).
Hypothesis F_add_com: forall x y, F x -> F y -> x + y = y + x.
Hypothesis F_add_mul_distrL: forall x y z, F x -> F y -> F z -> x * (y + z) = x * y + x * z.
Hypothesis F_add_mul_distrR: forall x y z, F x -> F y -> F z -> (x + y) * z = x * z + y * z.

Theorem CD_add_mul_distrR: forall z w u, CD_carr z -> CD_carr w -> CD_carr u -> (z :+: w) :*: u = z :*: u :+: w :*: u.
claim L_add_4_inner_mid: forall x y z w, F x -> F y -> F z -> F w -> (x + y) + (z + w) = (x + z) + (y + w).
{ let x y z w.
  assume Hx Hy Hz Hw.
  rewrite <- F_add_assoc (x + y) z w (F_add x y Hx Hy) Hz Hw.
  prove ((x + y) + z) + w = (x + z) + (y + w).
  rewrite F_add_assoc x y z Hx Hy Hz.
  prove (x + (y + z)) + w = (x + z) + (y + w).
  rewrite F_add_com y z Hy Hz.
  prove (x + (z + y)) + w = (x + z) + (y + w).
  rewrite <- F_add_assoc x z y Hx Hz Hy.
  prove ((x + z) + y) + w = (x + z) + (y + w).
  exact F_add_assoc (x + z) y w (F_add x z Hx Hz) Hy Hw.
}
let z w u.
assume Hz Hw Hu.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lp0u: F (proj0 u).
{ exact CD_proj0R u Hu. }
claim Lp1u: F (proj1 u).
{ exact CD_proj1R u Hu. }
claim Lp0zw: F (proj0 z + proj0 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1zw: F (proj1 z + proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lcp0u: F (conj (proj0 u)).
{ apply F_conj. exact ??. }
claim Lcp1u: F (conj (proj1 u)).
{ apply F_conj. exact ??. }
claim Lp0zp0u: F (proj0 z * proj0 u).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1z: F (conj (proj1 u) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1z: F (- conj (proj1 u) * proj1 z).
{ apply F_minus. exact ??. }
claim LzuL: F (proj0 z * proj0 u + - conj (proj1 u) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1up0z: F (proj1 u * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0u: F (proj1 z * conj (proj0 u)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzuR: F (proj1 u * proj0 z + proj1 z * conj (proj0 u)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp0wp0u: F (proj0 w * proj0 u).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1w: F (conj (proj1 u) * proj1 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1w: F (- conj (proj1 u) * proj1 w).
{ apply F_minus. exact ??. }
claim LwuL: F (proj0 w * proj0 u + - conj (proj1 u) * proj1 w).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1up0w: F (proj1 u * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1wcp0u: F (proj1 w * conj (proj0 u)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LwuR: F (proj1 u * proj0 w + proj1 w * conj (proj0 u)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
set zw := pa (proj0 z + proj0 w) (proj1 z + proj1 w).
set zu := pa (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)).
set wu := pa (proj0 w * proj0 u + - conj (proj1 u) * proj1 w) (proj1 u * proj0 w + proj1 w * conj (proj0 u)).
prove pa (proj0 zw * proj0 u + - conj (proj1 u) * proj1 zw)
         (proj1 u * proj0 zw + proj1 zw * conj (proj0 u))
    = pa (proj0 zu + proj0 wu) (proj1 zu + proj1 wu).
rewrite CD_proj0_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
rewrite CD_proj1_2 (proj0 z + proj0 w) (proj1 z + proj1 w) ?? ??.
prove pa ((proj0 z + proj0 w) * proj0 u + - conj (proj1 u) * (proj1 z + proj1 w))
         (proj1 u * (proj0 z + proj0 w) + (proj1 z + proj1 w) * conj (proj0 u))
    = pa (proj0 zu + proj0 wu) (proj1 zu + proj1 wu).
rewrite CD_proj0_2 (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)) ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)) ?? ??.
rewrite CD_proj0_2 (proj0 w * proj0 u + - conj (proj1 u) * proj1 w) (proj1 u * proj0 w + proj1 w * conj (proj0 u)) ?? ??.
rewrite CD_proj1_2 (proj0 w * proj0 u + - conj (proj1 u) * proj1 w) (proj1 u * proj0 w + proj1 w * conj (proj0 u)) ?? ??.
f_equal.
- prove (proj0 z + proj0 w) * proj0 u + - conj (proj1 u) * (proj1 z + proj1 w)
      = (proj0 z * proj0 u + - conj (proj1 u) * proj1 z)
      + (proj0 w * proj0 u + - conj (proj1 u) * proj1 w).
  rewrite L_add_4_inner_mid (proj0 z * proj0 u) (- conj (proj1 u) * proj1 z)
                            (proj0 w * proj0 u) (- conj (proj1 u) * proj1 w)
                            ?? ?? ?? ??.
  f_equal.
  + prove (proj0 z + proj0 w) * proj0 u = proj0 z * proj0 u + proj0 w * proj0 u.
    apply F_add_mul_distrR.
    * exact ??.
    * exact ??.
    * exact ??.
  + prove - conj (proj1 u) * (proj1 z + proj1 w) = (- conj (proj1 u) * proj1 z) + (- conj (proj1 u) * proj1 w).
    rewrite <- F_minus_add (conj (proj1 u) * proj1 z) (conj (proj1 u) * proj1 w) ?? ??.
    f_equal.
    prove conj (proj1 u) * (proj1 z + proj1 w) = (conj (proj1 u) * proj1 z) + (conj (proj1 u) * proj1 w).
    apply F_add_mul_distrL.
    * exact ??.
    * exact ??.
    * exact ??.
- prove (proj1 u * (proj0 z + proj0 w) + (proj1 z + proj1 w) * conj (proj0 u))
      = (proj1 u * proj0 z + proj1 z * conj (proj0 u))
      + (proj1 u * proj0 w + proj1 w * conj (proj0 u)).
  rewrite L_add_4_inner_mid (proj1 u * proj0 z) (proj1 z * conj (proj0 u))
                            (proj1 u * proj0 w) (proj1 w * conj (proj0 u))
                            ?? ?? ?? ??.
  f_equal.
  + apply F_add_mul_distrL.
    * exact ??.
    * exact ??.
    * exact ??.
  + apply F_add_mul_distrR.
    * exact ??.
    * exact ??.
    * exact ??.
Qed.

End CD_add_mul_distrR.

Section CD_add_mul_distrL.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_conj_add: forall x y, F x -> F y -> conj (x + y) = conj x + conj y.
Hypothesis F_add_assoc: forall x y z, F x -> F y -> F z -> (x + y) + z = x + (y + z).
Hypothesis F_add_com: forall x y, F x -> F y -> x + y = y + x.
Hypothesis F_add_mul_distrL: forall x y z, F x -> F y -> F z -> x * (y + z) = x * y + x * z.
Hypothesis F_add_mul_distrR: forall x y z, F x -> F y -> F z -> (x + y) * z = x * z + y * z.

Theorem CD_add_mul_distrL: forall z w u, CD_carr z -> CD_carr w -> CD_carr u -> z :*: (w :+: u) = z :*: w :+: z :*: u.
claim L_add_4_inner_mid: forall x y z w, F x -> F y -> F z -> F w -> (x + y) + (z + w) = (x + z) + (y + w).
{ let x y z w.
  assume Hx Hy Hz Hw.
  rewrite <- F_add_assoc (x + y) z w (F_add x y Hx Hy) Hz Hw.
  prove ((x + y) + z) + w = (x + z) + (y + w).
  rewrite F_add_assoc x y z Hx Hy Hz.
  prove (x + (y + z)) + w = (x + z) + (y + w).
  rewrite F_add_com y z Hy Hz.
  prove (x + (z + y)) + w = (x + z) + (y + w).
  rewrite <- F_add_assoc x z y Hx Hz Hy.
  prove ((x + z) + y) + w = (x + z) + (y + w).
  exact F_add_assoc (x + z) y w (F_add x z Hx Hz) Hy Hw.
}
let z w u.
assume Hz Hw Hu.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lp0u: F (proj0 u).
{ exact CD_proj0R u Hu. }
claim Lp1u: F (proj1 u).
{ exact CD_proj1R u Hu. }
claim Lp0wu: F (proj0 w + proj0 u).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wu: F (proj1 w + proj1 u).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact ??. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact ??. }
claim Lcp0u: F (conj (proj0 u)).
{ apply F_conj. exact ??. }
claim Lcp1u: F (conj (proj1 u)).
{ apply F_conj. exact ??. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim LzwL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzwR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp0zp0u: F (proj0 z * proj0 u).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1z: F (conj (proj1 u) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lcp1up1z: F (- conj (proj1 u) * proj1 z).
{ apply F_minus. exact ??. }
claim LzuL: F (proj0 z * proj0 u + - conj (proj1 u) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1up0z: F (proj1 u * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0u: F (proj1 z * conj (proj0 u)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LzuR: F (proj1 u * proj0 z + proj1 z * conj (proj0 u)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
set wu := pa (proj0 w + proj0 u) (proj1 w + proj1 u).
set zw := pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
set zu := pa (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)).
prove pa (proj0 z * proj0 wu + - conj (proj1 wu) * proj1 z)
         (proj1 wu * proj0 z + proj1 z * conj (proj0 wu))
    = pa (proj0 zw + proj0 zu) (proj1 zw + proj1 zu).
rewrite CD_proj0_2 (proj0 w + proj0 u) (proj1 w + proj1 u) ?? ??.
rewrite CD_proj1_2 (proj0 w + proj0 u) (proj1 w + proj1 u) ?? ??.
rewrite CD_proj0_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)) ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)) ?? ??.
rewrite CD_proj0_2 (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)) ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 u + - conj (proj1 u) * proj1 z) (proj1 u * proj0 z + proj1 z * conj (proj0 u)) ?? ??.
f_equal.
- rewrite L_add_4_inner_mid (proj0 z * proj0 w) (- conj (proj1 w) * proj1 z)
                            (proj0 z * proj0 u) (- conj (proj1 u) * proj1 z)
                            ?? ?? ?? ??.
  f_equal.
  + apply F_add_mul_distrL.
    * exact ??.
    * exact ??.
    * exact ??.
  + prove - conj (proj1 w + proj1 u) * proj1 z = (- conj (proj1 w) * proj1 z) + (- conj (proj1 u) * proj1 z).
    rewrite F_conj_add (proj1 w) (proj1 u) ?? ??.
    prove - (conj (proj1 w) + conj (proj1 u)) * proj1 z = (- conj (proj1 w) * proj1 z) + (- conj (proj1 u) * proj1 z).
    rewrite F_add_mul_distrR (conj (proj1 w)) (conj (proj1 u)) (proj1 z) ?? ?? ??.
    prove - (conj (proj1 w) * proj1 z + conj (proj1 u) * proj1 z) = (- conj (proj1 w) * proj1 z) + (- conj (proj1 u) * proj1 z).
    apply F_minus_add.
    * exact ??.
    * exact ??.
- rewrite L_add_4_inner_mid (proj1 w * proj0 z) (proj1 z * conj (proj0 w))
                            (proj1 u * proj0 z) (proj1 z * conj (proj0 u))
                            ?? ?? ?? ??.
  f_equal.
  + apply F_add_mul_distrR.
    * exact ??.
    * exact ??.
    * exact ??.
  + prove proj1 z * conj (proj0 w + proj0 u) = proj1 z * conj (proj0 w) + proj1 z * conj (proj0 u).
    rewrite F_conj_add (proj0 w) (proj0 u) ?? ??.
    apply F_add_mul_distrL.
    * exact ??.
    * exact ??.
    * exact ??.
Qed.

End CD_add_mul_distrL.

Section CD_minus_mul_distrR.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_conj_minus: forall x, F x -> conj (- x) = - conj x.
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_minus_mul_distrR: forall x y, F x -> F y -> x * (- y) = - (x * y).
Hypothesis F_minus_mul_distrL: forall x y, F x -> F y -> (- x) * y = - (x * y).

Theorem CD_minus_mul_distrR: forall z w, CD_carr z -> CD_carr w -> z :*: (:-: w) = :-: z :*: w.
let z w.
assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lmp0w: F (- proj0 w).
{ apply F_minus. exact ??. }
claim Lmp1w: F (- proj1 w).
{ apply F_minus. exact ??. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact ??. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact ??. }
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lmcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LmulL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LmulR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
prove pa (proj0 z * proj0 (pa (- proj0 w) (- proj1 w)) + - conj (proj1 (pa (- proj0 w) (- proj1 w))) * proj1 z)
         (proj1 (pa (- proj0 w) (- proj1 w)) * proj0 z + proj1 z * conj (proj0 (pa (- proj0 w) (- proj1 w))))
    = pa (- proj0 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w))))
         (- proj1 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)))).
rewrite CD_proj0_2 (- proj0 w) (- proj1 w) (F_minus (proj0 w) (CD_proj0R w Hw)) ??.
rewrite CD_proj1_2 (- proj0 w) (- proj1 w) (F_minus (proj0 w) (CD_proj0R w Hw)) ??.
rewrite CD_proj0_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                   (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                   ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                   (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                   ?? ??.
prove pa (proj0 z * (- proj0 w) + - conj (- proj1 w) * proj1 z)
         ((- proj1 w) * proj0 z + proj1 z * conj (- proj0 w))
    = pa (- (proj0 z * proj0 w + - conj (proj1 w) * proj1 z))
         (- (proj1 w * proj0 z + proj1 z * conj (proj0 w))).
f_equal.
- prove proj0 z * (- proj0 w) + - conj (- proj1 w) * proj1 z
      = - (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
  rewrite F_minus_add (proj0 z * proj0 w) (- conj (proj1 w) * proj1 z) ?? ??.
  f_equal.
  + prove proj0 z * (- proj0 w) = - proj0 z * proj0 w.
    exact F_minus_mul_distrR (proj0 z) (proj0 w) ?? ??.
  + prove - conj (- proj1 w) * proj1 z = - - conj (proj1 w) * proj1 z.
    f_equal.
    prove conj (- proj1 w) * proj1 z = - conj (proj1 w) * proj1 z.
    rewrite F_conj_minus (proj1 w) ??.
    exact F_minus_mul_distrL (conj (proj1 w)) (proj1 z) ?? ??.
- prove (- proj1 w) * proj0 z + proj1 z * conj (- proj0 w)
      = - (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
  rewrite F_minus_add (proj1 w * proj0 z) (proj1 z * conj (proj0 w)) ?? ??.
  f_equal.
  + prove (- proj1 w) * proj0 z = - proj1 w * proj0 z.
    exact F_minus_mul_distrL (proj1 w) (proj0 z) ?? ??.
  + prove proj1 z * conj (- proj0 w) = - proj1 z * conj (proj0 w).
    rewrite F_conj_minus (proj0 w) ??.
    exact F_minus_mul_distrR (proj1 z) (conj (proj0 w)) ?? ??.
Qed.

End CD_minus_mul_distrR.

Section CD_minus_mul_distrL.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.
Prefix - 358 := minus.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).
Hypothesis F_minus_add: forall x y, F x -> F y -> -(x + y) = - x + - y.
Hypothesis F_minus_mul_distrR: forall x y, F x -> F y -> x * (- y) = - (x * y).
Hypothesis F_minus_mul_distrL: forall x y, F x -> F y -> (- x) * y = - (x * y).

Theorem CD_minus_mul_distrL: forall z w, CD_carr z -> CD_carr w -> (:-: z) :*: w = :-: z :*: w.
let z w.
assume Hz Hw.
claim Lp0z: F (proj0 z).
{ exact CD_proj0R z Hz. }
claim Lp1z: F (proj1 z).
{ exact CD_proj1R z Hz. }
claim Lp0w: F (proj0 w).
{ exact CD_proj0R w Hw. }
claim Lp1w: F (proj1 w).
{ exact CD_proj1R w Hw. }
claim Lmp0z: F (- proj0 z).
{ apply F_minus. exact ??. }
claim Lmp1z: F (- proj1 z).
{ apply F_minus. exact ??. }
claim Lcp0w: F (conj (proj0 w)).
{ apply F_conj. exact ??. }
claim Lcp1w: F (conj (proj1 w)).
{ apply F_conj. exact ??. }
claim Lcp1wp1z: F (conj (proj1 w) * proj1 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lmcp1wp1z: F (- conj (proj1 w) * proj1 z).
{ apply F_minus. exact ??. }
claim Lp0zp0w: F (proj0 z * proj0 w).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LmulL: F (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
{ apply F_add.
  - exact ??.
  - exact ??.
}
claim Lp1wp0z: F (proj1 w * proj0 z).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim Lp1zcp0w: F (proj1 z * conj (proj0 w)).
{ apply F_mul.
  - exact ??.
  - exact ??.
}
claim LmulR: F (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
{ apply F_add.
  - exact ??.
  - exact ??.
}
prove pa (proj0 (pa (- proj0 z) (- proj1 z)) * proj0 w + - conj (proj1 w) * proj1 (pa (- proj0 z) (- proj1 z))) (proj1 w * proj0 (pa (- proj0 z) (- proj1 z)) + proj1 (pa (- proj0 z) (- proj1 z)) * conj (proj0 w))
    = pa (- proj0 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w))))
         (- proj1 (pa (proj0 z * proj0 w + - conj (proj1 w) * proj1 z) (proj1 w * proj0 z + proj1 z * conj (proj0 w)))).
rewrite CD_proj0_2 (- proj0 z) (- proj1 z) ?? ??.
rewrite CD_proj1_2 (- proj0 z) (- proj1 z) ?? ??.
rewrite CD_proj0_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                   (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                   ?? ??.
rewrite CD_proj1_2 (proj0 z * proj0 w + - conj (proj1 w) * proj1 z)
                   (proj1 w * proj0 z + proj1 z * conj (proj0 w))
                   ?? ??.
prove pa ((- proj0 z) * proj0 w + - conj (proj1 w) * (- proj1 z))
         (proj1 w * (- proj0 z) + (- proj1 z) * conj (proj0 w))
    = pa (- (proj0 z * proj0 w + - conj (proj1 w) * proj1 z))
         (- (proj1 w * proj0 z + proj1 z * conj (proj0 w))).
f_equal.
- prove (- proj0 z) * proj0 w + - conj (proj1 w) * (- proj1 z)
      = - (proj0 z * proj0 w + - conj (proj1 w) * proj1 z).
  rewrite F_minus_add (proj0 z * proj0 w) (- conj (proj1 w) * proj1 z) ?? ??.
  f_equal.
  + prove (- proj0 z) * proj0 w = - proj0 z * proj0 w.
    exact F_minus_mul_distrL (proj0 z) (proj0 w) ?? ??.
  + prove - conj (proj1 w) * (- proj1 z) = - - conj (proj1 w) * proj1 z.
    f_equal.
    prove conj (proj1 w) * (- proj1 z) = - conj (proj1 w) * proj1 z.
    exact F_minus_mul_distrR (conj (proj1 w)) (proj1 z) ?? ??.
- prove proj1 w * (- proj0 z) + (- proj1 z) * conj (proj0 w)
      = - (proj1 w * proj0 z + proj1 z * conj (proj0 w)).
  rewrite F_minus_add (proj1 w * proj0 z) (proj1 z * conj (proj0 w)) ?? ??.
  f_equal.
  + prove proj1 w * (- proj0 z) = - proj1 w * proj0 z.
    exact F_minus_mul_distrR (proj1 w) (proj0 z) ?? ??.
  + prove (- proj1 z) * conj (proj0 w) = - proj1 z * conj (proj0 w).
    exact F_minus_mul_distrL (proj1 z) (conj (proj0 w)) ?? ??.
Qed.

End CD_minus_mul_distrL.

Section CD_exp_nat.

Variable minus:set -> set.
Variable conj:set -> set.
Variable add:set -> set -> set.
Variable mul:set -> set -> set.

Prefix - 358 := minus.
Postfix ' 100 := conj.
Infix + 360 right := add.
Infix * 355 right := mul.

Prefix :-: 358 := CD_minus minus.
Postfix ' 100 := CD_conj minus conj.
Infix :+: 360 right := CD_add add.
Infix :*: 355 right := CD_mul minus conj add mul.
Infix ^ 342 := CD_exp_nat minus conj add mul.

Theorem CD_exp_nat_0: forall z, z ^ 0 = 1.
let z.
exact nat_primrec_0 1 (fun _ r => z :*: r).
Qed.

Theorem CD_exp_nat_S: forall z n, nat_p n -> z ^ (ordsucc n) = z :*: z ^ n.
let z n. assume Hn.
exact nat_primrec_S 1 (fun _ r => z :*: r) n Hn.
Qed.

Section CD_exp_nat_1_2.

Hypothesis F_0: F 0.
Hypothesis F_1: F 1.
Hypothesis F_minus_0: - 0 = 0.
Hypothesis F_conj_0: conj 0 = 0.
Hypothesis F_conj_1: conj 1 = 1.
Hypothesis F_add_0L: forall x, F x -> 0 + x = x.
Hypothesis F_add_0R: forall x, F x -> x + 0 = x.
Hypothesis F_mul_0L: forall x, F x -> 0 * x = 0.
Hypothesis F_mul_1R: forall x, F x -> x * 1 = x.

Theorem CD_exp_nat_1: forall z, CD_carr z -> z ^ 1 = z.
let z. assume Hz.
rewrite CD_exp_nat_S z 0 nat_0.
prove z :*: z ^ 0 = z.
rewrite CD_exp_nat_0 z.
prove z :*: 1 = z.
exact CD_mul_1R minus conj add mul F_0 F_1 F_minus_0 F_conj_0 F_conj_1 F_add_0L F_add_0R F_mul_0L F_mul_1R z Hz.
Qed.

Theorem CD_exp_nat_2: forall z, CD_carr z -> z ^ 2 = z :*: z.
let z. assume Hz.
rewrite CD_exp_nat_S z 1 nat_1.
prove z :*: z ^ 1 = z :*: z.
f_equal.
exact CD_exp_nat_1 z Hz.
Qed.

End CD_exp_nat_1_2.

Hypothesis F_minus: forall x, F x -> F (- x).
Hypothesis F_conj: forall x, F x -> F (conj x).
Hypothesis F_add: forall x y, F x -> F y -> F (x + y).
Hypothesis F_mul: forall x y, F x -> F y -> F (x * y).

Hypothesis F_0: F 0.
Hypothesis F_1: F 1.

Theorem CD_exp_nat_CD: forall z, CD_carr z -> forall n, nat_p n -> CD_carr (z ^ n).
let z. assume Hz.
apply nat_ind.
- rewrite CD_exp_nat_0.
  prove CD_carr 1.
  exact CD_carr_0ext F_0 1 F_1.
- let n. assume Hn.
  assume IHn: CD_carr (z ^ n).
  rewrite CD_exp_nat_S z n Hn.
  prove CD_carr (z :*: z ^ n).
  apply CD_mul_CD minus conj add mul F_minus F_conj F_add F_mul.
  + prove CD_carr z. exact Hz.
  + prove CD_carr (z ^ n). exact IHn.
Qed.

End CD_exp_nat.

End Alg.

Opaque CD_carr.
Opaque CD_proj0.
Opaque CD_proj1.
Opaque CD_exp_nat.
