(** Part 13 **)
Section SurQuaternions.

Theorem quaternion_tag_fresh: forall z, CSNo z -> forall u :e z, {3} /:e u.
let z. assume Hz.
apply Sing_nat_fresh_extension 3 nat_3 In_1_3 z.
prove ExtendedSNoElt_ 3 z.
exact CSNo_ExtendedSNoElt_3 z Hz.
Qed.

Definition CSNo_pair : set -> set -> set := pair_tag {3}.

Theorem CSNo_pair_0 : forall x, CSNo_pair x 0 = x.
exact pair_tag_0 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem CSNo_pair_prop_1 : forall x1 y1 x2 y2, CSNo x1 -> CSNo x2 -> CSNo_pair x1 y1 = CSNo_pair x2 y2 -> x1 = x2.
exact pair_tag_prop_1 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem CSNo_pair_prop_2 : forall x1 y1 x2 y2, CSNo x1 -> CSNo y1 -> CSNo x2 -> CSNo y2 -> CSNo_pair x1 y1 = CSNo_pair x2 y2 -> y1 = y2.
exact pair_tag_prop_2 {3} CSNo quaternion_tag_fresh.
Qed.

Definition HSNo : set -> prop := CD_carr {3} CSNo.

Theorem HSNo_I : forall x y, CSNo x -> CSNo y -> HSNo (CSNo_pair x y).
exact CD_carr_I {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_E : forall z, HSNo z ->
  forall p:set -> prop,
      (forall x y, CSNo x -> CSNo y -> z = CSNo_pair x y -> p (CSNo_pair x y))
    -> p z.
exact CD_carr_E {3} CSNo quaternion_tag_fresh.
Qed.

Theorem CSNo_HSNo : forall x, CSNo x -> HSNo x.
exact CD_carr_0ext {3} CSNo quaternion_tag_fresh CSNo_0.
Qed.

Theorem HSNo_0: HSNo 0.
apply CSNo_HSNo. exact CSNo_0.
Qed.

Theorem HSNo_1: HSNo 1.
apply CSNo_HSNo. exact CSNo_1.
Qed.

Let ctag : set -> set := fun alpha => SetAdjoin alpha {3}.
Postfix '' 100 := ctag.

Theorem HSNo_ExtendedSNoElt_4: forall z, HSNo z -> ExtendedSNoElt_ 4 z.
let z. assume Hz.
apply HSNo_E z Hz.
let x y.
assume Hx: CSNo x.
assume Hy: CSNo y.
assume Hzxy: z = CSNo_pair x y.
let v.
assume Hv: v :e Union (CSNo_pair x y).
apply UnionE_impred (CSNo_pair x y) v Hv.
let u.
assume H1: v :e u.
assume H2: u :e CSNo_pair x y.
apply binunionE x {w ''|w :e y} u H2.
- assume H3: u :e x.
  claim L1: v :e Union x.
  { exact UnionI x v u H1 H3. }
  prove ordinal v \/ exists i :e 4, v = {i}.
  exact extension_SNoElt_mon 3 4 (ordsuccI1 3) x (CSNo_ExtendedSNoElt_3 x Hx) v L1.
- assume H3: u :e {w ''|w :e y}.
  apply ReplE_impred y ctag u H3.
  let w.
  assume Hw: w :e y.
  assume H4: u = w ''.
  claim L2: v :e w ''.
  { rewrite <- H4. exact H1. }
  apply binunionE w {{3}} v L2.
  + assume H5: v :e w.
    claim L3: v :e Union y.
    { exact UnionI y v w H5 Hw. }
    exact extension_SNoElt_mon 3 4 (ordsuccI1 3) y (CSNo_ExtendedSNoElt_3 y Hy) v L3.
  + assume H5: v :e {{3}}.
    prove ordinal v \/ exists i :e 4, v = {i}.
    apply orIR.
    witness 3. apply andI.
    * prove 3 :e 4. exact In_3_4.
    * prove v = {3}. exact SingE {3} v H5.
Qed.

Prefix - 358 := minus_CSNo.
Infix + 360 right := add_CSNo.
Infix * 355 right := mul_CSNo.
Infix :/: 353 := div_CSNo.
Postfix ' 100 := conj_CSNo.

Let i := Complex_i.
Definition Quaternion_j : set := CSNo_pair 0 1.
Definition Quaternion_k : set := CSNo_pair 0 i.

Let j := Quaternion_j.
Let k := Quaternion_k.

Definition HSNo_proj0 : set -> set := CD_proj0 {3} CSNo.
Definition HSNo_proj1 : set -> set := CD_proj1 {3} CSNo.

Let p0 : set -> set := HSNo_proj0.
Let p1 : set -> set := HSNo_proj1.
Let pa : set -> set -> set := CSNo_pair.

Theorem HSNo_proj0_1: forall z, HSNo z -> CSNo (p0 z) /\ exists y, CSNo y /\ z = pa (p0 z) y.
exact CD_proj0_1 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj0_2: forall x y, CSNo x -> CSNo y -> p0 (pa x y) = x.
exact CD_proj0_2 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj1_1: forall z, HSNo z -> CSNo (p1 z) /\ z = pa (p0 z) (p1 z).
exact CD_proj1_1 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj1_2: forall x y, CSNo x -> CSNo y -> p1 (pa x y) = y.
exact CD_proj1_2 {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj0R: forall z, HSNo z -> CSNo (p0 z).
exact CD_proj0R {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj1R: forall z, HSNo z -> CSNo (p1 z).
exact CD_proj1R {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj0p1: forall z, HSNo z -> z = pa (p0 z) (p1 z).
exact CD_proj0proj1_eta {3} CSNo quaternion_tag_fresh.
Qed.

Theorem HSNo_proj0proj1_split: forall z w, HSNo z -> HSNo w -> p0 z = p0 w -> p1 z = p1 w -> z = w.
exact CD_proj0proj1_split {3} CSNo quaternion_tag_fresh.
Qed.

Definition HSNoLev : set -> set := fun z => CSNoLev (p0 z) :\/: CSNoLev (p1 z).

Theorem HSNoLev_ordinal: forall z, HSNo z -> ordinal (HSNoLev z).
let z. assume Hz.
apply HSNo_E z Hz.
let x y.
assume Hx Hy.
assume Hzxy: z = pa x y.
prove ordinal (CSNoLev (p0 (pa x y)) :\/: CSNoLev (p1 (pa x y))).
rewrite HSNo_proj0_2 x y Hx Hy.
rewrite HSNo_proj1_2 x y Hx Hy.
prove ordinal (CSNoLev x :\/: CSNoLev y).
exact ordinal_binunion (CSNoLev x) (CSNoLev y) (CSNoLev_ordinal x Hx) (CSNoLev_ordinal y Hy).
Qed.

Definition minus_HSNo : set -> set := CD_minus {3} CSNo minus_CSNo.
Definition conj_HSNo : set -> set := CD_conj {3} CSNo minus_CSNo conj_CSNo.
Definition add_HSNo : set -> set -> set := CD_add {3} CSNo add_CSNo.
Definition mul_HSNo : set -> set -> set := CD_mul {3} CSNo minus_CSNo conj_CSNo add_CSNo mul_CSNo.
Definition exp_HSNo_nat : set -> set -> set := CD_exp_nat {3} CSNo minus_CSNo conj_CSNo add_CSNo mul_CSNo.

Let plus' := add_HSNo.
Let mult' := mul_HSNo.

Prefix :-: 358 := minus_HSNo.
Postfix '' 100 := conj_HSNo.
Infix :+: 360 right := add_HSNo.
Infix :*: 355 right := mul_HSNo.
Infix :^: 355 right := exp_HSNo_nat.

Theorem HSNo_Complex_i : HSNo i.
apply CSNo_HSNo. exact CSNo_Complex_i.
Qed.

Theorem HSNo_Quaternion_j: HSNo j.
prove HSNo (pa 0 1).
apply HSNo_I.
- exact CSNo_0.
- exact CSNo_1.
Qed.

Theorem HSNo_Quaternion_k: HSNo k.
prove HSNo (pa 0 i).
apply HSNo_I.
- exact CSNo_0.
- exact CSNo_Complex_i.
Qed.

Theorem HSNo_minus_HSNo : forall z, HSNo z -> HSNo (minus_HSNo z).
exact CD_minus_CD {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo.
Qed.

Theorem minus_HSNo_proj0: forall z, HSNo z -> p0 (:-: z) = - p0 z.
exact CD_minus_proj0 {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo.
Qed.

Theorem minus_HSNo_proj1: forall z, HSNo z -> p1 (:-: z) = - p1 z.
exact CD_minus_proj1 {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo.
Qed.

Theorem HSNo_conj_HSNo : forall z, HSNo z -> HSNo (conj_HSNo z).
exact CD_conj_CD {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo conj_CSNo CSNo_conj_CSNo.
Qed.

Theorem conj_HSNo_proj0: forall z, HSNo z -> p0 (z '') = (p0 z) '.
exact CD_conj_proj0 {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo conj_CSNo CSNo_conj_CSNo.
Qed.

Theorem conj_HSNo_proj1: forall z, HSNo z -> p1 (z '') = - p1 z.
exact CD_conj_proj1 {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo conj_CSNo CSNo_conj_CSNo.
Qed.

Theorem HSNo_add_HSNo : forall z w, HSNo z -> HSNo w -> HSNo (add_HSNo z w).
exact CD_add_CD {3} CSNo quaternion_tag_fresh add_CSNo CSNo_add_CSNo.
Qed.

Theorem add_HSNo_proj0: forall z w, HSNo z -> HSNo w -> p0 (plus' z w) = p0 z + p0 w.
exact CD_add_proj0 {3} CSNo quaternion_tag_fresh add_CSNo CSNo_add_CSNo.
Qed.

Theorem add_HSNo_proj1: forall z w, HSNo z -> HSNo w -> p1 (plus' z w) = p1 z + p1 w.
exact CD_add_proj1 {3} CSNo quaternion_tag_fresh add_CSNo CSNo_add_CSNo.
Qed.

Theorem HSNo_mul_HSNo : forall z w, HSNo z -> HSNo w -> HSNo (z :*: w).
exact CD_mul_CD {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo.
Qed.

Theorem mul_HSNo_proj0: forall z w, HSNo z -> HSNo w -> p0 (mult' z w) = p0 z * p0 w + - (p1 w ' * p1 z).
exact CD_mul_proj0 {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo.
Qed.

Theorem mul_HSNo_proj1: forall z w, HSNo z -> HSNo w -> p1 (mult' z w) = p1 w * p0 z + p1 z * p0 w '.
exact CD_mul_proj1 {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo.
Qed.

Theorem CSNo_HSNo_proj0: forall x, CSNo x -> p0 x = x.
exact CD_proj0_F {3} CSNo quaternion_tag_fresh CSNo_0.
Qed.

Theorem CSNo_HSNo_proj1: forall x, CSNo x -> p1 x = 0.
exact CD_proj1_F {3} CSNo quaternion_tag_fresh CSNo_0.
Qed.

Theorem HSNo_p0_0 : p0 0 = 0.
exact CSNo_HSNo_proj0 0 CSNo_0.
Qed.

Theorem HSNo_p1_0 : p1 0 = 0.
exact CSNo_HSNo_proj1 0 CSNo_0.
Qed.

Theorem HSNo_p0_1 : p0 1 = 1.
exact CSNo_HSNo_proj0 1 CSNo_1.
Qed.

Theorem HSNo_p1_1 : p1 1 = 0.
exact CSNo_HSNo_proj1 1 CSNo_1.
Qed.

Theorem HSNo_p0_i : p0 i = i.
exact CSNo_HSNo_proj0 i CSNo_Complex_i.
Qed.

Theorem HSNo_p1_i : p1 i = 0.
exact CSNo_HSNo_proj1 i CSNo_Complex_i.
Qed.

Theorem HSNo_p0_j : p0 j = 0.
exact HSNo_proj0_2 0 1 CSNo_0 CSNo_1.
Qed.

Theorem HSNo_p1_j : p1 j = 1.
exact HSNo_proj1_2 0 1 CSNo_0 CSNo_1.
Qed.

Theorem HSNo_p0_k : p0 k = 0.
exact HSNo_proj0_2 0 i CSNo_0 CSNo_Complex_i.
Qed.

Theorem HSNo_p1_k : p1 k = i.
exact HSNo_proj1_2 0 i CSNo_0 CSNo_Complex_i.
Qed.

Theorem minus_HSNo_minus_CSNo : forall x, CSNo x -> :-: x = - x.
exact CD_minus_F_eq {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_0 minus_CSNo_0.
Qed.

Theorem minus_HSNo_0 : :-: 0 = 0.
rewrite minus_HSNo_minus_CSNo 0 CSNo_0.
exact minus_CSNo_0.
Qed.

Theorem conj_HSNo_conj_CSNo: forall x, CSNo x -> x '' = x '.
exact CD_conj_F_eq {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_0 minus_CSNo_0 conj_CSNo.
Qed.

Theorem conj_HSNo_id_SNo: forall x, SNo x -> x '' = x.
let x. assume Hx.
rewrite conj_HSNo_conj_CSNo x (SNo_CSNo x Hx).
prove x ' = x.
exact conj_CSNo_id_SNo x Hx.
Qed.

Theorem conj_HSNo_0 : 0 '' = 0.
rewrite conj_HSNo_conj_CSNo 0 CSNo_0.
exact conj_CSNo_0.
Qed.

Theorem conj_HSNo_1 : 1 '' = 1.
rewrite conj_HSNo_conj_CSNo 1 CSNo_1.
exact conj_CSNo_1.
Qed.

Theorem add_HSNo_add_CSNo: forall x y, CSNo x -> CSNo y -> x :+: y = x + y.
exact CD_add_F_eq {3} CSNo quaternion_tag_fresh add_CSNo CSNo_0 (add_CSNo_0L 0 CSNo_0).
Qed.

Theorem mul_HSNo_mul_CSNo: forall x y, CSNo x -> CSNo y -> x :*: y = x * y.
exact CD_mul_F_eq {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_conj_CSNo CSNo_mul_CSNo minus_CSNo_0 add_CSNo_0R mul_CSNo_0L mul_CSNo_0R.
Qed.

Theorem minus_HSNo_invol : forall z, HSNo z -> :-: :-: z = z.
exact CD_minus_invol {3} CSNo quaternion_tag_fresh minus_CSNo CSNo_minus_CSNo minus_CSNo_invol.
Qed.

Theorem conj_HSNo_invol : forall z, HSNo z -> z '' '' = z.
exact CD_conj_invol {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo CSNo_minus_CSNo CSNo_conj_CSNo minus_CSNo_invol conj_CSNo_invol.
Qed.

Theorem conj_minus_HSNo: forall z, HSNo z -> (:-: z) '' = :-: (z '').
exact CD_conj_minus {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo CSNo_minus_CSNo CSNo_conj_CSNo conj_minus_CSNo.
Qed.

Theorem minus_add_HSNo: forall z w, HSNo z -> HSNo w -> :-: (z :+: w) = :-: z :+: :-: w.
exact CD_minus_add {3} CSNo quaternion_tag_fresh minus_CSNo add_CSNo CSNo_minus_CSNo CSNo_add_CSNo minus_add_CSNo.
Qed.

Theorem conj_add_HSNo: forall z w, HSNo z -> HSNo w -> (z :+: w) '' = z '' :+: w ''.
exact CD_conj_add {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo minus_add_CSNo conj_add_CSNo.
Qed.

Theorem add_HSNo_com : forall z w, HSNo z -> HSNo w -> z :+: w = w :+: z.
exact CD_add_com {3} CSNo quaternion_tag_fresh add_CSNo add_CSNo_com.
Qed.

Theorem add_HSNo_assoc: forall z w v, HSNo z -> HSNo w -> HSNo v -> (z :+: w) :+: v = z :+: (w :+: v).
apply CD_add_assoc {3} CSNo quaternion_tag_fresh add_CSNo CSNo_add_CSNo add_CSNo_assoc.
Qed.

Theorem add_HSNo_0L : forall z, HSNo z -> add_HSNo 0 z = z.
exact CD_add_0L {3} CSNo quaternion_tag_fresh add_CSNo CSNo_0 add_CSNo_0L.
Qed.

Theorem add_HSNo_0R : forall z, HSNo z -> add_HSNo z 0 = z.
exact CD_add_0R {3} CSNo quaternion_tag_fresh add_CSNo CSNo_0 add_CSNo_0R.
Qed.

Theorem add_HSNo_minus_HSNo_linv : forall z, HSNo z -> add_HSNo (minus_HSNo z) z = 0.
exact CD_add_minus_linv {3} CSNo quaternion_tag_fresh minus_CSNo add_CSNo CSNo_minus_CSNo add_CSNo_minus_CSNo_linv.
Qed.

Theorem add_HSNo_minus_HSNo_rinv : forall z, HSNo z -> add_HSNo z (minus_HSNo z) = 0.
exact CD_add_minus_rinv {3} CSNo quaternion_tag_fresh minus_CSNo add_CSNo CSNo_minus_CSNo add_CSNo_minus_CSNo_rinv.
Qed.

Theorem mul_HSNo_0R: forall z, HSNo z -> z :*: 0 = 0.
exact CD_mul_0R {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 minus_CSNo_0 conj_CSNo_0 (add_CSNo_0L 0 CSNo_0) mul_CSNo_0L mul_CSNo_0R.
Qed.

Theorem mul_HSNo_0L: forall z, HSNo z -> 0 :*: z = 0.
exact CD_mul_0L {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_conj_CSNo minus_CSNo_0 (add_CSNo_0L 0 CSNo_0) mul_CSNo_0L mul_CSNo_0R.
Qed.

Theorem mul_HSNo_1R: forall z, HSNo z -> z :*: 1 = z.
exact CD_mul_1R {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_1 minus_CSNo_0 conj_CSNo_0 conj_CSNo_1 add_CSNo_0L add_CSNo_0R mul_CSNo_0L mul_CSNo_1R.
Qed.

Theorem mul_HSNo_1L: forall z, HSNo z -> 1 :*: z = z.
exact CD_mul_1L {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_1 CSNo_conj_CSNo minus_CSNo_0 add_CSNo_0R mul_CSNo_0L mul_CSNo_0R mul_CSNo_1L mul_CSNo_1R.
Qed.

Theorem conj_mul_HSNo: forall z w, HSNo z -> HSNo w -> (z :*: w) '' = w '' :*: z ''.
exact CD_conj_mul {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo minus_CSNo_invol conj_CSNo_invol conj_minus_CSNo conj_add_CSNo minus_add_CSNo add_CSNo_com conj_mul_CSNo minus_mul_CSNo_distrR minus_mul_CSNo_distrL.
Qed.

Theorem mul_HSNo_distrL : forall z w u, HSNo z -> HSNo w -> HSNo u -> z :*: (w :+: u) = z :*: w :+: z :*: u.
exact CD_add_mul_distrL {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo minus_add_CSNo conj_add_CSNo add_CSNo_assoc add_CSNo_com mul_CSNo_distrL mul_CSNo_distrR.
Qed.

Theorem mul_HSNo_distrR : forall z w u, HSNo z -> HSNo w -> HSNo u -> (z :+: w) :*: u = z :*: u :+: w :*: u.
exact CD_add_mul_distrR {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo minus_add_CSNo add_CSNo_assoc add_CSNo_com mul_CSNo_distrL mul_CSNo_distrR.
Qed.

Theorem minus_mul_HSNo_distrR: forall z w, HSNo z -> HSNo w -> z :*: (:-: w) = :-: z :*: w.
exact CD_minus_mul_distrR {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo conj_minus_CSNo minus_add_CSNo minus_mul_CSNo_distrR minus_mul_CSNo_distrL.
Qed.

Theorem minus_mul_HSNo_distrL: forall z w, HSNo z -> HSNo w -> (:-: z) :*: w = :-: z :*: w.
exact CD_minus_mul_distrL {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo minus_add_CSNo minus_mul_CSNo_distrR minus_mul_CSNo_distrL.
Qed.

Theorem exp_HSNo_nat_0: forall z, z :^: 0 = 1.
exact CD_exp_nat_0 {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo.
Qed.

Theorem exp_HSNo_nat_S: forall z n, nat_p n -> z :^: (ordsucc n) = z :*: z :^: n.
exact CD_exp_nat_S {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo.
Qed.

Theorem exp_HSNo_nat_1: forall z, HSNo z -> z :^: 1 = z.
exact CD_exp_nat_1 {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_1 minus_CSNo_0 conj_CSNo_0 conj_CSNo_1 add_CSNo_0L add_CSNo_0R mul_CSNo_0L mul_CSNo_1R.
Qed.

Theorem exp_HSNo_nat_2: forall z, HSNo z -> z :^: 2 = z :*: z.
exact CD_exp_nat_2 {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_0 CSNo_1 minus_CSNo_0 conj_CSNo_0 conj_CSNo_1 add_CSNo_0L add_CSNo_0R mul_CSNo_0L mul_CSNo_1R.
Qed.

Theorem HSNo_exp_HSNo_nat: forall z, HSNo z -> forall n, nat_p n -> HSNo (z :^: n).
exact CD_exp_nat_CD {3} CSNo quaternion_tag_fresh minus_CSNo conj_CSNo add_CSNo mul_CSNo CSNo_minus_CSNo CSNo_conj_CSNo CSNo_add_CSNo CSNo_mul_CSNo CSNo_0 CSNo_1.
Qed.

Theorem add_CSNo_com_3b_1_2 : forall x y z, CSNo x -> CSNo y -> CSNo z
  -> (x + y) + z = (x + z) + y.
let x y z.
assume Hx Hy Hz.
prove (x + y) + z = (x + z) + y.
rewrite add_CSNo_assoc x y z Hx Hy Hz.
prove x + y + z = (x + z) + y.
rewrite add_CSNo_assoc x z y Hx Hz Hy.
prove x + y + z = x + z + y.
f_equal.
exact add_CSNo_com y z Hy Hz.
Qed.

Theorem add_CSNo_com_4_inner_mid : forall x y z w, CSNo x -> CSNo y -> CSNo z -> CSNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
let x y z w.
assume Hx Hy Hz Hw.
rewrite <- add_CSNo_assoc (x + y) z w (CSNo_add_CSNo x y Hx Hy) Hz Hw.
prove ((x + y) + z) + w = (x + z) + (y + w).
rewrite add_CSNo_com_3b_1_2 x y z Hx Hy Hz.
prove ((x + z) + y) + w = (x + z) + (y + w).
exact add_CSNo_assoc (x + z) y w (CSNo_add_CSNo x z Hx Hz) Hy Hw.
Qed.

Theorem add_CSNo_rotate_4_0312: forall x y z w, CSNo x -> CSNo y -> CSNo z -> CSNo w -> (x + y) + (z + w) = (x + w) + (y + z).
let x y z w. assume Hx Hy Hz Hw.
rewrite add_CSNo_com z w Hz Hw.
prove (x + y) + (w + z) = (x + w) + (y + z).
exact add_CSNo_com_4_inner_mid x y w z Hx Hy Hw Hz.
Qed.

Theorem Quaternion_i_sqr : i :*: i = :-: 1.
rewrite mul_HSNo_mul_CSNo i i CSNo_Complex_i CSNo_Complex_i.
rewrite minus_HSNo_minus_CSNo 1 CSNo_1.
prove i * i = - 1.
exact Complex_i_sqr.
Qed.

Theorem Quaternion_j_sqr : j :*: j = :-: 1.
claim Ljj: HSNo (j :*: j).
{ exact HSNo_mul_HSNo j j HSNo_Quaternion_j HSNo_Quaternion_j. }
claim Lm1: HSNo (:-: 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply HSNo_proj0proj1_split (j :*: j) (:-: 1) Ljj Lm1.
- prove p0 (j :*: j) = p0 (:-: 1).
  rewrite mul_HSNo_proj0 j j HSNo_Quaternion_j HSNo_Quaternion_j.
  rewrite minus_HSNo_proj0 1 HSNo_1.
  prove p0 j * p0 j + - p1 j ' * p1 j = - p0 1.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  rewrite CSNo_HSNo_proj0 1 CSNo_1.
  prove 0 * 0 + - 1 ' * 1 = - 1.
  rewrite conj_CSNo_1.
  rewrite mul_CSNo_0L 0 CSNo_0.
  rewrite mul_CSNo_1L 1 CSNo_1.
  prove 0 + - 1 = - 1.
  exact add_CSNo_0L (- 1) (CSNo_minus_CSNo 1 CSNo_1).
- prove p1 (j :*: j) = p1 (:-: 1).
  rewrite mul_HSNo_proj1 j j HSNo_Quaternion_j HSNo_Quaternion_j.
  rewrite minus_HSNo_proj1 1 HSNo_1.
  prove p1 j * p0 j + p1 j * p0 j ' = - p1 1.
  rewrite HSNo_p1_1. rewrite minus_CSNo_0.
  prove p1 j * p0 j + p1 j * p0 j ' = 0.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  prove 1 * 0 + 1 * 0 ' = 0.
  rewrite conj_CSNo_0.
  prove 1 * 0 + 1 * 0 = 0.
  rewrite mul_CSNo_0R 1 CSNo_1.
  exact add_CSNo_0L 0 CSNo_0.
Qed.

Theorem Quaternion_k_sqr : k :*: k = :-: 1.
claim Lkk: HSNo (k :*: k).
{ exact HSNo_mul_HSNo k k HSNo_Quaternion_k HSNo_Quaternion_k. }
claim Lm1: HSNo (:-: 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply HSNo_proj0proj1_split (k :*: k) (:-: 1) Lkk Lm1.
- prove p0 (k :*: k) = p0 (:-: 1).
  rewrite mul_HSNo_proj0 k k HSNo_Quaternion_k HSNo_Quaternion_k.
  rewrite minus_HSNo_proj0 1 HSNo_1.
  prove p0 k * p0 k + - p1 k ' * p1 k = - p0 1.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  rewrite CSNo_HSNo_proj0 1 CSNo_1.
  prove 0 * 0 + - i ' * i = - 1.
  rewrite mul_CSNo_0L 0 CSNo_0.
  rewrite conj_CSNo_i.
  prove 0 + - (- i) * i = - 1.
  rewrite <- minus_mul_CSNo_distrL (- i) i (CSNo_minus_CSNo i CSNo_Complex_i) CSNo_Complex_i.
  prove 0 + (- - i) * i = - 1.
  rewrite minus_CSNo_invol i CSNo_Complex_i.
  prove 0 + i * i = - 1.
  rewrite Complex_i_sqr.
  prove 0 + - 1 = - 1.
  exact add_CSNo_0L (- 1) (CSNo_minus_CSNo 1 CSNo_1).
- prove p1 (k :*: k) = p1 (:-: 1).
  rewrite mul_HSNo_proj1 k k HSNo_Quaternion_k HSNo_Quaternion_k.
  rewrite minus_HSNo_proj1 1 HSNo_1.
  prove p1 k * p0 k + p1 k * p0 k ' = - p1 1.
  rewrite HSNo_p1_1. rewrite minus_CSNo_0.
  prove p1 k * p0 k + p1 k * p0 k ' = 0.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  prove i * 0 + i * 0 ' = 0.
  rewrite conj_CSNo_0.
  prove i * 0 + i * 0 = 0.
  rewrite mul_CSNo_0R i CSNo_Complex_i.
  exact add_CSNo_0L 0 CSNo_0.
Qed.

Theorem Quaternion_i_j: i :*: j = k.
claim Lij: HSNo (i :*: j).
{ exact HSNo_mul_HSNo i j HSNo_Complex_i HSNo_Quaternion_j. }
apply HSNo_proj0proj1_split (i :*: j) k Lij HSNo_Quaternion_k.
- prove p0 (i :*: j) = p0 k.
  rewrite HSNo_p0_k.
  rewrite mul_HSNo_proj0 i j HSNo_Complex_i HSNo_Quaternion_j.
  prove p0 i * p0 j + - (p1 j ' * p1 i) = 0.
  rewrite HSNo_p0_i. rewrite HSNo_p1_i. rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  prove i * 0 + - (1 ' * 0) = 0.
  rewrite mul_CSNo_0R i CSNo_Complex_i.
  rewrite mul_CSNo_0R (1 ') (CSNo_conj_CSNo 1 CSNo_1).
  prove 0 + - 0 = 0.
  rewrite minus_CSNo_0.
  exact add_CSNo_0L 0 CSNo_0.
- prove p1 (i :*: j) = p1 k.
  rewrite HSNo_p1_k.
  rewrite mul_HSNo_proj1 i j HSNo_Complex_i HSNo_Quaternion_j.
  prove p1 j * p0 i + p1 i * p0 j ' = i.
  rewrite HSNo_p0_i. rewrite HSNo_p1_i. rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  prove 1 * i + 0 * 0 ' = i.
  rewrite mul_CSNo_1L i CSNo_Complex_i.
  rewrite mul_CSNo_0L (0 ') (CSNo_conj_CSNo 0 CSNo_0).
  prove i + 0 = i.
  exact add_CSNo_0R i CSNo_Complex_i.
Qed.

Theorem Quaternion_j_k: j :*: k = i.
claim Ljk: HSNo (j :*: k).
{ exact HSNo_mul_HSNo j k HSNo_Quaternion_j HSNo_Quaternion_k. }
apply HSNo_proj0proj1_split (j :*: k) i Ljk HSNo_Complex_i.
- prove p0 (j :*: k) = p0 i.
  rewrite HSNo_p0_i.
  rewrite mul_HSNo_proj0 j k HSNo_Quaternion_j HSNo_Quaternion_k.
  prove p0 j * p0 k + - (p1 k ' * p1 j) = i.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j. rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  prove 0 * 0 + - (i ' * 1) = i.
  rewrite mul_CSNo_0R 0 CSNo_0.
  rewrite mul_CSNo_1R (i ') (CSNo_conj_CSNo i CSNo_Complex_i).
  prove 0 + - (i ') = i.
  rewrite conj_CSNo_i.
  prove 0 + - - i = i.
  rewrite minus_CSNo_invol i CSNo_Complex_i.
  exact add_CSNo_0L i CSNo_Complex_i.
- prove p1 (j :*: k) = p1 i.
  rewrite HSNo_p1_i.
  rewrite mul_HSNo_proj1 j k HSNo_Quaternion_j HSNo_Quaternion_k.
  prove p1 k * p0 j + p1 j * p0 k ' = 0.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j. rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  prove i * 0 + 1 * 0 ' = 0.
  rewrite conj_CSNo_id_SNo 0 SNo_0.
  rewrite mul_CSNo_0R i CSNo_Complex_i.
  rewrite mul_CSNo_0R 1 CSNo_1.
  exact add_CSNo_0R 0 CSNo_0.
Qed.

Theorem Quaternion_k_i: k :*: i = j.
claim Lki: HSNo (k :*: i).
{ exact HSNo_mul_HSNo k i HSNo_Quaternion_k HSNo_Complex_i. }
apply HSNo_proj0proj1_split (k :*: i) j Lki HSNo_Quaternion_j.
- prove p0 (k :*: i) = p0 j.
  rewrite HSNo_p0_j.
  rewrite mul_HSNo_proj0 k i HSNo_Quaternion_k HSNo_Complex_i.
  prove p0 k * p0 i + - (p1 i ' * p1 k) = 0.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k. rewrite HSNo_p0_i. rewrite HSNo_p1_i.
  prove 0 * i + - (0 ' * i) = 0.
  rewrite conj_CSNo_id_SNo 0 SNo_0.
  prove 0 * i + - (0 * i) = 0.
  rewrite mul_CSNo_0L i CSNo_Complex_i.
  prove 0 + - 0 = 0.
  rewrite minus_CSNo_0.
  exact add_CSNo_0R 0 CSNo_0.
- prove p1 (k :*: i) = p1 j.
  rewrite HSNo_p1_j.
  rewrite mul_HSNo_proj1 k i HSNo_Quaternion_k HSNo_Complex_i.
  prove p1 i * p0 k + p1 k * p0 i ' = 1.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k. rewrite HSNo_p0_i. rewrite HSNo_p1_i.
  prove 0 * 0 + i * (i ') = 1.
  rewrite mul_CSNo_0L 0 CSNo_0.
  rewrite conj_CSNo_i.
  prove 0 + i * (- i) = 1.
  rewrite minus_mul_CSNo_distrR i i CSNo_Complex_i CSNo_Complex_i.
  prove 0 + - i * i = 1.
  rewrite Complex_i_sqr.
  prove 0 + - - 1 = 1.
  rewrite minus_CSNo_invol 1 CSNo_1.
  exact add_CSNo_0L 1 CSNo_1.
Qed.

Theorem Quaternion_j_i: j :*: i = :-: k.
claim Lji: HSNo (j :*: i).
{ exact HSNo_mul_HSNo j i HSNo_Quaternion_j HSNo_Complex_i. }
apply HSNo_proj0proj1_split (j :*: i) (:-: k) Lji (HSNo_minus_HSNo k HSNo_Quaternion_k).
- prove p0 (j :*: i) = p0 (:-: k).
  rewrite minus_HSNo_proj0 k HSNo_Quaternion_k.
  rewrite HSNo_p0_k.
  rewrite mul_HSNo_proj0 j i HSNo_Quaternion_j HSNo_Complex_i.
  prove p0 j * p0 i + - (p1 i ' * p1 j) = - 0.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j. rewrite HSNo_p0_i. rewrite HSNo_p1_i.
  prove 0 * i + - (0 ' * 1) = - 0.
  rewrite conj_CSNo_id_SNo 0 SNo_0.
  rewrite mul_CSNo_0L i CSNo_Complex_i.
  rewrite mul_CSNo_0L 1 CSNo_1.
  prove 0 + - 0 = - 0.
  exact add_CSNo_0L (- 0) (CSNo_minus_CSNo 0 CSNo_0).
- prove p1 (j :*: i) = p1 (:-: k).
  rewrite minus_HSNo_proj1 k HSNo_Quaternion_k.
  rewrite HSNo_p1_k.
  rewrite mul_HSNo_proj1 j i HSNo_Quaternion_j HSNo_Complex_i.
  prove p1 i * p0 j + p1 j * p0 i ' = - i.
  rewrite HSNo_p0_j. rewrite HSNo_p1_j. rewrite HSNo_p0_i. rewrite HSNo_p1_i.
  prove 0 * 0 + 1 * i ' = - i.
  rewrite mul_CSNo_0R 0 CSNo_0.
  rewrite mul_CSNo_1L (i ') (CSNo_conj_CSNo i CSNo_Complex_i).
  rewrite conj_CSNo_i.
  prove 0 + - i = - i.
  exact add_CSNo_0L (- i) (CSNo_minus_CSNo i CSNo_Complex_i).
Qed.

Theorem Quaternion_k_j: k :*: j = :-: i.
claim Lkj: HSNo (k :*: j).
{ exact HSNo_mul_HSNo k j HSNo_Quaternion_k HSNo_Quaternion_j. }
apply HSNo_proj0proj1_split (k :*: j) (:-: i) Lkj (HSNo_minus_HSNo i HSNo_Complex_i).
- prove p0 (k :*: j) = p0 (:-: i).
  rewrite minus_HSNo_proj0 i HSNo_Complex_i.
  rewrite HSNo_p0_i.
  rewrite mul_HSNo_proj0 k j HSNo_Quaternion_k HSNo_Quaternion_j.
  prove p0 k * p0 j + - (p1 j ' * p1 k) = - i.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k. rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  prove 0 * 0 + - (1 ' * i) = - i.
  rewrite mul_CSNo_0R 0 CSNo_0.
  rewrite conj_CSNo_id_SNo 1 SNo_1.
  rewrite mul_CSNo_1L i CSNo_Complex_i.
  prove 0 + - i = - i.
  exact add_CSNo_0L (- i) (CSNo_minus_CSNo i CSNo_Complex_i).
- prove p1 (k :*: j) = p1 (:-: i).
  rewrite minus_HSNo_proj1 i HSNo_Complex_i.
  rewrite HSNo_p1_i.
  rewrite mul_HSNo_proj1 k j HSNo_Quaternion_k HSNo_Quaternion_j.
  prove p1 j * p0 k + p1 k * p0 j ' = - 0.
  rewrite HSNo_p0_k. rewrite HSNo_p1_k. rewrite HSNo_p0_j. rewrite HSNo_p1_j.
  prove 1 * 0 + i * 0 ' = - 0.
  rewrite conj_CSNo_id_SNo 0 SNo_0.
  rewrite minus_CSNo_0.
  rewrite mul_CSNo_0R 1 CSNo_1.
  rewrite mul_CSNo_0R i CSNo_Complex_i.
  exact add_CSNo_0R 0 CSNo_0.
Qed.

Theorem Quaternion_i_k: i :*: k = :-: j.
claim Lik: HSNo (i :*: k).
{ exact HSNo_mul_HSNo i k HSNo_Complex_i HSNo_Quaternion_k. }
apply HSNo_proj0proj1_split (i :*: k) (:-: j) Lik (HSNo_minus_HSNo j HSNo_Quaternion_j).
- prove p0 (i :*: k) = p0 (:-: j).
  rewrite minus_HSNo_proj0 j HSNo_Quaternion_j.
  rewrite HSNo_p0_j.
  rewrite mul_HSNo_proj0 i k HSNo_Complex_i HSNo_Quaternion_k.
  prove p0 i * p0 k + - (p1 k ' * p1 i) = - 0.
  rewrite HSNo_p0_i. rewrite HSNo_p1_i. rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  prove i * 0 + - (i ' * 0) = - 0.
  rewrite mul_CSNo_0R i CSNo_Complex_i.
  rewrite mul_CSNo_0R (i ') (CSNo_conj_CSNo i CSNo_Complex_i).
  prove 0 + - 0 = - 0.
  exact add_CSNo_0L (- 0) (CSNo_minus_CSNo 0 CSNo_0).
- prove p1 (i :*: k) = p1 (:-: j).
  rewrite minus_HSNo_proj1 j HSNo_Quaternion_j.
  rewrite HSNo_p1_j.
  rewrite mul_HSNo_proj1 i k HSNo_Complex_i HSNo_Quaternion_k.
  prove p1 k * p0 i + p1 i * p0 k ' = - 1.
  rewrite HSNo_p0_i. rewrite HSNo_p1_i. rewrite HSNo_p0_k. rewrite HSNo_p1_k.
  prove i * i + 0 * 0 ' = - 1.
  rewrite mul_CSNo_0L (0 ') (CSNo_conj_CSNo 0 CSNo_0).
  rewrite Complex_i_sqr.
  prove - 1 + 0 = - 1.
  exact add_CSNo_0R (- 1) (CSNo_minus_CSNo 1 CSNo_1).
Qed.

Theorem add_CSNo_rotate_3_1 : forall x y z, CSNo x -> CSNo y -> CSNo z ->
  x + y + z = z + x + y.
let x y z.
assume Hx Hy Hz.
prove x + (y + z) = z + (x + y).
transitivity x + (z + y),
             (x + z) + y,
             (z + x) + y.
- f_equal. exact add_CSNo_com y z Hy Hz.
- symmetry. exact add_CSNo_assoc x z y Hx Hz Hy.
- f_equal. exact add_CSNo_com x z Hx Hz.
- exact add_CSNo_assoc z x y Hz Hx Hy.
Qed.

Theorem mul_CSNo_rotate_3_1 : forall x y z, CSNo x -> CSNo y -> CSNo z ->
  x * y * z = z * x * y.
let x y z.
assume Hx Hy Hz.
prove x * (y * z) = z * (x * y).
transitivity x * (z * y),
             (x * z) * y,
             (z * x) * y.
- f_equal. exact mul_CSNo_com y z Hy Hz.
- exact mul_CSNo_assoc x z y Hx Hz Hy.
- f_equal. exact mul_CSNo_com x z Hx Hz.
- symmetry. exact mul_CSNo_assoc z x y Hz Hx Hy.
Qed.

Theorem mul_HSNo_assoc: forall z w v, HSNo z -> HSNo w -> HSNo v -> z :*: (w :*: v) = (z :*: w) :*: v.
let z w v. assume Hz Hw Hv.
claim Lwv: HSNo (mult' w v).
{ exact HSNo_mul_HSNo w v Hw Hv. }
claim Lzw: HSNo (mult' z w).
{ exact HSNo_mul_HSNo z w Hz Hw. }
claim Lzwv1: HSNo (mult' z (mult' w v)).
{ exact HSNo_mul_HSNo z (mult' w v) Hz Lwv. }
claim Lzwv2: HSNo (mult' (mult' z w) v).
{ exact HSNo_mul_HSNo (mult' z w) v Lzw Hv. }
claim Lp0zR: CSNo (p0 z).
{ exact HSNo_proj0R z Hz. }
claim Lp0wR: CSNo (p0 w).
{ exact HSNo_proj0R w Hw. }
claim Lp0vR: CSNo (p0 v).
{ exact HSNo_proj0R v Hv. }
claim Lp1zR: CSNo (p1 z).
{ exact HSNo_proj1R z Hz. }
claim Lp1wR: CSNo (p1 w).
{ exact HSNo_proj1R w Hw. }
claim Lp1vR: CSNo (p1 v).
{ exact HSNo_proj1R v Hv. }
claim L1: CSNo (p0 w ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L2: CSNo (p1 w ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L3: CSNo (p1 v ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L4: CSNo (p0 v ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L5: CSNo (p0 v ' ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L6: CSNo (p1 w ' ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L7: CSNo (p1 w * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L8: CSNo (p0 z * p0 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L9: CSNo (p0 w * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L10: CSNo (p0 w * p0 v).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L11: CSNo (p1 v * p0 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L12: CSNo ((p1 v * p0 w) ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L13: CSNo ((p0 w * p0 v) ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L14: CSNo (p1 z * p0 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L15: CSNo (p0 z * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L16: CSNo (p0 v ' * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L17: CSNo (p1 v * p1 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L18: CSNo (p1 v ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L19: CSNo (p1 w ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L20: CSNo (p1 v ' * p1 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L21: CSNo (p1 w * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L22: CSNo (p0 w ' * p1 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L23: CSNo (p0 v ' ' * p1 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L24: CSNo ((p1 w * p0 v ') ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L25: CSNo ((p1 v ' * p1 w) ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L26: CSNo (- p1 w ' * p1 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L27: CSNo (p0 w ' * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L28: CSNo (p0 v ' * p0 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L29: CSNo (- p1 v ' * p1 w).
{ apply CSNo_minus_CSNo. exact ??. }
claim L30: CSNo (p1 w ' * p1 w ' ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L31: CSNo ((- p1 v ' * p1 w) ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L32: CSNo (p1 v * p0 z * p0 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L33: CSNo (p1 v * p0 w * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L34: CSNo (p0 z * p0 w * p0 v).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L35: CSNo (- (p1 v ' * p1 w) ').
{ apply CSNo_minus_CSNo. exact ??. }
claim L36: CSNo (p1 v * p1 w ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L37: CSNo (p1 w * p0 z * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L38: CSNo (p1 w * p0 v ' * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L39: CSNo (p1 z * p1 v * p1 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L40: CSNo (p0 z * p1 v ' * p1 w).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L41: CSNo (p0 v * p1 w ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L42: CSNo (- p1 v * p1 w ' * p1 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L43: CSNo (p1 z * p0 w ' * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L44: CSNo (p1 z * p0 v ' * p0 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L45: CSNo (- p1 z * p1 v * p1 w ').
{ apply CSNo_minus_CSNo. exact ??. }
claim L46: CSNo (- p0 z * p1 v ' * p1 w).
{ apply CSNo_minus_CSNo. exact ??. }
claim L47: CSNo (p0 w ' * p1 v ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L48: CSNo (- p0 v * p1 w ' * p1 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L49: CSNo (- p0 w ' * p1 v ' * p1 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L50: CSNo (p1 w * p0 z + p1 z * p0 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L51: CSNo (p1 v * p0 w + p1 w * p0 v ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L52: CSNo (p0 z * p0 w + - p1 w ' * p1 z).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L53: CSNo (p0 w * p0 v + - p1 v ' * p1 w).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L54: CSNo ((p1 v * p0 w + p1 w * p0 v ') ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L55: CSNo ((p0 w * p0 v + - p1 v ' * p1 w) ').
{ apply CSNo_conj_CSNo. exact ??. }
claim L56: CSNo (p0 w ' * p1 v ' + p0 v ' ' * p1 w).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L57: CSNo ((p1 v * p0 w) ' + (p1 w * p0 v ') ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L58: CSNo ((p1 v * p0 w + p1 w * p0 v ') * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L59: CSNo (p0 v ' * p0 w ' + - (p1 v ' * p1 w) ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L60: CSNo ((p0 w * p0 v) ' + (- p1 v ' * p1 w) ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L61: CSNo (p1 v * (p0 z * p0 w + - p1 w ' * p1 z)).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L62: CSNo ((p1 w * p0 z + p1 z * p0 w ') * p0 v ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L63: CSNo (p0 z * (p0 w * p0 v + - p1 v ' * p1 w)).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L64: CSNo ((p1 v * p0 w + p1 w * p0 v ') ' * p1 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L65: CSNo (p1 z * (p0 w * p0 v + - p1 v ' * p1 w) ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L66: CSNo (- (p1 v * p0 w + p1 w * p0 v ') ' * p1 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L67: CSNo (p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L68: CSNo (p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L69: CSNo (- p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L70: CSNo (- p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L71: CSNo (p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L72: CSNo (- p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L73: CSNo (p1 v * (p0 z * p0 w + - p1 w ' * p1 z) + (p1 w * p0 z + p1 z * p0 w ') * p0 v ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L74: CSNo ((p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 w * p0 v + - p1 v ' * p1 w) ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L75: CSNo (p0 z * (p0 w * p0 v + - p1 v ' * p1 w) + - (p1 v * p0 w + p1 w * p0 v ') ' * p1 z).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L76: CSNo (p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L77: CSNo (p1 v * p0 w * p0 z + p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L78: CSNo (p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z).
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L79: CSNo (p0 v * p1 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L80: CSNo (p1 z * p0 v).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L81: CSNo (p1 w ' * p1 z * p0 v).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L82: CSNo (- p1 w ' * p1 z * p0 v).
{ apply CSNo_minus_CSNo. exact ??. }
claim L83: CSNo (p1 v ' * p1 w * p0 z).
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L84: CSNo (p1 v ' * p1 z * p0 w ').
{ apply CSNo_mul_CSNo.
  - exact ??.
  - exact ??.
}
claim L85: CSNo (- p1 v ' * p1 w * p0 z).
{ apply CSNo_minus_CSNo. exact ??. }
claim L86: CSNo (- p1 v ' * p1 z * p0 w ').
{ apply CSNo_minus_CSNo. exact ??. }
claim L87: CSNo (- p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L88: CSNo (- p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w ').
{ apply CSNo_add_CSNo.
  - exact ??.
  - exact ??.
}
claim L89: CSNo (- p1 v ').
{ apply CSNo_minus_CSNo. exact ??. }
claim L90: CSNo (- p1 v * p1 w ').
{ apply CSNo_minus_CSNo. exact ??. }
apply HSNo_proj0proj1_split (mult' z (mult' w v)) (mult' (mult' z w) v) Lzwv1 Lzwv2.
- prove p0 (mult' z (mult' w v)) = p0 (mult' (mult' z w) v).
  transitivity p0 z * p0 (mult' w v) + - p1 (mult' w v) ' * p1 z,
               p0 z * (p0 w * p0 v + - p1 v ' * p1 w) + - (p1 v * p0 w + p1 w * p0 v ') ' * p1 z,
               p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z,
               p0 z * p0 w * p0 v + - p1 w ' * p1 z * p0 v + - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w ',
               (p0 z * p0 w + - p1 w ' * p1 z) * p0 v + - p1 v ' * (p1 w * p0 z + p1 z * p0 w '),
               p0 (mult' z w) * p0 v + - p1 v ' * p1 (mult' z w).
  + exact mul_HSNo_proj0 z (mult' w v) Hz Lwv.
  + prove p0 z * p0 (mult' w v) + - p1 (mult' w v) ' * p1 z
        = p0 z * (p0 w * p0 v + - p1 v ' * p1 w) + - (p1 v * p0 w + p1 w * p0 v ') ' * p1 z.
    f_equal.
    * f_equal. exact mul_HSNo_proj0 w v Hw Hv.
    * f_equal. f_equal. f_equal.
      exact mul_HSNo_proj1 w v Hw Hv.
  + prove p0 z * (p0 w * p0 v + - p1 v ' * p1 w) + - (p1 v * p0 w + p1 w * p0 v ') ' * p1 z
        = p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z.
    rewrite <- add_CSNo_assoc (p0 z * p0 w * p0 v) (- p0 z * p1 v ' * p1 w) (- p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z) ?? ?? ??.
    f_equal.
    * prove p0 z * (p0 w * p0 v + - p1 v ' * p1 w) = p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w.
      rewrite mul_CSNo_distrL (p0 z) (p0 w * p0 v) (- p1 v ' * p1 w) ?? ?? ??.
      prove p0 z * p0 w * p0 v + p0 z * (- p1 v ' * p1 w) = p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w.
      f_equal.
      prove p0 z * (- p1 v ' * p1 w) = - p0 z * p1 v ' * p1 w.
      exact minus_mul_CSNo_distrR (p0 z) (p1 v ' * p1 w) ?? ??.
    * { prove - (p1 v * p0 w + p1 w * p0 v ') ' * p1 z = - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z.
        transitivity - (p0 w ' * p1 v ' * p1 z + p0 v * p1 w ' * p1 z).
        - f_equal.
          prove (p1 v * p0 w + p1 w * p0 v ') ' * p1 z = p0 w ' * p1 v ' * p1 z + p0 v * p1 w ' * p1 z.
          transitivity (p0 w ' * p1 v ' + p0 v * p1 w ') * p1 z.
          + f_equal.
            prove (p1 v * p0 w + p1 w * p0 v ') ' = p0 w ' * p1 v ' + p0 v * p1 w '.
            transitivity (p1 v * p0 w) ' + (p1 w * p0 v ') '.
            * exact conj_add_CSNo (p1 v * p0 w) (p1 w * p0 v ') ?? ??.
            * { prove (p1 v * p0 w) ' + (p1 w * p0 v ') ' = p0 w ' * p1 v ' + p0 v * p1 w '.
                f_equal.
                - exact conj_mul_CSNo (p1 v) (p0 w) ?? ??.
                - rewrite conj_mul_CSNo (p1 w) (p0 v ') ?? ??.
                  prove p0 v ' ' * p1 w ' = p0 v * p1 w '.
                  f_equal.
                  exact conj_CSNo_invol (p0 v) ??.
              }
          + prove (p0 w ' * p1 v ' + p0 v * p1 w ') * p1 z = p0 w ' * p1 v ' * p1 z + p0 v * p1 w ' * p1 z.
            rewrite mul_CSNo_distrR (p0 w ' * p1 v ') (p0 v * p1 w ') (p1 z) ?? ?? ??.
            f_equal.
            * symmetry. exact mul_CSNo_assoc (p0 w ') (p1 v ') (p1 z) ?? ?? ??.
            * symmetry. exact mul_CSNo_assoc (p0 v) (p1 w ') (p1 z) ?? ?? ??.
        - prove - (p0 w ' * p1 v ' * p1 z + p0 v * p1 w ' * p1 z) = - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z.
          exact minus_add_CSNo (p0 w ' * p1 v ' * p1 z) (p0 v * p1 w ' * p1 z) ?? ??.
      }
  + prove p0 z * p0 w * p0 v + - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z
        = p0 z * p0 w * p0 v + - p1 w ' * p1 z * p0 v + - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w '.
    f_equal.
    prove - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z + - p0 v * p1 w ' * p1 z
        = - p1 w ' * p1 z * p0 v + - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w '.
    rewrite add_CSNo_rotate_3_1 (- p0 z * p1 v ' * p1 w) (- p0 w ' * p1 v ' * p1 z) (- p0 v * p1 w ' * p1 z) ?? ?? ??.
    prove - p0 v * p1 w ' * p1 z + - p0 z * p1 v ' * p1 w + - p0 w ' * p1 v ' * p1 z
        = - p1 w ' * p1 z * p0 v + - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w '.
    f_equal.
    * prove - p0 v * p1 w ' * p1 z = - p1 w ' * p1 z * p0 v.
      f_equal.
      symmetry.
      exact mul_CSNo_rotate_3_1 (p1 w ') (p1 z) (p0 v) ?? ?? ??.
    * { f_equal.
        - prove - p0 z * p1 v ' * p1 w = - p1 v ' * p1 w * p0 z.
          f_equal.
          symmetry.
          exact mul_CSNo_rotate_3_1 (p1 v ') (p1 w) (p0 z) ?? ?? ??.
        - prove - p0 w ' * p1 v ' * p1 z = - p1 v ' * p1 z * p0 w '.
          f_equal.
          symmetry.
          exact mul_CSNo_rotate_3_1 (p1 v ') (p1 z) (p0 w ') ?? ?? ??.
      }
  + prove p0 z * p0 w * p0 v + - p1 w ' * p1 z * p0 v + - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w '
        = (p0 z * p0 w + - p1 w ' * p1 z) * p0 v + - p1 v ' * (p1 w * p0 z + p1 z * p0 w ').
    rewrite <- add_CSNo_assoc (p0 z * p0 w * p0 v) (- p1 w ' * p1 z * p0 v) (- p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w ') ?? ?? ??.
    f_equal.
    * prove p0 z * p0 w * p0 v + - p1 w ' * p1 z * p0 v = (p0 z * p0 w + - p1 w ' * p1 z) * p0 v.
      rewrite mul_CSNo_assoc (p0 z) (p0 w) (p0 v) ?? ?? ??.
      prove (p0 z * p0 w) * p0 v + - p1 w ' * p1 z * p0 v = (p0 z * p0 w + - p1 w ' * p1 z) * p0 v.
      rewrite mul_CSNo_assoc (p1 w ') (p1 z) (p0 v) ?? ?? ??.
      rewrite <- minus_mul_CSNo_distrL (p1 w ' * p1 z) (p0 v) ?? ??.
      prove (p0 z * p0 w) * p0 v + (- p1 w ' * p1 z) * p0 v = (p0 z * p0 w + - p1 w ' * p1 z) * p0 v.
      symmetry.
      exact mul_CSNo_distrR (p0 z * p0 w) (- p1 w ' * p1 z) (p0 v) ?? ?? ??.
    * prove - p1 v ' * p1 w * p0 z + - p1 v ' * p1 z * p0 w ' = - p1 v ' * (p1 w * p0 z + p1 z * p0 w ').
      rewrite <- minus_mul_CSNo_distrL (p1 v ') (p1 w * p0 z) ?? ??.
      rewrite <- minus_mul_CSNo_distrL (p1 v ') (p1 z * p0 w ') ?? ??.
      rewrite <- mul_CSNo_distrL (- p1 v ') (p1 w * p0 z) (p1 z * p0 w ') ?? ?? ??.
      exact minus_mul_CSNo_distrL (p1 v ') (p1 w * p0 z + p1 z * p0 w ') ?? ??.
  + prove (p0 z * p0 w + - p1 w ' * p1 z) * p0 v + - p1 v ' * (p1 w * p0 z + p1 z * p0 w ')
        = p0 (mult' z w) * p0 v + - p1 v ' * p1 (mult' z w).
    f_equal.
    * f_equal. symmetry. exact mul_HSNo_proj0 z w Hz Hw.
    * f_equal. f_equal. symmetry. exact mul_HSNo_proj1 z w Hz Hw.
  + symmetry. exact mul_HSNo_proj0 (mult' z w) v Lzw Hv.
- prove p1 (mult' z (mult' w v)) = p1 (mult' (mult' z w) v).
  transitivity p1 (mult' w v) * p0 z + p1 z * p0 (mult' w v) ',
               (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 w * p0 v + - (p1 v ' * p1 w)) ',
               (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 v ' * p0 w ' + - p1 v * p1 w '),
               p1 v * p0 w * p0 z + p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w ',
               p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ',
               p1 v * (p0 z * p0 w + - p1 w ' * p1 z)+ (p1 w * p0 z + p1 z * p0 w ') * p0 v ',
               p1 v * p0 (mult' z w) + p1 (mult' z w) * p0 v '.
  + exact mul_HSNo_proj1 z (mult' w v) Hz Lwv.
  + prove p1 (mult' w v) * p0 z + p1 z * p0 (mult' w v) '
        = (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 w * p0 v + - (p1 v ' * p1 w)) '.
    f_equal.
    * f_equal. exact mul_HSNo_proj1 w v Hw Hv.
    * f_equal. f_equal. exact mul_HSNo_proj0 w v Hw Hv.
  + prove (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 w * p0 v + - (p1 v ' * p1 w)) '
        = (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 v ' * p0 w ' + - p1 v * p1 w ').
    f_equal. f_equal.
    prove (p0 w * p0 v + - (p1 v ' * p1 w)) ' = p0 v ' * p0 w ' + - p1 v * p1 w '.
    rewrite conj_add_CSNo (p0 w * p0 v) (- (p1 v ' * p1 w)) ?? ??.
    rewrite conj_minus_CSNo (p1 v ' * p1 w) ??.
    prove (p0 w * p0 v) ' + - (p1 v ' * p1 w) ' = p0 v ' * p0 w ' + - p1 v * p1 w '.
    f_equal.
    * exact conj_mul_CSNo (p0 w) (p0 v) ?? ??.
    * f_equal.
      rewrite conj_mul_CSNo (p1 v ') (p1 w) ?? ??.
      prove p1 w ' * p1 v ' ' = p1 v * p1 w '.
      rewrite conj_CSNo_invol (p1 v) ??.
      prove p1 w ' * p1 v = p1 v * p1 w '.
      exact mul_CSNo_com (p1 w ') (p1 v) ?? ??.
  + prove (p1 v * p0 w + p1 w * p0 v ') * p0 z + p1 z * (p0 v ' * p0 w ' + - p1 v * p1 w ')
        = p1 v * p0 w * p0 z + p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w '.
    rewrite <- add_CSNo_assoc (p1 v * p0 w * p0 z) (p1 w * p0 v ' * p0 z) (p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w ') ?? ?? ??.
    f_equal.
    * prove (p1 v * p0 w + p1 w * p0 v ') * p0 z = p1 v * p0 w * p0 z + p1 w * p0 v ' * p0 z.
      rewrite mul_CSNo_distrR (p1 v * p0 w) (p1 w * p0 v ') (p0 z) ?? ?? ??.
      rewrite mul_CSNo_assoc (p1 v) (p0 w) (p0 z) ?? ?? ??.
      rewrite mul_CSNo_assoc (p1 w) (p0 v ') (p0 z) ?? ?? ??.
      reflexivity.
    * prove p1 z * (p0 v ' * p0 w ' + - p1 v * p1 w ') = p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w '.
      rewrite mul_CSNo_distrL (p1 z) (p0 v ' * p0 w ') (- p1 v * p1 w ') ?? ?? ??.
      f_equal.
      prove p1 z * (- p1 v * p1 w ') = - p1 z * p1 v * p1 w '.
      exact minus_mul_CSNo_distrR (p1 z) (p1 v * p1 w ') ?? ??.
  + prove p1 v * p0 w * p0 z + p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w '
        = p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v '.
    f_equal.
    * f_equal. exact mul_CSNo_com (p0 w) (p0 z) ?? ??.
    * { prove p1 w * p0 v ' * p0 z + p1 z * p0 v ' * p0 w ' + - p1 z * p1 v * p1 w '
            = - p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v '.
        rewrite add_CSNo_rotate_3_1 (p1 w * p0 v ' * p0 z) (p1 z * p0 v ' * p0 w ') (- p1 z * p1 v * p1 w ') ?? ?? ??.
	f_equal.
	- prove - p1 z * p1 v * p1 w ' = - p1 v * p1 w ' * p1 z.
	  f_equal.
	  symmetry.
	  exact mul_CSNo_rotate_3_1 (p1 v) (p1 w ') (p1 z) ?? ?? ??.
	- f_equal.
	  + prove p1 w * p0 v ' * p0 z = p1 w * p0 z * p0 v '.
	    f_equal.
	    exact mul_CSNo_com (p0 v ') (p0 z) ?? ??.
	  + prove p1 z * p0 v ' * p0 w ' = p1 z * p0 w ' * p0 v '.
	    f_equal.
	    exact mul_CSNo_com (p0 v ') (p0 w ') ?? ??.
      }
  + prove p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z + p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v '
        = p1 v * (p0 z * p0 w + - p1 w ' * p1 z) + (p1 w * p0 z + p1 z * p0 w ') * p0 v '.
    rewrite <- add_CSNo_assoc (p1 v * p0 z * p0 w) (- p1 v * p1 w ' * p1 z) (p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ') ?? ?? ??.
    f_equal.
    * prove p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z = p1 v * (p0 z * p0 w + - p1 w ' * p1 z).
      rewrite mul_CSNo_distrL (p1 v) (p0 z * p0 w) (- p1 w ' * p1 z) ?? ?? ??.
      prove p1 v * p0 z * p0 w + - p1 v * p1 w ' * p1 z = p1 v * p0 z * p0 w + p1 v * (- p1 w ' * p1 z).
      f_equal.
      prove - p1 v * p1 w ' * p1 z = p1 v * (- p1 w ' * p1 z).
      symmetry.
      exact minus_mul_CSNo_distrR (p1 v) (p1 w ' * p1 z) ?? ??.
    * prove p1 w * p0 z * p0 v ' + p1 z * p0 w ' * p0 v ' = (p1 w * p0 z + p1 z * p0 w ') * p0 v '.
      rewrite mul_CSNo_assoc (p1 w) (p0 z) (p0 v ') ?? ?? ??.
      rewrite mul_CSNo_assoc (p1 z) (p0 w ') (p0 v ') ?? ?? ??.
      symmetry.
      exact mul_CSNo_distrR (p1 w * p0 z) (p1 z * p0 w ') (p0 v ') ?? ?? ??.
  + prove p1 v * (p0 z * p0 w + - p1 w ' * p1 z) + (p1 w * p0 z + p1 z * p0 w ') * p0 v '
        = p1 v * p0 (mult' z w) + p1 (mult' z w) * p0 v '.
    f_equal.
    * f_equal. symmetry. exact mul_HSNo_proj0 z w Hz Hw.
    * f_equal. symmetry. exact mul_HSNo_proj1 z w Hz Hw.
  + symmetry. 
    prove p1 (mult' (mult' z w) v) = p1 v * p0 (mult' z w) + p1 (mult' z w) * p0 v '.
    exact mul_HSNo_proj1 (mult' z w) v Lzw Hv.
Qed.

Theorem conj_HSNo_i: i '' = :-: i.
rewrite conj_HSNo_conj_CSNo i CSNo_Complex_i.
rewrite minus_HSNo_minus_CSNo i CSNo_Complex_i.
prove i ' = - i.
exact conj_CSNo_i.
Qed.

Theorem conj_HSNo_j: j '' = :-: j.
apply HSNo_proj0proj1_split (j '') (:-: j) (HSNo_conj_HSNo j HSNo_Quaternion_j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
- prove p0 (j '') = p0 (:-: j).
  rewrite conj_HSNo_proj0 j HSNo_Quaternion_j.
  rewrite minus_HSNo_proj0 j HSNo_Quaternion_j.
  prove p0 j ' = - p0 j.
  rewrite HSNo_p0_j.
  prove 0 ' = - 0.
  rewrite minus_CSNo_0.
  exact conj_CSNo_id_SNo 0 SNo_0.
- prove p1 (j '') = p1 (:-: j).
  rewrite conj_HSNo_proj1 j HSNo_Quaternion_j.
  rewrite minus_HSNo_proj1 j HSNo_Quaternion_j.
  prove - p1 j = - p1 j.
  reflexivity.
Qed.

Theorem conj_HSNo_k: k '' = :-: k.
apply HSNo_proj0proj1_split (k '') (:-: k) (HSNo_conj_HSNo k HSNo_Quaternion_k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
- prove p0 (k '') = p0 (:-: k).
  rewrite conj_HSNo_proj0 k HSNo_Quaternion_k.
  rewrite minus_HSNo_proj0 k HSNo_Quaternion_k.
  prove p0 k ' = - p0 k.
  rewrite HSNo_p0_k.
  prove 0 ' = - 0.
  rewrite minus_CSNo_0.
  exact conj_CSNo_id_SNo 0 SNo_0.
- prove p1 (k '') = p1 (:-: k).
  rewrite conj_HSNo_proj1 k HSNo_Quaternion_k.
  rewrite minus_HSNo_proj1 k HSNo_Quaternion_k.
  prove - p1 k = - p1 k.
  reflexivity.
Qed.

End SurQuaternions.

Section Quaternions.

Prefix - 358 := minus_HSNo.
Infix + 360 right := add_HSNo.
Infix * 355 right := mul_HSNo.

Let i := Complex_i.
Let j := Quaternion_j.
Let k := Quaternion_k.
Let p0 : set -> set := HSNo_proj0.
Let p1 : set -> set := HSNo_proj1.
Let pa : set -> set -> set := CSNo_pair.

Definition quaternion : set := {pa (u 0) (u 1)|u :e complex :*: complex}.

Theorem quaternion_I : forall x y :e complex, pa x y :e quaternion.
let x. assume Hx. let y. assume Hy.
prove pa x y :e quaternion.
rewrite <- tuple_2_0_eq x y.
rewrite <- tuple_2_1_eq x y at 2.
prove pa ((x,y) 0) ((x,y) 1) :e quaternion.
apply ReplI (complex :*: complex) (fun u => pa (u 0) (u 1)).
prove (x,y) :e complex :*: complex.
exact tuple_2_setprod complex complex x Hx y Hy.
Qed.

Theorem quaternion_E : forall z :e quaternion, forall p:prop,
   (forall x y :e complex, z = pa x y -> p)
 -> p.
let z. assume Hz. let p. assume Hp.
apply ReplE_impred (complex :*: complex) (fun u => pa (u 0) (u 1)) z Hz.
let u.
assume Hu: u :e complex :*: complex.
assume Hzu: z = pa (u 0) (u 1).
exact Hp (u 0) (ap0_Sigma complex (fun _ => complex) u Hu)
         (u 1) (ap1_Sigma complex (fun _ => complex) u Hu)
         Hzu.
Qed.

Theorem quaternion_HSNo: forall z :e quaternion, HSNo z.
let z. assume Hz.
apply quaternion_E z Hz.
let x. assume Hx. let y. assume Hy.
assume Hzxy: z = pa x y.
prove HSNo z.
rewrite Hzxy. apply HSNo_I.
- exact complex_CSNo x Hx.
- exact complex_CSNo y Hy.
Qed.

Theorem complex_quaternion: complex c= quaternion.
let x. assume Hx: x :e complex.
prove x :e quaternion.
rewrite <- CSNo_pair_0 x.
prove pa x 0 :e quaternion.
apply quaternion_I.
- exact Hx.
- exact complex_0.
Qed.

Theorem quaternion_0 : 0 :e quaternion.
exact complex_quaternion 0 complex_0.
Qed.

Theorem quaternion_1 : 1 :e quaternion.
exact complex_quaternion 1 complex_1.
Qed.

Theorem quaternion_i : i :e quaternion.
exact complex_quaternion i complex_i.
Qed.

Theorem quaternion_j : j :e quaternion.
prove pa 0 1 :e quaternion.
apply quaternion_I.
- exact complex_0.
- exact complex_1.
Qed.

Theorem quaternion_k : k :e quaternion.
prove pa 0 i :e quaternion.
apply quaternion_I.
- exact complex_0.
- exact complex_i.
Qed.

Theorem quaternion_p0_eq: forall x y :e complex, p0 (pa x y) = x.
let x. assume Hx. let y. assume Hy.
exact HSNo_proj0_2 x y (complex_CSNo x Hx) (complex_CSNo y Hy).
Qed.

Theorem quaternion_p1_eq: forall x y :e complex, p1 (pa x y) = y.
let x. assume Hx. let y. assume Hy.
exact HSNo_proj1_2 x y (complex_CSNo x Hx) (complex_CSNo y Hy).
Qed.

Theorem quaternion_p0_complex: forall z :e quaternion, p0 z :e complex.
let z. assume Hz. apply quaternion_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove p0 (pa x y) :e complex.
rewrite quaternion_p0_eq x Hx y Hy.
prove x :e complex. exact Hx.
Qed.

Theorem quaternion_p1_complex: forall z :e quaternion, p1 z :e complex.
let z. assume Hz. apply quaternion_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove p1 (pa x y) :e complex.
rewrite quaternion_p1_eq x Hx y Hy.
prove y :e complex. exact Hy.
Qed.

Theorem quaternion_proj0proj1_split: forall z w :e quaternion, p0 z = p0 w -> p1 z = p1 w -> z = w.
let z. assume Hz. let w. assume Hw.
exact HSNo_proj0proj1_split z w (quaternion_HSNo z Hz) (quaternion_HSNo w Hw).
Qed.

Theorem quaternion_minus_HSNo : forall z :e quaternion, - z :e quaternion.
let z. assume Hz.
prove pa (minus_CSNo (p0 z)) (minus_CSNo (p1 z)) :e quaternion.
apply quaternion_I.
- apply complex_minus_CSNo. exact quaternion_p0_complex z Hz.
- apply complex_minus_CSNo. exact quaternion_p1_complex z Hz.
Qed.

Theorem quaternion_conj_HSNo : forall z :e quaternion, conj_HSNo z :e quaternion.
let z. assume Hz.
prove pa (conj_CSNo (p0 z)) (minus_CSNo (p1 z)) :e quaternion.
apply quaternion_I.
- apply complex_conj_CSNo. exact quaternion_p0_complex z Hz.
- apply complex_minus_CSNo. exact quaternion_p1_complex z Hz.
Qed.

Theorem quaternion_add_HSNo : forall z w :e quaternion, z + w :e quaternion.
let z. assume Hz. let w. assume Hw.
prove pa (add_CSNo (p0 z) (p0 w)) (add_CSNo (p1 z) (p1 w)) :e quaternion.
apply quaternion_I.
- apply complex_add_CSNo.
  + exact quaternion_p0_complex z Hz.
  + exact quaternion_p0_complex w Hw.
- apply complex_add_CSNo.
  + exact quaternion_p1_complex z Hz.
  + exact quaternion_p1_complex w Hw.
Qed.

Theorem quaternion_mul_HSNo : forall z w :e quaternion, z * w :e quaternion.
let z. assume Hz. let w. assume Hw.
prove pa (add_CSNo (mul_CSNo (p0 z) (p0 w)) (minus_CSNo (mul_CSNo (conj_CSNo (p1 w)) (p1 z))))
         (add_CSNo (mul_CSNo (p1 w) (p0 z)) (mul_CSNo (p1 z) (conj_CSNo (p0 w))))
       :e quaternion.
claim Lz0: p0 z :e complex.
{ exact quaternion_p0_complex z Hz. }
claim Lz1: p1 z :e complex.
{ exact quaternion_p1_complex z Hz. }
claim Lw0: p0 w :e complex.
{ exact quaternion_p0_complex w Hw. }
claim Lw1: p1 w :e complex.
{ exact quaternion_p1_complex w Hw. }
apply quaternion_I.
- apply complex_add_CSNo.
  + apply complex_mul_CSNo.
    * exact ??.
    * exact ??.
  + apply complex_minus_CSNo. apply complex_mul_CSNo.
    * apply complex_conj_CSNo. exact ??.
    * exact ??.
- apply complex_add_CSNo.
  + apply complex_mul_CSNo.
    * exact ??.
    * exact ??.
  + apply complex_mul_CSNo.
    * exact ??.
    * apply complex_conj_CSNo. exact ??.
Qed.

Theorem complex_p0_eq: forall x :e complex, p0 x = x.
let x. assume Hx.
rewrite <- CSNo_pair_0 x at 1.
exact quaternion_p0_eq x Hx 0 complex_0.
Qed.

Theorem complex_p1_eq: forall x :e complex, p1 x = 0.
let x. assume Hx.
rewrite <- CSNo_pair_0 x.
exact quaternion_p1_eq x Hx 0 complex_0.
Qed.

End Quaternions.

Opaque CSNo_pair.
Opaque HSNo.
Opaque Quaternion_j.
Opaque Quaternion_k.
Opaque HSNo_proj0.
Opaque HSNo_proj1.
Opaque HSNoLev.
Opaque minus_HSNo.
Opaque conj_HSNo.
Opaque add_HSNo.
Opaque mul_HSNo.
Opaque exp_HSNo_nat.
Opaque quaternion.
