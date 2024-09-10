(** Part 14 **)
Section SurOctonions.

Theorem octonion_tag_fresh: forall x, HSNo x -> forall u :e x, {4} /:e u.
let z. assume Hz.
apply Sing_nat_fresh_extension 4 nat_4 In_1_4 z.
prove ExtendedSNoElt_ 4 z.
exact HSNo_ExtendedSNoElt_4 z Hz.
Qed.

Definition HSNo_pair : set -> set -> set := pair_tag {4}.

Theorem HSNo_pair_0 : forall x, HSNo_pair x 0 = x.
exact pair_tag_0 {4} HSNo octonion_tag_fresh.
Qed.

Theorem HSNo_pair_prop_1 : forall x1 y1 x2 y2, HSNo x1 -> HSNo x2 -> HSNo_pair x1 y1 = HSNo_pair x2 y2 -> x1 = x2.
exact pair_tag_prop_1 {4} HSNo octonion_tag_fresh.
Qed.

Theorem HSNo_pair_prop_2 : forall x1 y1 x2 y2, HSNo x1 -> HSNo y1 -> HSNo x2 -> HSNo y2 -> HSNo_pair x1 y1 = HSNo_pair x2 y2 -> y1 = y2.
exact pair_tag_prop_2 {4} HSNo octonion_tag_fresh.
Qed.

Definition OSNo : set -> prop := CD_carr {4} HSNo.

Theorem OSNo_I : forall x y, HSNo x -> HSNo y -> OSNo (HSNo_pair x y).
exact CD_carr_I {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_E : forall z, OSNo z ->
  forall p:set -> prop,
      (forall x y, HSNo x -> HSNo y -> z = HSNo_pair x y -> p (HSNo_pair x y))
    -> p z.
exact CD_carr_E {4} HSNo octonion_tag_fresh.
Qed.

Theorem HSNo_OSNo : forall x, HSNo x -> OSNo x.
exact CD_carr_0ext {4} HSNo octonion_tag_fresh HSNo_0.
Qed.

Theorem OSNo_0: OSNo 0.
apply HSNo_OSNo. exact HSNo_0.
Qed.

Theorem OSNo_1: OSNo 1.
apply HSNo_OSNo. exact HSNo_1.
Qed.

Let ctag : set -> set := fun alpha => SetAdjoin alpha {4}.
Postfix '' 100 := ctag.

Theorem OSNo_ExtendedSNoElt_5: forall z, OSNo z -> ExtendedSNoElt_ 5 z.
let z. assume Hz.
apply OSNo_E z Hz.
let x y.
assume Hx: HSNo x.
assume Hy: HSNo y.
assume Hzxy: z = HSNo_pair x y.
let v.
assume Hv: v :e Union (HSNo_pair x y).
apply UnionE_impred (HSNo_pair x y) v Hv.
let u.
assume H1: v :e u.
assume H2: u :e HSNo_pair x y.
apply binunionE x {w ''|w :e y} u H2.
- assume H3: u :e x.
  claim L1: v :e Union x.
  { exact UnionI x v u H1 H3. }
  prove ordinal v \/ exists i :e 5, v = {i}.
  exact extension_SNoElt_mon 4 5 (ordsuccI1 4) x (HSNo_ExtendedSNoElt_4 x Hx) v L1.
- assume H3: u :e {w ''|w :e y}.
  apply ReplE_impred y ctag u H3.
  let w.
  assume Hw: w :e y.
  assume H4: u = w ''.
  claim L2: v :e w ''.
  { rewrite <- H4. exact H1. }
  apply binunionE w {{4}} v L2.
  + assume H5: v :e w.
    claim L3: v :e Union y.
    { exact UnionI y v w H5 Hw. }
    exact extension_SNoElt_mon 4 5 (ordsuccI1 4) y (HSNo_ExtendedSNoElt_4 y Hy) v L3.
  + assume H5: v :e {{4}}.
    prove ordinal v \/ exists i :e 5, v = {i}.
    apply orIR.
    witness 4. apply andI.
    * prove 4 :e 5. exact In_4_5.
    * prove v = {4}. exact SingE {4} v H5.
Qed.

Prefix - 358 := minus_HSNo.
Infix + 360 right := add_HSNo.
Infix * 355 right := mul_HSNo.
Infix :/: 353 := div_HSNo.
Postfix ' 100 := conj_HSNo.

Let i := Complex_i.
Let j := Quaternion_j.
Let k := Quaternion_k.

Definition OSNo_proj0 : set -> set := CD_proj0 {4} HSNo.
Definition OSNo_proj1 : set -> set := CD_proj1 {4} HSNo.

Let p0 : set -> set := OSNo_proj0.
Let p1 : set -> set := OSNo_proj1.
Let pa : set -> set -> set := HSNo_pair.

Theorem OSNo_proj0_1: forall z, OSNo z -> HSNo (p0 z) /\ exists y, HSNo y /\ z = pa (p0 z) y.
exact CD_proj0_1 {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj0_2: forall x y, HSNo x -> HSNo y -> p0 (pa x y) = x.
exact CD_proj0_2 {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj1_1: forall z, OSNo z -> HSNo (p1 z) /\ z = pa (p0 z) (p1 z).
exact CD_proj1_1 {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj1_2: forall x y, HSNo x -> HSNo y -> p1 (pa x y) = y.
exact CD_proj1_2 {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj0R: forall z, OSNo z -> HSNo (p0 z).
exact CD_proj0R {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj1R: forall z, OSNo z -> HSNo (p1 z).
exact CD_proj1R {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj0p1: forall z, OSNo z -> z = pa (p0 z) (p1 z).
exact CD_proj0proj1_eta {4} HSNo octonion_tag_fresh.
Qed.

Theorem OSNo_proj0proj1_split: forall z w, OSNo z -> OSNo w -> p0 z = p0 w -> p1 z = p1 w -> z = w.
exact CD_proj0proj1_split {4} HSNo octonion_tag_fresh.
Qed.

Definition OSNoLev : set -> set := fun z => HSNoLev (p0 z) :\/: HSNoLev (p1 z).

Theorem OSNoLev_ordinal: forall z, OSNo z -> ordinal (OSNoLev z).
let z. assume Hz.
apply OSNo_E z Hz.
let x y.
assume Hx Hy.
assume Hzxy: z = pa x y.
prove ordinal (HSNoLev (p0 (pa x y)) :\/: HSNoLev (p1 (pa x y))).
rewrite OSNo_proj0_2 x y Hx Hy.
rewrite OSNo_proj1_2 x y Hx Hy.
prove ordinal (HSNoLev x :\/: HSNoLev y).
exact ordinal_binunion (HSNoLev x) (HSNoLev y) (HSNoLev_ordinal x Hx) (HSNoLev_ordinal y Hy).
Qed.

Definition minus_OSNo : set -> set := CD_minus {4} HSNo minus_HSNo.
Definition conj_OSNo : set -> set := CD_conj {4} HSNo minus_HSNo conj_HSNo.
Definition add_OSNo : set -> set -> set := CD_add {4} HSNo add_HSNo.
Definition mul_OSNo : set -> set -> set := CD_mul {4} HSNo minus_HSNo conj_HSNo add_HSNo mul_HSNo.
Definition exp_OSNo_nat : set -> set -> set := CD_exp_nat {4} HSNo minus_HSNo conj_HSNo add_HSNo mul_HSNo.

Let plus' := add_OSNo.
Let mult' := mul_OSNo.

Prefix :-: 358 := minus_OSNo.
Postfix '' 100 := conj_OSNo.
Infix :+: 360 right := add_OSNo.
Infix :*: 355 right := mul_OSNo.
Infix :^: 355 right := exp_OSNo_nat.

Theorem OSNo_minus_OSNo : forall z, OSNo z -> OSNo (minus_OSNo z).
exact CD_minus_CD {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo.
Qed.

Theorem minus_OSNo_proj0: forall z, OSNo z -> p0 (:-: z) = - p0 z.
exact CD_minus_proj0 {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo.
Qed.

Theorem minus_OSNo_proj1: forall z, OSNo z -> p1 (:-: z) = - p1 z.
exact CD_minus_proj1 {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo.
Qed.

Theorem OSNo_conj_OSNo : forall z, OSNo z -> OSNo (conj_OSNo z).
exact CD_conj_CD {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo conj_HSNo HSNo_conj_HSNo.
Qed.

Theorem conj_OSNo_proj0: forall z, OSNo z -> p0 (z '') = (p0 z) '.
exact CD_conj_proj0 {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo conj_HSNo HSNo_conj_HSNo.
Qed.

Theorem conj_OSNo_proj1: forall z, OSNo z -> p1 (z '') = - p1 z.
exact CD_conj_proj1 {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo conj_HSNo HSNo_conj_HSNo.
Qed.

Theorem OSNo_add_OSNo : forall z w, OSNo z -> OSNo w -> OSNo (add_OSNo z w).
exact CD_add_CD {4} HSNo octonion_tag_fresh add_HSNo HSNo_add_HSNo.
Qed.

Theorem add_OSNo_proj0: forall z w, OSNo z -> OSNo w -> p0 (plus' z w) = p0 z + p0 w.
exact CD_add_proj0 {4} HSNo octonion_tag_fresh add_HSNo HSNo_add_HSNo.
Qed.

Theorem add_OSNo_proj1: forall z w, OSNo z -> OSNo w -> p1 (plus' z w) = p1 z + p1 w.
exact CD_add_proj1 {4} HSNo octonion_tag_fresh add_HSNo HSNo_add_HSNo.
Qed.

Theorem OSNo_mul_OSNo : forall z w, OSNo z -> OSNo w -> OSNo (z :*: w).
exact CD_mul_CD {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo.
Qed.

Theorem mul_OSNo_proj0: forall z w, OSNo z -> OSNo w -> p0 (mult' z w) = p0 z * p0 w + - (p1 w ' * p1 z).
exact CD_mul_proj0 {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo.
Qed.

Theorem mul_OSNo_proj1: forall z w, OSNo z -> OSNo w -> p1 (mult' z w) = p1 w * p0 z + p1 z * p0 w '.
exact CD_mul_proj1 {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo.
Qed.

Theorem HSNo_OSNo_proj0: forall x, HSNo x -> p0 x = x.
exact CD_proj0_F {4} HSNo octonion_tag_fresh HSNo_0.
Qed.

Theorem HSNo_OSNo_proj1: forall x, HSNo x -> p1 x = 0.
exact CD_proj1_F {4} HSNo octonion_tag_fresh HSNo_0.
Qed.

Theorem OSNo_p0_0 : p0 0 = 0.
exact HSNo_OSNo_proj0 0 HSNo_0.
Qed.

Theorem OSNo_p1_0 : p1 0 = 0.
exact HSNo_OSNo_proj1 0 HSNo_0.
Qed.

Theorem OSNo_p0_1 : p0 1 = 1.
exact HSNo_OSNo_proj0 1 HSNo_1.
Qed.

Theorem OSNo_p1_1 : p1 1 = 0.
exact HSNo_OSNo_proj1 1 HSNo_1.
Qed.

Theorem OSNo_p0_i : p0 i = i.
exact HSNo_OSNo_proj0 i HSNo_Complex_i.
Qed.

Theorem OSNo_p1_i : p1 i = 0.
exact HSNo_OSNo_proj1 i HSNo_Complex_i.
Qed.

Theorem OSNo_p0_j : p0 j = j.
exact HSNo_OSNo_proj0 j HSNo_Quaternion_j.
Qed.

Theorem OSNo_p1_j : p1 j = 0.
exact HSNo_OSNo_proj1 j HSNo_Quaternion_j.
Qed.

Theorem OSNo_p0_k : p0 k = k.
exact HSNo_OSNo_proj0 k HSNo_Quaternion_k.
Qed.

Theorem OSNo_p1_k : p1 k = 0.
exact HSNo_OSNo_proj1 k HSNo_Quaternion_k.
Qed.

Theorem minus_OSNo_minus_HSNo : forall x, HSNo x -> :-: x = - x.
exact CD_minus_F_eq {4} HSNo octonion_tag_fresh minus_HSNo HSNo_0 minus_HSNo_0.
Qed.

Theorem minus_OSNo_0 : :-: 0 = 0.
rewrite minus_OSNo_minus_HSNo 0 HSNo_0.
exact minus_HSNo_0.
Qed.

Theorem conj_OSNo_conj_HSNo: forall x, HSNo x -> x '' = x '.
exact CD_conj_F_eq {4} HSNo octonion_tag_fresh minus_HSNo HSNo_0 minus_HSNo_0 conj_HSNo.
Qed.

Theorem conj_OSNo_0 : 0 '' = 0.
rewrite conj_OSNo_conj_HSNo 0 HSNo_0.
exact conj_HSNo_0.
Qed.

Theorem conj_OSNo_1 : 1 '' = 1.
rewrite conj_OSNo_conj_HSNo 1 HSNo_1.
exact conj_HSNo_1.
Qed.

Theorem add_OSNo_add_HSNo: forall x y, HSNo x -> HSNo y -> x :+: y = x + y.
exact CD_add_F_eq {4} HSNo octonion_tag_fresh add_HSNo HSNo_0 (add_HSNo_0L 0 HSNo_0).
Qed.

Theorem mul_OSNo_mul_HSNo: forall x y, HSNo x -> HSNo y -> x :*: y = x * y.
exact CD_mul_F_eq {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_conj_HSNo HSNo_mul_HSNo minus_HSNo_0 add_HSNo_0R mul_HSNo_0L mul_HSNo_0R.
Qed.

Theorem minus_OSNo_invol : forall z, OSNo z -> :-: :-: z = z.
exact CD_minus_invol {4} HSNo octonion_tag_fresh minus_HSNo HSNo_minus_HSNo minus_HSNo_invol.
Qed.

Theorem conj_OSNo_invol : forall z, OSNo z -> z '' '' = z.
exact CD_conj_invol {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo HSNo_minus_HSNo HSNo_conj_HSNo minus_HSNo_invol conj_HSNo_invol.
Qed.

Theorem conj_minus_OSNo: forall z, OSNo z -> (:-: z) '' = :-: (z '').
exact CD_conj_minus {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo HSNo_minus_HSNo HSNo_conj_HSNo conj_minus_HSNo.
Qed.

Theorem minus_add_OSNo: forall z w, OSNo z -> OSNo w -> :-: (z :+: w) = :-: z :+: :-: w.
exact CD_minus_add {4} HSNo octonion_tag_fresh minus_HSNo add_HSNo HSNo_minus_HSNo HSNo_add_HSNo minus_add_HSNo.
Qed.

Theorem conj_add_OSNo: forall z w, OSNo z -> OSNo w -> (z :+: w) '' = z '' :+: w ''.
exact CD_conj_add {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo minus_add_HSNo conj_add_HSNo.
Qed.

Theorem add_OSNo_com : forall z w, OSNo z -> OSNo w -> z :+: w = w :+: z.
exact CD_add_com {4} HSNo octonion_tag_fresh add_HSNo add_HSNo_com.
Qed.

Theorem add_OSNo_assoc: forall z w v, OSNo z -> OSNo w -> OSNo v -> (z :+: w) :+: v = z :+: (w :+: v).
apply CD_add_assoc {4} HSNo octonion_tag_fresh add_HSNo HSNo_add_HSNo add_HSNo_assoc.
Qed.

Theorem add_OSNo_0L : forall z, OSNo z -> add_OSNo 0 z = z.
exact CD_add_0L {4} HSNo octonion_tag_fresh add_HSNo HSNo_0 add_HSNo_0L.
Qed.

Theorem add_OSNo_0R : forall z, OSNo z -> add_OSNo z 0 = z.
exact CD_add_0R {4} HSNo octonion_tag_fresh add_HSNo HSNo_0 add_HSNo_0R.
Qed.

Theorem add_OSNo_minus_OSNo_linv : forall z, OSNo z -> add_OSNo (minus_OSNo z) z = 0.
exact CD_add_minus_linv {4} HSNo octonion_tag_fresh minus_HSNo add_HSNo HSNo_minus_HSNo add_HSNo_minus_HSNo_linv.
Qed.

Theorem add_OSNo_minus_OSNo_rinv : forall z, OSNo z -> add_OSNo z (minus_OSNo z) = 0.
exact CD_add_minus_rinv {4} HSNo octonion_tag_fresh minus_HSNo add_HSNo HSNo_minus_HSNo add_HSNo_minus_HSNo_rinv.
Qed.

Theorem mul_OSNo_0R: forall z, OSNo z -> z :*: 0 = 0.
exact CD_mul_0R {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 minus_HSNo_0 conj_HSNo_0 (add_HSNo_0L 0 HSNo_0) mul_HSNo_0L mul_HSNo_0R.
Qed.

Theorem mul_OSNo_0L: forall z, OSNo z -> 0 :*: z = 0.
exact CD_mul_0L {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_conj_HSNo minus_HSNo_0 (add_HSNo_0L 0 HSNo_0) mul_HSNo_0L mul_HSNo_0R.
Qed.

Theorem mul_OSNo_1R: forall z, OSNo z -> z :*: 1 = z.
exact CD_mul_1R {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_1 minus_HSNo_0 conj_HSNo_0 conj_HSNo_1 add_HSNo_0L add_HSNo_0R mul_HSNo_0L mul_HSNo_1R.
Qed.

Theorem mul_OSNo_1L: forall z, OSNo z -> 1 :*: z = z.
exact CD_mul_1L {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_1 HSNo_conj_HSNo minus_HSNo_0 add_HSNo_0R mul_HSNo_0L mul_HSNo_0R mul_HSNo_1L mul_HSNo_1R.
Qed.

Theorem conj_mul_OSNo: forall z w, OSNo z -> OSNo w -> (z :*: w) '' = w '' :*: z ''.
exact CD_conj_mul {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo minus_HSNo_invol conj_HSNo_invol conj_minus_HSNo conj_add_HSNo minus_add_HSNo add_HSNo_com conj_mul_HSNo minus_mul_HSNo_distrR minus_mul_HSNo_distrL.
Qed.

Theorem mul_OSNo_distrL : forall z w u, OSNo z -> OSNo w -> OSNo u -> z :*: (w :+: u) = z :*: w :+: z :*: u.
exact CD_add_mul_distrL {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo minus_add_HSNo conj_add_HSNo add_HSNo_assoc add_HSNo_com mul_HSNo_distrL mul_HSNo_distrR.
Qed.

Theorem mul_OSNo_distrR : forall z w u, OSNo z -> OSNo w -> OSNo u -> (z :+: w) :*: u = z :*: u :+: w :*: u.
exact CD_add_mul_distrR {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo minus_add_HSNo add_HSNo_assoc add_HSNo_com mul_HSNo_distrL mul_HSNo_distrR.
Qed.

Theorem minus_mul_OSNo_distrR: forall z w, OSNo z -> OSNo w -> z :*: (:-: w) = :-: z :*: w.
exact CD_minus_mul_distrR {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo conj_minus_HSNo minus_add_HSNo minus_mul_HSNo_distrR minus_mul_HSNo_distrL.
Qed.

Theorem minus_mul_OSNo_distrL: forall z w, OSNo z -> OSNo w -> (:-: z) :*: w = :-: z :*: w.
exact CD_minus_mul_distrL {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo minus_add_HSNo minus_mul_HSNo_distrR minus_mul_HSNo_distrL.
Qed.

Theorem exp_OSNo_nat_0: forall z, z :^: 0 = 1.
exact CD_exp_nat_0 {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo.
Qed.

Theorem exp_OSNo_nat_S: forall z n, nat_p n -> z :^: (ordsucc n) = z :*: z :^: n.
exact CD_exp_nat_S {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo.
Qed.

Theorem exp_OSNo_nat_1: forall z, OSNo z -> z :^: 1 = z.
exact CD_exp_nat_1 {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_1 minus_HSNo_0 conj_HSNo_0 conj_HSNo_1 add_HSNo_0L add_HSNo_0R mul_HSNo_0L mul_HSNo_1R.
Qed.

Theorem exp_OSNo_nat_2: forall z, OSNo z -> z :^: 2 = z :*: z.
exact CD_exp_nat_2 {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_0 HSNo_1 minus_HSNo_0 conj_HSNo_0 conj_HSNo_1 add_HSNo_0L add_HSNo_0R mul_HSNo_0L mul_HSNo_1R.
Qed.

Theorem OSNo_exp_OSNo_nat: forall z, OSNo z -> forall n, nat_p n -> OSNo (z :^: n).
exact CD_exp_nat_CD {4} HSNo octonion_tag_fresh minus_HSNo conj_HSNo add_HSNo mul_HSNo HSNo_minus_HSNo HSNo_conj_HSNo HSNo_add_HSNo HSNo_mul_HSNo HSNo_0 HSNo_1.
Qed.

Theorem add_HSNo_com_3b_1_2 : forall x y z, HSNo x -> HSNo y -> HSNo z
  -> (x + y) + z = (x + z) + y.
let x y z.
assume Hx Hy Hz.
prove (x + y) + z = (x + z) + y.
rewrite add_HSNo_assoc x y z Hx Hy Hz.
prove x + y + z = (x + z) + y.
rewrite add_HSNo_assoc x z y Hx Hz Hy.
prove x + y + z = x + z + y.
f_equal.
exact add_HSNo_com y z Hy Hz.
Qed.

Theorem add_HSNo_com_4_inner_mid : forall x y z w, HSNo x -> HSNo y -> HSNo z -> HSNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
let x y z w.
assume Hx Hy Hz Hw.
rewrite <- add_HSNo_assoc (x + y) z w (HSNo_add_HSNo x y Hx Hy) Hz Hw.
prove ((x + y) + z) + w = (x + z) + (y + w).
rewrite add_HSNo_com_3b_1_2 x y z Hx Hy Hz.
prove ((x + z) + y) + w = (x + z) + (y + w).
exact add_HSNo_assoc (x + z) y w (HSNo_add_HSNo x z Hx Hz) Hy Hw.
Qed.

Theorem add_HSNo_rotate_4_0312: forall x y z w, HSNo x -> HSNo y -> HSNo z -> HSNo w -> (x + y) + (z + w) = (x + w) + (y + z).
let x y z w. assume Hx Hy Hz Hw.
rewrite add_HSNo_com z w Hz Hw.
prove (x + y) + (w + z) = (x + w) + (y + z).
exact add_HSNo_com_4_inner_mid x y w z Hx Hy Hw Hz.
Qed.

Definition Octonion_i0 : set := pa 0 1.
Definition Octonion_i3 : set := pa 0 (- Complex_i).
Definition Octonion_i5 : set := pa 0 (- Quaternion_k).
Definition Octonion_i6 : set := pa 0 (- Quaternion_j).

Let i0 := Octonion_i0.
Let i1 := Complex_i.
Let i2 := Quaternion_j.
Let i3 := Octonion_i3.
Let i4 := Quaternion_k.
Let i5 := Octonion_i5.
Let i6 := Octonion_i6.

Theorem OSNo_Complex_i : OSNo i.
apply HSNo_OSNo. exact HSNo_Complex_i.
Qed.

Theorem OSNo_Quaternion_j: OSNo j.
apply HSNo_OSNo. exact HSNo_Quaternion_j.
Qed.

Theorem OSNo_Quaternion_k: OSNo k.
apply HSNo_OSNo. exact HSNo_Quaternion_k.
Qed.

Theorem OSNo_Octonion_i0: OSNo i0.
exact OSNo_I 0 1 HSNo_0 HSNo_1.
Qed.

Theorem OSNo_Octonion_i3: OSNo i3.
exact OSNo_I 0 (- i) HSNo_0 (HSNo_minus_HSNo i HSNo_Complex_i).
Qed.

Theorem OSNo_Octonion_i5: OSNo i5.
exact OSNo_I 0 (- k) HSNo_0 (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem OSNo_Octonion_i6: OSNo i6.
exact OSNo_I 0 (- j) HSNo_0 (HSNo_minus_HSNo j HSNo_Quaternion_j).
Qed.

Theorem OSNo_p0_i0: p0 i0 = 0.
exact OSNo_proj0_2 0 1 HSNo_0 HSNo_1.
Qed.

Theorem OSNo_p1_i0: p1 i0 = 1.
exact OSNo_proj1_2 0 1 HSNo_0 HSNo_1.
Qed.

Theorem OSNo_p0_i3: p0 i3 = 0.
exact OSNo_proj0_2 0 (- i) HSNo_0 (HSNo_minus_HSNo i HSNo_Complex_i).
Qed.

Theorem OSNo_p1_i3: p1 i3 = - i.
exact OSNo_proj1_2 0 (- i) HSNo_0 (HSNo_minus_HSNo i HSNo_Complex_i).
Qed.

Theorem OSNo_p0_i5: p0 i5 = 0.
exact OSNo_proj0_2 0 (- k) HSNo_0 (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem OSNo_p1_i5: p1 i5 = - k.
exact OSNo_proj1_2 0 (- k) HSNo_0 (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem OSNo_p0_i6: p0 i6 = 0.
exact OSNo_proj0_2 0 (- j) HSNo_0 (HSNo_minus_HSNo j HSNo_Quaternion_j).
Qed.

Theorem OSNo_p1_i6: p1 i6 = - j.
exact OSNo_proj1_2 0 (- j) HSNo_0 (HSNo_minus_HSNo j HSNo_Quaternion_j).
Qed.

Theorem Octonion_i1_sqr : i1 :*: i1 = :-: 1.
rewrite mul_OSNo_mul_HSNo i i HSNo_Complex_i HSNo_Complex_i.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
prove i * i = - 1.
exact Quaternion_i_sqr.
Qed.

Theorem Octonion_i2_sqr : i2 :*: i2 = :-: 1.
rewrite mul_OSNo_mul_HSNo j j HSNo_Quaternion_j HSNo_Quaternion_j.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
prove j * j = - 1.
exact Quaternion_j_sqr.
Qed.

Theorem Octonion_i4_sqr : i4 :*: i4 = :-: 1.
rewrite mul_OSNo_mul_HSNo k k HSNo_Quaternion_k HSNo_Quaternion_k.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
prove k * k = - 1.
exact Quaternion_k_sqr.
Qed.

Theorem Octonion_i0_sqr : i0 :*: i0 = :-: 1.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
claim Li0i0: OSNo (i0 :*: i0).
{ exact OSNo_mul_OSNo i0 i0 OSNo_Octonion_i0 OSNo_Octonion_i0. }
prove i0 :*: i0 = - 1.
claim L1: HSNo (- 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply OSNo_proj0proj1_split (i0 :*: i0) (- 1) Li0i0 (HSNo_OSNo (- 1) L1).
- prove p0 (i0 :*: i0) = p0 (- 1).
  rewrite HSNo_OSNo_proj0 (- 1) L1.
  prove p0 (i0 :*: i0) = - 1.
  rewrite mul_OSNo_proj0 i0 i0 OSNo_Octonion_i0 OSNo_Octonion_i0.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - (1 ' * 1) = - 1.
  rewrite mul_HSNo_0L 0 HSNo_0.
  prove 0 + - (1 ' * 1) = - 1.
  rewrite conj_HSNo_id_SNo 1 SNo_1.
  prove 0 + - (1 * 1) = - 1.
  rewrite mul_HSNo_1L 1 HSNo_1.
  prove 0 + - 1 = - 1.
  exact add_HSNo_0L (- 1) L1.
- prove p1 (i0 :*: i0) = p1 (- 1).
  rewrite HSNo_OSNo_proj1 (- 1) L1.
  prove p1 (i0 :*: i0) = 0.
  rewrite mul_OSNo_proj1 i0 i0 OSNo_Octonion_i0 OSNo_Octonion_i0.
  prove p1 i0 * p0 i0 + p1 i0 * p0 i0 ' = 0.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 1 * 0 + 1 * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i3_sqr : i3 :*: i3 = :-: 1.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
claim Li3i3: OSNo (i3 :*: i3).
{ exact OSNo_mul_OSNo i3 i3 OSNo_Octonion_i3 OSNo_Octonion_i3. }
prove i3 :*: i3 = - 1.
claim L1: HSNo (- 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply OSNo_proj0proj1_split (i3 :*: i3) (- 1) Li3i3 (HSNo_OSNo (- 1) L1).
- prove p0 (i3 :*: i3) = p0 (- 1).
  rewrite HSNo_OSNo_proj0 (- 1) L1.
  prove p0 (i3 :*: i3) = - 1.
  rewrite mul_OSNo_proj0 i3 i3 OSNo_Octonion_i3 OSNo_Octonion_i3.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  rewrite mul_HSNo_0R 0 HSNo_0.
  prove 0 + - ((- i) ' * (- i)) = - 1.
  rewrite conj_minus_HSNo i HSNo_Complex_i.
  prove 0 + - ((- i ') * (- i)) = - 1.
  rewrite conj_HSNo_i.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  prove 0 + - (i * (- i)) = - 1.
  rewrite minus_mul_HSNo_distrR i i HSNo_Complex_i HSNo_Complex_i.
  prove 0 + - - i * i = - 1.
  rewrite minus_HSNo_invol (i * i) (HSNo_mul_HSNo i i HSNo_Complex_i HSNo_Complex_i).
  rewrite Quaternion_i_sqr.
  prove 0 + - 1 = - 1.
  exact add_HSNo_0L (- 1) L1.
- prove p1 (i3 :*: i3) = p1 (- 1).
  rewrite HSNo_OSNo_proj1 (- 1) L1.
  prove p1 (i3 :*: i3) = 0.
  rewrite mul_OSNo_proj1 i3 i3 OSNo_Octonion_i3 OSNo_Octonion_i3.
  prove p1 i3 * p0 i3 + p1 i3 * p0 i3 ' = 0.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove (- i) * 0 + (- i) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  prove (- i) * 0 + (- i) * 0 = 0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i5_sqr : i5 :*: i5 = :-: 1.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
claim Li5i5: OSNo (i5 :*: i5).
{ exact OSNo_mul_OSNo i5 i5 OSNo_Octonion_i5 OSNo_Octonion_i5. }
prove i5 :*: i5 = - 1.
claim L1: HSNo (- 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply OSNo_proj0proj1_split (i5 :*: i5) (- 1) Li5i5 (HSNo_OSNo (- 1) L1).
- prove p0 (i5 :*: i5) = p0 (- 1).
  rewrite HSNo_OSNo_proj0 (- 1) L1.
  prove p0 (i5 :*: i5) = - 1.
  rewrite mul_OSNo_proj0 i5 i5 OSNo_Octonion_i5 OSNo_Octonion_i5.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  rewrite mul_HSNo_0L 0 HSNo_0.
  prove 0 + - ((- k) ' * (- k)) = - 1.
  rewrite conj_minus_HSNo k HSNo_Quaternion_k.
  prove 0 + - ((- k ') * (- k)) = - 1.
  rewrite conj_HSNo_k.
  prove 0 + - ((- - k) * (- k)) = - 1.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  prove 0 + - (k * (- k)) = - 1.
  rewrite minus_mul_HSNo_distrR k k HSNo_Quaternion_k HSNo_Quaternion_k.
  prove 0 + - - (k * k) = - 1.
  rewrite Quaternion_k_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  prove 0 + - 1 = - 1.
  exact add_HSNo_0L (- 1) L1.
- prove p1 (i5 :*: i5) = p1 (- 1).
  rewrite HSNo_OSNo_proj1 (- 1) L1.
  prove p1 (i5 :*: i5) = 0.
  rewrite mul_OSNo_proj1 i5 i5 OSNo_Octonion_i5 OSNo_Octonion_i5.
  prove p1 i5 * p0 i5 + p1 i5 * p0 i5 ' = 0.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove (- k) * 0 + (- k) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i6_sqr : i6 :*: i6 = :-: 1.
rewrite minus_OSNo_minus_HSNo 1 HSNo_1.
claim Li6i6: OSNo (i6 :*: i6).
{ exact OSNo_mul_OSNo i6 i6 OSNo_Octonion_i6 OSNo_Octonion_i6. }
prove i6 :*: i6 = - 1.
claim L1: HSNo (- 1).
{ exact HSNo_minus_HSNo 1 HSNo_1. }
apply OSNo_proj0proj1_split (i6 :*: i6) (- 1) Li6i6 (HSNo_OSNo (- 1) L1).
- prove p0 (i6 :*: i6) = p0 (- 1).
  rewrite HSNo_OSNo_proj0 (- 1) L1.
  prove p0 (i6 :*: i6) = - 1.
  rewrite mul_OSNo_proj0 i6 i6 OSNo_Octonion_i6 OSNo_Octonion_i6.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  rewrite mul_HSNo_0L 0 HSNo_0.
  prove 0 + - ((- j) ' * (- j)) = - 1.
  rewrite conj_minus_HSNo j HSNo_Quaternion_j.
  prove 0 + - ((- j ') * (- j)) = - 1.
  rewrite conj_HSNo_j.
  prove 0 + - ((- - j) * (- j)) = - 1.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  prove 0 + - (j * (- j)) = - 1.
  rewrite minus_mul_HSNo_distrR j j HSNo_Quaternion_j HSNo_Quaternion_j.
  prove 0 + - - (j * j) = - 1.
  rewrite Quaternion_j_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  prove 0 + - 1 = - 1.
  exact add_HSNo_0L (- 1) L1.
- prove p1 (i6 :*: i6) = p1 (- 1).
  rewrite HSNo_OSNo_proj1 (- 1) L1.
  prove p1 (i6 :*: i6) = 0.
  rewrite mul_OSNo_proj1 i6 i6 OSNo_Octonion_i6 OSNo_Octonion_i6.
  prove p1 i6 * p0 i6 + p1 i6 * p0 i6 ' = 0.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove (- j) * 0 + (- j) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i1_i2: i1 :*: i2 = i4.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li1i2: OSNo (i1 :*: i2).
{ exact OSNo_mul_OSNo i1 i2 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i2) i4 ?? ??.
- rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i1 i2 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove i * j + - (0 ' * 0) = k.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (i * j) (HSNo_mul_HSNo i j HSNo_Complex_i HSNo_Quaternion_j).
  exact Quaternion_i_j.
- rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i1 i2 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * i + 0 * j ' = 0.
  rewrite mul_HSNo_0L (j ') (HSNo_conj_HSNo j HSNo_Quaternion_j).
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i2_i1: i2 :*: i1 = :-: i4.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li2i1: OSNo (i2 :*: i1).
{ exact OSNo_mul_OSNo i2 i1 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i1) (:-: i4) ?? (OSNo_minus_OSNo i4 ??).
- rewrite minus_OSNo_proj0 i4 ??. rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i2 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove j * i + - (0 ' * 0) = - k.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (j * i) (HSNo_mul_HSNo j i HSNo_Quaternion_j HSNo_Complex_i).
  exact Quaternion_j_i.
- rewrite minus_OSNo_proj1 i4 ??. rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i2 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * j + 0 * i ' = - 0.
  rewrite mul_HSNo_0L (i ') (HSNo_conj_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i2_i4: i2 :*: i4 = i1.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li2i4: OSNo (i2 :*: i4).
{ exact OSNo_mul_OSNo i2 i4 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i4) i1 ?? ??.
- rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i2 i4 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove j * k + - (0 ' * 0) = i.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (j * k) (HSNo_mul_HSNo j k HSNo_Quaternion_j HSNo_Quaternion_k).
  exact Quaternion_j_k.
- rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i2 i4 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * j + 0 * k ' = 0.
  rewrite mul_HSNo_0L (k ') (HSNo_conj_HSNo k HSNo_Quaternion_k).
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i4_i2: i4 :*: i2 = :-: i1.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li4i2: OSNo (i4 :*: i2).
{ exact OSNo_mul_OSNo i4 i2 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i2) (:-: i1) ?? (OSNo_minus_OSNo i1 ??).
- rewrite minus_OSNo_proj0 i1 ??. rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i4 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove k * j + - (0 ' * 0) = - i.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (k * j) (HSNo_mul_HSNo k j HSNo_Quaternion_k HSNo_Quaternion_j).
  exact Quaternion_k_j.
- rewrite minus_OSNo_proj1 i1 ??. rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i4 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * k + 0 * j ' = - 0.
  rewrite mul_HSNo_0L (j ') (HSNo_conj_HSNo j HSNo_Quaternion_j).
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i4_i1: i4 :*: i1 = i2.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li4i1: OSNo (i4 :*: i1).
{ exact OSNo_mul_OSNo i4 i1 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i1) i2 ?? ??.
- rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i4 i1 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove k * i + - (0 ' * 0) = j.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (k * i) (HSNo_mul_HSNo k i HSNo_Quaternion_k HSNo_Complex_i).
  exact Quaternion_k_i.
- rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i4 i1 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * k + 0 * i ' = 0.
  rewrite mul_HSNo_0L (i ') (HSNo_conj_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i1_i4: i1 :*: i4 = :-: i2.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li1i4: OSNo (i1 :*: i4).
{ exact OSNo_mul_OSNo i1 i4 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i4) (:-: i2) ?? (OSNo_minus_OSNo i2 ??).
- rewrite minus_OSNo_proj0 i2 ??. rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i1 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove i * k + - (0 ' * 0) = - j.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 0 HSNo_0.
  rewrite minus_HSNo_0.
  rewrite add_HSNo_0R (i * k) (HSNo_mul_HSNo i k HSNo_Complex_i HSNo_Quaternion_k).
  exact Quaternion_i_k.
- rewrite minus_OSNo_proj1 i2 ??. rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i1 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * i + 0 * k ' = - 0.
  rewrite mul_HSNo_0L (k ') (HSNo_conj_HSNo k HSNo_Quaternion_k).
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i2_i3: i2 :*: i3 = i5.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li2i3: OSNo (i2 :*: i3).
{ exact OSNo_mul_OSNo i2 i3 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i3) i5 ?? ??.
- rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i2 i3 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove j * 0 + - ((- i) ' * 0) = 0.
  rewrite mul_HSNo_0R j HSNo_Quaternion_j.
  rewrite mul_HSNo_0R ((- i) ') (HSNo_conj_HSNo (- i) (HSNo_minus_HSNo i HSNo_Complex_i)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i2 i3 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove (- i) * j + 0 * 0 ' = (- k).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL i j HSNo_Complex_i HSNo_Quaternion_j.
  rewrite Quaternion_i_j.
  exact add_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem Octonion_i3_i2: i3 :*: i2 = :-: i5.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li3i2: OSNo (i3 :*: i2).
{ exact OSNo_mul_OSNo i3 i2 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i2) (:-: i5) ?? (OSNo_minus_OSNo i5 ??).
- rewrite minus_OSNo_proj0 i5 ??. rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i3 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * j + - (0 ' * (- i)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  rewrite mul_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i5 ??. rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i3 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * 0 + (- i) * j ' = - (- k).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_j.
  rewrite minus_mul_HSNo_distrL i (- j) HSNo_Complex_i (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_mul_HSNo_distrR i j HSNo_Complex_i HSNo_Quaternion_j.
  rewrite Quaternion_i_j.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0L k HSNo_Quaternion_k.
Qed.

Theorem Octonion_i3_i5: i3 :*: i5 = i2.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li3i5: OSNo (i3 :*: i5).
{ exact OSNo_mul_OSNo i3 i5 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i5) i2 ?? ??.
- rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i3 i5 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * 0 + - ((- k) ' * (- i)) = j.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo k HSNo_Quaternion_k.
  rewrite conj_HSNo_k.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  prove 0 + - (k * (- i)) = j.
  rewrite minus_mul_HSNo_distrR k i HSNo_Quaternion_k HSNo_Complex_i.
  rewrite Quaternion_k_i.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0L j HSNo_Quaternion_j.
- rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i3 i5 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove (- k) * 0 + (- i) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i5_i3: i5 :*: i3 = :-: i2.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li5i3: OSNo (i5 :*: i3).
{ exact OSNo_mul_OSNo i5 i3 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i3) (:-: i2) ?? (OSNo_minus_OSNo i2 ??).
- rewrite minus_OSNo_proj0 i2 ??. rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i5 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * 0 + - ((- i) ' * (- k)) = - j.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo i HSNo_Complex_i.
  rewrite conj_HSNo_i.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  prove 0 + - (i * (- k)) = - j.
  rewrite minus_mul_HSNo_distrR i k HSNo_Complex_i HSNo_Quaternion_k.
  rewrite Quaternion_i_k.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
- rewrite minus_OSNo_proj1 i2 ??. rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i5 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove (- i) * 0 + (- k) * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i5_i2: i5 :*: i2 = i3.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li5i2: OSNo (i5 :*: i2).
{ exact OSNo_mul_OSNo i5 i2 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i2) i3 ?? ??.
- rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i5 i2 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * j + - (0 ' * (- k)) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  rewrite mul_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i5 i2 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * 0 + (- k) * j ' = (- i).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_j.
  rewrite minus_mul_HSNo_distrR (- k) j (HSNo_minus_HSNo k HSNo_Quaternion_k) HSNo_Quaternion_j.
  rewrite minus_mul_HSNo_distrL k j HSNo_Quaternion_k HSNo_Quaternion_j.
  rewrite Quaternion_k_j.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
Qed.

Theorem Octonion_i2_i5: i2 :*: i5 = :-: i3.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li2i5: OSNo (i2 :*: i5).
{ exact OSNo_mul_OSNo i2 i5 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i5) (:-: i3) ?? (OSNo_minus_OSNo i3 ??).
- rewrite minus_OSNo_proj0 i3 ??. rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i2 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove j * 0 + - ((- k) ' * 0) = - 0.
  rewrite mul_HSNo_0R j HSNo_Quaternion_j.
  rewrite mul_HSNo_0R ((- k) ') (HSNo_conj_HSNo (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i3 ??. rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i2 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove (- k) * j + 0 * 0 ' = - (- i).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL k j HSNo_Quaternion_k HSNo_Quaternion_j.
  rewrite Quaternion_k_j.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0R i HSNo_Complex_i.
Qed.

Theorem Octonion_i3_i4: i3 :*: i4 = i6.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li3i4: OSNo (i3 :*: i4).
{ exact OSNo_mul_OSNo i3 i4 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i4) i6 ?? ??.
- rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i3 i4 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * k + - (0 ' * (- i)) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  rewrite mul_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i3 i4 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * 0 + (- i) * k ' = (- j).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_k.
  rewrite minus_mul_HSNo_distrR (- i) k (HSNo_minus_HSNo i HSNo_Complex_i) HSNo_Quaternion_k.
  rewrite minus_mul_HSNo_distrL i k HSNo_Complex_i HSNo_Quaternion_k.
  rewrite Quaternion_i_k.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
Qed.

Theorem Octonion_i4_i3: i4 :*: i3 = :-: i6.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li4i3: OSNo (i4 :*: i3).
{ exact OSNo_mul_OSNo i4 i3 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i3) (:-: i6) ?? (OSNo_minus_OSNo i6 ??).
- rewrite minus_OSNo_proj0 i6 ??. rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i4 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove k * 0 + - ((- i) ' * 0) = - 0.
  rewrite mul_HSNo_0R k HSNo_Quaternion_k.
  rewrite mul_HSNo_0R ((- i) ') (HSNo_conj_HSNo (- i) (HSNo_minus_HSNo i HSNo_Complex_i)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i6 ??. rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i4 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove (- i) * k + 0 * 0 ' = - (- j).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL i k HSNo_Complex_i HSNo_Quaternion_k.
  prove - i * k + 0 = - - j.
  rewrite Quaternion_i_k.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0R j HSNo_Quaternion_j.
Qed.

Theorem Octonion_i4_i6: i4 :*: i6 = i3.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li4i6: OSNo (i4 :*: i6).
{ exact OSNo_mul_OSNo i4 i6 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i6) i3 ?? ??.
- rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i4 i6 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove k * 0 + - ((- j) ' * 0) = 0.
  rewrite mul_HSNo_0R k HSNo_Quaternion_k.
  rewrite mul_HSNo_0R ((- j) ') (HSNo_conj_HSNo (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i4 i6 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove (- j) * k + 0 * 0 ' = (- i).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL j k HSNo_Quaternion_j HSNo_Quaternion_k.
  rewrite Quaternion_j_k.
  exact add_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
Qed.

Theorem Octonion_i6_i4: i6 :*: i4 = :-: i3.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li6i4: OSNo (i6 :*: i4).
{ exact OSNo_mul_OSNo i6 i4 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i4) (:-: i3) ?? (OSNo_minus_OSNo i3 ??).
- rewrite minus_OSNo_proj0 i3 ??. rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i6 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * k + - (0 ' * (- j)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  rewrite mul_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i3 ??. rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i6 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * 0 + (- j) * k ' = - (- i).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_k.
  rewrite minus_mul_HSNo_distrR (- j) k (HSNo_minus_HSNo j HSNo_Quaternion_j) HSNo_Quaternion_k.
  rewrite minus_mul_HSNo_distrL j k HSNo_Quaternion_j HSNo_Quaternion_k.
  rewrite Quaternion_j_k.
  prove 0 + - - i = - - i.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0L i HSNo_Complex_i.
Qed.

Theorem Octonion_i6_i3: i6 :*: i3 = i4.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li6i3: OSNo (i6 :*: i3).
{ exact OSNo_mul_OSNo i6 i3 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i3) i4 ?? ??.
- rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i6 i3 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * 0 + - ((- i) ' * (- j)) = k.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo i HSNo_Complex_i.
  rewrite conj_HSNo_i.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  prove 0 + - (i * (- j)) = k.
  rewrite minus_mul_HSNo_distrR i j HSNo_Complex_i HSNo_Quaternion_j.
  rewrite Quaternion_i_j.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0L k HSNo_Quaternion_k.
- rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i6 i3 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove (- i) * 0 + (- j) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i3_i6: i3 :*: i6 = :-: i4.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li3i6: OSNo (i3 :*: i6).
{ exact OSNo_mul_OSNo i3 i6 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i6) (:-: i4) ?? (OSNo_minus_OSNo i4 ??).
- rewrite minus_OSNo_proj0 i4 ??. rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i3 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * 0 + - ((- j) ' * (- i)) = - k.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo j HSNo_Quaternion_j.
  rewrite conj_HSNo_j.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  prove 0 + - (j * (- i)) = - k.
  rewrite minus_mul_HSNo_distrR j i HSNo_Quaternion_j HSNo_Complex_i.
  rewrite Quaternion_j_i.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
- rewrite minus_OSNo_proj1 i4 ??. rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i3 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove (- j) * 0 + (- i) * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i4_i5: i4 :*: i5 = i0.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li4i5: OSNo (i4 :*: i5).
{ exact OSNo_mul_OSNo i4 i5 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i5) i0 ?? ??.
- rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i4 i5 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove k * 0 + - ((- k) ' * 0) = 0.
  rewrite mul_HSNo_0R k HSNo_Quaternion_k.
  rewrite mul_HSNo_0R ((- k) ') (HSNo_conj_HSNo (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i4 i5 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove (- k) * k + 0 * 0 ' = 1.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL k k HSNo_Quaternion_k HSNo_Quaternion_k.
  rewrite Quaternion_k_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0R 1 HSNo_1.
Qed.

Theorem Octonion_i5_i4: i5 :*: i4 = :-: i0.
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li5i4: OSNo (i5 :*: i4).
{ exact OSNo_mul_OSNo i5 i4 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i4) (:-: i0) ?? (OSNo_minus_OSNo i0 ??).
- rewrite minus_OSNo_proj0 i0 ??. rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i5 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * k + - (0 ' * (- k)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  rewrite mul_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i0 ??. rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i5 i4 ?? ??.
  rewrite OSNo_p0_k. rewrite OSNo_p1_k. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * 0 + (- k) * k ' = - 1.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_k.
  prove 0 + (- k) * (- k) = - 1.
  rewrite minus_mul_HSNo_distrL k (- k) HSNo_Quaternion_k (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite minus_mul_HSNo_distrR k k HSNo_Quaternion_k HSNo_Quaternion_k.
  prove 0 + - - k * k = - 1.
  rewrite Quaternion_k_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0L (- 1) (HSNo_minus_HSNo 1 HSNo_1).
Qed.

Theorem Octonion_i5_i0: i5 :*: i0 = i4.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li5i0: OSNo (i5 :*: i0).
{ exact OSNo_mul_OSNo i5 i0 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i0) i4 ?? ??.
- rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i5 i0 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - (1 ' * (- k)) = k.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_id_SNo 1 SNo_1.
  rewrite mul_HSNo_1L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  prove 0 + - - k = k.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0L k HSNo_Quaternion_k.
- rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i5 i0 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 1 * 0 + (- k) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite mul_HSNo_0R 1 HSNo_1.
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i0_i5: i0 :*: i5 = :-: i4.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li0i5: OSNo (i0 :*: i5).
{ exact OSNo_mul_OSNo i0 i5 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i5) (:-: i4) ?? (OSNo_minus_OSNo i4 ??).
- rewrite minus_OSNo_proj0 i4 ??. rewrite OSNo_p0_k.
  rewrite mul_OSNo_proj0 i0 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - ((- k) ' * 1) = - k.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo k HSNo_Quaternion_k.
  rewrite conj_HSNo_k.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  prove 0 + - (k * 1) = - k.
  rewrite mul_HSNo_1R k HSNo_Quaternion_k.
  exact add_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
- rewrite minus_OSNo_proj1 i4 ??. rewrite OSNo_p1_k.
  rewrite mul_OSNo_proj1 i0 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove (- k) * 0 + 1 * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i0_i4: i0 :*: i4 = i5.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li0i4: OSNo (i0 :*: i4).
{ exact OSNo_mul_OSNo i0 i4 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i4) i5 ?? ??.
- rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i0 i4 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * k + - (0 ' * 1) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L k HSNo_Quaternion_k.
  rewrite mul_HSNo_0L 1 HSNo_1.
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i0 i4 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 0 * 0 + 1 * k ' = (- k).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite mul_HSNo_1L (k ') (HSNo_conj_HSNo k HSNo_Quaternion_k).
  prove 0 + k ' = (- k).
  rewrite conj_HSNo_k.
  prove 0 + - k = (- k).
  exact add_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem Octonion_i4_i0: i4 :*: i0 = :-: i5.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li4: OSNo i4.
{ exact OSNo_Quaternion_k. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li4i0: OSNo (i4 :*: i0).
{ exact OSNo_mul_OSNo i4 i0 ?? ??. }
apply OSNo_proj0proj1_split (i4 :*: i0) (:-: i5) ?? (OSNo_minus_OSNo i5 ??).
- rewrite minus_OSNo_proj0 i5 ??. rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i4 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove k * 0 + - (1 ' * 0) = - 0.
  rewrite mul_HSNo_0R k HSNo_Quaternion_k.
  rewrite mul_HSNo_0R (1 ') (HSNo_conj_HSNo 1 HSNo_1).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i5 ??. rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i4 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_k. rewrite OSNo_p1_k.
  prove 1 * k + 0 * 0 ' = - (- k).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite mul_HSNo_1L k HSNo_Quaternion_k.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0R k HSNo_Quaternion_k.
Qed.

Theorem Octonion_i5_i6: i5 :*: i6 = i1.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li5i6: OSNo (i5 :*: i6).
{ exact OSNo_mul_OSNo i5 i6 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i6) i1 ?? ??.
- rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i5 i6 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * 0 + - ((- j) ' * (- k)) = i.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo j HSNo_Quaternion_j.
  rewrite conj_HSNo_j.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  prove 0 + - (j * (- k)) = i.
  rewrite minus_mul_HSNo_distrR j k HSNo_Quaternion_j HSNo_Quaternion_k.
  rewrite Quaternion_j_k.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0L i HSNo_Complex_i.
- rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i5 i6 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove (- j) * 0 + (- k) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i6_i5: i6 :*: i5 = :-: i1.
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li6i5: OSNo (i6 :*: i5).
{ exact OSNo_mul_OSNo i6 i5 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i5) (:-: i1) ?? (OSNo_minus_OSNo i1 ??).
- rewrite minus_OSNo_proj0 i1 ??. rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i6 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * 0 + - ((- k) ' * (- j)) = - i.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo k HSNo_Quaternion_k.
  rewrite conj_HSNo_k.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  prove 0 + - (k * (- j)) = - i.
  rewrite minus_mul_HSNo_distrR k j HSNo_Quaternion_k HSNo_Quaternion_j.
  rewrite Quaternion_k_j.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
- rewrite minus_OSNo_proj1 i1 ??. rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i6 i5 ?? ??.
  rewrite OSNo_p0_i5. rewrite OSNo_p1_i5. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove (- k) * 0 + (- j) * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i6_i1: i6 :*: i1 = i5.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li6i1: OSNo (i6 :*: i1).
{ exact OSNo_mul_OSNo i6 i1 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i1) i5 ?? ??.
- rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i6 i1 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * i + - (0 ' * (- j)) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  rewrite mul_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i6 i1 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * 0 + (- j) * i ' = (- k).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_i.
  rewrite minus_mul_HSNo_distrL j (- i) HSNo_Quaternion_j (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_mul_HSNo_distrR j i HSNo_Quaternion_j HSNo_Complex_i.
  rewrite Quaternion_j_i.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  exact add_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
Qed.

Theorem Octonion_i1_i6: i1 :*: i6 = :-: i5.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li1i6: OSNo (i1 :*: i6).
{ exact OSNo_mul_OSNo i1 i6 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i6) (:-: i5) ?? (OSNo_minus_OSNo i5 ??).
- rewrite minus_OSNo_proj0 i5 ??. rewrite OSNo_p0_i5.
  rewrite mul_OSNo_proj0 i1 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove i * 0 + - ((- j) ' * 0) = - 0.
  rewrite mul_HSNo_0R i HSNo_Complex_i.
  rewrite mul_HSNo_0R ((- j) ') (HSNo_conj_HSNo (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i5 ??. rewrite OSNo_p1_i5.
  rewrite mul_OSNo_proj1 i1 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove (- j) * i + 0 * 0 ' = - (- k).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL j i HSNo_Quaternion_j HSNo_Complex_i.
  rewrite Quaternion_j_i.
  rewrite minus_HSNo_invol k HSNo_Quaternion_k.
  prove k + 0 = k.
  exact add_HSNo_0R k HSNo_Quaternion_k.
Qed.

Theorem Octonion_i1_i5: i1 :*: i5 = i6.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li1i5: OSNo (i1 :*: i5).
{ exact OSNo_mul_OSNo i1 i5 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i5) i6 ?? ??.
- rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i1 i5 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove i * 0 + - ((- k) ' * 0) = 0.
  rewrite mul_HSNo_0R i HSNo_Complex_i.
  rewrite mul_HSNo_0R ((- k) ') (HSNo_conj_HSNo (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i1 i5 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove (- k) * i + 0 * 0 ' = (- j).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL k i HSNo_Quaternion_k HSNo_Complex_i.
  rewrite Quaternion_k_i.
  exact add_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
Qed.

Theorem Octonion_i5_i1: i5 :*: i1 = :-: i6.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li5: OSNo i5.
{ exact OSNo_Octonion_i5. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li5i1: OSNo (i5 :*: i1).
{ exact OSNo_mul_OSNo i5 i1 ?? ??. }
apply OSNo_proj0proj1_split (i5 :*: i1) (:-: i6) ?? (OSNo_minus_OSNo i6 ??).
- rewrite minus_OSNo_proj0 i6 ??. rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i5 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * i + - (0 ' * (- k)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  rewrite mul_HSNo_0L (- k) (HSNo_minus_HSNo k HSNo_Quaternion_k).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i6 ??. rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i5 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i5. rewrite OSNo_p1_i5.
  prove 0 * 0 + (- k) * i ' = - (- j).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_i.
  rewrite minus_mul_HSNo_distrL k (- i) HSNo_Quaternion_k (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_mul_HSNo_distrR k i HSNo_Quaternion_k HSNo_Complex_i.
  rewrite Quaternion_k_i.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0L j HSNo_Quaternion_j.
Qed.

Theorem Octonion_i6_i0: i6 :*: i0 = i2.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li6i0: OSNo (i6 :*: i0).
{ exact OSNo_mul_OSNo i6 i0 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i0) i2 ?? ??.
- rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i6 i0 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - (1 ' * (- j)) = j.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_id_SNo 1 SNo_1.
  rewrite mul_HSNo_1L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  exact add_HSNo_0L j HSNo_Quaternion_j.
- rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i6 i0 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 1 * 0 + (- j) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i0_i6: i0 :*: i6 = :-: i2.
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li0i6: OSNo (i0 :*: i6).
{ exact OSNo_mul_OSNo i0 i6 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i6) (:-: i2) ?? (OSNo_minus_OSNo i2 ??).
- rewrite minus_OSNo_proj0 i2 ??. rewrite OSNo_p0_j.
  rewrite mul_OSNo_proj0 i0 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - ((- j) ' * 1) = - j.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo j HSNo_Quaternion_j.
  rewrite conj_HSNo_j.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  prove 0 + - (j * 1) = - j.
  rewrite mul_HSNo_1R j HSNo_Quaternion_j.
  exact add_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
- rewrite minus_OSNo_proj1 i2 ??. rewrite OSNo_p1_j.
  rewrite mul_OSNo_proj1 i0 i6 ?? ??.
  rewrite OSNo_p0_i6. rewrite OSNo_p1_i6. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove (- j) * 0 + 1 * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i0_i2: i0 :*: i2 = i6.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li0i2: OSNo (i0 :*: i2).
{ exact OSNo_mul_OSNo i0 i2 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i2) i6 ?? ??.
- rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i0 i2 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * j + - (0 ' * 1) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 1 HSNo_1.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i0 i2 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 0 * 0 + 1 * j ' = (- j).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite mul_HSNo_1L (j ') (HSNo_conj_HSNo j HSNo_Quaternion_j).
  rewrite add_HSNo_0L (j ') (HSNo_conj_HSNo j HSNo_Quaternion_j).
  prove j ' = - j.
  exact conj_HSNo_j.
Qed.

Theorem Octonion_i2_i0: i2 :*: i0 = :-: i6.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li2i0: OSNo (i2 :*: i0).
{ exact OSNo_mul_OSNo i2 i0 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i0) (:-: i6) ?? (OSNo_minus_OSNo i6 ??).
- rewrite minus_OSNo_proj0 i6 ??. rewrite OSNo_p0_i6.
  rewrite mul_OSNo_proj0 i2 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove j * 0 + - (1 ' * 0) = - 0.
  rewrite mul_HSNo_0R j HSNo_Quaternion_j.
  rewrite mul_HSNo_0R (1 ') (HSNo_conj_HSNo 1 HSNo_1).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i6 ??. rewrite OSNo_p1_i6.
  rewrite mul_OSNo_proj1 i2 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_j. rewrite OSNo_p1_j.
  prove 1 * j + 0 * 0 ' = - (- j).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_HSNo_invol j HSNo_Quaternion_j.
  rewrite mul_HSNo_1L j HSNo_Quaternion_j.
  exact add_HSNo_0R j HSNo_Quaternion_j.
Qed.

Theorem Octonion_i2_i6: i2 :*: i6 = i0.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li2i6: OSNo (i2 :*: i6).
{ exact OSNo_mul_OSNo i2 i6 ?? ??. }
apply OSNo_proj0proj1_split (i2 :*: i6) i0 ?? ??.
- rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i2 i6 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove j * 0 + - ((- j) ' * 0) = 0.
  rewrite mul_HSNo_0R j HSNo_Quaternion_j.
  rewrite mul_HSNo_0R ((- j) ') (HSNo_conj_HSNo (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i2 i6 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove (- j) * j + 0 * 0 ' = 1.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL j j HSNo_Quaternion_j HSNo_Quaternion_j.
  rewrite Quaternion_j_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0R 1 HSNo_1.
Qed.

Theorem Octonion_i6_i2: i6 :*: i2 = :-: i0.
claim Li2: OSNo i2.
{ exact OSNo_Quaternion_j. }
claim Li6: OSNo i6.
{ exact OSNo_Octonion_i6. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li6i2: OSNo (i6 :*: i2).
{ exact OSNo_mul_OSNo i6 i2 ?? ??. }
apply OSNo_proj0proj1_split (i6 :*: i2) (:-: i0) ?? (OSNo_minus_OSNo i0 ??).
- rewrite minus_OSNo_proj0 i0 ??. rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i6 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * j + - (0 ' * (- j)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L j HSNo_Quaternion_j.
  rewrite mul_HSNo_0L (- j) (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i0 ??. rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i6 i2 ?? ??.
  rewrite OSNo_p0_j. rewrite OSNo_p1_j. rewrite OSNo_p0_i6. rewrite OSNo_p1_i6.
  prove 0 * 0 + (- j) * j ' = - 1.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_j.
  rewrite minus_mul_HSNo_distrL j (- j) HSNo_Quaternion_j (HSNo_minus_HSNo j HSNo_Quaternion_j).
  rewrite minus_mul_HSNo_distrR j j HSNo_Quaternion_j HSNo_Quaternion_j.
  rewrite Quaternion_j_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0L (- 1) (HSNo_minus_HSNo 1 HSNo_1).
Qed.

Theorem Octonion_i0_i1: i0 :*: i1 = i3.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li0i1: OSNo (i0 :*: i1).
{ exact OSNo_mul_OSNo i0 i1 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i1) i3 ?? ??.
- rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i0 i1 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * i + - (0 ' * 1) = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 1 HSNo_1.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i0 i1 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 0 * 0 + 1 * i ' = (- i).
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite mul_HSNo_1L (i ') (HSNo_conj_HSNo i HSNo_Complex_i).
  rewrite add_HSNo_0L (i ') (HSNo_conj_HSNo i HSNo_Complex_i).
  exact conj_HSNo_i.
Qed.

Theorem Octonion_i1_i0: i1 :*: i0 = :-: i3.
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li1i0: OSNo (i1 :*: i0).
{ exact OSNo_mul_OSNo i1 i0 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i0) (:-: i3) ?? (OSNo_minus_OSNo i3 ??).
- rewrite minus_OSNo_proj0 i3 ??. rewrite OSNo_p0_i3.
  rewrite mul_OSNo_proj0 i1 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove i * 0 + - (1 ' * 0) = - 0.
  rewrite mul_HSNo_0R i HSNo_Complex_i.
  rewrite mul_HSNo_0R (1 ') (HSNo_conj_HSNo 1 HSNo_1).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i3 ??. rewrite OSNo_p1_i3.
  rewrite mul_OSNo_proj1 i1 i0 ?? ??.
  rewrite OSNo_p0_i0. rewrite OSNo_p1_i0. rewrite OSNo_p0_i. rewrite OSNo_p1_i.
  prove 1 * i + 0 * 0 ' = - (- i).
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  rewrite mul_HSNo_1L i HSNo_Complex_i.
  exact add_HSNo_0R i HSNo_Complex_i.
Qed.

Theorem Octonion_i1_i3: i1 :*: i3 = i0.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li1i3: OSNo (i1 :*: i3).
{ exact OSNo_mul_OSNo i1 i3 ?? ??. }
apply OSNo_proj0proj1_split (i1 :*: i3) i0 ?? ??.
- rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i1 i3 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove i * 0 + - ((- i) ' * 0) = 0.
  rewrite mul_HSNo_0R i HSNo_Complex_i.
  rewrite mul_HSNo_0R ((- i) ') (HSNo_conj_HSNo (- i) (HSNo_minus_HSNo i HSNo_Complex_i)).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i1 i3 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove (- i) * i + 0 * 0 ' = 1.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite minus_mul_HSNo_distrL i i HSNo_Complex_i HSNo_Complex_i.
  prove - i * i + 0 = 1.
  rewrite Quaternion_i_sqr.
  prove - - 1 + 0 = 1.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0R 1 HSNo_1.
Qed.

Theorem Octonion_i3_i1: i3 :*: i1 = :-: i0.
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li3i1: OSNo (i3 :*: i1).
{ exact OSNo_mul_OSNo i3 i1 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i1) (:-: i0) ?? (OSNo_minus_OSNo i0 ??).
- rewrite minus_OSNo_proj0 i0 ??. rewrite OSNo_p0_i0.
  rewrite mul_OSNo_proj0 i3 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * i + - (0 ' * (- i)) = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0L i HSNo_Complex_i.
  rewrite mul_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_HSNo_0.
  exact add_HSNo_0L 0 HSNo_0.
- rewrite minus_OSNo_proj1 i0 ??. rewrite OSNo_p1_i0.
  rewrite mul_OSNo_proj1 i3 i1 ?? ??.
  rewrite OSNo_p0_i. rewrite OSNo_p1_i. rewrite OSNo_p0_i3. rewrite OSNo_p1_i3.
  prove 0 * 0 + (- i) * i ' = - 1.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_i.
  rewrite minus_mul_HSNo_distrL i (- i) HSNo_Complex_i (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_mul_HSNo_distrR i i HSNo_Complex_i HSNo_Complex_i.
  rewrite Quaternion_i_sqr.
  rewrite minus_HSNo_invol 1 HSNo_1.
  exact add_HSNo_0L (- 1) (HSNo_minus_HSNo 1 HSNo_1).
Qed.

Theorem Octonion_i3_i0: i3 :*: i0 = i1.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li3i0: OSNo (i3 :*: i0).
{ exact OSNo_mul_OSNo i3 i0 ?? ??. }
apply OSNo_proj0proj1_split (i3 :*: i0) i1 ?? ??.
- rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i3 i0 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - (1 ' * (- i)) = i.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_HSNo_id_SNo 1 SNo_1.
  rewrite mul_HSNo_1L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  exact add_HSNo_0L i HSNo_Complex_i.
- rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i3 i0 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 1 * 0 + (- i) * 0 ' = 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

Theorem Octonion_i0_i3: i0 :*: i3 = :-: i1.
claim Li3: OSNo i3.
{ exact OSNo_Octonion_i3. }
claim Li0: OSNo i0.
{ exact OSNo_Octonion_i0. }
claim Li1: OSNo i1.
{ exact OSNo_Complex_i. }
claim Li0i3: OSNo (i0 :*: i3).
{ exact OSNo_mul_OSNo i0 i3 ?? ??. }
apply OSNo_proj0proj1_split (i0 :*: i3) (:-: i1) ?? (OSNo_minus_OSNo i1 ??).
- rewrite minus_OSNo_proj0 i1 ??. rewrite OSNo_p0_i.
  rewrite mul_OSNo_proj0 i0 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove 0 * 0 + - ((- i) ' * 1) = - i.
  rewrite mul_HSNo_0L 0 HSNo_0.
  rewrite conj_minus_HSNo i HSNo_Complex_i.
  rewrite conj_HSNo_i.
  rewrite minus_HSNo_invol i HSNo_Complex_i.
  prove 0 + - (i * 1) = - i.
  rewrite mul_HSNo_1R i HSNo_Complex_i.
  exact add_HSNo_0L (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
- rewrite minus_OSNo_proj1 i1 ??. rewrite OSNo_p1_i.
  rewrite mul_OSNo_proj1 i0 i3 ?? ??.
  rewrite OSNo_p0_i3. rewrite OSNo_p1_i3. rewrite OSNo_p0_i0. rewrite OSNo_p1_i0.
  prove (- i) * 0 + 1 * 0 ' = - 0.
  rewrite conj_HSNo_id_SNo 0 SNo_0.
  rewrite mul_HSNo_0R 1 HSNo_1.
  rewrite minus_HSNo_0.
  rewrite mul_HSNo_0R (- i) (HSNo_minus_HSNo i HSNo_Complex_i).
  exact add_HSNo_0L 0 HSNo_0.
Qed.

End SurOctonions.

Section Octonions.

Prefix - 358 := minus_OSNo.
Infix + 360 right := add_OSNo.
Infix * 355 right := mul_OSNo.

Let i0 := Octonion_i0.
Let i1 := Complex_i.
Let i2 := Quaternion_j.
Let i3 := Octonion_i3.
Let i4 := Quaternion_k.
Let i5 := Octonion_i5.
Let i6 := Octonion_i6.
Let i := Complex_i.
Let j := Quaternion_j.
Let k := Quaternion_k.
Let p0 : set -> set := OSNo_proj0.
Let p1 : set -> set := OSNo_proj1.
Let pa : set -> set -> set := HSNo_pair.

Definition octonion : set := {pa (u 0) (u 1)|u :e quaternion :*: quaternion}.

Theorem octonion_I : forall x y :e quaternion, pa x y :e octonion.
let x. assume Hx. let y. assume Hy.
prove pa x y :e octonion.
rewrite <- tuple_2_0_eq x y.
rewrite <- tuple_2_1_eq x y at 2.
prove pa ((x,y) 0) ((x,y) 1) :e octonion.
apply ReplI (quaternion :*: quaternion) (fun u => pa (u 0) (u 1)).
prove (x,y) :e quaternion :*: quaternion.
exact tuple_2_setprod quaternion quaternion x Hx y Hy.
Qed.

Theorem octonion_E : forall z :e octonion, forall p:prop,
   (forall x y :e quaternion, z = pa x y -> p)
 -> p.
let z. assume Hz. let p. assume Hp.
apply ReplE_impred (quaternion :*: quaternion) (fun u => pa (u 0) (u 1)) z Hz.
let u.
assume Hu: u :e quaternion :*: quaternion.
assume Hzu: z = pa (u 0) (u 1).
exact Hp (u 0) (ap0_Sigma quaternion (fun _ => quaternion) u Hu)
         (u 1) (ap1_Sigma quaternion (fun _ => quaternion) u Hu)
         Hzu.
Qed.

Theorem octonion_OSNo: forall z :e octonion, OSNo z.
let z. assume Hz.
apply octonion_E z Hz.
let x. assume Hx. let y. assume Hy.
assume Hzxy: z = pa x y.
prove OSNo z.
rewrite Hzxy. apply OSNo_I.
- exact quaternion_HSNo x Hx.
- exact quaternion_HSNo y Hy.
Qed.

Theorem quaternion_octonion: quaternion c= octonion.
let x. assume Hx: x :e quaternion.
prove x :e octonion.
rewrite <- HSNo_pair_0 x.
prove pa x 0 :e octonion.
apply octonion_I.
- exact Hx.
- exact quaternion_0.
Qed.

Theorem octonion_0 : 0 :e octonion.
exact quaternion_octonion 0 quaternion_0.
Qed.

Theorem octonion_1 : 1 :e octonion.
exact quaternion_octonion 1 quaternion_1.
Qed.

Theorem octonion_i : i :e octonion.
exact quaternion_octonion i quaternion_i.
Qed.

Theorem octonion_j : j :e octonion.
exact quaternion_octonion j quaternion_j.
Qed.

Theorem octonion_k : k :e octonion.
exact quaternion_octonion k quaternion_k.
Qed.

Theorem octonion_i0 : i0 :e octonion.
prove pa 0 1 :e octonion.
apply octonion_I.
- exact quaternion_0.
- exact quaternion_1.
Qed.

Theorem octonion_i3 : i3 :e octonion.
prove pa 0 (minus_HSNo i) :e octonion.
apply octonion_I.
- exact quaternion_0.
- apply quaternion_minus_HSNo. exact quaternion_i.
Qed.

Theorem octonion_i5 : i5 :e octonion.
prove pa 0 (minus_HSNo k) :e octonion.
apply octonion_I.
- exact quaternion_0.
- apply quaternion_minus_HSNo. exact quaternion_k.
Qed.

Theorem octonion_i6 : i6 :e octonion.
prove pa 0 (minus_HSNo j) :e octonion.
apply octonion_I.
- exact quaternion_0.
- apply quaternion_minus_HSNo. exact quaternion_j.
Qed.

Theorem octonion_p0_eq: forall x y :e quaternion, p0 (pa x y) = x.
let x. assume Hx. let y. assume Hy.
exact OSNo_proj0_2 x y (quaternion_HSNo x Hx) (quaternion_HSNo y Hy).
Qed.

Theorem octonion_p1_eq: forall x y :e quaternion, p1 (pa x y) = y.
let x. assume Hx. let y. assume Hy.
exact OSNo_proj1_2 x y (quaternion_HSNo x Hx) (quaternion_HSNo y Hy).
Qed.

Theorem octonion_p0_quaternion: forall z :e octonion, p0 z :e quaternion.
let z. assume Hz. apply octonion_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove p0 (pa x y) :e quaternion.
rewrite octonion_p0_eq x Hx y Hy.
prove x :e quaternion. exact Hx.
Qed.

Theorem octonion_p1_quaternion: forall z :e octonion, p1 z :e quaternion.
let z. assume Hz. apply octonion_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove p1 (pa x y) :e quaternion.
rewrite octonion_p1_eq x Hx y Hy.
prove y :e quaternion. exact Hy.
Qed.

Theorem octonion_proj0proj1_split: forall z w :e octonion, p0 z = p0 w -> p1 z = p1 w -> z = w.
let z. assume Hz. let w. assume Hw.
exact OSNo_proj0proj1_split z w (octonion_OSNo z Hz) (octonion_OSNo w Hw).
Qed.

Theorem octonion_minus_OSNo : forall z :e octonion, - z :e octonion.
let z. assume Hz.
prove pa (minus_HSNo (p0 z)) (minus_HSNo (p1 z)) :e octonion.
apply octonion_I.
- apply quaternion_minus_HSNo. exact octonion_p0_quaternion z Hz.
- apply quaternion_minus_HSNo. exact octonion_p1_quaternion z Hz.
Qed.

Theorem octonion_conj_OSNo : forall z :e octonion, conj_OSNo z :e octonion.
let z. assume Hz.
prove pa (conj_HSNo (p0 z)) (minus_HSNo (p1 z)) :e octonion.
apply octonion_I.
- apply quaternion_conj_HSNo. exact octonion_p0_quaternion z Hz.
- apply quaternion_minus_HSNo. exact octonion_p1_quaternion z Hz.
Qed.

Theorem octonion_add_OSNo : forall z w :e octonion, z + w :e octonion.
let z. assume Hz. let w. assume Hw.
prove pa (add_HSNo (p0 z) (p0 w)) (add_HSNo (p1 z) (p1 w)) :e octonion.
apply octonion_I.
- apply quaternion_add_HSNo.
  + exact octonion_p0_quaternion z Hz.
  + exact octonion_p0_quaternion w Hw.
- apply quaternion_add_HSNo.
  + exact octonion_p1_quaternion z Hz.
  + exact octonion_p1_quaternion w Hw.
Qed.

Theorem octonion_mul_OSNo : forall z w :e octonion, z * w :e octonion.
let z. assume Hz. let w. assume Hw.
prove pa (add_HSNo (mul_HSNo (p0 z) (p0 w)) (minus_HSNo (mul_HSNo (conj_HSNo (p1 w)) (p1 z))))
         (add_HSNo (mul_HSNo (p1 w) (p0 z)) (mul_HSNo (p1 z) (conj_HSNo (p0 w))))
       :e octonion.
claim Lz0: p0 z :e quaternion.
{ exact octonion_p0_quaternion z Hz. }
claim Lz1: p1 z :e quaternion.
{ exact octonion_p1_quaternion z Hz. }
claim Lw0: p0 w :e quaternion.
{ exact octonion_p0_quaternion w Hw. }
claim Lw1: p1 w :e quaternion.
{ exact octonion_p1_quaternion w Hw. }
apply octonion_I.
- apply quaternion_add_HSNo.
  + apply quaternion_mul_HSNo.
    * exact ??.
    * exact ??.
  + apply quaternion_minus_HSNo. apply quaternion_mul_HSNo.
    * apply quaternion_conj_HSNo. exact ??.
    * exact ??.
- apply quaternion_add_HSNo.
  + apply quaternion_mul_HSNo.
    * exact ??.
    * exact ??.
  + apply quaternion_mul_HSNo.
    * exact ??.
    * apply quaternion_conj_HSNo. exact ??.
Qed.

Theorem quaternion_p0_eq': forall x :e quaternion, p0 x = x.
let x. assume Hx.
rewrite <- HSNo_pair_0 x at 1.
exact octonion_p0_eq x Hx 0 quaternion_0.
Qed.

Theorem quaternion_p1_eq': forall x :e quaternion, p1 x = 0.
let x. assume Hx.
rewrite <- HSNo_pair_0 x.
exact octonion_p1_eq x Hx 0 quaternion_0.
Qed.

End Octonions.

Opaque HSNo_pair.
Opaque OSNo.
Opaque OSNo_proj0.
Opaque OSNo_proj1.
Opaque OSNoLev.
Opaque minus_OSNo.
Opaque conj_OSNo.
Opaque add_OSNo.
Opaque mul_OSNo.
Opaque exp_OSNo_nat.
Opaque Octonion_i0.
Opaque Octonion_i3.
Opaque Octonion_i5.
Opaque Octonion_i6.
Opaque octonion.
