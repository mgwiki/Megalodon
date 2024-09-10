(** Part 12 **)
Section Tags.

Variable tagn:set.
Hypothesis tagn_nat: nat_p tagn.
Hypothesis tagn_1: 1 :e tagn.

Theorem not_TransSet_Sing_tagn : ~TransSet {tagn}.
assume H1: TransSet {tagn}.
claim L1: 0 :e {tagn}.
{ apply H1 tagn (SingI tagn).
  prove 0 :e tagn.
  exact nat_trans tagn tagn_nat 1 tagn_1 0 In_0_1.
}
apply In_no2cycle 0 1 In_0_1.
prove 1 :e 0.
rewrite SingE tagn 0 L1 at 2.
prove 1 :e tagn.
exact tagn_1.
Qed.

Theorem not_ordinal_Sing_tagn : ~ordinal {tagn}.
assume H1. apply H1. assume H2 _. exact not_TransSet_Sing_tagn H2.
Qed.

End Tags.

Section ExtendedSNo.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Definition ExtendedSNoElt_:set -> set -> prop := fun n x => forall v :e Union x, ordinal v \/ exists i :e n, v = {i}.

Theorem extension_SNoElt_mon: forall M N, M c= N -> forall x, ExtendedSNoElt_ M x -> ExtendedSNoElt_ N x.
let M N. assume HMN. let x. assume Hx.
let v. assume Hv.
apply Hx v Hv.
- assume H1: ordinal v.
  prove ordinal v \/ exists i :e N, v = {i}.
  apply orIL. exact H1.
- assume H. apply H.
  let i. assume H. apply H.
  assume Hi: i :e M.
  assume H1: v = {i}.
  prove ordinal v \/ exists i :e N, v = {i}.
  apply orIR. witness i. apply andI.
  + prove i :e N. exact HMN i Hi.
  + exact H1.
Qed.

Theorem Sing_nat_fresh_extension: forall n, nat_p n -> 1 :e n -> forall x, ExtendedSNoElt_ n x -> forall u :e x, {n} /:e u.
let n.
assume Hn.
assume Hn1: 1 :e n.
let x. assume Hx.
let u. assume Hu.
assume H1: {n} :e u.
claim L1: {n} :e Union x.
{ exact UnionI x {n} u H1 Hu. }
apply Hx {n} L1.
- exact not_ordinal_Sing_tagn n Hn Hn1.
- assume H. apply H.
  let i. assume H. apply H.
  assume Hi: i :e n.
  assume H2: {n} = {i}.
  apply In_irref i.
  rewrite <- Sing_inj n i H2 at 2.
  exact Hi.
Qed.

Theorem SNo_ExtendedSNoElt_2: forall x, SNo x -> ExtendedSNoElt_ 2 x.
let x. assume Hx.
let v. assume Hv.
prove ordinal v \/ exists i :e 2, v = {i}.
apply UnionE_impred x v Hv.
let u.
assume H1: v :e u.
assume H2: u :e x.
apply SNoLev_ x Hx.
assume H3: x c= SNoElts_ (SNoLev x).
assume _.
apply binunionE (SNoLev x) {beta '|beta :e SNoLev x} u (H3 u H2).
- assume H4: u :e SNoLev x.
  claim Luo: ordinal u.
  { exact ordinal_Hered (SNoLev x) (SNoLev_ordinal x Hx) u H4. }
  prove ordinal v \/ exists i :e 2, v = {i}.
  apply orIL.
  exact ordinal_Hered u Luo v H1.
- assume H4: u :e {beta '|beta :e SNoLev x}.
  apply ReplE_impred (SNoLev x) tag u H4.
  let beta.
  assume Hb: beta :e SNoLev x.
  assume Hub: u = beta '.
  claim Lv: v :e beta '.
  { rewrite <- Hub. exact H1. }
  apply binunionE beta {{1}} v Lv.
  + assume H5: v :e beta.
    claim Lbo: ordinal beta.
    { exact ordinal_Hered (SNoLev x) (SNoLev_ordinal x Hx) beta Hb. }
    prove ordinal v \/ exists i :e 2, v = {i}.
    apply orIL.
    exact ordinal_Hered beta Lbo v H5.
  + assume H5: v :e {{1}}.
    prove ordinal v \/ exists i :e 2, v = {i}.
    apply orIR.
    witness 1. apply andI.
    * exact In_1_2.
    * prove v = {1}.
      exact SingE {1} v H5.
Qed.

End ExtendedSNo.

Section SurComplex.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Theorem complex_tag_fresh: forall x, SNo x -> forall u :e x, {2} /:e u.
let x. assume Hx.
apply Sing_nat_fresh_extension 2 nat_2 In_1_2 x.
prove ExtendedSNoElt_ 2 x.
exact SNo_ExtendedSNoElt_2 x Hx.
Qed.

Definition SNo_pair : set -> set -> set := pair_tag {2}.

Theorem SNo_pair_0 : forall x, SNo_pair x 0 = x.
exact pair_tag_0 {2} SNo complex_tag_fresh.
Qed.

Theorem SNo_pair_prop_1 : forall x1 y1 x2 y2, SNo x1 -> SNo x2 -> SNo_pair x1 y1 = SNo_pair x2 y2 -> x1 = x2.
exact pair_tag_prop_1 {2} SNo complex_tag_fresh.
Qed.

Theorem SNo_pair_prop_2 : forall x1 y1 x2 y2, SNo x1 -> SNo y1 -> SNo x2 -> SNo y2 -> SNo_pair x1 y1 = SNo_pair x2 y2 -> y1 = y2.
exact pair_tag_prop_2 {2} SNo complex_tag_fresh.
Qed.

Definition CSNo : set -> prop := CD_carr {2} SNo.

Theorem CSNo_I : forall x y, SNo x -> SNo y -> CSNo (SNo_pair x y).
exact CD_carr_I {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_E : forall z, CSNo z ->
  forall p:set -> prop,
      (forall x y, SNo x -> SNo y -> z = SNo_pair x y -> p (SNo_pair x y))
    -> p z.
exact CD_carr_E {2} SNo complex_tag_fresh.
Qed.

Theorem SNo_CSNo : forall x, SNo x -> CSNo x.
exact CD_carr_0ext {2} SNo complex_tag_fresh SNo_0.
Qed.

Theorem CSNo_0: CSNo 0.
apply SNo_CSNo. exact SNo_0.
Qed.

Theorem CSNo_1: CSNo 1.
apply SNo_CSNo. exact SNo_1.
Qed.

Let ctag : set -> set := fun alpha => SetAdjoin alpha {2}.
Postfix '' 100 := ctag.

Theorem CSNo_ExtendedSNoElt_3: forall z, CSNo z -> ExtendedSNoElt_ 3 z.
let z. assume Hz.
apply CSNo_E z Hz.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hzxy: z = SNo_pair x y.
let v.
assume Hv: v :e Union (SNo_pair x y).
apply UnionE_impred (SNo_pair x y) v Hv.
let u.
assume H1: v :e u.
assume H2: u :e SNo_pair x y.
apply binunionE x {w ''|w :e y} u H2.
- assume H3: u :e x.
  claim L1: v :e Union x.
  { exact UnionI x v u H1 H3. }
  prove ordinal v \/ exists i :e 3, v = {i}.
  exact extension_SNoElt_mon 2 3 (ordsuccI1 2) x (SNo_ExtendedSNoElt_2 x Hx) v L1.
- assume H3: u :e {w ''|w :e y}.
  apply ReplE_impred y ctag u H3.
  let w.
  assume Hw: w :e y.
  assume H4: u = w ''.
  claim L2: v :e w ''.
  { rewrite <- H4. exact H1. }
  apply binunionE w {{2}} v L2.
  + assume H5: v :e w.
    claim L3: v :e Union y.
    { exact UnionI y v w H5 Hw. }
    exact extension_SNoElt_mon 2 3 (ordsuccI1 2) y (SNo_ExtendedSNoElt_2 y Hy) v L3.
  + assume H5: v :e {{2}}.
    prove ordinal v \/ exists i :e 3, v = {i}.
    apply orIR.
    witness 2. apply andI.
    * prove 2 :e 3. exact In_2_3.
    * prove v = {2}. exact SingE {2} v H5.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.

Definition Complex_i : set := SNo_pair 0 1.
Definition CSNo_Re : set -> set := CD_proj0 {2} SNo.
Definition CSNo_Im : set -> set := CD_proj1 {2} SNo.

Let i := Complex_i.
Let Re : set -> set := CSNo_Re.
Let Im : set -> set := CSNo_Im.
Let pa : set -> set -> set := SNo_pair.

Theorem CSNo_Re1: forall z, CSNo z -> SNo (Re z) /\ exists y, SNo y /\ z = pa (Re z) y.
exact CD_proj0_1 {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_Re2: forall x y, SNo x -> SNo y -> Re (pa x y) = x.
exact CD_proj0_2 {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_Im1: forall z, CSNo z -> SNo (Im z) /\ z = pa (Re z) (Im z).
exact CD_proj1_1 {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_Im2: forall x y, SNo x -> SNo y -> Im (pa x y) = y.
exact CD_proj1_2 {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_ReR: forall z, CSNo z -> SNo (Re z).
exact CD_proj0R {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_ImR: forall z, CSNo z -> SNo (Im z).
exact CD_proj1R {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_ReIm: forall z, CSNo z -> z = pa (Re z) (Im z).
exact CD_proj0proj1_eta {2} SNo complex_tag_fresh.
Qed.

Theorem CSNo_ReIm_split: forall z w, CSNo z -> CSNo w -> Re z = Re w -> Im z = Im w -> z = w.
exact CD_proj0proj1_split {2} SNo complex_tag_fresh.
Qed.

Definition CSNoLev : set -> set := fun z => SNoLev (Re z) :\/: SNoLev (Im z).

Theorem CSNoLev_ordinal: forall z, CSNo z -> ordinal (CSNoLev z).
let z. assume Hz.
apply CSNo_E z Hz.
let x y.
assume Hx Hy.
assume Hzxy: z = pa x y.
prove ordinal (SNoLev (Re (pa x y)) :\/: SNoLev (Im (pa x y))).
rewrite CSNo_Re2 x y Hx Hy.
rewrite CSNo_Im2 x y Hx Hy.
prove ordinal (SNoLev x :\/: SNoLev y).
exact ordinal_binunion (SNoLev x) (SNoLev y) (SNoLev_ordinal x Hx) (SNoLev_ordinal y Hy).
Qed.

Let conj : set -> set := fun x => x.

Definition minus_CSNo : set -> set := CD_minus {2} SNo minus_SNo.
Definition conj_CSNo : set -> set := CD_conj {2} SNo minus_SNo conj.
Definition add_CSNo : set -> set -> set := CD_add {2} SNo add_SNo.
Definition mul_CSNo : set -> set -> set := CD_mul {2} SNo minus_SNo conj add_SNo mul_SNo.
Definition exp_CSNo_nat : set -> set -> set := CD_exp_nat {2} SNo minus_SNo conj add_SNo mul_SNo.

Definition abs_sqr_CSNo : set -> set := fun z => Re z ^ 2 + Im z ^ 2.

Definition recip_CSNo : set -> set := fun z => pa (Re z :/: abs_sqr_CSNo z) (- (Im z :/: abs_sqr_CSNo z)).

Let plus' := add_CSNo.
Let mult' := mul_CSNo.

Prefix :-: 358 := minus_CSNo.
Postfix ' 100 := conj_CSNo.
Infix :+: 360 right := add_CSNo.
Infix :*: 355 right := mul_CSNo.
Infix :^: 355 right := exp_CSNo_nat.

Definition div_CSNo : set -> set -> set := fun z w => z :*: recip_CSNo w.

Theorem CSNo_Complex_i : CSNo i.
prove CSNo (pa 0 1).
apply CSNo_I.
- exact SNo_0.
- exact SNo_1.
Qed.

Theorem CSNo_minus_CSNo : forall z, CSNo z -> CSNo (minus_CSNo z).
exact CD_minus_CD {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo.
Qed.

Theorem minus_CSNo_CRe: forall z, CSNo z -> Re (:-: z) = - Re z.
exact CD_minus_proj0 {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo.
Qed.

Theorem minus_CSNo_CIm: forall z, CSNo z -> Im (:-: z) = - Im z.
exact CD_minus_proj1 {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo.
Qed.

Theorem CSNo_conj_CSNo : forall z, CSNo z -> CSNo (conj_CSNo z).
exact CD_conj_CD {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo conj (fun x H => H).
Qed.

Theorem conj_CSNo_CRe: forall z, CSNo z -> Re (z ') = Re z.
exact CD_conj_proj0 {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo conj (fun x H => H).
Qed.

Theorem conj_CSNo_CIm: forall z, CSNo z -> Im (z ') = - Im z.
exact CD_conj_proj1 {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo conj (fun x H => H).
Qed.

Theorem CSNo_add_CSNo : forall z w, CSNo z -> CSNo w -> CSNo (add_CSNo z w).
exact CD_add_CD {2} SNo complex_tag_fresh add_SNo SNo_add_SNo.
Qed.

Theorem CSNo_add_CSNo_3 : forall z w v, CSNo z -> CSNo w -> CSNo v -> CSNo (z :+: w :+: v).
let z w v. assume Hz Hw Hv.
apply CSNo_add_CSNo.
- exact ??.
- apply CSNo_add_CSNo.
  + exact ??.
  + exact ??.
Qed.

Theorem add_CSNo_CRe: forall z w, CSNo z -> CSNo w -> Re (plus' z w) = Re z + Re w.
exact CD_add_proj0 {2} SNo complex_tag_fresh add_SNo SNo_add_SNo.
Qed.

Theorem add_CSNo_CIm: forall z w, CSNo z -> CSNo w -> Im (plus' z w) = Im z + Im w.
exact CD_add_proj1 {2} SNo complex_tag_fresh add_SNo SNo_add_SNo.
Qed.

Theorem CSNo_mul_CSNo : forall z w, CSNo z -> CSNo w -> CSNo (z :*: w).
exact CD_mul_CD {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo.
Qed.

Theorem CSNo_mul_CSNo_3 : forall z w v, CSNo z -> CSNo w -> CSNo v -> CSNo (z :*: w :*: v).
let z w v. assume Hz Hw Hv.
apply CSNo_mul_CSNo.
- exact ??.
- apply CSNo_mul_CSNo.
  + exact ??.
  + exact ??.
Qed.

Theorem mul_CSNo_CRe: forall z w, CSNo z -> CSNo w -> Re (mult' z w) = Re z * Re w + - (Im w * Im z).
exact CD_mul_proj0 {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo.
Qed.

Theorem mul_CSNo_CIm: forall z w, CSNo z -> CSNo w -> Im (mult' z w) = Im w * Re z + Im z * Re w.
exact CD_mul_proj1 {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo.
Qed.

Theorem SNo_Re: forall x, SNo x -> Re x = x.
exact CD_proj0_F {2} SNo complex_tag_fresh SNo_0.
Qed.

Theorem SNo_Im: forall x, SNo x -> Im x = 0.
exact CD_proj1_F {2} SNo complex_tag_fresh SNo_0.
Qed.

Theorem Re_0 : Re 0 = 0.
exact SNo_Re 0 SNo_0.
Qed.

Theorem Im_0 : Im 0 = 0.
exact SNo_Im 0 SNo_0.
Qed.

Theorem Re_1 : Re 1 = 1.
exact SNo_Re 1 SNo_1.
Qed.

Theorem Im_1 : Im 1 = 0.
exact SNo_Im 1 SNo_1.
Qed.

Theorem Re_i : Re i = 0.
exact CSNo_Re2 0 1 SNo_0 SNo_1.
Qed.

Theorem Im_i : Im i = 1.
exact CSNo_Im2 0 1 SNo_0 SNo_1.
Qed.

Theorem conj_CSNo_id_SNo: forall x, SNo x -> x ' = x.
exact CD_conj_F_eq {2} SNo complex_tag_fresh minus_SNo SNo_0 minus_SNo_0 conj.
Qed.

Theorem conj_CSNo_0 : 0 ' = 0.
exact conj_CSNo_id_SNo 0 SNo_0.
Qed.

Theorem conj_CSNo_1 : 1 ' = 1.
exact conj_CSNo_id_SNo 1 SNo_1.
Qed.

Theorem conj_CSNo_i : i ' = :-: i.
apply CSNo_ReIm_split (i ') (:-: i)
                      (CSNo_conj_CSNo i CSNo_Complex_i)
                      (CSNo_minus_CSNo i CSNo_Complex_i).
- prove Re (i ') = Re (:-: i).
  rewrite conj_CSNo_CRe i CSNo_Complex_i.
  rewrite minus_CSNo_CRe i CSNo_Complex_i.
  prove Re i = - Re i.
  rewrite Re_i.
  symmetry.
  exact minus_SNo_0.
- prove Im (i ') = Im (:-: i).
  rewrite minus_CSNo_CIm i CSNo_Complex_i.
  exact conj_CSNo_CIm i CSNo_Complex_i.
Qed.

Theorem minus_CSNo_minus_SNo : forall x, SNo x -> :-: x = - x.
exact CD_minus_F_eq {2} SNo complex_tag_fresh minus_SNo SNo_0 minus_SNo_0.
Qed.

Theorem minus_CSNo_0 : :-: 0 = 0.
rewrite minus_CSNo_minus_SNo 0 SNo_0.
exact minus_SNo_0.
Qed.

Theorem add_CSNo_add_SNo: forall x y, SNo x -> SNo y -> x :+: y = x + y.
exact CD_add_F_eq {2} SNo complex_tag_fresh add_SNo SNo_0 (add_SNo_0L 0 SNo_0).
Qed.

Theorem mul_CSNo_mul_SNo: forall x y, SNo x -> SNo y -> x :*: y = x * y.
exact CD_mul_F_eq {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 (fun x H => H) SNo_mul_SNo minus_SNo_0 add_SNo_0R mul_SNo_zeroL mul_SNo_zeroR.
Qed.

Theorem minus_CSNo_invol : forall z, CSNo z -> :-: :-: z = z.
exact CD_minus_invol {2} SNo complex_tag_fresh minus_SNo SNo_minus_SNo minus_SNo_invol.
Qed.

Theorem conj_CSNo_invol : forall z, CSNo z -> z ' ' = z.
exact CD_conj_invol {2} SNo complex_tag_fresh minus_SNo conj SNo_minus_SNo (fun x H => H) minus_SNo_invol (fun x _ q H => H).
Qed.

Theorem conj_minus_CSNo: forall z, CSNo z -> (:-: z) ' = :-: (z ').
exact CD_conj_minus {2} SNo complex_tag_fresh minus_SNo conj SNo_minus_SNo (fun x H => H) (fun x _ q H => H).
Qed.

Theorem minus_add_CSNo: forall z w, CSNo z -> CSNo w -> :-: (z :+: w) = :-: z :+: :-: w.
exact CD_minus_add {2} SNo complex_tag_fresh minus_SNo add_SNo SNo_minus_SNo SNo_add_SNo minus_add_SNo_distr.
Qed.

Theorem conj_add_CSNo: forall z w, CSNo z -> CSNo w -> (z :+: w) ' = z ' :+: w '.
exact CD_conj_add {2} SNo complex_tag_fresh minus_SNo conj add_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo minus_add_SNo_distr (fun x y _ _ q H => H).
Qed.

Theorem add_CSNo_com : forall z w, CSNo z -> CSNo w -> z :+: w = w :+: z.
exact CD_add_com {2} SNo complex_tag_fresh add_SNo add_SNo_com.
Qed.

Theorem add_CSNo_assoc: forall z w v, CSNo z -> CSNo w -> CSNo v -> (z :+: w) :+: v = z :+: (w :+: v).
claim L1: forall x y z, SNo x -> SNo y -> SNo z -> (x + y) + z = x + (y + z).
{ let x y z. assume Hx Hy Hz. symmetry. exact add_SNo_assoc x y z Hx Hy Hz. }
apply CD_add_assoc {2} SNo complex_tag_fresh add_SNo SNo_add_SNo L1.
Qed.

Theorem add_CSNo_0L : forall z, CSNo z -> add_CSNo 0 z = z.
exact CD_add_0L {2} SNo complex_tag_fresh add_SNo SNo_0 add_SNo_0L.
Qed.

Theorem add_CSNo_0R : forall z, CSNo z -> add_CSNo z 0 = z.
exact CD_add_0R {2} SNo complex_tag_fresh add_SNo SNo_0 add_SNo_0R.
Qed.

Theorem add_CSNo_minus_CSNo_linv : forall z, CSNo z -> add_CSNo (minus_CSNo z) z = 0.
exact CD_add_minus_linv {2} SNo complex_tag_fresh minus_SNo add_SNo SNo_minus_SNo add_SNo_minus_SNo_linv.
Qed.

Theorem add_CSNo_minus_CSNo_rinv : forall z, CSNo z -> add_CSNo z (minus_CSNo z) = 0.
exact CD_add_minus_rinv {2} SNo complex_tag_fresh minus_SNo add_SNo SNo_minus_SNo add_SNo_minus_SNo_rinv.
Qed.

Theorem mul_CSNo_0R: forall z, CSNo z -> z :*: 0 = 0.
exact CD_mul_0R {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 minus_SNo_0 (fun q H => H) (add_SNo_0L 0 SNo_0) mul_SNo_zeroL mul_SNo_zeroR.
Qed.

Theorem mul_CSNo_0L: forall z, CSNo z -> 0 :*: z = 0.
exact CD_mul_0L {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 (fun x H => H) minus_SNo_0 (add_SNo_0L 0 SNo_0) mul_SNo_zeroL mul_SNo_zeroR.
Qed.

Theorem mul_CSNo_1R: forall z, CSNo z -> z :*: 1 = z.
exact CD_mul_1R {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 SNo_1 minus_SNo_0 (fun q H => H) (fun q H => H) add_SNo_0L add_SNo_0R mul_SNo_zeroL mul_SNo_oneR.
Qed.

Theorem mul_CSNo_1L: forall z, CSNo z -> 1 :*: z = z.
exact CD_mul_1L {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 SNo_1 (fun x H => H) minus_SNo_0 add_SNo_0R mul_SNo_zeroL mul_SNo_zeroR mul_SNo_oneL mul_SNo_oneR.
Qed.

Theorem conj_mul_CSNo: forall z w, CSNo z -> CSNo w -> (z :*: w) ' = w ' :*: z '.
exact CD_conj_mul {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun z H => H) SNo_add_SNo SNo_mul_SNo minus_SNo_invol (fun x _ q H => H) (fun x _ q H => H) (fun x y _ _ q H => H) minus_add_SNo_distr add_SNo_com mul_SNo_com mul_SNo_minus_distrR mul_SNo_minus_distrL.
Qed.

Theorem mul_CSNo_distrL : forall z w u, CSNo z -> CSNo w -> CSNo u -> z :*: (w :+: u) = z :*: w :+: z :*: u.
claim L1: forall x y z, SNo x -> SNo y -> SNo z -> (x + y) + z = x + (y + z).
{ let x y z. assume Hx Hy Hz. symmetry. exact add_SNo_assoc x y z Hx Hy Hz. }
exact CD_add_mul_distrL {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo minus_add_SNo_distr (fun x y _ _ q H => H) L1 add_SNo_com mul_SNo_distrL mul_SNo_distrR.
Qed.

Theorem mul_CSNo_distrR : forall z w u, CSNo z -> CSNo w -> CSNo u -> (z :+: w) :*: u = z :*: u :+: w :*: u.
claim L1: forall x y z, SNo x -> SNo y -> SNo z -> (x + y) + z = x + (y + z).
{ let x y z. assume Hx Hy Hz. symmetry. exact add_SNo_assoc x y z Hx Hy Hz. }
exact CD_add_mul_distrR {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo minus_add_SNo_distr L1 add_SNo_com mul_SNo_distrL mul_SNo_distrR.
Qed.

Theorem minus_mul_CSNo_distrR: forall z w, CSNo z -> CSNo w -> z :*: (:-: w) = :-: z :*: w.
exact CD_minus_mul_distrR {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo (fun x _ q H => H) minus_add_SNo_distr mul_SNo_minus_distrR mul_SNo_minus_distrL.
Qed.

Theorem minus_mul_CSNo_distrL: forall z w, CSNo z -> CSNo w -> (:-: z) :*: w = :-: z :*: w.
exact CD_minus_mul_distrL {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo minus_add_SNo_distr mul_SNo_minus_distrR mul_SNo_minus_distrL.
Qed.

Theorem exp_CSNo_nat_0: forall z, z :^: 0 = 1.
exact CD_exp_nat_0 {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo.
Qed.

Theorem exp_CSNo_nat_S: forall z n, nat_p n -> z :^: (ordsucc n) = z :*: z :^: n.
exact CD_exp_nat_S {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo.
Qed.

Theorem exp_CSNo_nat_1: forall z, CSNo z -> z :^: 1 = z.
exact CD_exp_nat_1 {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 SNo_1 minus_SNo_0 (fun q H => H) (fun q H => H) add_SNo_0L add_SNo_0R mul_SNo_zeroL mul_SNo_oneR.
Qed.

Theorem exp_CSNo_nat_2: forall z, CSNo z -> z :^: 2 = z :*: z.
exact CD_exp_nat_2 {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_0 SNo_1 minus_SNo_0 (fun q H => H) (fun q H => H) add_SNo_0L add_SNo_0R mul_SNo_zeroL mul_SNo_oneR.
Qed.

Theorem CSNo_exp_CSNo_nat: forall z, CSNo z -> forall n, nat_p n -> CSNo (z :^: n).
exact CD_exp_nat_CD {2} SNo complex_tag_fresh minus_SNo conj add_SNo mul_SNo SNo_minus_SNo (fun x H => H) SNo_add_SNo SNo_mul_SNo SNo_0 SNo_1.
Qed.

Theorem add_SNo_rotate_4_0312: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y) + (z + w) = (x + w) + (y + z).
let x y z w. assume Hx Hy Hz Hw.
rewrite add_SNo_com z w Hz Hw.
prove (x + y) + (w + z) = (x + w) + (y + z).
exact add_SNo_com_4_inner_mid x y w z Hx Hy Hw Hz.
Qed.

Theorem mul_CSNo_com : forall z w, CSNo z -> CSNo w -> z :*: w = w :*: z.
let z w. assume Hz Hw.
claim Lzw: CSNo (mult' z w).
{ exact CSNo_mul_CSNo z w Hz Hw. }
claim Lwz: CSNo (mult' w z).
{ exact CSNo_mul_CSNo w z Hw Hz. }
claim LRezR: SNo (Re z).
{ exact CSNo_ReR z Hz. }
claim LRewR: SNo (Re w).
{ exact CSNo_ReR w Hw. }
claim LImzR: SNo (Im z).
{ exact CSNo_ImR z Hz. }
claim LImwR: SNo (Im w).
{ exact CSNo_ImR w Hw. }
apply CSNo_ReIm_split (mult' z w) (mult' w z) Lzw Lwz.
- prove Re (mult' z w) = Re (mult' w z).
  transitivity Re z * Re w + - (Im w * Im z),
               Re w * Re z + - (Im z * Im w).
  + exact mul_CSNo_CRe z w Hz Hw.
  + f_equal.
    * exact mul_SNo_com (Re z) (Re w) LRezR LRewR.
    * f_equal. exact mul_SNo_com (Im w) (Im z) LImwR LImzR.
  + symmetry. exact mul_CSNo_CRe w z Hw Hz.
- prove Im (mult' z w) = Im (mult' w z).
  transitivity Im w * Re z + Im z * Re w,
               Im z * Re w + Im w * Re z.
  + exact mul_CSNo_CIm z w Hz Hw.
  + exact add_SNo_com (Im w * Re z) (Im z * Re w) (SNo_mul_SNo (Im w) (Re z) LImwR LRezR) (SNo_mul_SNo (Im z) (Re w) LImzR LRewR).
  + symmetry. exact mul_CSNo_CIm w z Hw Hz.
Qed.

Theorem mul_CSNo_assoc: forall z w v, CSNo z -> CSNo w -> CSNo v -> z :*: (w :*: v) = (z :*: w) :*: v.
let z w v. assume Hz Hw Hv.
claim Lwv: CSNo (mult' w v).
{ exact CSNo_mul_CSNo w v Hw Hv. }
claim Lzw: CSNo (mult' z w).
{ exact CSNo_mul_CSNo z w Hz Hw. }
claim Lzwv1: CSNo (mult' z (mult' w v)).
{ exact CSNo_mul_CSNo z (mult' w v) Hz Lwv. }
claim Lzwv2: CSNo (mult' (mult' z w) v).
{ exact CSNo_mul_CSNo (mult' z w) v Lzw Hv. }
claim LRezR: SNo (Re z).
{ exact CSNo_ReR z Hz. }
claim LRewR: SNo (Re w).
{ exact CSNo_ReR w Hw. }
claim LRevR: SNo (Re v).
{ exact CSNo_ReR v Hv. }
claim LImzR: SNo (Im z).
{ exact CSNo_ImR z Hz. }
claim LImwR: SNo (Im w).
{ exact CSNo_ImR w Hw. }
claim LImvR: SNo (Im v).
{ exact CSNo_ImR v Hv. }
apply CSNo_ReIm_split (mult' z (mult' w v)) (mult' (mult' z w) v) Lzwv1 Lzwv2.
- prove Re (mult' z (mult' w v)) = Re (mult' (mult' z w) v).
  transitivity Re z * Re (mult' w v) + - (Im (mult' w v) * Im z),
               (Re z * Re w * Re v + - (Re z * Im v * Im w))
                 + (- Im v * Re w * Im z + - Im w * Re v * Im z),
               (Re z * Re w * Re v + - Im w * Re v * Im z)
                 + (- (Re z * Im v * Im w) + - Im v * Re w * Im z),
               Re (mult' z w) * Re v + - (Im v * Im (mult' z w)).
  + exact mul_CSNo_CRe z (mult' w v) Hz Lwv.
  + f_equal.
    * { prove Re z * Re (mult' w v) = Re z * Re w * Re v + - (Re z * Im v * Im w).
        transitivity Re z * (Re w * Re v + - (Im v * Im w)),
                     Re z * Re w * Re v + Re z * (- (Im v * Im w)).
        - f_equal. exact mul_CSNo_CRe w v Hw Hv.
	- apply mul_SNo_distrL (Re z) (Re w * Re v) (- (Im v * Im w)) LRezR (SNo_mul_SNo (Re w) (Re v) LRewR LRevR).
	  apply SNo_minus_SNo.
	  exact SNo_mul_SNo (Im v) (Im w) LImvR LImwR.
	- f_equal.
	  prove Re z * (- (Im v * Im w)) = - (Re z * Im v * Im w).
	  exact mul_SNo_minus_distrR (Re z) (Im v * Im w) LRezR (SNo_mul_SNo (Im v) (Im w) LImvR LImwR).
      }
    * { prove - (Im (mult' w v) * Im z) = - Im v * Re w * Im z + - Im w * Re v * Im z.
        transitivity - (Im v * Re w * Im z + Im w * Re v * Im z).
	- f_equal.
          prove Im (mult' w v) * Im z  = Im v * Re w * Im z + Im w * Re v * Im z.
	  transitivity (Im v * Re w + Im w * Re v) * Im z,
                       (Im v * Re w) * Im z + (Im w * Re v) * Im z.
	  + f_equal. exact mul_CSNo_CIm w v Hw Hv.
          + prove (Im v * Re w + Im w * Re v) * Im z
                = (Im v * Re w) * Im z + (Im w * Re v) * Im z.
	    exact mul_SNo_distrR (Im v * Re w) (Im w * Re v) (Im z)
                    (SNo_mul_SNo (Im v) (Re w) LImvR LRewR)
                    (SNo_mul_SNo (Im w) (Re v) LImwR LRevR)
                    LImzR.
          + f_equal.
            * symmetry. exact mul_SNo_assoc (Im v) (Re w) (Im z) ?? ?? ??.
            * symmetry. exact mul_SNo_assoc (Im w) (Re v) (Im z) ?? ?? ??.
        - prove - (Im v * Re w * Im z + Im w * Re v * Im z)
              = - Im v * Re w * Im z + - Im w * Re v * Im z.
          apply minus_add_SNo_distr.
	  + exact SNo_mul_SNo_3 (Im v) (Re w) (Im z) LImvR LRewR LImzR.
	  + exact SNo_mul_SNo_3 (Im w) (Re v) (Im z) LImwR LRevR LImzR.
      }
  + apply add_SNo_rotate_4_0312.
    * exact SNo_mul_SNo_3 (Re z) (Re w) (Re v) LRezR LRewR LRevR.
    * apply SNo_minus_SNo.
      exact SNo_mul_SNo_3 (Re z) (Im v) (Im w) LRezR LImvR LImwR.
    * apply SNo_minus_SNo.
      exact SNo_mul_SNo_3 (Im v) (Re w) (Im z) LImvR LRewR LImzR.
    * apply SNo_minus_SNo.
      exact SNo_mul_SNo_3 (Im w) (Re v) (Im z) LImwR LRevR LImzR.
  + prove (Re z * Re w * Re v + - Im w * Re v * Im z) + (- (Re z * Im v * Im w) + - Im v * Re w * Im z)
        = (Re (mult' z w) * Re v) + - (Im v * Im (mult' z w)).
    f_equal.
    * { prove Re z * Re w * Re v + - Im w * Re v * Im z = Re (mult' z w) * Re v.
        transitivity (Re z * Re w) * Re v + (- (Im w * Im z)) * Re v,
                     (Re z * Re w + - (Im w * Im z)) * Re v.
	- f_equal.
	  + prove Re z * Re w * Re v = (Re z * Re w) * Re v.
	    exact mul_SNo_assoc (Re z) (Re w) (Re v) LRezR LRewR LRevR.
	  + prove - (Im w * Re v * Im z) = (- (Im w * Im z)) * Re v.
	    transitivity - ((Im w * Im z) * Re v).
	    * { f_equal.
                transitivity (Im w * Im z * Re v).
                - f_equal. exact mul_SNo_com (Re v) (Im z) ?? ??.
                - exact mul_SNo_assoc (Im w) (Im z) (Re v) ?? ?? ??.
              }
	    * symmetry.
              prove (- (Im w * Im z)) * Re v = - ((Im w * Im z) * Re v).
	      exact mul_SNo_minus_distrL (Im w * Im z) (Re v) (SNo_mul_SNo (Im w) (Im z) LImwR LImzR) LRevR.
	- symmetry. exact mul_SNo_distrR (Re z * Re w) (- (Im w * Im z)) (Re v) (SNo_mul_SNo (Re z) (Re w) LRezR LRewR) (SNo_minus_SNo (Im w * Im z) (SNo_mul_SNo (Im w) (Im z) LImwR LImzR)) LRevR.
	- f_equal. symmetry. exact mul_CSNo_CRe z w Hz Hw.
      }
    * { prove - (Re z * Im v * Im w) + - Im v * Re w * Im z = - (Im v * Im (mult' z w)).
        transitivity - (Re z * Im v * Im w + Im v * Re w * Im z).
        - symmetry. apply minus_add_SNo_distr.
	  + exact SNo_mul_SNo_3 (Re z) (Im v) (Im w) ?? ?? ??.
	  + exact SNo_mul_SNo_3 (Im v) (Re w) (Im z) ?? ?? ??.
	- f_equal.
          prove Re z * Im v * Im w + Im v * Re w * Im z = Im v * Im (mult' z w).
          rewrite mul_SNo_com_3_0_1 (Re z) (Im v) (Im w) ?? ?? ??.
          transitivity Im v * (Re z * Im w + Re w * Im z).
          + symmetry. exact mul_SNo_distrL (Im v) (Re z * Im w) (Re w * Im z) ?? (SNo_mul_SNo (Re z) (Im w) ?? ??) (SNo_mul_SNo (Re w) (Im z) ?? ??).
          + prove Im v * (Re z * Im w + Re w * Im z) = Im v * Im (mult' z w).
            f_equal. symmetry.
            prove Im (mult' z w) = Re z * Im w + Re w * Im z.
            rewrite mul_SNo_com (Re z) (Im w) ?? ??.
            rewrite mul_SNo_com (Re w) (Im z) ?? ??.
            exact mul_CSNo_CIm z w Hz Hw.
      }
  + prove (Re (mult' z w) * Re v) + - (Im v * Im (mult' z w))
        = Re (mult' (mult' z w) v).
    symmetry.
    exact mul_CSNo_CRe (mult' z w) v Lzw Hv.
- prove Im (mult' z (mult' w v)) = Im (mult' (mult' z w) v).
  transitivity Im (mult' w v) * Re z + Im z * Re (mult' w v),
               (Im v * Re w + Im w * Re v) * Re z + Im z * (Re w * Re v + - (Im v * Im w)),
               (Im v * Re w * Re z + Im w * Re v * Re z) + (Im z * Re w * Re v + - (Im z * Im v * Im w)),
               (Im v * Re w * Re z + - (Im z * Im v * Im w)) + (Im w * Re v * Re z + Im z * Re w * Re v),
               Im v * (Re z * Re w + - (Im w * Im z)) + (Im w * Re z + Im z * Re w) * Re v,
               Im v * Re (mult' z w) + Im (mult' z w) * Re v.
  + prove Im (mult' z (mult' w v)) = Im (mult' w v) * Re z + Im z * Re (mult' w v).
    exact mul_CSNo_CIm z (mult' w v) Hz Lwv.
  + prove Im (mult' w v) * Re z + Im z * Re (mult' w v) = (Im v * Re w + Im w * Re v) * Re z + Im z * (Re w * Re v + - (Im v * Im w)).
    f_equal.
    * f_equal. exact mul_CSNo_CIm w v ?? ??.
    * f_equal. exact mul_CSNo_CRe w v ?? ??.
  + prove (Im v * Re w + Im w * Re v) * Re z + Im z * (Re w * Re v + - (Im v * Im w)) = (Im v * Re w * Re z + Im w * Re v * Re z) + (Im z * Re w * Re v + - (Im z * Im v * Im w)).
    f_equal.
    * { transitivity (Im v * Re w) * Re z + (Im w * Re v) * Re z.
        - exact mul_SNo_distrR (Im v * Re w) (Im w * Re v) (Re z) (SNo_mul_SNo (Im v) (Re w) ?? ??) (SNo_mul_SNo (Im w) (Re v) ?? ??) ??.
        - f_equal.
          + symmetry. exact mul_SNo_assoc (Im v) (Re w) (Re z) ?? ?? ??.
          + symmetry. exact mul_SNo_assoc (Im w) (Re v) (Re z) ?? ?? ??.
      }
    * { transitivity Im z * Re w * Re v + Im z * (- (Im v * Im w)).
        - apply mul_SNo_distrL (Im z) (Re w * Re v) (- (Im v * Im w)) ?? (SNo_mul_SNo (Re w) (Re v) ?? ??).
          apply SNo_minus_SNo.
          exact SNo_mul_SNo (Im v) (Im w) ?? ??.
        - f_equal.
          prove Im z * (- (Im v * Im w)) = - Im z * Im v * Im w.
          exact mul_SNo_minus_distrR (Im z) (Im v * Im w) ?? (SNo_mul_SNo (Im v) (Im w) ?? ??).
      }
  + prove (Im v * Re w * Re z + Im w * Re v * Re z) + (Im z * Re w * Re v + - (Im z * Im v * Im w)) = (Im v * Re w * Re z + - (Im z * Im v * Im w)) + (Im w * Re v * Re z + Im z * Re w * Re v).
    apply add_SNo_rotate_4_0312.
    * { apply SNo_mul_SNo_3.
        - exact ??.
        - exact ??.
        - exact ??.
      }
    * { apply SNo_mul_SNo_3.
        - exact ??.
        - exact ??.
        - exact ??.
      }
    * { apply SNo_mul_SNo_3.
        - exact ??.
        - exact ??.
        - exact ??.
      }
    * { apply SNo_minus_SNo.
        apply SNo_mul_SNo_3.
        - exact ??.
        - exact ??.
        - exact ??.
      }
  + f_equal.
    * { prove Im v * Re w * Re z + - (Im z * Im v * Im w) = Im v * (Re z * Re w + - (Im w * Im z)).
        rewrite mul_SNo_com (Re w) (Re z) ?? ??.
        rewrite mul_SNo_com (Im w) (Im z) ?? ??.
        rewrite mul_SNo_com_3_0_1 (Im z) (Im v) (Im w) ?? ?? ??.
        prove Im v * Re z * Re w + - (Im v * Im z * Im w) = Im v * (Re z * Re w + - (Im z * Im w)).
        rewrite <- mul_SNo_minus_distrR (Im v) (Im z * Im w) ?? (SNo_mul_SNo (Im z) (Im w) ?? ??).
        symmetry.
        prove Im v * (Re z * Re w + - (Im z * Im w)) = Im v * Re z * Re w + Im v * (- Im z * Im w).
        exact mul_SNo_distrL (Im v) (Re z * Re w) (- (Im z * Im w)) ??
                             (SNo_mul_SNo (Re z) (Re w) ?? ??)
                             (SNo_minus_SNo (Im z * Im w) (SNo_mul_SNo (Im z) (Im w) ?? ??)).
      }
    * { prove Im w * Re v * Re z + Im z * Re w * Re v = (Im w * Re z + Im z * Re w) * Re v.
        rewrite mul_SNo_com (Re v) (Re z) ?? ??.
        rewrite mul_SNo_assoc (Im w) (Re z) (Re v) ?? ?? ??.
        rewrite mul_SNo_assoc (Im z) (Re w) (Re v) ?? ?? ??.
        symmetry.
        exact mul_SNo_distrR (Im w * Re z) (Im z * Re w) (Re v) (SNo_mul_SNo (Im w) (Re z) ?? ??) (SNo_mul_SNo (Im z) (Re w) ?? ??) ??.
      }
  + prove Im v * (Re z * Re w + - (Im w * Im z)) + (Im w * Re z + Im z * Re w) * Re v = Im v * Re (mult' z w) + Im (mult' z w) * Re v.
    f_equal.
    * f_equal. symmetry. exact mul_CSNo_CRe z w Hz Hw.
    * f_equal. symmetry. exact mul_CSNo_CIm z w Hz Hw.
  + prove Im v * Re (mult' z w) + Im (mult' z w) * Re v = Im (mult' (mult' z w) v).
    symmetry. exact mul_CSNo_CIm (mult' z w) v Lzw Hv.
Qed.

Theorem Complex_i_sqr : i :*: i = :-: 1.
claim Lii: CSNo (i :*: i).
{ exact CSNo_mul_CSNo i i CSNo_Complex_i CSNo_Complex_i. }
claim Lm1: CSNo (:-: 1).
{ exact CSNo_minus_CSNo 1 CSNo_1. }
apply CSNo_ReIm_split (i :*: i) (:-: 1) Lii Lm1.
- prove Re (i :*: i) = Re (:-: 1).
  rewrite mul_CSNo_CRe i i CSNo_Complex_i CSNo_Complex_i.
  rewrite minus_CSNo_CRe 1 CSNo_1.
  prove Re i * Re i + - Im i * Im i = - Re 1.
  rewrite Re_i. rewrite Im_i. rewrite Re_1.
  prove 0 * 0 + - 1 * 1 = - 1.
  rewrite mul_SNo_zeroL 0 SNo_0.
  rewrite mul_SNo_oneL 1 SNo_1.
  prove 0 + - 1 = - 1.
  exact add_SNo_0L (- 1) (SNo_minus_SNo 1 SNo_1).
- prove Im (i :*: i) = Im (:-: 1).
  rewrite mul_CSNo_CIm i i CSNo_Complex_i CSNo_Complex_i.
  rewrite minus_CSNo_CIm 1 CSNo_1.
  prove Im i * Re i + Im i * Re i = - Im 1.
  rewrite Re_i. rewrite Im_i. rewrite Im_1.
  prove 1 * 0 + 1 * 0 = - 0.
  rewrite minus_SNo_0.
  rewrite mul_SNo_zeroR 1 SNo_1.
  prove 0 + 0 = 0.
  exact add_SNo_0L 0 SNo_0.
Qed.

Theorem SNo_abs_sqr_CSNo: forall z, CSNo z -> SNo (abs_sqr_CSNo z).
let z. assume Hz.
prove SNo (Re z ^ 2 + Im z ^ 2).
apply SNo_add_SNo.
- apply SNo_exp_SNo_nat.
  + exact CSNo_ReR z Hz.
  + exact nat_2.
- apply SNo_exp_SNo_nat.
  + exact CSNo_ImR z Hz.
  + exact nat_2.
Qed.

Theorem abs_sqr_CSNo_nonneg: forall z, CSNo z -> 0 <= abs_sqr_CSNo z.
let z. assume Hz.
set x := Re z.
set y := Im z.
claim Lx: SNo x.
{ exact CSNo_ReR z Hz. }
claim Ly: SNo y.
{ exact CSNo_ImR z Hz. }
claim Lxx: SNo (x ^ 2).
{ exact SNo_exp_SNo_nat x Lx 2 nat_2. }
claim Lyy: SNo (y ^ 2).
{ exact SNo_exp_SNo_nat y Ly 2 nat_2. }
prove 0 <= x ^ 2 + y ^ 2.
rewrite <- add_SNo_0L 0 SNo_0 at 1.
prove 0 + 0 <= x ^ 2 + y ^ 2.
apply add_SNo_Le3 0 0 (x ^ 2) (y ^ 2) SNo_0 SNo_0 Lxx Lyy.
- rewrite exp_SNo_nat_2 x Lx. exact SNo_sqr_nonneg x Lx.
- rewrite exp_SNo_nat_2 y Ly. exact SNo_sqr_nonneg y Ly.
Qed.

Theorem abs_sqr_CSNo_zero: forall z, CSNo z ->  abs_sqr_CSNo z = 0 -> z = 0.
let z. assume Hz.
set x := Re z.
set y := Im z.
set s := x ^ 2 + y ^ 2.
assume H1: s = 0.
claim Lx: SNo x.
{ exact CSNo_ReR z Hz. }
claim Ly: SNo y.
{ exact CSNo_ImR z Hz. }
claim Lxx: SNo (x ^ 2).
{ exact SNo_exp_SNo_nat x Lx 2 nat_2. }
claim Lyy: SNo (y ^ 2).
{ exact SNo_exp_SNo_nat y Ly 2 nat_2. }
claim Ls: SNo s.
{ exact SNo_add_SNo (x ^ 2) (y ^ 2) Lxx Lyy. }
prove z = 0.
apply CSNo_ReIm_split z 0 Hz CSNo_0.
- prove Re z = Re 0. rewrite Re_0.
  prove x = 0.
  apply SNo_zero_or_sqr_pos' x Lx.
  + assume H2: x = 0. exact H2.
  + assume H2: 0 < x ^ 2. prove False.
    apply SNoLt_irref 0.
    prove 0 < 0.
    rewrite <- H1 at 2.
    prove 0 < s.
    apply SNoLtLe_tra 0 (x ^ 2) s SNo_0 ?? ?? H2.
    prove x ^ 2 <= s.
    rewrite <- add_SNo_0R (x ^ 2) ?? at 1.
    prove x ^ 2 + 0 <= s.
    apply add_SNo_Le2 (x ^ 2) 0 (y ^ 2) ?? SNo_0 ??.
    prove 0 <= y ^ 2.
    apply SNo_sqr_nonneg' y Ly.
- prove Im z = Im 0. rewrite Im_0.
  prove y = 0.
  apply SNo_zero_or_sqr_pos' y Ly.
  + assume H2: y = 0. exact H2.
  + assume H2: 0 < y ^ 2. prove False.
    apply SNoLt_irref 0.
    prove 0 < 0.
    rewrite <- H1 at 2.
    prove 0 < s.
    apply SNoLtLe_tra 0 (y ^ 2) s SNo_0 ?? ?? H2.
    prove y ^ 2 <= s.
    rewrite <- add_SNo_0L (y ^ 2) ?? at 1.
    prove 0 + y ^ 2 <= s.
    apply add_SNo_Le1 0 (y ^ 2) (x ^ 2) SNo_0 ?? ??.
    prove 0 <= x ^ 2.
    apply SNo_sqr_nonneg' x Lx.
Qed.

Theorem CSNo_recip_CSNo: forall z, CSNo z -> CSNo (recip_CSNo z).
let z. assume Hz.
set s := Re z ^ 2 + Im z ^ 2.
claim LRezR: SNo (Re z).
{ exact CSNo_ReR z Hz. }
claim LImzR: SNo (Im z).
{ exact CSNo_ImR z Hz. }
claim Ls: SNo s.
{ exact SNo_abs_sqr_CSNo z Hz. }
prove CSNo (pa (Re z :/: s) (- (Im z :/: s))).
apply CSNo_I.
- prove SNo (Re z :/: s).
  apply SNo_div_SNo.
  + exact LRezR.
  + exact Ls.
- prove SNo (- (Im z :/: s)).
  apply SNo_minus_SNo.
  apply SNo_div_SNo.
  + exact LImzR.
  + exact Ls.
Qed.

Theorem CSNo_relative_recip : forall z, CSNo z -> forall u, SNo u -> (Re z ^ 2 + Im z ^ 2) * u = 1 -> z :*: (u :*: Re z :+: :-: i :*: u :*: Im z) = 1.
let z. assume Hz. let u. assume Hu.
assume Hur: (Re z ^ 2 + Im z ^ 2) * u = 1.
prove z :*: (u :*: Re z :+: :-: i :*: u :*: Im z) = 1.
claim LRezR: SNo (Re z).
{ exact CSNo_ReR z Hz. }
claim LImzR: SNo (Im z).
{ exact CSNo_ImR z Hz. }
prove z :*: (u :*: Re z :+: :-: i :*: u :*: Im z) = 1.
rewrite mul_CSNo_mul_SNo u (Re z) Hu LRezR.
rewrite mul_CSNo_mul_SNo u (Im z) Hu LImzR.
prove z :*: (u * Re z :+: :-: i :*: u * Im z) = 1.
claim LuRez: SNo (u * Re z).
{ exact SNo_mul_SNo u (Re z) ?? ??. }
claim LuRez': CSNo (u * Re z).
{ apply SNo_CSNo. exact LuRez. }
claim LuImz: SNo (u * Im z).
{ exact SNo_mul_SNo u (Im z) ?? ??. }
claim LuImz': CSNo (u * Im z).
{ apply SNo_CSNo. exact LuImz. }
claim LiuImz: CSNo (i :*: u * Im z).
{ apply CSNo_mul_CSNo.
  - exact CSNo_Complex_i.
  - exact LuImz'.
}
claim LmiuImz: CSNo (:-: i :*: u * Im z).
{ apply CSNo_minus_CSNo. exact LiuImz. }
claim L1: CSNo (u * Re z :+: :-: i :*: u * Im z).
{ apply CSNo_add_CSNo.
  - prove CSNo (u * Re z). exact LuRez'.
  - prove CSNo (:-: i :*: u * Im z). exact LmiuImz.
}
claim LRezRez: SNo (Re z * Re z).
{ exact SNo_mul_SNo (Re z) (Re z) ?? ??. }
claim LImzImz: SNo (Im z * Im z).
{ exact SNo_mul_SNo (Im z) (Im z) ?? ??. }
apply CSNo_ReIm_split (z :*: (u * Re z :+: :-: i :*: u * Im z)) 1
                      (CSNo_mul_CSNo z (u * Re z :+: :-: i :*: u * Im z) Hz L1)
		      CSNo_1.
- prove Re (z :*: (u * Re z :+: :-: i :*: u * Im z)) = Re 1.
  rewrite Re_1.
  rewrite mul_CSNo_CRe z (u * Re z :+: :-: i :*: u * Im z) Hz L1.
  prove Re z * Re (u * Re z :+: :-: i :*: u * Im z)
      + - Im (u * Re z :+: :-: i :*: u * Im z) * Im z = 1.
  rewrite add_CSNo_CRe (u * Re z) (:-: i :*: u * Im z) LuRez' LmiuImz.
  rewrite add_CSNo_CIm (u * Re z) (:-: i :*: u * Im z) LuRez' LmiuImz.
  prove Re z * (Re (u * Re z) + Re (:-: i :*: u * Im z))
      + - (Im (u * Re z) + Im (:-: i :*: u * Im z)) * Im z = 1.
  rewrite minus_CSNo_CRe (i :*: u * Im z) LiuImz.
  rewrite minus_CSNo_CIm (i :*: u * Im z) LiuImz.
  rewrite SNo_Re (u * Re z) LuRez.
  rewrite SNo_Im (u * Re z) LuRez.
  prove Re z * (u * Re z + - Re (i :*: u * Im z))
      + - (0 + - Im (i :*: u * Im z)) * Im z = 1.
  rewrite mul_CSNo_CRe i (u * Im z) CSNo_Complex_i LuImz'.
  prove Re z * (u * Re z + - (Re i * Re (u * Im z) + - Im (u * Im z) * Im i))
      + - (0 + - Im (i :*: u * Im z)) * Im z = 1.
  rewrite mul_CSNo_CIm i (u * Im z) CSNo_Complex_i LuImz'.
  prove Re z * (u * Re z + - (Re i * Re (u * Im z) + - Im (u * Im z) * Im i))
      + - (0 + - (Im (u * Im z) * Re i + Im i * Re (u * Im z))) * Im z = 1.
  rewrite Re_i. rewrite Im_i.
  prove Re z * (u * Re z + - (0 * Re (u * Im z) + - Im (u * Im z) * 1))
      + - (0 + - (Im (u * Im z) * 0 + 1 * Re (u * Im z))) * Im z = 1.
  rewrite SNo_Re (u * Im z) LuImz.
  rewrite SNo_Im (u * Im z) LuImz.
  prove Re z * (u * Re z + - (0 * (u * Im z) + - 0 * 1))
      + - (0 + - (0 * 0 + 1 * (u * Im z))) * Im z = 1.
  rewrite mul_SNo_zeroR 0 SNo_0.
  rewrite mul_SNo_zeroL (u * Im z) LuImz.
  rewrite mul_SNo_zeroL 1 SNo_1.
  prove Re z * (u * Re z + - (0 + - 0))
      + - (0 + - (0 + 1 * (u * Im z))) * Im z = 1.
  rewrite minus_SNo_0.
  rewrite add_SNo_0L 0 SNo_0.
  rewrite minus_SNo_0.
  rewrite add_SNo_0R (u * Re z) LuRez.
  prove Re z * (u * Re z)
      + - (0 + - (0 + 1 * (u * Im z))) * Im z = 1.
  rewrite mul_SNo_oneL (u * Im z) LuImz.
  prove Re z * (u * Re z)
      + - (0 + - (0 + (u * Im z))) * Im z = 1.
  rewrite add_SNo_0L (u * Im z) LuImz.
  rewrite add_SNo_0L (- u * Im z) (SNo_minus_SNo (u * Im z) LuImz).
  prove Re z * (u * Re z)
      + - (- (u * Im z)) * Im z = 1.
  rewrite <- mul_SNo_minus_distrL (- u * Im z) (Im z) (SNo_minus_SNo (u * Im z) LuImz) LImzR.
  rewrite minus_SNo_invol (u * Im z) LuImz.
  prove Re z * (u * Re z) + (u * Im z) * Im z = 1.
  rewrite mul_SNo_com_3_0_1 (Re z) u (Re z) ?? ?? ??.
  rewrite <- mul_SNo_assoc u (Im z) (Im z) ?? ?? ??.
  prove u * (Re z * Re z) + u * (Im z * Im z) = 1.
  rewrite mul_SNo_com u (Re z * Re z) ?? ??.
  rewrite mul_SNo_com u (Im z * Im z) ?? ??.
  rewrite <- mul_SNo_distrR (Re z * Re z) (Im z * Im z) u ?? ?? ??.
  rewrite <- exp_SNo_nat_2 (Re z) ??.
  rewrite <- exp_SNo_nat_2 (Im z) ??.
  exact Hur.
- prove Im (z :*: (u * Re z :+: :-: i :*: u * Im z)) = Im 1.
  rewrite mul_CSNo_CIm z (u * Re z :+: :-: i :*: u * Im z) Hz L1.
  rewrite Im_1.
  prove Im (u * Re z :+: :-: i :*: u * Im z) * Re z
      + Im z * Re (u * Re z :+: :-: i :*: u * Im z) = 0.
  rewrite add_CSNo_CRe (u * Re z) (:-: i :*: u * Im z) LuRez' LmiuImz.
  rewrite add_CSNo_CIm (u * Re z) (:-: i :*: u * Im z) LuRez' LmiuImz.
  prove (Im (u * Re z) + Im (:-: i :*: u * Im z)) * Re z
      + Im z * (Re (u * Re z) + Re (:-: i :*: u * Im z)) = 0.
  rewrite minus_CSNo_CRe (i :*: u * Im z) LiuImz.
  rewrite minus_CSNo_CIm (i :*: u * Im z) LiuImz.
  prove (Im (u * Re z) + - Im (i :*: u * Im z)) * Re z
      + Im z * (Re (u * Re z) + - Re (i :*: u * Im z)) = 0.
  rewrite SNo_Re (u * Re z) LuRez.
  rewrite SNo_Im (u * Re z) LuRez.
  prove (0 + - Im (i :*: u * Im z)) * Re z
      + Im z * ((u * Re z) + - Re (i :*: u * Im z)) = 0.
  rewrite mul_CSNo_CRe i (u * Im z) CSNo_Complex_i LuImz'.
  prove (0 + - Im (i :*: u * Im z)) * Re z
      + Im z * ((u * Re z) + - (Re i * Re (u * Im z) + - Im (u * Im z) * Im i)) = 0.
  rewrite mul_CSNo_CIm i (u * Im z) CSNo_Complex_i LuImz'.
  prove (0 + - (Im (u * Im z) * Re i + Im i * Re (u * Im z))) * Re z
      + Im z * ((u * Re z) + - (Re i * Re (u * Im z) + - Im (u * Im z) * Im i)) = 0.
  rewrite Re_i. rewrite Im_i.
  prove (0 + - (Im (u * Im z) * 0 + 1 * Re (u * Im z))) * Re z
      + Im z * ((u * Re z) + - (0 * Re (u * Im z) + - Im (u * Im z) * 1)) = 0.
  rewrite SNo_Re (u * Im z) LuImz.
  rewrite SNo_Im (u * Im z) LuImz.
  prove (0 + - (0 * 0 + 1 * (u * Im z))) * Re z
      + Im z * ((u * Re z) + - (0 * (u * Im z) + - 0 * 1)) = 0.
  rewrite mul_SNo_zeroL 0 SNo_0.
  rewrite mul_SNo_zeroL (u * Im z) ??.
  rewrite mul_SNo_zeroL 1 SNo_1.
  rewrite mul_SNo_oneL (u * Im z) ??.
  prove (0 + - (0 + u * Im z)) * Re z
      + Im z * ((u * Re z) + - (0 + - 0)) = 0.
  rewrite minus_SNo_0.
  rewrite add_SNo_0L 0 SNo_0.
  rewrite minus_SNo_0.
  rewrite add_SNo_0R (u * Re z) ??.
  rewrite add_SNo_0L (u * Im z) ??.
  prove (0 + - (u * Im z)) * Re z
      + Im z * (u * Re z) = 0.
  rewrite add_SNo_0L (- (u * Im z)) (SNo_minus_SNo (u * Im z) ??).
  prove (- (u * Im z)) * Re z
      + Im z * (u * Re z) = 0.
  rewrite mul_SNo_minus_distrL (u * Im z) (Re z) ?? ??.
  prove - (u * Im z) * Re z + Im z * u * Re z = 0.
  rewrite <- mul_SNo_assoc u (Im z) (Re z) ?? ?? ??.
  rewrite mul_SNo_com (Im z) (Re z) ?? ??.
  rewrite mul_SNo_com_3_0_1 (Im z) u (Re z) ?? ?? ??.
  prove - u * Re z * Im z + u * Im z * Re z = 0.
  rewrite mul_SNo_com (Re z) (Im z) ?? ??.
  prove - u * Im z * Re z + u * Im z * Re z = 0.
  exact add_SNo_minus_SNo_linv (u * Im z * Re z) (SNo_mul_SNo_3 u (Im z) (Re z) ?? ?? ??).
Qed.

Theorem recip_CSNo_invR : forall z, CSNo z -> z <> 0 -> z :*: recip_CSNo z = 1.
let z. assume Hz Hznz.
set x := Re z.
set y := Im z.
set s := x ^ 2 + y ^ 2.
set u := recip_SNo s.
claim Lx: SNo x.
{ exact CSNo_ReR z Hz. }
claim Ly: SNo y.
{ exact CSNo_ImR z Hz. }
claim Ls: SNo s.
{ exact SNo_abs_sqr_CSNo z Hz. }
claim LsC: CSNo s.
{ exact SNo_CSNo s Ls. }
claim Lu: SNo u.
{ exact SNo_recip_SNo s Ls. }
claim LuC: CSNo u.
{ exact SNo_CSNo u Lu. }
claim LReuS: SNo (Re u).
{ exact CSNo_ReR u LuC. }
claim LImuS: SNo (Im u).
{ exact CSNo_ImR u LuC. }
claim Luy: CSNo (u :*: y).
{ apply CSNo_mul_CSNo.
  - exact LuC.
  - apply SNo_CSNo. exact Ly.
}
claim Lsnz: s <> 0.
{ assume H1: s = 0.
  apply Hznz.
  prove z = 0.
  exact abs_sqr_CSNo_zero z Hz H1.
}
claim L1: Re (i :*: u :*: y) = 0.
{ rewrite mul_CSNo_CRe i (u :*: y) CSNo_Complex_i ??.
  prove Re i * Re (u :*: y) + - (Im (u :*: y) * Im i) = 0.
  rewrite Re_i. rewrite Im_i.
  prove 0 * Re (u :*: y) + - (Im (u :*: y) * 1) = 0.
  rewrite mul_SNo_zeroL (Re (u :*: y)) (CSNo_ReR (u :*: y) (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
  rewrite mul_SNo_oneR (Im (u :*: y)) (CSNo_ImR (u :*: y) (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
  prove 0 + - Im (u :*: y) = 0.
  rewrite mul_CSNo_CIm u y 
                       LuC (SNo_CSNo y Ly).
  prove 0 + - (Im y * Re u + Im u * Re y) = 0.
  rewrite SNo_Im y Ly.
  rewrite SNo_Im u Lu.
  prove 0 + - (0 * Re u + 0 * Re y) = 0.
  rewrite mul_SNo_zeroL (Re u) LReuS.
  rewrite mul_SNo_zeroL (Re y) (CSNo_ReR y (SNo_CSNo y Ly)).
  prove 0 + - (0 + 0) = 0.
  rewrite add_SNo_0L 0 SNo_0.
  rewrite minus_SNo_0.
  exact add_SNo_0L 0 SNo_0.
}
claim L2: Im (i :*: u :*: y) = u * y.
{ rewrite mul_CSNo_CIm i (u :*: y) CSNo_Complex_i ??.
  prove Im (u :*: y) * Re i + Im i * Re (u :*: y) = u * y.
  rewrite Re_i. rewrite Im_i.
  prove Im (u :*: y) * 0 + 1 * Re (u :*: y) = u * y.
  rewrite mul_SNo_zeroR (Im (u :*: y)) (CSNo_ImR (u :*: y) (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
  rewrite mul_SNo_oneL (Re (u :*: y)) (CSNo_ReR (u :*: y) (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
  prove 0 + Re (u :*: y) = u * y.
  rewrite mul_CSNo_mul_SNo u y Lu Ly.
  rewrite SNo_Re (u * y) (SNo_mul_SNo u y ?? ??).
  prove 0 + u * y = u * y.
  exact add_SNo_0L (u * y) (SNo_mul_SNo u y ?? ??).
}
prove z :*: pa (x :/: s) (- (y :/: s)) = 1.
transitivity (z :*: (u :*: x :+: :-: i :*: u :*: y)).
- prove z :*: pa (x :/: s) (- (y :/: s)) = z :*: (u :*: x :+: :-: i :*: u :*: y).
  f_equal.
  prove pa (x :/: s) (- (y :/: s)) = u :*: x :+: :-: i :*: u :*: y.
  apply CSNo_ReIm_split (pa (x :/: s) (- (y :/: s))) (u :*: x :+: :-: i :*: u :*: y).
  + prove CSNo (pa (x :/: s) (- (y :/: s))).
    apply CSNo_I.
    * prove SNo (x :/: s). exact SNo_div_SNo x s ?? ??.
    * apply SNo_minus_SNo.
      prove SNo (y :/: s). exact SNo_div_SNo y s ?? ??.
  + prove CSNo (u :*: x :+: :-: i :*: u :*: y).
    apply CSNo_add_CSNo.
    * exact CSNo_mul_CSNo u x LuC (SNo_CSNo x Lx).
    * { apply CSNo_minus_CSNo. apply CSNo_mul_CSNo.
        - exact CSNo_Complex_i.
        - exact CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly).
      }
  + prove Re (pa (x :/: s) (- (y :/: s))) = Re (u :*: x :+: :-: i :*: u :*: y).
    rewrite CSNo_Re2 (x :/: s) (- (y :/: s))
                     (SNo_div_SNo x s Lx Ls)
                     (SNo_minus_SNo (y :/: s)
                       (SNo_div_SNo y s Ly Ls)).
    prove x :/: s = Re (u :*: x :+: :-: i :*: u :*: y).
    rewrite add_CSNo_CRe (u :*: x) (:-: i :*: u :*: y)
                         (CSNo_mul_CSNo u x LuC (SNo_CSNo x Lx))
                         (CSNo_minus_CSNo (i :*: u :*: y)
                           (CSNo_mul_CSNo i (u :*: y)
                                          CSNo_Complex_i
                                          (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly)))).
    prove x :/: s = Re (u :*: x) + Re (:-: i :*: u :*: y).
    rewrite mul_CSNo_mul_SNo u x Lu Lx.
    prove x :/: s = Re (u * x) + Re (:-: i :*: u :*: y).
    rewrite SNo_Re (u * x) (SNo_mul_SNo u x ?? ??).
    prove x :/: s = u * x + Re (:-: i :*: u :*: y).
    rewrite minus_CSNo_CRe (i :*: u :*: y)
                           (CSNo_mul_CSNo i (u :*: y)
                                          CSNo_Complex_i
                                          (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
    prove x :/: s = u * x + - Re (i :*: u :*: y).
    rewrite L1.
    prove x :/: s = u * x + - 0.
    rewrite minus_SNo_0.
    prove x :/: s = u * x + 0.
    rewrite add_SNo_0R (u * x) (SNo_mul_SNo u x ?? ??).
    prove x * u = u * x.
    exact mul_SNo_com x u ?? ??.
  + prove Im (pa (x :/: s) (- (y :/: s))) = Im (u :*: x :+: :-: i :*: u :*: y).
    rewrite CSNo_Im2 (x :/: s) (- (y :/: s))
                     (SNo_div_SNo x s Lx Ls)
                     (SNo_minus_SNo (y :/: s)
                       (SNo_div_SNo y s Ly Ls)).
    rewrite add_CSNo_CIm (u :*: x) (:-: i :*: u :*: y)
                         (CSNo_mul_CSNo u x LuC (SNo_CSNo x Lx))
                         (CSNo_minus_CSNo (i :*: u :*: y)
                           (CSNo_mul_CSNo i (u :*: y)
                                          CSNo_Complex_i
                                          (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly)))).
    prove - (y :/: s) = Im (u :*: x) + Im (:-: i :*: u :*: y).
    rewrite minus_CSNo_CIm (i :*: u :*: y)
                           (CSNo_mul_CSNo i (u :*: y)
                                          CSNo_Complex_i
                                          (CSNo_mul_CSNo u y LuC (SNo_CSNo y Ly))).
    prove - (y :/: s) = Im (u :*: x) + - Im (i :*: u :*: y).
    rewrite mul_CSNo_mul_SNo u x Lu Lx.
    rewrite SNo_Im (u * x) (SNo_mul_SNo u x ?? ??).
    prove - (y :/: s) = 0 + - Im (i :*: u :*: y).
    rewrite L2.
    prove - (y :/: s) = 0 + - (u * y).
    prove - (y * u) = 0 + - (u * y).
    rewrite add_SNo_0L (- u * y) (SNo_minus_SNo (u * y) (SNo_mul_SNo u y ?? ??)).
    f_equal.
    exact mul_SNo_com y u ?? ??.
- prove z :*: (u :*: x :+: :-: i :*: u :*: y) = 1.
  apply CSNo_relative_recip z Hz u Lu.
  prove (x ^ 2 + y ^ 2) * u = 1.
  prove s * u = 1.
  exact recip_SNo_invR s Ls Lsnz.
Qed.

Theorem recip_CSNo_invL : forall z, CSNo z -> z <> 0 -> recip_CSNo z :*: z = 1.
let z. assume Hz Hznz.
rewrite mul_CSNo_com (recip_CSNo z) z (CSNo_recip_CSNo z Hz) Hz.
exact recip_CSNo_invR z Hz Hznz.
Qed.

Theorem CSNo_div_CSNo: forall z w, CSNo z -> CSNo w -> CSNo (div_CSNo z w).
let z w. assume Hz Hw.
exact CSNo_mul_CSNo z (recip_CSNo w) Hz (CSNo_recip_CSNo w Hw).
Qed.

Theorem mul_div_CSNo_invL: forall z w, CSNo z -> CSNo w -> w <> 0 -> (div_CSNo z w) :*: w = z.
let z w. assume Hz Hw Hw0.
prove (z :*: recip_CSNo w) :*: w = z.
rewrite <- mul_CSNo_assoc z (recip_CSNo w) w Hz (CSNo_recip_CSNo w Hw) Hw.
prove z :*: (recip_CSNo w :*: w) = z.
rewrite recip_CSNo_invL w Hw Hw0.
prove z :*: 1 = z.
exact mul_CSNo_1R z Hz.
Qed.

Theorem mul_div_CSNo_invR: forall z w, CSNo z -> CSNo w -> w <> 0 -> w :*: (div_CSNo z w) = z.
let z w. assume Hz Hw Hw0.
rewrite mul_CSNo_com w (div_CSNo z w) Hw (CSNo_div_CSNo z w Hz Hw).
exact mul_div_CSNo_invL z w Hz Hw Hw0.
Qed.

Theorem sqrt_SNo_nonneg_sqr_id: forall x, SNo x -> 0 <= x -> sqrt_SNo_nonneg (x ^ 2) = x.
let x. assume Hx Hxnn.
claim Lx2S: SNo (x ^ 2).
{ exact SNo_exp_SNo_nat x Hx 2 nat_2. }
claim Lx2nn: 0 <= x ^ 2.
{ rewrite exp_SNo_nat_2 x Hx. exact SNo_sqr_nonneg x Hx. }
claim Lsx2S: SNo (sqrt_SNo_nonneg (x ^ 2)).
{ exact SNo_sqrt_SNo_nonneg (x ^ 2) ?? ??. }
claim Lsx2nn: 0 <= sqrt_SNo_nonneg (x ^ 2).
{ exact sqrt_SNo_nonneg_nonneg (x ^ 2) ?? ??. }
claim Lsx22xx: sqrt_SNo_nonneg (x ^ 2) * sqrt_SNo_nonneg (x ^ 2) = x * x.
{ rewrite <- exp_SNo_nat_2 x Hx.
  exact sqrt_SNo_nonneg_sqr (x ^ 2) ?? ??.
}
apply SNoLeE 0 x SNo_0 Hx Hxnn.
- assume H1: 0 < x.
  claim L1: 0 < sqrt_SNo_nonneg (x ^ 2).
  { apply SNoLeE 0 (sqrt_SNo_nonneg (x ^ 2)) SNo_0 ?? ??.
    - assume H2: 0 < sqrt_SNo_nonneg (x ^ 2). exact H2.
    - assume H2: 0 = sqrt_SNo_nonneg (x ^ 2). prove False.
      apply SNoLt_irref 0.
      rewrite <- mul_SNo_zeroR 0 SNo_0 at 2.
      prove 0 < 0 * 0.
      rewrite H2 at 2 3. rewrite Lsx22xx.
      prove 0 < x * x.
      exact mul_SNo_pos_pos x x ?? ?? ?? ??.
  }
  apply SNoLt_trichotomy_or_impred (sqrt_SNo_nonneg (x ^ 2)) x Lsx2S Hx.
  + assume H2: sqrt_SNo_nonneg (x ^ 2) < x. prove False.
    apply SNoLt_irref (x * x).
    prove x * x < x * x.
    rewrite <- Lsx22xx at 1.
    prove sqrt_SNo_nonneg (x ^ 2) * sqrt_SNo_nonneg (x ^ 2) < x * x.
    exact pos_mul_SNo_Lt2 (sqrt_SNo_nonneg (x ^ 2)) (sqrt_SNo_nonneg (x ^ 2)) x x
                          ?? ?? ?? ?? L1 L1 H2 H2.
  + assume H2: sqrt_SNo_nonneg (x ^ 2) = x. exact H2.
  + assume H2: x < sqrt_SNo_nonneg (x ^ 2). prove False.
    apply SNoLt_irref (x * x).
    prove x * x < x * x.
    rewrite <- Lsx22xx at 2.
    prove x * x < sqrt_SNo_nonneg (x ^ 2) * sqrt_SNo_nonneg (x ^ 2).
    exact pos_mul_SNo_Lt2 x x (sqrt_SNo_nonneg (x ^ 2)) (sqrt_SNo_nonneg (x ^ 2))
                          ?? ?? ?? ?? H1 H1 H2 H2.
- assume H1: 0 = x.
  rewrite exp_SNo_nat_2 x Hx.
  rewrite <- H1.
  prove sqrt_SNo_nonneg (0 * 0) = 0.
  rewrite mul_SNo_zeroL 0 SNo_0.
  prove sqrt_SNo_nonneg 0 = 0.
  exact sqrt_SNo_nonneg_0.
Qed.

Theorem sqrt_SNo_nonneg_mon_strict: forall x y, SNo x -> SNo y -> 0 <= x -> x < y -> sqrt_SNo_nonneg x < sqrt_SNo_nonneg y.
let x y. assume Hx Hy Hxnn Hxy.
claim LsxS: SNo (sqrt_SNo_nonneg x).
{ exact SNo_sqrt_SNo_nonneg x ?? ??. }
claim Lsxnn: 0 <= sqrt_SNo_nonneg x.
{ exact sqrt_SNo_nonneg_nonneg x ?? ??. }
claim Lynn: 0 <= y.
{ apply SNoLe_tra 0 x y SNo_0 ?? ?? ??. prove x <= y. apply SNoLtLe. exact Hxy. }
claim LsyS: SNo (sqrt_SNo_nonneg y).
{ exact SNo_sqrt_SNo_nonneg y ?? ??. }
claim Lsynn: 0 <= sqrt_SNo_nonneg y.
{ exact sqrt_SNo_nonneg_nonneg y ?? ??. }
apply SNoLtLe_or (sqrt_SNo_nonneg x) (sqrt_SNo_nonneg y) ?? ??.
- assume H2. exact H2.
- assume H2: sqrt_SNo_nonneg y <= sqrt_SNo_nonneg x. prove False.
  apply SNoLt_irref x.
  prove x < x.
  apply SNoLtLe_tra x y x Hx Hy Hx Hxy.
  prove y <= x.
  rewrite <- sqrt_SNo_nonneg_sqr y ?? ??.
  rewrite <- sqrt_SNo_nonneg_sqr x ?? ??.
  prove sqrt_SNo_nonneg y * sqrt_SNo_nonneg y <= sqrt_SNo_nonneg x * sqrt_SNo_nonneg x.
  apply nonneg_mul_SNo_Le2 (sqrt_SNo_nonneg y) (sqrt_SNo_nonneg y) (sqrt_SNo_nonneg x) (sqrt_SNo_nonneg x) ?? ?? ?? ?? ?? ?? ?? ??.
Qed.

Theorem sqrt_SNo_nonneg_mon: forall x y, SNo x -> SNo y -> 0 <= x -> x <= y -> sqrt_SNo_nonneg x <= sqrt_SNo_nonneg y.
let x y. assume Hx Hy Hxnn Hxy.
apply SNoLeE x y Hx Hy Hxy.
- assume H1: x < y.
  prove sqrt_SNo_nonneg x <= sqrt_SNo_nonneg y.
  apply SNoLtLe.
  prove sqrt_SNo_nonneg x < sqrt_SNo_nonneg y.
  exact sqrt_SNo_nonneg_mon_strict x y Hx Hy Hxnn H1.
- assume H1: x = y. rewrite H1. apply SNoLe_ref.
Qed.

Theorem sqrt_SNo_nonneg_mul_SNo: forall x y, SNo x -> SNo y -> 0 <= x -> 0 <= y -> sqrt_SNo_nonneg (x * y) = sqrt_SNo_nonneg x * sqrt_SNo_nonneg y.
let x y. assume Hx Hy Hxnn Hynn.
claim LsxS: SNo (sqrt_SNo_nonneg x).
{ exact SNo_sqrt_SNo_nonneg x ?? ??. }
claim Lsxnn: 0 <= sqrt_SNo_nonneg x.
{ exact sqrt_SNo_nonneg_nonneg x ?? ??. }
claim LsyS: SNo (sqrt_SNo_nonneg y).
{ exact SNo_sqrt_SNo_nonneg y ?? ??. }
claim Lsynn: 0 <= sqrt_SNo_nonneg y.
{ exact sqrt_SNo_nonneg_nonneg y ?? ??. }
claim LsxsyS: SNo (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y).
{ apply SNo_mul_SNo.
  - exact ??.
  - exact ??.
}
claim L1: (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y) ^ 2 = x * y.
{ rewrite exp_SNo_nat_2 (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y) ??.
  prove (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y)
      * (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y)
      = x * y.
  rewrite mul_SNo_com_4_inner_mid (sqrt_SNo_nonneg x) (sqrt_SNo_nonneg y) (sqrt_SNo_nonneg x) (sqrt_SNo_nonneg y) ?? ?? ?? ??.
  f_equal.
  - exact sqrt_SNo_nonneg_sqr x ?? ??.
  - exact sqrt_SNo_nonneg_sqr y ?? ??.
}
rewrite <- L1.
apply sqrt_SNo_nonneg_sqr_id.
- prove SNo (sqrt_SNo_nonneg x * sqrt_SNo_nonneg y).
  exact LsxsyS.
- prove 0 <= sqrt_SNo_nonneg x * sqrt_SNo_nonneg y.
  apply mul_SNo_nonneg_nonneg.
  + exact ??.
  + exact ??.
  + exact ??.
  + exact ??.
Qed.

Definition modulus_CSNo: set -> set := fun z => sqrt_SNo_nonneg (abs_sqr_CSNo z).

Theorem SNo_modulus_CSNo: forall z, CSNo z -> SNo (modulus_CSNo z).
let z. assume Hz.
prove SNo (sqrt_SNo_nonneg (abs_sqr_CSNo z)).
apply SNo_sqrt_SNo_nonneg.
- exact SNo_abs_sqr_CSNo z Hz.
- exact abs_sqr_CSNo_nonneg z Hz.
Qed.

Theorem modulus_CSNo_nonneg: forall z, CSNo z -> 0 <= modulus_CSNo z.
let z. assume Hz.
prove 0 <= sqrt_SNo_nonneg (abs_sqr_CSNo z).
apply sqrt_SNo_nonneg_nonneg.
- exact SNo_abs_sqr_CSNo z Hz.
- exact abs_sqr_CSNo_nonneg z Hz.
Qed.

Definition sqrt_CSNo: set -> set := fun z =>
  if Im z < 0 \/ Im z = 0 /\ Re z < 0 then
    pa (sqrt_SNo_nonneg (eps_ 1 * (Re z + modulus_CSNo z)))
       (- sqrt_SNo_nonneg (eps_ 1 * (- Re z + modulus_CSNo z)))
  else
    pa (sqrt_SNo_nonneg (eps_ 1 * (Re z + modulus_CSNo z)))
       (sqrt_SNo_nonneg (eps_ 1 * (- Re z + modulus_CSNo z))).

Theorem sqrt_CSNo_sqrt: forall z, CSNo z -> sqrt_CSNo z :^: 2 = z.
let z. assume Hz.
set x := Re z.
set y := Im z.
set gamma := (sqrt_SNo_nonneg (eps_ 1 * (x + modulus_CSNo z))).
set delta := (sqrt_SNo_nonneg (eps_ 1 * (- x + modulus_CSNo z))).
prove (if y < 0 \/ y = 0 /\ x < 0 then pa gamma (- delta) else pa gamma delta) :^: 2 = z.
claim Lx: SNo x.
{ exact CSNo_ReR z Hz. }
claim Ly: SNo y.
{ exact CSNo_ImR z Hz. }
claim Lmx: SNo (- x).
{ apply SNo_minus_SNo. exact Lx. }
claim Lmy: SNo (- y).
{ apply SNo_minus_SNo. exact Ly. }
claim LmS: SNo (modulus_CSNo z).
{ exact SNo_modulus_CSNo z Hz. }
claim Lmnn: 0 <= modulus_CSNo z.
{ exact modulus_CSNo_nonneg z Hz. }
claim Lx2S: SNo (x ^ 2).
{ exact SNo_exp_SNo_nat x Lx 2 nat_2. }
claim Ly2S: SNo (y ^ 2).
{ exact SNo_exp_SNo_nat y Ly 2 nat_2. }
claim Lx2nn: 0 <= x ^ 2.
{ rewrite exp_SNo_nat_2 x Lx. exact SNo_sqr_nonneg x Lx. }
claim Ly2nn: 0 <= y ^ 2.
{ rewrite exp_SNo_nat_2 y Ly. exact SNo_sqr_nonneg y Ly. }
claim Lx2mx2: x ^ 2 = (- x) ^ 2.
{ rewrite exp_SNo_nat_2 x Lx.
  rewrite exp_SNo_nat_2 (- x) Lmx.
  prove x * x = (- x) * (- x).
  symmetry.
  exact mul_SNo_minus_minus x x Lx Lx.
}
claim LazS: SNo (abs_sqr_CSNo z).
{ exact SNo_abs_sqr_CSNo z Hz. }
claim Laznn: 0 <= abs_sqr_CSNo z.
{ exact abs_sqr_CSNo_nonneg z Hz. }
claim Lsx2S: SNo (sqrt_SNo_nonneg (x ^ 2)).
{ exact SNo_sqrt_SNo_nonneg (x ^ 2) ?? ??. }
claim Lsx2nn: 0 <= sqrt_SNo_nonneg (x ^ 2).
{ exact sqrt_SNo_nonneg_nonneg (x ^ 2) ?? ??. }
claim Lsy2S: SNo (sqrt_SNo_nonneg (y ^ 2)).
{ exact SNo_sqrt_SNo_nonneg (y ^ 2) ?? ??. }
claim Lmgtx: x <= modulus_CSNo z.
{ prove x <= sqrt_SNo_nonneg (x ^ 2 + y ^ 2).
  apply SNoLe_tra x (sqrt_SNo_nonneg (x ^ 2)) (sqrt_SNo_nonneg (x ^ 2 + y ^ 2))
                  Lx ?? ??.
  - prove x <= sqrt_SNo_nonneg (x ^ 2).
    apply SNoLtLe_or x 0 Lx SNo_0.
    + assume H1: x < 0.
      apply SNoLe_tra x 0 (sqrt_SNo_nonneg (x ^ 2)) Lx SNo_0 ??.
      * apply SNoLtLe. exact H1.
      * prove 0 <= sqrt_SNo_nonneg (x ^ 2). exact Lsx2nn.
    + assume H1: 0 <= x.
      rewrite sqrt_SNo_nonneg_sqr_id x Lx H1.
      apply SNoLe_ref.
  - prove sqrt_SNo_nonneg (x ^ 2) <= sqrt_SNo_nonneg (x ^ 2 + y ^ 2).
    apply sqrt_SNo_nonneg_mon.
    + exact ??.
    + exact ??.
    + exact ??.
    + prove x ^ 2 <= x ^ 2 + y ^ 2.
      rewrite <- add_SNo_0R (x ^ 2) ?? at 1.
      prove x ^ 2 + 0 <= x ^ 2 + y ^ 2.
      apply add_SNo_Le2.
      * exact ??.
      * exact SNo_0.
      * exact ??.
      * exact ??.
}
claim Lmgtnx: - x <= modulus_CSNo z.
{ prove - x <= sqrt_SNo_nonneg (x ^ 2 + y ^ 2).
  apply SNoLe_tra (- x) (sqrt_SNo_nonneg (x ^ 2)) (sqrt_SNo_nonneg (x ^ 2 + y ^ 2))
                  Lmx ?? ??.
  - prove - x <= sqrt_SNo_nonneg (x ^ 2).
    apply SNoLtLe_or (- x) 0 Lmx SNo_0.
    + assume H1: - x < 0.
      apply SNoLe_tra (- x) 0 (sqrt_SNo_nonneg (x ^ 2)) Lmx SNo_0 ??.
      * apply SNoLtLe. exact H1.
      * prove 0 <= sqrt_SNo_nonneg (x ^ 2). exact Lsx2nn.
    + assume H1: 0 <= - x.
      rewrite Lx2mx2.
      rewrite sqrt_SNo_nonneg_sqr_id (- x) Lmx H1.
      apply SNoLe_ref.
  - prove sqrt_SNo_nonneg (x ^ 2) <= sqrt_SNo_nonneg (x ^ 2 + y ^ 2).
    apply sqrt_SNo_nonneg_mon.
    + exact ??.
    + exact ??.
    + exact ??.
    + prove x ^ 2 <= x ^ 2 + y ^ 2.
      rewrite <- add_SNo_0R (x ^ 2) ?? at 1.
      prove x ^ 2 + 0 <= x ^ 2 + y ^ 2.
      apply add_SNo_Le2.
      * exact ??.
      * exact SNo_0.
      * exact ??.
      * exact ??.
}
claim LaS: SNo (x + modulus_CSNo z).
{ apply SNo_add_SNo.
  - exact ??.
  - exact ??.
}
claim LmaS: SNo (- x + modulus_CSNo z).
{ apply SNo_add_SNo.
  - exact ??.
  - exact ??.
}
claim LmmS: SNo (- modulus_CSNo z).
{ apply SNo_minus_SNo. exact ??. }
claim LammS: SNo (x + - modulus_CSNo z).
{ apply SNo_add_SNo.
  - exact ??.
  - exact ??.
}
claim Le1S: SNo (eps_ 1).
{ exact SNo_eps_ 1 (nat_p_omega 1 nat_1). }
claim Le1nn: 0 <= eps_ 1.
{ apply SNoLtLe. exact SNo_eps_pos 1 (nat_p_omega 1 nat_1). }
claim Le12S: SNo (eps_ 1 ^ 2).
{ apply SNo_exp_SNo_nat.
  - exact ??.
  - exact nat_2.
}
claim Le12nn: 0 <= eps_ 1 ^ 2.
{ rewrite exp_SNo_nat_2 (eps_ 1) ??.
  apply mul_SNo_nonneg_nonneg.
  - exact ??.
  - exact ??.
  - exact ??.
  - exact ??.
}
claim Le1aS: SNo (eps_ 1 * (x + modulus_CSNo z)).
{ apply SNo_mul_SNo.
  - exact ??.
  - exact ??.
}
claim Lann: 0 <= x + modulus_CSNo z.
{ rewrite add_SNo_com x (modulus_CSNo z) ?? ??.
  prove 0 <= modulus_CSNo z + x.
  rewrite <- minus_SNo_invol x Lx.
  prove 0 <= modulus_CSNo z + - - x.
  apply add_SNo_minus_Le2b (modulus_CSNo z) (- x) 0 ?? Lmx SNo_0.
  prove 0 + - x <= modulus_CSNo z.
  rewrite add_SNo_0L (- x) Lmx.
  prove - x <= modulus_CSNo z.
  exact Lmgtnx.
}
claim Le1ann: 0 <= eps_ 1 * (x + modulus_CSNo z).
{ apply mul_SNo_nonneg_nonneg (eps_ 1) (x + modulus_CSNo z).
  - exact ??.
  - exact ??.
  - exact ??.
  - exact ??.
}
claim Le1maS: SNo (eps_ 1 * (- x + modulus_CSNo z)).
{ apply SNo_mul_SNo.
  - exact ??.
  - exact ??.
}
claim Lmann: 0 <= - x + modulus_CSNo z.
{ rewrite add_SNo_com (- x) (modulus_CSNo z) ?? ??.
  prove 0 <= modulus_CSNo z + - x.
  apply add_SNo_minus_Le2b (modulus_CSNo z) x 0 ?? Lx SNo_0.
  prove 0 + x <= modulus_CSNo z.
  rewrite add_SNo_0L x Lx.
  prove x <= modulus_CSNo z.
  exact Lmgtx.
}
claim Le1mann: 0 <= eps_ 1 * (- x + modulus_CSNo z).
{ apply mul_SNo_nonneg_nonneg (eps_ 1) (- x + modulus_CSNo z).
  - exact ??.
  - exact ??.
  - exact ??.
  - exact ??.
}
claim LmxmzxmzS: SNo ((- x + modulus_CSNo z) * (x + modulus_CSNo z)).
{ apply SNo_mul_SNo.
  - exact ??.
  - exact ??.
}
claim Lmxmzxmznn: 0 <= (- x + modulus_CSNo z) * (x + modulus_CSNo z).
{ apply mul_SNo_nonneg_nonneg.
  - exact ??.
  - exact ??.
  - exact ??.
  - exact ??.
}
claim LgammaS: SNo gamma.
{ apply SNo_sqrt_SNo_nonneg.
  - exact ??.
  - exact ??.
}
claim Lgammann: 0 <= gamma.
{ apply sqrt_SNo_nonneg_nonneg.
  - exact ??.
  - exact ??.
}
claim LdeltaS: SNo delta.
{ apply SNo_sqrt_SNo_nonneg.
  - exact ??.
  - exact ??.
}
claim Ldeltann: 0 <= delta.
{ apply sqrt_SNo_nonneg_nonneg.
  - exact ??.
  - exact ??.
}
claim LmdeltaS: SNo (- delta).
{ apply SNo_minus_SNo. exact ??. }
claim LdeltagammaS: SNo (delta * gamma).
{ apply SNo_mul_SNo.
  - exact ??.
  - exact ??.
}
claim Lpa1: CSNo (pa gamma (- delta)).
{ apply CSNo_I.
  - exact ??.
  - exact ??.
}
claim Lpa2: CSNo (pa gamma delta).
{ apply CSNo_I.
  - exact ??.
  - exact ??.
}
claim Lpa1s: CSNo (pa gamma (- delta) :^: 2).
{ apply CSNo_exp_CSNo_nat.
  - exact ??.
  - exact nat_2.
}
claim Lpa2s: CSNo (pa gamma delta :^: 2).
{ apply CSNo_exp_CSNo_nat.
  - exact ??.
  - exact nat_2.
}
claim Lgamma2eq: gamma * gamma = eps_ 1 * (x + modulus_CSNo z).
{ exact sqrt_SNo_nonneg_sqr (eps_ 1 * (x + modulus_CSNo z)) ?? ??. }
claim Ldelta2eq: delta * delta = eps_ 1 * (- x + modulus_CSNo z).
{ exact sqrt_SNo_nonneg_sqr (eps_ 1 * (- x + modulus_CSNo z)) ?? ??. }
claim Ldeltagamma: delta * gamma = eps_ 1 * sqrt_SNo_nonneg (y ^ 2).
{ apply sqrt_SNo_nonneg_mul_SNo (eps_ 1 * (- x + modulus_CSNo z)) (eps_ 1 * (x + modulus_CSNo z)) ?? ?? ?? ?? (fun u _ => u = eps_ 1 * sqrt_SNo_nonneg (y ^ 2)).
  prove sqrt_SNo_nonneg ((eps_ 1 * (- x + modulus_CSNo z)) * (eps_ 1 * (x + modulus_CSNo z))) = eps_ 1 * sqrt_SNo_nonneg (y ^ 2).
  rewrite mul_SNo_com_4_inner_mid (eps_ 1) (- x + modulus_CSNo z) (eps_ 1) (x + modulus_CSNo z) ?? ?? ?? ??.
  prove sqrt_SNo_nonneg ((eps_ 1 * eps_ 1) * ((- x + modulus_CSNo z) * (x + modulus_CSNo z))) = eps_ 1 * sqrt_SNo_nonneg (y ^ 2).
  rewrite <- exp_SNo_nat_2 (eps_ 1) ??.
  apply sqrt_SNo_nonneg_mul_SNo (eps_ 1 ^ 2) ((- x + modulus_CSNo z) * (x + modulus_CSNo z)) ?? ?? ?? ?? (fun _ v => v = eps_ 1 * sqrt_SNo_nonneg (y ^ 2)).
  prove sqrt_SNo_nonneg (eps_ 1 ^ 2) * sqrt_SNo_nonneg ((- x + modulus_CSNo z) * (x + modulus_CSNo z)) = eps_ 1 * sqrt_SNo_nonneg (y ^ 2).
  rewrite sqrt_SNo_nonneg_sqr_id (eps_ 1) ?? ??.
  prove (eps_ 1) * sqrt_SNo_nonneg ((- x + modulus_CSNo z) * (x + modulus_CSNo z)) = eps_ 1 * sqrt_SNo_nonneg (y ^ 2).
  f_equal. f_equal.
  prove (- x + modulus_CSNo z) * (x + modulus_CSNo z) = y ^ 2.
  rewrite SNo_foil (- x) (modulus_CSNo z) x (modulus_CSNo z) ?? ?? ?? ??.
  prove (- x) * x + (- x) * modulus_CSNo z + modulus_CSNo z * x + modulus_CSNo z * modulus_CSNo z = y ^ 2.
  rewrite mul_SNo_minus_distrL x (modulus_CSNo z) ?? ??.
  rewrite mul_SNo_com (modulus_CSNo z) x ?? ??.
  rewrite add_SNo_minus_L2 (x * modulus_CSNo z) (modulus_CSNo z * modulus_CSNo z)
                           (SNo_mul_SNo x (modulus_CSNo z) ?? ??)
                           (SNo_mul_SNo (modulus_CSNo z) (modulus_CSNo z) ?? ??).
  prove (- x) * x + modulus_CSNo z * modulus_CSNo z = y ^ 2.
  prove (- x) * x + sqrt_SNo_nonneg (abs_sqr_CSNo z) * sqrt_SNo_nonneg (abs_sqr_CSNo z) = y ^ 2.
  rewrite sqrt_SNo_nonneg_sqr (abs_sqr_CSNo z) ?? ??.
  prove (- x) * x + x ^ 2 + y ^ 2 = y ^ 2.
  apply mul_SNo_minus_distrL x x ?? ?? (fun _ v => v + x ^ 2 + y ^ 2 = y ^ 2).
  rewrite <- exp_SNo_nat_2 x ??.
  prove - x ^ 2 + x ^ 2 + y ^ 2 = y ^ 2.
  exact add_SNo_minus_L2 (x ^ 2) (y ^ 2) ?? ??.
}
claim Lgamma2mdelta2: gamma * gamma + - (delta * delta) = x.
{ rewrite Lgamma2eq. rewrite Ldelta2eq.
  prove eps_ 1 * (x + modulus_CSNo z) + - eps_ 1 * (- x + modulus_CSNo z) = x.
  rewrite <- mul_SNo_minus_distrR (eps_ 1) (- x + modulus_CSNo z) ?? ??.
  prove eps_ 1 * (x + modulus_CSNo z) + eps_ 1 * (- (- x + modulus_CSNo z)) = x.
  rewrite minus_add_SNo_distr (- x) (modulus_CSNo z) ?? ??.
  rewrite minus_SNo_invol x ??.
  prove eps_ 1 * (x + modulus_CSNo z) + eps_ 1 * (x + - modulus_CSNo z) = x.
  rewrite <- mul_SNo_distrL (eps_ 1) (x + modulus_CSNo z) (x + - modulus_CSNo z)
                            ?? ?? ??.
  prove eps_ 1 * ((x + modulus_CSNo z) + (x + - modulus_CSNo z)) = x.
  rewrite add_SNo_com_4_inner_mid x (modulus_CSNo z) x (- modulus_CSNo z) ?? ?? ?? ??.
  prove eps_ 1 * ((x + x) + (modulus_CSNo z + - modulus_CSNo z)) = x.
  rewrite add_SNo_minus_SNo_rinv (modulus_CSNo z) ??.
  prove eps_ 1 * ((x + x) + 0) = x.
  rewrite add_SNo_0R (x + x) (SNo_add_SNo x x ?? ??).
  prove eps_ 1 * (x + x) = x.
  rewrite mul_SNo_distrL (eps_ 1) x x ?? ?? ??.
  prove eps_ 1 * x + eps_ 1 * x = x.
  rewrite <- mul_SNo_distrR (eps_ 1) (eps_ 1) x ?? ?? ??.
  prove (eps_ 1 + eps_ 1) * x = x.
  rewrite eps_1_half_eq1.
  exact mul_SNo_oneL x ??.
}
apply SNoLt_trichotomy_or_impred y 0 Ly SNo_0.
- assume H1: y < 0.
  claim Lcase1cond: y < 0 \/ y = 0 /\ x < 0.
  { apply orIL. exact H1. }
  rewrite If_i_1 (y < 0 \/ y = 0 /\ x < 0) (pa gamma (- delta)) (pa gamma delta) Lcase1cond.
  prove pa gamma (- delta) :^: 2 = z.
  apply CSNo_ReIm_split (pa gamma (- delta) :^: 2) z ?? Hz.
  + rewrite exp_CSNo_nat_2 (pa gamma (- delta)) ??.
    prove Re (pa gamma (- delta) :*: pa gamma (- delta)) = x.
    rewrite mul_CSNo_CRe (pa gamma (- delta)) (pa gamma (- delta)) ?? ??.
    rewrite CSNo_Re2 gamma (- delta) ?? ??.
    rewrite CSNo_Im2 gamma (- delta) ?? ??.
    prove gamma * gamma + - ((- delta) * (- delta)) = x.
    rewrite mul_SNo_minus_minus delta delta ?? ??.
    prove gamma * gamma + - (delta * delta) = x.
    exact Lgamma2mdelta2.
  + rewrite exp_CSNo_nat_2 (pa gamma (- delta)) ??.
    prove Im (pa gamma (- delta) :*: pa gamma (- delta)) = y.
    rewrite mul_CSNo_CIm (pa gamma (- delta)) (pa gamma (- delta)) ?? ??.
    rewrite CSNo_Re2 gamma (- delta) ?? ??.
    rewrite CSNo_Im2 gamma (- delta) ?? ??.
    prove (- delta) * gamma + (- delta) * gamma = y.
    rewrite mul_SNo_minus_distrL delta gamma ?? ??.
    prove - delta * gamma + - delta * gamma = y.
    rewrite <- minus_add_SNo_distr (delta * gamma) (delta * gamma) ?? ??.
    prove - (delta * gamma + delta * gamma) = y.
    rewrite Ldeltagamma.
    prove - (eps_ 1 * sqrt_SNo_nonneg (y ^ 2) + eps_ 1 * sqrt_SNo_nonneg (y ^ 2)) = y.
    rewrite <- mul_SNo_distrR (eps_ 1) (eps_ 1) (sqrt_SNo_nonneg (y ^ 2)) ?? ?? ??.
    rewrite eps_1_half_eq1.
    rewrite mul_SNo_oneL (sqrt_SNo_nonneg (y ^ 2)) ??.
    prove - sqrt_SNo_nonneg (y ^ 2) = y.
    rewrite exp_SNo_nat_2 y ??.
    prove - sqrt_SNo_nonneg (y * y) = y.
    rewrite <- mul_SNo_minus_minus y y ?? ??.
    prove - sqrt_SNo_nonneg ((- y) * (- y)) = y.
    rewrite <- exp_SNo_nat_2 (- y) ??.
    prove - sqrt_SNo_nonneg ((- y) ^ 2) = y.
    claim L1: 0 <= - y.
    { apply SNoLtLe.
      prove 0 < - y.
      apply minus_SNo_Lt_contra2 y 0 ?? SNo_0.
      prove y < - 0.
      rewrite minus_SNo_0.
      exact H1.
    }
    rewrite sqrt_SNo_nonneg_sqr_id (- y) ?? ??.
    exact minus_SNo_invol y ??.
- assume H1: y = 0.
  apply SNoLtLe_or x 0 Lx SNo_0.
  + assume H2: x < 0.
    claim Lcase1cond: y < 0 \/ y = 0 /\ x < 0.
    { apply orIR. apply andI.
      - exact H1.
      - exact H2.
    }
    rewrite If_i_1 (y < 0 \/ y = 0 /\ x < 0) (pa gamma (- delta)) (pa gamma delta) Lcase1cond.
    prove pa gamma (- delta) :^: 2 = z.
    apply CSNo_ReIm_split (pa gamma (- delta) :^: 2) z ?? Hz.
    * rewrite exp_CSNo_nat_2 (pa gamma (- delta)) ??.
      prove Re (pa gamma (- delta) :*: pa gamma (- delta)) = x.
      rewrite mul_CSNo_CRe (pa gamma (- delta)) (pa gamma (- delta)) ?? ??.
      rewrite CSNo_Re2 gamma (- delta) ?? ??.
      rewrite CSNo_Im2 gamma (- delta) ?? ??.
      prove gamma * gamma + - ((- delta) * (- delta)) = x.
      rewrite mul_SNo_minus_minus delta delta ?? ??.
      prove gamma * gamma + - (delta * delta) = x.
      exact Lgamma2mdelta2.
    * rewrite exp_CSNo_nat_2 (pa gamma (- delta)) ??.
      prove Im (pa gamma (- delta) :*: pa gamma (- delta)) = y.
      rewrite mul_CSNo_CIm (pa gamma (- delta)) (pa gamma (- delta)) ?? ??.
      rewrite CSNo_Re2 gamma (- delta) ?? ??.
      rewrite CSNo_Im2 gamma (- delta) ?? ??.
      prove (- delta) * gamma + (- delta) * gamma = y.
      rewrite mul_SNo_minus_distrL delta gamma ?? ??.
      prove - delta * gamma + - delta * gamma = y.
      rewrite Ldeltagamma.
      prove - eps_ 1 * sqrt_SNo_nonneg (y ^ 2) + - eps_ 1 * sqrt_SNo_nonneg (y ^ 2) = y.
      rewrite exp_SNo_nat_2 y ??.
      rewrite H1.
      prove - eps_ 1 * sqrt_SNo_nonneg (0 * 0) + - eps_ 1 * sqrt_SNo_nonneg (0 * 0) = 0.
      rewrite mul_SNo_zeroL 0 SNo_0. rewrite sqrt_SNo_nonneg_0.
      prove - eps_ 1 * 0 + - eps_ 1 * 0 = 0.
      rewrite mul_SNo_zeroR (eps_ 1) ??.
      prove - 0 + - 0 = 0.
      rewrite minus_SNo_0.
      prove 0 + 0 = 0.
      exact add_SNo_0L 0 SNo_0.
  + assume H2: 0 <= x.
    claim Lcase2cond: ~(y < 0 \/ y = 0 /\ x < 0).
    { assume H. apply H.
      - assume H3: y < 0.
        apply SNoLt_irref y.
        prove y < y.
        rewrite H1 at 2. exact H3.
      - assume H. apply H.
        assume H3: y = 0.
        assume H4: x < 0.
        apply SNoLt_irref x.
        prove x < x.
        exact SNoLtLe_tra x 0 x ?? SNo_0 ?? H4 H2.
    }
    rewrite If_i_0 (y < 0 \/ y = 0 /\ x < 0) (pa gamma (- delta)) (pa gamma delta) Lcase2cond.
    prove pa gamma delta :^: 2 = z.
    apply CSNo_ReIm_split (pa gamma delta :^: 2) z ?? Hz.
    * rewrite exp_CSNo_nat_2 (pa gamma delta) ??.
      prove Re (pa gamma delta :*: pa gamma delta) = x.
      rewrite mul_CSNo_CRe (pa gamma delta) (pa gamma delta) ?? ??.
      rewrite CSNo_Re2 gamma delta ?? ??.
      rewrite CSNo_Im2 gamma delta ?? ??.
      prove gamma * gamma + - (delta * delta) = x.
      exact Lgamma2mdelta2.
    * rewrite exp_CSNo_nat_2 (pa gamma delta) ??.
      prove Im (pa gamma delta :*: pa gamma delta) = y.
      rewrite mul_CSNo_CIm (pa gamma delta) (pa gamma delta) ?? ??.
      rewrite CSNo_Re2 gamma delta ?? ??.
      rewrite CSNo_Im2 gamma delta ?? ??.
      prove delta * gamma + delta * gamma = y.
      rewrite Ldeltagamma.
      prove eps_ 1 * sqrt_SNo_nonneg (y ^ 2) + eps_ 1 * sqrt_SNo_nonneg (y ^ 2) = y.
      rewrite exp_SNo_nat_2 y ??.
      rewrite H1.
      prove eps_ 1 * sqrt_SNo_nonneg (0 * 0) + eps_ 1 * sqrt_SNo_nonneg (0 * 0) = 0.
      rewrite mul_SNo_zeroL 0 SNo_0. rewrite sqrt_SNo_nonneg_0.
      prove eps_ 1 * 0 + eps_ 1 * 0 = 0.
      rewrite mul_SNo_zeroR (eps_ 1) ??.
      prove 0 + 0 = 0.
      exact add_SNo_0L 0 SNo_0.
- assume H1: 0 < y.
  claim Lcase2cond: ~(y < 0 \/ y = 0 /\ x < 0).
  { assume H. apply H.
    - assume H2: y < 0.
      apply SNoLt_irref y.
      prove y < y.
      exact SNoLt_tra y 0 y ?? SNo_0 ?? H2 H1.
    - assume H. apply H.
      assume H2: y = 0.
      assume H3: x < 0.
      apply SNoLt_irref y.
      rewrite H2 at 1. exact H1.
  }
  rewrite If_i_0 (y < 0 \/ y = 0 /\ x < 0) (pa gamma (- delta)) (pa gamma delta) Lcase2cond.
  prove pa gamma delta :^: 2 = z.
  apply CSNo_ReIm_split (pa gamma delta :^: 2) z ?? Hz.
  + rewrite exp_CSNo_nat_2 (pa gamma delta) ??.
    prove Re (pa gamma delta :*: pa gamma delta) = x.
    rewrite mul_CSNo_CRe (pa gamma delta) (pa gamma delta) ?? ??.
    rewrite CSNo_Re2 gamma delta ?? ??.
    rewrite CSNo_Im2 gamma delta ?? ??.
    prove gamma * gamma + - (delta * delta) = x.
    exact Lgamma2mdelta2.
  + rewrite exp_CSNo_nat_2 (pa gamma delta) ??.
    prove Im (pa gamma delta :*: pa gamma delta) = y.
    rewrite mul_CSNo_CIm (pa gamma delta) (pa gamma delta) ?? ??.
    rewrite CSNo_Re2 gamma delta ?? ??.
    rewrite CSNo_Im2 gamma delta ?? ??.
    prove delta * gamma + delta * gamma = y.
    rewrite Ldeltagamma.
    prove eps_ 1 * sqrt_SNo_nonneg (y ^ 2) + eps_ 1 * sqrt_SNo_nonneg (y ^ 2) = y.
    rewrite <- mul_SNo_distrR (eps_ 1) (eps_ 1) (sqrt_SNo_nonneg (y ^ 2)) ?? ?? ??.
    rewrite eps_1_half_eq1.
    rewrite mul_SNo_oneL (sqrt_SNo_nonneg (y ^ 2)) ??.
    prove sqrt_SNo_nonneg (y ^ 2) = y.
    apply sqrt_SNo_nonneg_sqr_id y ??.
    prove 0 <= y.
    apply SNoLtLe. exact H1.
Qed.

End SurComplex.

Section Complex.

Prefix - 358 := minus_CSNo.
Infix + 360 right := add_CSNo.
Infix * 355 right := mul_CSNo.

Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Let i := Complex_i.
Let Re : set -> set := CSNo_Re.
Let Im : set -> set := CSNo_Im.
Let pa : set -> set -> set := SNo_pair.

Definition complex : set := {pa (u 0) (u 1)|u :e real :*: real}.

Theorem complex_I : forall x y :e real, pa x y :e complex.
let x. assume Hx. let y. assume Hy.
prove pa x y :e complex.
rewrite <- tuple_2_0_eq x y.
rewrite <- tuple_2_1_eq x y at 2.
prove pa ((x,y) 0) ((x,y) 1) :e complex.
apply ReplI (real :*: real) (fun u => pa (u 0) (u 1)).
prove (x,y) :e real :*: real.
exact tuple_2_setprod real real x Hx y Hy.
Qed.

Theorem complex_E : forall z :e complex, forall p:prop,
   (forall x y :e real, z = pa x y -> p)
 -> p.
let z. assume Hz. let p. assume Hp.
apply ReplE_impred (real :*: real) (fun u => pa (u 0) (u 1)) z Hz.
let u.
assume Hu: u :e real :*: real.
assume Hzu: z = pa (u 0) (u 1).
exact Hp (u 0) (ap0_Sigma real (fun _ => real) u Hu)
         (u 1) (ap1_Sigma real (fun _ => real) u Hu)
         Hzu.
Qed.

Theorem complex_CSNo: forall z :e complex, CSNo z.
let z. assume Hz.
apply complex_E z Hz.
let x. assume Hx. let y. assume Hy.
assume Hzxy: z = pa x y.
prove CSNo z.
rewrite Hzxy. apply CSNo_I.
- exact real_SNo x Hx.
- exact real_SNo y Hy.
Qed.

Theorem real_complex: real c= complex.
let x. assume Hx: x :e real.
prove x :e complex.
rewrite <- SNo_pair_0 x.
prove pa x 0 :e complex.
apply complex_I.
- exact Hx.
- exact real_0.
Qed.

Theorem complex_0 : 0 :e complex.
exact real_complex 0 real_0.
Qed.

Theorem complex_1 : 1 :e complex.
exact real_complex 1 real_1.
Qed.

Theorem complex_i : i :e complex.
prove pa 0 1 :e complex.
apply complex_I.
- exact real_0.
- exact real_1.
Qed.

Theorem complex_Re_eq: forall x y :e real, Re (pa x y) = x.
let x. assume Hx. let y. assume Hy.
exact CSNo_Re2 x y (real_SNo x Hx) (real_SNo y Hy).
Qed.

Theorem complex_Im_eq: forall x y :e real, Im (pa x y) = y.
let x. assume Hx. let y. assume Hy.
exact CSNo_Im2 x y (real_SNo x Hx) (real_SNo y Hy).
Qed.

Theorem complex_Re_real: forall z :e complex, Re z :e real.
let z. assume Hz. apply complex_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove Re (pa x y) :e real.
rewrite complex_Re_eq x Hx y Hy.
prove x :e real. exact Hx.
Qed.

Theorem complex_Im_real: forall z :e complex, Im z :e real.
let z. assume Hz. apply complex_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
prove Im (pa x y) :e real.
rewrite complex_Im_eq x Hx y Hy.
prove y :e real. exact Hy.
Qed.

Theorem complex_ReIm_split: forall z w :e complex, Re z = Re w -> Im z = Im w -> z = w.
let z. assume Hz. let w. assume Hw.
exact CSNo_ReIm_split z w (complex_CSNo z Hz) (complex_CSNo w Hw).
Qed.

Theorem complex_minus_CSNo : forall z :e complex, - z :e complex.
let z. assume Hz.
prove pa (minus_SNo (Re z)) (minus_SNo (Im z)) :e complex.
apply complex_I.
- apply real_minus_SNo. exact complex_Re_real z Hz.
- apply real_minus_SNo. exact complex_Im_real z Hz.
Qed.

Theorem complex_conj_CSNo : forall z :e complex, conj_CSNo z :e complex.
let z. assume Hz.
prove pa (Re z) (minus_SNo (Im z)) :e complex.
apply complex_I.
- exact complex_Re_real z Hz.
- apply real_minus_SNo. exact complex_Im_real z Hz.
Qed.

Theorem complex_add_CSNo : forall z w :e complex, z + w :e complex.
let z. assume Hz. let w. assume Hw.
prove pa (add_SNo (Re z) (Re w)) (add_SNo (Im z) (Im w)) :e complex.
apply complex_I.
- apply real_add_SNo.
  + exact complex_Re_real z Hz.
  + exact complex_Re_real w Hw.
- apply real_add_SNo.
  + exact complex_Im_real z Hz.
  + exact complex_Im_real w Hw.
Qed.

Theorem complex_mul_CSNo : forall z w :e complex, z * w :e complex.
let z. assume Hz. let w. assume Hw.
prove pa (add_SNo (mul_SNo (Re z) (Re w)) (minus_SNo (mul_SNo (Im w) (Im z))))
         (add_SNo (mul_SNo (Im w) (Re z)) (mul_SNo (Im z) (Re w)))
       :e complex.
claim Lz0: Re z :e real.
{ exact complex_Re_real z Hz. }
claim Lz1: Im z :e real.
{ exact complex_Im_real z Hz. }
claim Lw0: Re w :e real.
{ exact complex_Re_real w Hw. }
claim Lw1: Im w :e real.
{ exact complex_Im_real w Hw. }
apply complex_I.
- apply real_add_SNo.
  + apply real_mul_SNo.
    * exact ??.
    * exact ??.
  + apply real_minus_SNo. apply real_mul_SNo.
    * exact ??.
    * exact ??.
- apply real_add_SNo.
  + apply real_mul_SNo.
    * exact ??.
    * exact ??.
  + apply real_mul_SNo.
    * exact ??.
    * exact ??.
Qed.

Theorem real_Re_eq: forall x :e real, Re x = x.
let x. assume Hx.
rewrite <- SNo_pair_0 x at 1.
exact complex_Re_eq x Hx 0 real_0.
Qed.

Theorem real_Im_eq: forall x :e real, Im x = 0.
let x. assume Hx.
rewrite <- SNo_pair_0 x.
exact complex_Im_eq x Hx 0 real_0.
Qed.

Theorem mul_i_real_eq: forall x :e real, i * x = pa 0 x.
let x. assume Hx.
prove pa (add_SNo (mul_SNo (Re (pa 0 1)) (Re x))
                  (minus_SNo (mul_SNo (Im x) (Im (pa 0 1)))))
         (add_SNo (mul_SNo (Im x) (Re (pa 0 1)))
                  (mul_SNo (Im (pa 0 1)) (Re x)))
    = pa 0 x.
rewrite real_Re_eq x Hx.
rewrite real_Im_eq x Hx.
rewrite complex_Re_eq 0 real_0 1 real_1.
rewrite complex_Im_eq 0 real_0 1 real_1.
prove pa (add_SNo (mul_SNo 0 x)
                  (minus_SNo (mul_SNo 0 1)))
         (add_SNo (mul_SNo 0 0)
                  (mul_SNo 1 x))
    = pa 0 x.
rewrite mul_SNo_zeroL x (real_SNo x Hx).
rewrite mul_SNo_zeroL 1 SNo_1.
rewrite minus_SNo_0.
rewrite mul_SNo_zeroL 0 SNo_0.
rewrite mul_SNo_oneL x (real_SNo x Hx).
prove pa (add_SNo 0 0) (add_SNo 0 x)
    = pa 0 x.
rewrite add_SNo_0L 0 SNo_0.
rewrite add_SNo_0L x (real_SNo x Hx).
reflexivity.
Qed.

Theorem real_Re_i_eq: forall x :e real, Re (i * x) = 0.
let x. assume Hx.
rewrite mul_i_real_eq x Hx.
prove Re (pa 0 x) = 0.
exact complex_Re_eq 0 real_0 x Hx.
Qed.

Theorem real_Im_i_eq: forall x :e real, Im (i * x) = x.
let x. assume Hx.
rewrite mul_i_real_eq x Hx.
prove Im (pa 0 x) = x.
exact complex_Im_eq 0 real_0 x Hx.
Qed.

Theorem complex_eta : forall z :e complex, z = Re z + i * Im z.
let z. assume Hz. apply complex_E z Hz.
let x. assume Hx. let y. assume Hy Hzxy.
rewrite Hzxy.
rewrite complex_Re_eq x Hx y Hy.
rewrite complex_Im_eq x Hx y Hy.
prove pa x y = x + i * y.
prove pa x y = pa (add_SNo (Re x) (Re (i * y))) (add_SNo (Im x) (Im (i * y))).
rewrite real_Re_eq x Hx.
rewrite real_Im_eq x Hx.
rewrite real_Re_i_eq y Hy.
rewrite real_Im_i_eq y Hy.
prove pa x y = pa (add_SNo x 0) (add_SNo 0 y).
rewrite add_SNo_0R x (real_SNo x Hx).
rewrite add_SNo_0L y (real_SNo y Hy).
reflexivity.
Qed.

Section ComplexDiv.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.

Theorem complex_recip_CSNo: forall z :e complex, recip_CSNo z :e complex.
let z. assume Hz.
claim Lz: CSNo z.
{ exact complex_CSNo z Hz. }
apply complex_E z Hz.
let x. assume Hx. let y. assume Hy.
assume Hzxy: z = pa x y.
prove recip_CSNo z :e complex.
prove pa (Re z :/: (Re z ^ 2 + Im z ^ 2)) (- (Im z :/: (Re z ^ 2 + Im z ^ 2))) :e complex.
claim LRez: Re z :e real.
{ rewrite Hzxy. rewrite complex_Re_eq x Hx y Hy. exact Hx. }
claim LImz: Im z :e real.
{ rewrite Hzxy. rewrite complex_Im_eq x Hx y Hy. exact Hy. }
claim LRez2: Re z ^ 2 :e real.
{ rewrite exp_SNo_nat_2 (Re z) (CSNo_ReR z Lz).
  exact real_mul_SNo (Re z) ?? (Re z) ??.
}
claim LImz2: Im z ^ 2 :e real.
{ rewrite exp_SNo_nat_2 (Im z) (CSNo_ImR z Lz).
  exact real_mul_SNo (Im z) ?? (Im z) ??.
}
claim LRez2Imz2: Re z ^ 2 + Im z ^ 2 :e real.
{ apply real_add_SNo.
  - exact ??.
  - exact ??.
}
apply complex_I.
- prove Re z :/: (Re z ^ 2 + Im z ^ 2) :e real.
  apply real_div_SNo.
  + exact LRez.
  + exact LRez2Imz2.
- prove - (Im z :/: (Re z ^ 2 + Im z ^ 2)) :e real.
  apply real_minus_SNo. apply real_div_SNo.
  + exact LImz.
  + exact LRez2Imz2.
Qed.

Theorem complex_div_CSNo: forall z w :e complex, div_CSNo z w :e complex.
let z. assume Hz. let w. assume Hw.
exact complex_mul_CSNo z Hz (recip_CSNo w) (complex_recip_CSNo w Hw).
Qed.

End ComplexDiv.

Theorem complex_real_set_eq : real = {z :e complex | Re z = z}.
apply set_ext.
- let x. assume Hx: x :e real. apply SepI.
  + exact real_complex x Hx.
  + exact real_Re_eq x Hx.
- let z. assume Hz: z :e {z :e complex | Re z = z}.
  apply SepE complex (fun z => Re z = z) z Hz.
  assume Hz1: z :e complex.
  assume Hz2: Re z = z.
  prove z :e real.
  rewrite <- Hz2.
  exact complex_Re_real z Hz1.
Qed.

End Complex.

Opaque SNo_pair.
Opaque CSNo.
Opaque Complex_i.
Opaque CSNo_Re.
Opaque CSNo_Im.
Opaque CSNoLev.
Opaque minus_CSNo.
Opaque conj_CSNo.
Opaque add_CSNo.
Opaque mul_CSNo.
Opaque exp_CSNo_nat.
Opaque abs_sqr_CSNo.
Opaque recip_CSNo.
Opaque div_CSNo.
Opaque modulus_CSNo.
Opaque sqrt_CSNo.
Opaque complex.
