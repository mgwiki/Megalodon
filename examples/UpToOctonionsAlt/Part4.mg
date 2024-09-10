(** Part 4 **)

Section SurrealMinus.

(* Parameter minus_SNo "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "268a6c1da15b8fe97d37be85147bc7767b27098cdae193faac127195e8824808" *)
Definition minus_SNo : set -> set
  := SNo_rec_i (fun x m => SNoCut {m z|z :e SNoR x} {m w|w :e SNoL x}).

Prefix - 358 := minus_SNo.

(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem minus_SNo_eq : forall x, SNo x -> - x = SNoCut {- z|z :e SNoR x} {- w|w :e SNoL x}.
claim L1: forall x, SNo x ->
  forall g h:set -> set, (forall w :e SNoS_ (SNoLev x), g w = h w)
   -> SNoCut {g z|z :e SNoR x} {g w|w :e SNoL x}
    = SNoCut {h z|z :e SNoR x} {h w|w :e SNoL x}.
{ let x. assume Hx: SNo x.
  let g h.
  assume Hgh: forall w :e SNoS_ (SNoLev x), g w = h w.
  prove SNoCut {g z|z :e SNoR x} {g w|w :e SNoL x}
      = SNoCut {h z|z :e SNoR x} {h w|w :e SNoL x}.
  claim L1a: {g z|z :e SNoR x} = {h z|z :e SNoR x}.
  { apply ReplEq_ext.
    let z. assume Hz: z :e SNoR x.
    prove g z = h z.
    apply Hgh.
    prove z :e SNoS_ (SNoLev x).
    exact SNoR_SNoS x Hx z Hz.
  }
  claim L1b: {g w|w :e SNoL x} = {h w|w :e SNoL x}.
  { apply ReplEq_ext.
    let w. assume Hw: w :e SNoL x.
    prove g w = h w.
    apply Hgh.
    prove w :e SNoS_ (SNoLev x).
    exact SNoL_SNoS x Hx w Hw.
  }
  rewrite L1a. rewrite L1b. reflexivity.
}
exact SNo_rec_i_eq (fun x m => SNoCut {m z|z :e SNoR x} {m w|w :e SNoL x}) L1.
Qed.

Theorem minus_SNo_prop1 : forall x, SNo x -> SNo (- x) /\ (forall u :e SNoL x, - x < - u) /\ (forall u :e SNoR x, - u < - x) /\ SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), SNo (- w) /\ (forall u :e SNoL w, - w < - u) /\ (forall u :e SNoR w, - u < - w) /\ SNoCutP {- z|z :e SNoR w} {- v|v :e SNoL w}.
claim IHLx : forall w :e SNoL x, SNo (- w) /\ (forall u :e SNoL w, - w < - u) /\ (forall u :e SNoR w, - u < - w).
{ let w. assume Hw: w :e SNoL x.
  apply SNoL_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: w < x.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  apply IH w Lw. assume H _. exact H.
}
claim IHRx : forall z :e SNoR x, SNo (- z) /\ (forall u :e SNoL z, - z < - u) /\ (forall u :e SNoR z, - u < - z).
{ let w. assume Hw: w :e SNoR x.
  apply SNoR_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: x < w.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  apply IH w Lw. assume H _. exact H.
}
set L := {- z|z :e SNoR x}.
set R := {- w|w :e SNoL x}.
claim LLR: SNoCutP L R.
{ prove (forall w :e L, SNo w)
     /\ (forall z :e R, SNo z)
     /\ (forall w :e L, forall z :e R, w < z).
  apply and3I.
  - let w. assume Hw: w :e L.
    prove SNo w.
    apply ReplE_impred (SNoR x) (fun z => - z) w Hw.
    let z.
    assume Hz: z :e SNoR x.
    assume Hwz: w = - z.
    apply IHRx z Hz. assume H2. apply H2.
    assume H2: SNo (- z).
    assume _ _.
    prove SNo w.
    rewrite Hwz. exact H2.
  - let z. assume Hz: z :e R.
    prove SNo z.
    apply ReplE_impred (SNoL x) (fun w => - w) z Hz.
    let w.
    assume Hw: w :e SNoL x.
    assume Hzw: z = - w.
    apply IHLx w Hw. assume H2. apply H2.
    assume H2: SNo (- w).
    assume _ _.
    prove SNo z.
    rewrite Hzw. exact H2.
  - let w. assume Hw: w :e L.
    let z. assume Hz: z :e R.
    apply ReplE_impred (SNoR x) (fun z => - z) w Hw.
    let u.
    assume Hu: u :e SNoR x.
    assume Hwu: w = - u.
    apply SNoR_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: x < u.
    apply SNoLev_prop u Hu1.
    assume Hu1a: ordinal (SNoLev u).
    assume Hu1b: SNo_ (SNoLev u) u.
    apply ReplE_impred (SNoL x) (fun w => - w) z Hz.
    let v.
    assume Hv: v :e SNoL x.
    assume Hzv: z = - v.
    apply SNoL_E x Hx v Hv.
    assume Hv1: SNo v.
    assume Hv2: SNoLev v :e SNoLev x.
    assume Hv3: v < x.
    apply SNoLev_prop v Hv1.
    assume Hv1a: ordinal (SNoLev v).
    assume Hv1b: SNo_ (SNoLev v) v.
    apply IHLx v Hv. assume H2. apply H2.
    assume H2: SNo (- v).
    assume H3: forall u :e SNoL v, - v < - u.
    assume H4: forall u :e SNoR v, - u < - v.
    apply IHRx u Hu. assume H5. apply H5.
    assume H5: SNo (- u).
    assume H6: forall v :e SNoL u, - u < - v.
    assume H7: forall v :e SNoR u, - v < - u.
    prove w < z.
    rewrite Hwu. rewrite Hzv.
    prove - u < - v.
    claim Lvu: v < u.
    { exact SNoLt_tra v x u Hv1 Hx Hu1 Hv3 Hu3. }
    apply SNoLtE v u Hv1 Hu1 Lvu.
    + let z. assume Hz: SNo z.
      assume Hz1: SNoLev z :e SNoLev v :/\: SNoLev u.
      assume Hz2: SNoEq_ (SNoLev z) z v.
      assume Hz3: SNoEq_ (SNoLev z) z u.
      assume Hz4: v < z.
      assume Hz5: z < u.
      assume Hz6: SNoLev z /:e v.
      assume Hz7: SNoLev z :e u.
      apply SNoLev_prop z Hz.
      assume Hza: ordinal (SNoLev z).
      assume Hzb: SNo_ (SNoLev z) z.
      apply binintersectE (SNoLev v) (SNoLev u) (SNoLev z) Hz1.
      assume Hz1a: SNoLev z :e SNoLev v.
      assume Hz1b: SNoLev z :e SNoLev u.
      claim LzLx: z :e SNoS_ (SNoLev x).
      { apply SNoS_I2 z x Hz Hx.
        prove SNoLev z :e SNoLev x.
        apply SNoLev_ordinal x Hx.
        assume Hx2: TransSet (SNoLev x).
        assume _.
        exact Hx2 (SNoLev u) Hu2 (SNoLev z) Hz1b.
      }
      claim Lmz: SNo (- z).
      { apply IH z LzLx.
        assume H. apply H. assume H. apply H. assume H _ _ _. exact H.
      }
      prove - u < - v.
      apply SNoLt_tra (- u) (- z) (- v) H5 Lmz H2.
      * { prove - u < - z.
          apply H6.
          prove z :e SNoL u.
          prove z :e {x :e SNoS_ (SNoLev u) | x < u}.
          apply SepI.
          - prove z :e SNoS_ (SNoLev u).
            apply SNoS_I2 z u Hz Hu1 Hz1b.
          - prove z < u. exact Hz5.
        }
      * { prove - z < - v.
          apply H4.
          prove z :e SNoR v.
          prove z :e {x :e SNoS_ (SNoLev v) | v < x}.
          apply SepI.
          - prove z :e SNoS_ (SNoLev v).
            exact SNoS_I2 z v Hz Hv1 Hz1a.
          - prove v < z. exact Hz4.
        }
    + assume H8: SNoLev v :e SNoLev u.
      assume H9: SNoEq_ (SNoLev v) v u.
      assume H10: SNoLev v :e u.
      prove - u < - v.
      apply H6.
      prove v :e SNoL u.
      prove v :e {x :e SNoS_ (SNoLev u) | x < u}.
      apply SepI.
      * prove v :e SNoS_ (SNoLev u).
        exact SNoS_I2 v u Hv1 Hu1 H8.
      * prove v < u. exact Lvu.
    + assume H8: SNoLev u :e SNoLev v.
      assume H9: SNoEq_ (SNoLev u) v u.
      assume H10: SNoLev u /:e v.
      prove - u < - v.
      apply H4.
      prove u :e SNoR v.
      prove u :e {x :e SNoS_ (SNoLev v) | v < x}.
      apply SepI.
      * prove u :e SNoS_ (SNoLev v).
        exact SNoS_I2 u v Hu1 Hv1 H8.
      * prove v < u. exact Lvu.
}
claim LNLR: SNo (SNoCut L R).
{ exact SNoCutP_SNo_SNoCut L R LLR. }
apply andI.
- rewrite minus_SNo_eq x Hx. 
  apply and3I.
  + prove SNo (SNoCut L R). exact LNLR.
  + prove forall u :e SNoL x, SNoCut L R < - u.
    let u. assume Hu: u :e SNoL x.
    prove SNoCut L R < - u.
    apply SNoL_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: u < x.
    claim LmuR: - u :e R.
    { apply ReplI. prove u :e SNoL x. exact Hu. }
    prove SNoCut L R < - u.
    exact SNoCutP_SNoCut_R L R LLR (- u) LmuR. (** Using LLR here which was proven using IH **)
  + prove forall u :e SNoR x, - u < SNoCut L R.
    let u. assume Hu: u :e SNoR x.
    prove - u < SNoCut L R.
    apply SNoR_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: x < u.
    claim LmuL: - u :e L.
    { apply ReplI. prove u :e SNoR x. exact Hu. }
    prove - u < SNoCut L R.
    exact SNoCutP_SNoCut_L L R LLR (- u) LmuL. (** Using LLR here which was proven using IH **)
- prove SNoCutP L R. exact LLR.
Qed.

Theorem SNo_minus_SNo : forall x, SNo x -> SNo (- x).
let x. assume Hx.
apply minus_SNo_prop1 x Hx.
assume H. apply H. assume H. apply H.
assume H _ _ _. exact H.
Qed.

Theorem minus_SNo_Lt_contra : forall x y, SNo x -> SNo y -> x < y -> - y < - x.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hxy: x < y.
apply minus_SNo_prop1 x Hx.
assume H1. apply H1. assume H1. apply H1.
assume H1: SNo (- x).
assume H2: forall u :e SNoL x, - x < - u.
assume H3: forall u :e SNoR x, - u < - x.
assume _.
apply minus_SNo_prop1 y Hy.
assume H4. apply H4. assume H4. apply H4.
assume H4: SNo (- y).
assume H5: forall u :e SNoL y, - y < - u.
assume H6: forall u :e SNoR y, - u < - y.
assume _.
apply SNoLtE x y Hx Hy Hxy.
- let z. assume Hz: SNo z.
  assume Hz1: SNoLev z :e SNoLev x :/\: SNoLev y.
  assume Hz2: SNoEq_ (SNoLev z) z x.
  assume Hz3: SNoEq_ (SNoLev z) z y.
  assume Hz4: x < z.
  assume Hz5: z < y.
  assume Hz6: SNoLev z /:e x.
  assume Hz7: SNoLev z :e y.
  apply binintersectE (SNoLev x) (SNoLev y) (SNoLev z) Hz1.
  assume Hz1x Hz1y.
  prove - y < - x.
  apply SNoLt_tra (- y) (- z) (- x) H4 (SNo_minus_SNo z Hz) H1.
  + prove - y < - z.
    apply H5 z.
    prove z :e SNoL y.
    prove z :e {x :e SNoS_ (SNoLev y) | x < y}.
    apply SepI.
    * prove z :e SNoS_ (SNoLev y).
      exact SNoS_I2 z y Hz Hy Hz1y.
    * prove z < y. exact Hz5.
  + prove - z < - x.
    apply H3 z.
    prove z :e SNoR x.
    prove z :e {z :e SNoS_ (SNoLev x) | x < z}.
    apply SepI.
    * prove z :e SNoS_ (SNoLev x).
      exact SNoS_I2 z x Hz Hx Hz1x.
    * prove x < z. exact Hz4.
- assume H7: SNoLev x :e SNoLev y.
  assume H8: SNoEq_ (SNoLev x) x y.
  assume H9: SNoLev x :e y.
  apply H5 x.
  prove x :e SNoL y.
  prove x :e {x :e SNoS_ (SNoLev y) | x < y}.
  apply SepI.
  + prove x :e SNoS_ (SNoLev y).
    exact SNoS_I2 x y Hx Hy H7.
  + prove x < y. exact Hxy.
- assume H7: SNoLev y :e SNoLev x.
  assume H8: SNoEq_ (SNoLev y) x y.
  assume H9: SNoLev y /:e x.
  prove - y < - x.
  apply H3 y.
  prove y :e SNoR x.
  prove y :e {y :e SNoS_ (SNoLev x) | x < y}.
  apply SepI.
  + prove y :e SNoS_ (SNoLev x).
    exact SNoS_I2 y x Hy Hx H7.
  + prove x < y. exact Hxy.
Qed.

Theorem minus_SNo_Le_contra : forall x y, SNo x -> SNo y -> x <= y -> - y <= - x.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hxy: x <= y.
apply SNoLeE x y Hx Hy Hxy.
- assume H1: x < y.
  prove -y <= -x.
  apply SNoLtLe.
  prove -y < -x.
  exact minus_SNo_Lt_contra x y Hx Hy H1.
- assume H1: x = y.
  prove -y <= -x.
  rewrite H1.
  prove -y <= -y.
  apply SNoLe_ref.
Qed.

Theorem minus_SNo_SNoCutP : forall x, SNo x -> SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
let x. assume Hx: SNo x.
apply minus_SNo_prop1 x Hx.
assume H1. apply H1. assume H1. apply H1.
assume _ _ _ H1.
exact H1.
Qed.

Theorem minus_SNo_SNoCutP_gen : forall L R, SNoCutP L R -> SNoCutP {- z|z :e R} {- w|w :e L}.
let L R.
assume HLR: SNoCutP L R.
apply HLR. assume H. apply H.
assume HLR1: forall x :e L, SNo x.
assume HLR2: forall y :e R, SNo y.
assume HLR3: forall x :e L, forall y :e R, x < y.
set Lm := {- z|z :e R}.
set Rm := {- w|w :e L}.
prove (forall w :e Lm, SNo w)
   /\ (forall z :e Rm, SNo z)
   /\ (forall w :e Lm, forall z :e Rm, w < z).
apply and3I.
- let w. assume Hw: w :e Lm.
  prove SNo w.
  apply ReplE_impred R (fun z => - z) w Hw.
  let z.
  assume Hz: z :e R.
  assume Hwz: w = - z.
  rewrite Hwz.
  prove SNo (- z).
  apply SNo_minus_SNo.
  apply HLR2. exact Hz.
- let z. assume Hz: z :e Rm.
  prove SNo z.
  apply ReplE_impred L (fun w => - w) z Hz.
  let w.
  assume Hw: w :e L.
  assume Hzw: z = -w.
  rewrite Hzw.
  prove SNo (-w).
  apply SNo_minus_SNo.
  exact HLR1 w Hw.
- let w. assume Hw: w :e Lm.
  let z. assume Hz: z :e Rm.
  apply ReplE_impred R (fun z => - z) w Hw.
  let u.
  assume Hu: u :e R.
  assume Hwu: w = -u.
  apply ReplE_impred L (fun w => - w) z Hz.
  let v.
  assume Hv: v :e L.
  assume Hzv: z = -v.
  prove w < z.
  rewrite Hwu. rewrite Hzv.
  prove -u < -v.
  apply minus_SNo_Lt_contra v u (HLR1 v Hv) (HLR2 u Hu).
  prove v < u.
  exact HLR3 v Hv u Hu.
Qed.

Theorem minus_SNo_Lev_lem1 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, SNoLev (- x) c= SNoLev x.
apply ordinal_ind.
let alpha. assume Ha: ordinal alpha.
apply Ha. assume Ha1 Ha2.
assume IH: forall beta :e alpha, forall x :e SNoS_ beta, SNoLev (- x) c= SNoLev x.
let x. assume Hx: x :e SNoS_ alpha.
apply SNoS_E2 alpha Ha x Hx.
assume Hx1: SNoLev x :e alpha.
assume Hx2: ordinal (SNoLev x).
assume Hx3: SNo x.
assume Hx4: SNo_ (SNoLev x) x.
set L := {- z|z :e SNoR x}.
set R := {- w|w :e SNoL x}.
claim LLR: SNoCutP L R.
{ exact minus_SNo_SNoCutP x Hx3. }
prove SNoLev (- x) c= SNoLev x.
rewrite minus_SNo_eq x Hx3.
prove SNoLev (SNoCut L R) c= SNoLev x.
apply SNoCutP_SNoCut_impred L R LLR.
assume H2: SNo (SNoCut L R).
assume H3: SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume _ _ _.
claim L3: ordinal ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ apply ordinal_binunion.
  - apply ordinal_famunion.
    let w. assume Hw: w :e L.
    prove ordinal (ordsucc (SNoLev w)).
    apply ReplE_impred (SNoR x) (fun z => - z) w Hw.
    let u.
    assume Hu: u :e SNoR x.
    assume Hwu: w = - u.
    apply SNoR_E x Hx3 u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: x < u.
    apply ordinal_ordsucc.
    prove ordinal (SNoLev w).
    apply SNoLev_ordinal.
    prove SNo w.
    rewrite Hwu.
    exact SNo_minus_SNo u Hu1.
  - apply ordinal_famunion.
    let w. assume Hw: w :e R.
    prove ordinal (ordsucc (SNoLev w)).
    apply ReplE_impred (SNoL x) (fun z => - z) w Hw.
    let u.
    assume Hu: u :e SNoL x.
    assume Hwu: w = - u.
    apply SNoL_E x Hx3 u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: u < x.
    apply ordinal_ordsucc.
    prove ordinal (SNoLev w).
    apply SNoLev_ordinal.
    prove SNo w.
    rewrite Hwu.
    exact SNo_minus_SNo u Hu1.
}
claim L3a: TransSet ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ apply L3. assume H _. exact H. }
let beta. assume Hb: beta :e SNoLev (SNoCut L R).
claim Lb: beta :e ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ apply ordsuccE ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))) (SNoLev (SNoCut L R)) H3.
  - assume H4. exact L3a (SNoLev (SNoCut L R)) H4 beta Hb.
  - assume H4. rewrite <- H4. exact Hb.
}
prove beta :e SNoLev x.
apply binunionE (\/_ x :e L, ordsucc (SNoLev x)) (\/_ y :e R, ordsucc (SNoLev y)) beta Lb.
- assume H4: beta :e \/_ x :e L, ordsucc (SNoLev x).
  apply famunionE L (fun x => ordsucc (SNoLev x)) beta H4.
  let w. assume Hw. apply Hw.
  assume Hw1: w :e L.
  assume Hw2: beta :e ordsucc (SNoLev w).
  prove beta :e SNoLev x.
  apply ReplE_impred (SNoR x) (fun z => - z) w Hw1.
  let u.
  assume Hu: u :e SNoR x.
  assume Hwu: w = - u.
  apply SNoR_E x Hx3 u Hu.
  assume Hu1: SNo u.
  assume Hu2: SNoLev u :e SNoLev x.
  assume Hu3: x < u.
  claim Lu: u :e SNoS_ (ordsucc (SNoLev u)).
  { exact SNoS_SNoLev u Hu1. }
  claim LsLu: ordsucc (SNoLev u) :e alpha.
  { apply ordinal_ordsucc_In_eq (SNoLev x) (SNoLev u) Hx2 Hu2.
    - assume H2: ordsucc (SNoLev u) :e SNoLev x.
      exact Ha1 (SNoLev x) Hx1 (ordsucc (SNoLev u)) H2.
    - assume H2: SNoLev x = ordsucc (SNoLev u).
      rewrite <- H2. exact Hx1.
  }
  claim IHu: SNoLev (- u) c= SNoLev u.
  { exact IH (ordsucc (SNoLev u)) LsLu u Lu. }
  claim LLu: ordinal (SNoLev u).
  { exact SNoLev_ordinal u Hu1. }
  claim Lmu: SNo (- u).
  { exact SNo_minus_SNo u Hu1. }
  claim LLmu: ordinal (SNoLev (- u)).
  { exact SNoLev_ordinal (- u) Lmu. }
  claim LsLw: ordinal (ordsucc (SNoLev w)).
  { apply ordinal_ordsucc. rewrite Hwu. exact LLmu. }
  claim Lb: ordinal beta.
  { exact ordinal_Hered (ordsucc (SNoLev w)) LsLw beta Hw2. }
  apply ordinal_In_Or_Subq beta (SNoLev x) Lb Hx2.
  + assume H5: beta :e SNoLev x. exact H5.
  + assume H5: SNoLev x c= beta.
    prove False.
    claim LLub: SNoLev u :e beta.
    { exact H5 (SNoLev u) Hu2. }
    apply ordsuccE (SNoLev w) beta Hw2.
    * rewrite Hwu. assume H5: beta :e SNoLev (- u).
      apply In_no2cycle (SNoLev u) beta LLub.
      prove beta :e SNoLev u.
      exact IHu beta H5.
    * rewrite Hwu. assume H5: beta = SNoLev (- u).
      apply In_irref (SNoLev u).
      apply IHu (SNoLev u).
      prove SNoLev u :e SNoLev (- u). rewrite <- H5. exact LLub.
- assume H4: beta :e \/_ y :e R, ordsucc (SNoLev y).
  apply famunionE R (fun x => ordsucc (SNoLev x)) beta H4.
  let w. assume Hw. apply Hw.
  assume Hw1: w :e R.
  assume Hw2: beta :e ordsucc (SNoLev w).
  prove beta :e SNoLev x.
  apply ReplE_impred (SNoL x) (fun z => - z) w Hw1.
  let u.
  assume Hu: u :e SNoL x.
  assume Hwu: w = - u.
  apply SNoL_E x Hx3 u Hu.
  assume Hu1: SNo u.
  assume Hu2: SNoLev u :e SNoLev x.
  assume Hu3: u < x.
  claim Lu: u :e SNoS_ (ordsucc (SNoLev u)).
  { exact SNoS_SNoLev u Hu1. }
  claim LsLu: ordsucc (SNoLev u) :e alpha.
  { apply ordinal_ordsucc_In_eq (SNoLev x) (SNoLev u) Hx2 Hu2.
    - assume H2: ordsucc (SNoLev u) :e SNoLev x.
      exact Ha1 (SNoLev x) Hx1 (ordsucc (SNoLev u)) H2.
    - assume H2: SNoLev x = ordsucc (SNoLev u).
      rewrite <- H2. exact Hx1.
  }
  claim IHu: SNoLev (- u) c= SNoLev u.
  { exact IH (ordsucc (SNoLev u)) LsLu u Lu. }
  claim LLu: ordinal (SNoLev u).
  { exact SNoLev_ordinal u Hu1. }
  claim Lmu: SNo (- u).
  { exact SNo_minus_SNo u Hu1. }
  claim LLmu: ordinal (SNoLev (- u)).
  { exact SNoLev_ordinal (- u) Lmu. }
  claim LsLw: ordinal (ordsucc (SNoLev w)).
  { apply ordinal_ordsucc. rewrite Hwu. exact LLmu. }
  claim Lb: ordinal beta.
  { exact ordinal_Hered (ordsucc (SNoLev w)) LsLw beta Hw2. }
  apply ordinal_In_Or_Subq beta (SNoLev x) Lb Hx2.
  + assume H5: beta :e SNoLev x. exact H5.
  + assume H5: SNoLev x c= beta.
    prove False.
    claim LLub: SNoLev u :e beta.
    { exact H5 (SNoLev u) Hu2. }
    apply ordsuccE (SNoLev w) beta Hw2.
    * rewrite Hwu. assume H5: beta :e SNoLev (- u).
      apply In_no2cycle (SNoLev u) beta LLub.
      prove beta :e SNoLev u.
      exact IHu beta H5.
    * rewrite Hwu. assume H5: beta = SNoLev (- u).
      apply In_irref (SNoLev u).
      apply IHu (SNoLev u).
      prove SNoLev u :e SNoLev (- u). rewrite <- H5. exact LLub.
Qed.

Theorem minus_SNo_Lev_lem2 : forall x, SNo x -> SNoLev (- x) c= SNoLev x.
let x. assume Hx: SNo x.
claim LLx: ordinal (SNoLev x).
{ exact SNoLev_ordinal x Hx. }
claim LsLx: ordinal (ordsucc (SNoLev x)).
{ exact ordinal_ordsucc (SNoLev x) LLx. }
claim LxsLx: x :e SNoS_ (ordsucc (SNoLev x)).
{ exact SNoS_SNoLev x Hx. }
exact minus_SNo_Lev_lem1 (ordsucc (SNoLev x)) LsLx x LxsLx.
Qed.

Theorem minus_SNo_invol : forall x, SNo x -> - - x = x.
apply SNo_ind.
let L R.
assume HLR: SNoCutP L R.
assume IHL: forall x :e L, - - x = x.
assume IHR: forall y :e R, - - y = y.
apply HLR. assume H. apply H.
assume HLR1: forall x :e L, SNo x.
assume HLR2: forall y :e R, SNo y.
assume HLR3: forall x :e L, forall y :e R, x < y.
claim LCLR: SNo (SNoCut L R).
{ exact SNoCutP_SNo_SNoCut L R HLR. }
claim LmCLR: SNo (- SNoCut L R).
{ apply SNo_minus_SNo. exact LCLR. }
claim LmmCLR: SNo (- - SNoCut L R).
{ apply SNo_minus_SNo. exact LmCLR. }
claim L1: SNoLev (SNoCut L R) c= SNoLev (- - SNoCut L R)
       /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) (- - SNoCut L R).
{ apply SNoCutP_SNoCut_fst.
  - exact HLR.
  - prove SNo (- - SNoCut L R). exact LmmCLR.
  - prove forall x :e L, x < - - SNoCut L R.
    let x. assume Hx. rewrite <- IHL x Hx.
    claim Lx: SNo x.
    { exact HLR1 x Hx. }
    claim Lmx: SNo (- x).
    { exact SNo_minus_SNo x Lx. }
    prove - - x < - - SNoCut L R.
    apply minus_SNo_Lt_contra (- SNoCut L R) (- x) LmCLR Lmx.
    prove - SNoCut L R < - x.
    apply minus_SNo_Lt_contra x (SNoCut L R) Lx LCLR.
    prove x < SNoCut L R.
    exact SNoCutP_SNoCut_L L R HLR x Hx.
  - prove forall y :e R, - - SNoCut L R < y.
    let y. assume Hy. rewrite <- IHR y Hy.
    claim Ly: SNo y.
    { exact HLR2 y Hy. }
    claim Lmy: SNo (- y).
    { exact SNo_minus_SNo y Ly. }
    prove - - SNoCut L R < - - y.
    apply minus_SNo_Lt_contra (- y) (- SNoCut L R) Lmy LmCLR.
    prove - y < - SNoCut L R.
    apply minus_SNo_Lt_contra (SNoCut L R) y LCLR Ly.
    prove SNoCut L R < y.
    exact SNoCutP_SNoCut_R L R HLR y Hy.
}
apply L1.
assume L1a: SNoLev (SNoCut L R) c= SNoLev (- - SNoCut L R).
assume L1b: SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) (- - SNoCut L R).
prove - - SNoCut L R = SNoCut L R.
symmetry.
apply SNo_eq.
- exact LCLR.
- exact LmmCLR.
- prove SNoLev (SNoCut L R) = SNoLev (- - SNoCut L R).
  apply set_ext.
  + prove SNoLev (SNoCut L R) c= SNoLev (- - SNoCut L R).
    exact L1a.
  + prove SNoLev (- - SNoCut L R) c= SNoLev (SNoCut L R).
    apply Subq_tra (SNoLev (- - SNoCut L R)) (SNoLev (- SNoCut L R)) (SNoLev (SNoCut L R)).
    * prove SNoLev (- - SNoCut L R) c= SNoLev (- SNoCut L R).
      apply minus_SNo_Lev_lem2 (- SNoCut L R) LmCLR.
    * prove SNoLev (- SNoCut L R) c= SNoLev (SNoCut L R).
      apply minus_SNo_Lev_lem2 (SNoCut L R) LCLR.
- prove SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) (- - SNoCut L R).
  exact L1b.
Qed.

Theorem minus_SNo_Lev : forall x, SNo x -> SNoLev (- x) = SNoLev x.
let x. assume Hx.
apply set_ext.
- prove SNoLev (- x) c= SNoLev x.
  exact minus_SNo_Lev_lem2 x Hx.
- prove SNoLev x c= SNoLev (- x).
  rewrite <- minus_SNo_invol x Hx at 1.
  prove SNoLev (- - x) c= SNoLev (- x).
  exact minus_SNo_Lev_lem2 (- x) (SNo_minus_SNo x Hx).
Qed.

Theorem minus_SNo_SNo_ : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNo_ alpha (- x).
let alpha. assume Ha.
let x. assume Hx: SNo_ alpha x.
claim Lx: SNo x.
{ exact SNo_SNo alpha Ha x Hx. }
claim Lxa: SNoLev x = alpha.
{ exact SNoLev_uniq2 alpha Ha x Hx. }
claim Lmxa: SNoLev (- x) = alpha.
{ rewrite minus_SNo_Lev x Lx. exact Lxa. }
prove SNo_ alpha (- x).
rewrite <- Lmxa.
prove SNo_ (SNoLev (- x)) (- x).
apply SNoLev_.
prove SNo (- x).
exact SNo_minus_SNo x Lx.
Qed.

Theorem minus_SNo_SNoS_ : forall alpha, ordinal alpha -> forall x, x :e SNoS_ alpha -> - x :e SNoS_ alpha.
let alpha. assume Ha.
let x. assume Hx: x :e SNoS_ alpha.
apply SNoS_E2 alpha Ha x Hx.
assume Hx1: SNoLev x :e alpha.
assume Hx2: ordinal (SNoLev x).
assume Hx3: SNo x.
assume Hx4: SNo_ (SNoLev x) x.
claim Lbmx: SNo_ (SNoLev x) (- x).
{ exact minus_SNo_SNo_ (SNoLev x) Hx2 x Hx4. }
exact SNoS_I alpha Ha (- x) (SNoLev x) Hx1 Lbmx.
Qed.

Theorem minus_SNoCut_eq_lem : forall v, SNo v -> forall L R, SNoCutP L R -> v = SNoCut L R -> - v = SNoCut {- z|z :e R} {- w|w :e L}.
apply SNoLev_ind.
let v.
assume Hv: SNo v.
assume IHv: forall u :e SNoS_ (SNoLev v), forall L R, SNoCutP L R -> u = SNoCut L R -> - u = SNoCut {- z|z :e R} {- w|w :e L}.
let L R.
assume HLR: SNoCutP L R.
apply HLR. assume HLR1. apply HLR1.
assume HLR1: forall x :e L, SNo x.
assume HLR2: forall y :e R, SNo y.
assume HLR3: forall x :e L, forall y :e R, x < y.
assume HvLR: v = SNoCut L R.
set mL := {- w|w :e L}.
set mR := {- z|z :e R}.
set mLv := {- w|w :e SNoL v}.
set mRv := {- z|z :e SNoR v}.
claim L1: SNo (SNoCut L R).
{ exact SNoCutP_SNo_SNoCut L R HLR. }
claim L2: SNoCutP mR mL.
{ exact minus_SNo_SNoCutP_gen L R HLR. }
apply SNoCutP_SNoCut_impred mR mL L2.
assume H1: SNo (SNoCut mR mL).
assume H2: SNoLev (SNoCut mR mL) :e ordsucc ((\/_ x :e mR, ordsucc (SNoLev x)) :\/: (\/_ y :e mL, ordsucc (SNoLev y))).
assume H3: forall x :e mR, x < SNoCut mR mL.
assume H4: forall y :e mL, SNoCut mR mL < y.
assume H5: forall z, SNo z -> (forall x :e mR, x < z) -> (forall y :e mL, z < y) -> SNoLev (SNoCut mR mL) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut mR mL)) (SNoCut mR mL) z.
claim L3: forall x :e mR, x < - v.
{ let x. assume Hx: x :e mR.
  apply ReplE_impred R minus_SNo x Hx.
  let z.
  assume Hz: z :e R.
  assume Hxz: x = - z.
  prove x < - v.
  rewrite Hxz.
  prove - z < - v.
  apply minus_SNo_Lt_contra v z Hv (HLR2 z Hz).
  prove v < z.
  rewrite HvLR.
  prove SNoCut L R < z.
  exact SNoCutP_SNoCut_R L R HLR z Hz.
}
claim L4: forall y :e mL, - v < y.
{ let y. assume Hy: y :e mL.
  apply ReplE_impred L minus_SNo y Hy.
  let w.
  assume Hw: w :e L.
  assume Hyw: y = - w.
  prove - v < y.
  rewrite Hyw.
  prove - v < - w.
  apply minus_SNo_Lt_contra w v (HLR1 w Hw) Hv.
  prove w < v.
  rewrite HvLR.
  prove w < SNoCut L R.
  exact SNoCutP_SNoCut_L L R HLR w Hw.
}
apply H5 (- v) (SNo_minus_SNo v Hv) L3 L4.
assume H6: SNoLev (SNoCut mR mL) c= SNoLev (- v).
assume H7: SNoEq_ (SNoLev (SNoCut mR mL)) (SNoCut mR mL) (- v).
claim L5: ordinal (SNoLev (SNoCut mR mL)).
{ apply SNoLev_ordinal. exact H1. }
claim L6: ordinal (SNoLev (- v)).
{ apply SNoLev_ordinal. apply SNo_minus_SNo. exact Hv. }
apply ordinal_In_Or_Subq (SNoLev (SNoCut mR mL)) (SNoLev (- v)) L5 L6.
- assume H8: SNoLev (SNoCut mR mL) :e SNoLev (- v).
  prove False.
  claim L7: SNoCut mR mL :e SNoS_ (SNoLev v).
  { apply SNoS_I2.
    - prove SNo (SNoCut mR mL). exact H1.
    - prove SNo v. exact Hv.
    - prove SNoLev (SNoCut mR mL) :e SNoLev v.
      rewrite <- minus_SNo_Lev v Hv. exact H8.
  }
  claim LIH: - SNoCut mR mL = SNoCut {- z|z :e mL} {- w|w :e mR}.
  { exact IHv (SNoCut mR mL) L7 mR mL L2 (fun q H => H). }
  claim L8: {- z|z :e mL} = L.
  { apply Repl_invol_eq (fun x => x :e L) minus_SNo.
    - let x. assume Hx: x :e L.
      prove - - x = x.
      exact minus_SNo_invol x (HLR1 x Hx).
    - let x. assume Hx: x :e L. exact Hx.
  }
  claim L9: {- z|z :e mR} = R.
  { apply Repl_invol_eq (fun y => y :e R) minus_SNo.
    - let y. assume Hy: y :e R.
      prove - - y = y.
      exact minus_SNo_invol y (HLR2 y Hy).
    - let y. assume Hy: y :e R. exact Hy.
  }
  claim L10: - SNoCut mR mL = v.
  { rewrite LIH. rewrite L8. rewrite L9. symmetry. exact HvLR. }
  apply In_irref (SNoLev v).
  prove SNoLev v :e SNoLev v.
  rewrite <- L10 at 1.
  prove SNoLev (- SNoCut mR mL) :e SNoLev v.
  rewrite minus_SNo_Lev (SNoCut mR mL) H1.
  rewrite <- minus_SNo_Lev v Hv.
  exact H8.
- assume H8: SNoLev (- v) c= SNoLev (SNoCut mR mL).
  prove - v = SNoCut mR mL.
  symmetry.
  apply SNo_eq (SNoCut mR mL) (- v) H1 (SNo_minus_SNo v Hv).
  + prove SNoLev (SNoCut mR mL) = SNoLev (- v).
    apply set_ext.
    * exact H6.
    * exact H8.
  + prove SNoEq_ (SNoLev (SNoCut mR mL)) (SNoCut mR mL) (- v).
    exact H7.
Qed.

Theorem minus_SNoCut_eq : forall L R, SNoCutP L R -> - SNoCut L R = SNoCut {- z|z :e R} {- w|w :e L}.
let L R. assume HLR.
exact minus_SNoCut_eq_lem (SNoCut L R) (SNoCutP_SNo_SNoCut L R HLR) L R HLR (fun q H => H).
Qed.

Theorem minus_SNo_Lt_contra1 : forall x y, SNo x -> SNo y -> -x < y -> - y < x.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hxy: -x < y.
prove -y < x.
rewrite <- minus_SNo_invol x Hx.
prove -y < --x.
apply minus_SNo_Lt_contra (-x) y (SNo_minus_SNo x Hx) Hy.
prove -x < y.
exact Hxy.
Qed.

Theorem minus_SNo_Lt_contra2 : forall x y, SNo x -> SNo y -> x < -y -> y < - x.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hxy: x < -y.
prove y < -x.
rewrite <- minus_SNo_invol y Hy.
prove --y < -x.
apply minus_SNo_Lt_contra x (-y) Hx (SNo_minus_SNo y Hy).
prove x < -y.
exact Hxy.
Qed.

Theorem mordinal_SNoLev_min_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> - alpha <= z.
let alpha. assume Ha.
let z. assume Hz: SNo z.
assume H1: SNoLev z :e ordsucc alpha.
claim Lz1: SNo (-z).
{ exact SNo_minus_SNo z Hz. }
claim Lz2: SNoLev (-z) :e ordsucc alpha.
{ rewrite minus_SNo_Lev z Hz. exact H1. }
prove -alpha <= z.
rewrite <- minus_SNo_invol z Hz.
prove -alpha <= --z.
apply minus_SNo_Le_contra (-z) alpha Lz1 (ordinal_SNo alpha Ha).
prove -z <= alpha.
exact ordinal_SNoLev_max_2 alpha Ha (-z) Lz1 Lz2.
Qed.

Theorem minus_SNo_SNoS_omega : forall x :e SNoS_ omega, - x :e SNoS_ omega.
let x. assume Hx.
apply SNoS_E2 omega omega_ordinal x Hx.
assume Hx1: SNoLev x :e omega.
assume Hx2: ordinal (SNoLev x).
assume Hx3: SNo x.
assume Hx4: SNo_ (SNoLev x) x.
apply SNoS_I omega omega_ordinal (- x) (SNoLev (- x)).
- prove SNoLev (- x) :e omega.
  rewrite minus_SNo_Lev x Hx3.
  prove SNoLev x :e omega.
  exact Hx1.
- prove SNo_ (SNoLev (- x)) (- x).
  apply SNoLev_. exact SNo_minus_SNo x Hx3.
Qed.

Theorem SNoL_minus_SNoR: forall x, SNo x -> SNoL (- x) = {- w|w :e SNoR x}.
let x. assume Hx.
claim Lmx: SNo (- x).
{ exact SNo_minus_SNo x Hx. }
apply set_ext.
- let z. assume Hz: z :e SNoL (- x).
  apply SNoL_E (- x) Lmx z Hz.
  assume Hz1: SNo z.
  rewrite minus_SNo_Lev x Hx.
  assume Hz2: SNoLev z :e SNoLev x.
  assume Hz3: z < - x.
  prove z :e {- w|w :e SNoR x}.
  rewrite <- minus_SNo_invol z Hz1.
  apply ReplI.
  prove - z :e SNoR x.
  apply SNoR_I x Hx (- z) (SNo_minus_SNo z Hz1).
  + prove SNoLev (-z) :e SNoLev x.
    rewrite minus_SNo_Lev z Hz1. exact Hz2.
  + prove x < - z.
    apply minus_SNo_Lt_contra2 z x Hz1 Hx.
    exact Hz3.
- let z. assume Hz: z :e {- w|w :e SNoR x}.
  apply ReplE_impred (SNoR x) minus_SNo z Hz.
  let w. assume Hw: w :e SNoR x.
  assume Hzw: z = - w.
  prove z :e SNoL (- x).
  rewrite Hzw.
  prove - w :e SNoL (- x).
  apply SNoR_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: x < w.
  apply SNoL_I (- x) Lmx (- w) (SNo_minus_SNo w Hw1).
  + prove SNoLev (- w) :e SNoLev (- x).
    rewrite minus_SNo_Lev w Hw1.
    rewrite minus_SNo_Lev x Hx.
    exact Hw2.
  + prove - w < - x.
    apply minus_SNo_Lt_contra x w Hx Hw1.
    exact Hw3.
Qed.

End SurrealMinus.

Opaque minus_SNo.
