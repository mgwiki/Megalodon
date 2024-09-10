(** Part 7 **)
Section Int.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Definition int : set := omega :\/: {- n|n :e omega}.

Theorem int_SNo_cases : forall p:set -> prop,
    (forall n :e omega, p n)
 -> (forall n :e omega, p (- n))
 -> forall x :e int, p x.
let p. assume Hp1 Hp2.
let x. assume Hx. prove p x.
apply binunionE omega {- n|n :e omega} x Hx.
- assume Hx: x :e omega. exact Hp1 x Hx.
- assume Hx. apply ReplE_impred omega minus_SNo x Hx.
  let n. assume Hn: n :e omega.
  assume Hxn: x = - n.
  rewrite Hxn. exact Hp2 n Hn.
Qed.

Theorem int_3_cases: forall n :e int, forall p:prop,
    (forall m :e omega, n = - ordsucc m -> p)
 -> (n = 0 -> p)
 -> (forall m :e omega, n = ordsucc m -> p)
 -> p.
apply int_SNo_cases.
- let m. assume Hm: m :e omega.
  let p. assume Hneg H0 Hpos.
  claim L1: forall k, nat_p k -> m = ordsucc k -> p.
  { let k. assume Hk HmSk.
    exact Hpos k (nat_p_omega k Hk) HmSk.
  }
  exact nat_inv_impred (fun k => m = k -> p) H0 L1 m (omega_nat_p m Hm) (fun q H => H).
- let m. assume Hm: m :e omega.
  let p.
  assume Hneg: forall k :e omega, - m = - ordsucc k -> p.
  assume H0: - m = 0 -> p.
  assume Hpos: forall k :e omega, - m = ordsucc k -> p.
  claim L2: m = 0 -> p.
  { assume Hm0. apply H0. rewrite Hm0. exact minus_SNo_0. }
  claim L3: forall k, nat_p k -> m = ordsucc k -> p.
  { let k. assume Hk HmSk.
    apply Hneg k (nat_p_omega k Hk).
    prove - m = - ordsucc k.
    f_equal. exact HmSk.
  }
  apply nat_inv_impred (fun k => m = k -> p) L2 L3 m (omega_nat_p m Hm) (fun q H => H).
Qed.

Theorem int_SNo : forall x :e int, SNo x.
apply int_SNo_cases.
- exact omega_SNo.
- let n. assume Hn. prove SNo (- n).
  apply SNo_minus_SNo.
  prove SNo n. exact omega_SNo n Hn.
Qed.

Theorem Subq_omega_int : omega c= int.
let n. assume Hn.
prove n :e omega :\/: {- k|k :e omega}.
apply binunionI1.
exact Hn.
Qed.

Theorem int_minus_SNo_omega : forall n :e omega, - n :e int.
let n. assume Hn.
prove - n :e omega :\/: {- k|k :e omega}.
apply binunionI2.
prove - n :e {- k|k :e omega}.
apply ReplI. exact Hn.
Qed.

Theorem int_add_SNo_lem: forall n :e omega, forall m, nat_p m -> - n + m :e int.
let n. assume Hn.
claim Lnn: nat_p n.
{ exact omega_nat_p n Hn. }
claim Lno: ordinal n.
{ exact nat_p_ordinal n Lnn. }
claim LnS: SNo n.
{ exact ordinal_SNo n Lno. }
apply nat_ind.
- prove - n + 0 :e int. rewrite add_SNo_0R (- n) (SNo_minus_SNo n LnS).
  prove - n :e int.
  apply int_minus_SNo_omega.
  exact Hn.
- let m. assume Hm: nat_p m.
  assume IHm: - n + m :e int.
  claim Lmo: ordinal m.
  { exact nat_p_ordinal m Hm. }
  claim LmS: SNo m.
  { exact ordinal_SNo m Lmo. }
  prove - n + ordsucc m :e int.
  rewrite ordinal_ordsucc_SNo_eq m Lmo.
  prove - n + (1 + m) :e int.
  rewrite add_SNo_com_3_0_1 (- n) 1 m (SNo_minus_SNo n LnS) SNo_1 LmS.
  prove 1 + (- n + m) :e int.
  claim L1: forall k :e omega, - n + m = k -> 1 + (- n + m) :e int.
  { let k. assume Hk He.
    rewrite He. prove 1 + k :e int.
    rewrite <- ordinal_ordsucc_SNo_eq k (nat_p_ordinal k (omega_nat_p k Hk)).
    prove ordsucc k :e int. apply Subq_omega_int. apply omega_ordsucc. exact Hk.    
  }
  claim L2: forall k :e omega, - n + m = - k -> 1 + (- n + m) :e int.
  { let k. assume Hk He. rewrite He.
    prove 1 + - k :e int.
    apply nat_inv k (omega_nat_p k Hk).
    - assume H1: k = 0. rewrite H1. rewrite minus_SNo_0.
      rewrite add_SNo_0R 1 SNo_1.
      prove 1 :e int.
      apply Subq_omega_int.
      prove 1 :e omega.
      exact nat_p_omega 1 nat_1.
    - assume H1. apply H1. let k'. assume H1. apply H1.
      assume H1: nat_p k'.
      assume H2: k = ordsucc k'.
      rewrite H2.
      prove 1 + - (ordsucc k') :e int.
      rewrite ordinal_ordsucc_SNo_eq k' (nat_p_ordinal k' H1).
      prove 1 + - (1 +  k') :e int.
      rewrite minus_add_SNo_distr 1 k' SNo_1 (ordinal_SNo k' (nat_p_ordinal k' H1)).
      prove 1 + - 1 +  - k' :e int.
      rewrite add_SNo_minus_L2' 1 (- k') SNo_1 (SNo_minus_SNo k' (ordinal_SNo k' (nat_p_ordinal k' H1))).
      prove - k' :e int. apply int_minus_SNo_omega. exact nat_p_omega k' H1.
  }
  apply int_SNo_cases (fun x => - n + m = x -> 1 + (- n + m) :e int) L1 L2 (- n + m) IHm.
  reflexivity.
Qed.

Theorem int_add_SNo: forall x y :e int, x + y :e int.
apply int_SNo_cases.
- let n. assume Hn: n :e omega.
  apply int_SNo_cases.
  + let m. assume Hm: m :e omega. apply Subq_omega_int.
    prove n + m :e omega. exact add_SNo_In_omega n Hn m Hm.
  + let m. assume Hm: m :e omega.
    prove n + - m :e int.
    rewrite add_SNo_com n (- m)
                        (ordinal_SNo n (nat_p_ordinal n (omega_nat_p n Hn)))
                        (SNo_minus_SNo m (ordinal_SNo m (nat_p_ordinal m (omega_nat_p m Hm)))).
    prove - m + n :e int.
    exact int_add_SNo_lem m Hm n (omega_nat_p n Hn).
- let n. assume Hn: n :e omega.
  apply int_SNo_cases.
  + let m. assume Hm: m :e omega.
    prove - n + m :e int.
    exact int_add_SNo_lem n Hn m (omega_nat_p m Hm).
  + let m. assume Hm: m :e omega.
    prove - n + - m :e int.
    claim Ln: SNo n.
    { exact ordinal_SNo n (nat_p_ordinal n (omega_nat_p n Hn)). }
    claim Lm: SNo m.
    { exact ordinal_SNo m (nat_p_ordinal m (omega_nat_p m Hm)). }
    rewrite <- minus_add_SNo_distr n m Ln Lm.
    apply int_minus_SNo_omega.
    prove n + m :e omega. exact add_SNo_In_omega n Hn m Hm.
Qed.

Theorem int_minus_SNo: forall x :e int, - x :e int.
apply int_SNo_cases.
- let n. assume Hn. prove - n :e int.
  apply int_minus_SNo_omega. exact Hn.
- let n. assume Hn. prove - - n :e int.
  rewrite minus_SNo_invol n (ordinal_SNo n (nat_p_ordinal n (omega_nat_p n Hn))).
  prove n :e int. apply Subq_omega_int. exact Hn.
Qed.

Theorem int_mul_SNo: forall x y :e int, x * y :e int.
apply int_SNo_cases.
- let n. assume Hn: n :e omega.
  claim Lnn: nat_p n.
  { exact omega_nat_p n Hn. }
  claim Lno: ordinal n.
  { exact nat_p_ordinal n Lnn. }
  claim LnS: SNo n.
  { exact ordinal_SNo n Lno. }
  apply int_SNo_cases.
  + let m. assume Hm: m :e omega. apply Subq_omega_int.
    prove n * m :e omega. exact mul_SNo_In_omega n Hn m Hm.
  + let m. assume Hm: m :e omega.
    claim Lmn: nat_p m.
    { exact omega_nat_p m Hm. }
    claim Lmo: ordinal m.
    { exact nat_p_ordinal m Lmn. }
    claim LmS: SNo m.
    { exact ordinal_SNo m Lmo. }
    prove n * (- m) :e int.
    rewrite mul_SNo_com n (- m) LnS (SNo_minus_SNo m LmS).
    prove (- m) * n :e int.
    rewrite mul_SNo_minus_distrL m n LmS LnS.
    prove - (m * n) :e int.
    apply int_minus_SNo.
    prove m * n :e int.
    apply Subq_omega_int.
    exact mul_SNo_In_omega m Hm n Hn.
- let n. assume Hn: n :e omega.
  claim Lnn: nat_p n.
  { exact omega_nat_p n Hn. }
  claim Lno: ordinal n.
  { exact nat_p_ordinal n Lnn. }
  claim LnS: SNo n.
  { exact ordinal_SNo n Lno. }
  apply int_SNo_cases.
  + let m. assume Hm: m :e omega.
    claim Lmn: nat_p m.
    { exact omega_nat_p m Hm. }
    claim Lmo: ordinal m.
    { exact nat_p_ordinal m Lmn. }
    claim LmS: SNo m.
    { exact ordinal_SNo m Lmo. }
    prove (- n) * m :e int.
    rewrite mul_SNo_minus_distrL n m LnS LmS.
    prove - (n * m) :e int.
    apply int_minus_SNo.
    prove n * m :e int.
    apply Subq_omega_int.
    exact mul_SNo_In_omega n Hn m Hm.
  + let m. assume Hm: m :e omega.
    claim Lmn: nat_p m.
    { exact omega_nat_p m Hm. }
    claim Lmo: ordinal m.
    { exact nat_p_ordinal m Lmn. }
    claim LmS: SNo m.
    { exact ordinal_SNo m Lmo. }
    prove (- n) * (- m) :e int.
    rewrite mul_SNo_minus_distrL n (- m) LnS (SNo_minus_SNo m LmS).
    prove - (n * (- m)) :e int.
    rewrite mul_SNo_com n (- m) LnS (SNo_minus_SNo m LmS).
    prove - ((- m) * n) :e int.
    rewrite mul_SNo_minus_distrL m n LmS LnS.
    prove - - (m * n) :e int.
    rewrite minus_SNo_invol (m * n) (SNo_mul_SNo m n LmS LnS).
    prove m * n :e int. apply Subq_omega_int.
    prove m * n :e omega. exact mul_SNo_In_omega m Hm n Hn.
Qed.

End Int.

Section SurrealAbs.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(* Parameter abs_SNo "9f9389c36823b2e0124a7fe367eb786d080772b5171a5d059b10c47361cef0ef" "34f6dccfd6f62ca020248cdfbd473fcb15d8d9c5c55d1ec7c5ab6284006ff40f" *)
Definition abs_SNo : set -> set := fun x => if 0 <= x then x else - x.

Theorem nonneg_abs_SNo : forall x, 0 <= x -> abs_SNo x = x.
let x. assume Hx.
exact If_i_1 (0 <= x) x (- x) Hx.
Qed.

Theorem not_nonneg_abs_SNo : forall x, ~(0 <= x) -> abs_SNo x = - x.
let x. assume Hx.
exact If_i_0 (0 <= x) x (- x) Hx.
Qed.

Theorem abs_SNo_0 : abs_SNo 0 = 0.
apply nonneg_abs_SNo. prove 0 <= 0. apply SNoLe_ref.
Qed.

Theorem pos_abs_SNo : forall x, 0 < x -> abs_SNo x = x.
let x. assume Hx.
apply nonneg_abs_SNo. prove 0 <= x.
apply SNoLtLe. exact Hx.
Qed.

Theorem neg_abs_SNo : forall x, SNo x -> x < 0 -> abs_SNo x = - x.
let x. assume Hx1 Hx2.
apply not_nonneg_abs_SNo.
assume H1: 0 <= x.
prove False.
apply SNoLt_irref x.
prove x < x.
exact SNoLtLe_tra x 0 x Hx1 SNo_0 Hx1 Hx2 H1.
Qed.

Theorem SNo_abs_SNo : forall x, SNo x -> SNo (abs_SNo x).
let x. assume Hx.
apply xm (0 <= x).
- assume H1. rewrite nonneg_abs_SNo x H1. exact Hx.
- assume H1. rewrite not_nonneg_abs_SNo x H1.
  apply SNo_minus_SNo. exact Hx.
Qed.

Theorem abs_SNo_Lev : forall x, SNo x -> SNoLev (abs_SNo x) = SNoLev x.
let x. assume Hx.
apply xm (0 <= x).
- assume H1. rewrite nonneg_abs_SNo x H1. reflexivity.
- assume H1. rewrite not_nonneg_abs_SNo x H1.
  apply minus_SNo_Lev. exact Hx.
Qed.

Theorem abs_SNo_minus: forall x, SNo x -> abs_SNo (- x) = abs_SNo x.
let x. assume Hx.
apply SNoLtLe_or x 0 Hx SNo_0.
- assume H1: x < 0. rewrite neg_abs_SNo x Hx H1.
  prove abs_SNo (- x) = - x.
  claim L1: 0 <= - x.
  { apply SNoLtLe. prove 0 < - x.
    apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
    prove x < - 0. rewrite minus_SNo_0. exact H1.
  }
  exact nonneg_abs_SNo (- x) L1.
- assume H1: 0 <= x.
  apply SNoLtLe_or (- x) 0 (SNo_minus_SNo x Hx) SNo_0.
  + assume H2: - x < 0.
    rewrite nonneg_abs_SNo x H1.
    rewrite neg_abs_SNo (- x) (SNo_minus_SNo x Hx) H2.
    prove - - x = x.
    exact minus_SNo_invol x Hx.
  + assume H2: 0 <= - x.
    claim L2: x = 0.
    { apply SNoLe_antisym x 0 Hx SNo_0.
      - prove x <= 0.
        rewrite <- minus_SNo_0.
        rewrite <- minus_SNo_invol x Hx.
        prove - - x <= - 0.
        apply minus_SNo_Le_contra 0 (- x) SNo_0 (SNo_minus_SNo x Hx).
        prove 0 <= - x. exact H2.
      - prove 0 <= x. exact H1.
    }
    rewrite L2. f_equal. exact minus_SNo_0.
Qed.

Theorem abs_SNo_dist_swap: forall x y, SNo x -> SNo y -> abs_SNo (x + - y) = abs_SNo (y + - x).
let x y. assume Hx Hy.
claim Lmx: SNo (- x).
{ apply SNo_minus_SNo. exact Hx. }
claim Lmy: SNo (- y).
{ apply SNo_minus_SNo. exact Hy. }
claim Lymx: SNo (y + - x).
{ exact SNo_add_SNo y (- x) Hy Lmx. }
transitivity abs_SNo (- (y + - x)).
- f_equal. prove x + - y = - (y + - x).
  rewrite minus_add_SNo_distr y (- x) Hy Lmx.
  prove x + - y = - y + - - x.
  rewrite minus_SNo_invol x Hx.
  prove x + - y = - y + x.
  exact add_SNo_com x (- y) Hx Lmy.
- exact abs_SNo_minus (y + - x) Lymx.
Qed.

Theorem SNo_triangle: forall x y, SNo x -> SNo y -> abs_SNo (x + y) <= abs_SNo x + abs_SNo y.
let x y. assume Hx Hy.
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim Lmx: SNo (- x).
{ apply SNo_minus_SNo. exact Hx. }
claim Lmy: SNo (- y).
{ apply SNo_minus_SNo. exact Hy. }
apply SNoLtLe_or x 0 Hx SNo_0.
- assume H1: x < 0. rewrite neg_abs_SNo x Hx H1.
  apply SNoLtLe_or y 0 Hy SNo_0.
  + assume H2: y < 0. rewrite neg_abs_SNo y Hy H2.
    prove abs_SNo (x + y) <= - x + - y.
    claim L1: x + y < 0.
    { rewrite <- add_SNo_0L 0 SNo_0.
      prove x + y < 0 + 0.
      exact add_SNo_Lt3 x y 0 0 Hx Hy SNo_0 SNo_0 H1 H2.
    }
    rewrite neg_abs_SNo (x + y) Lxy L1.
    prove - (x + y) <= - x + - y.
    rewrite minus_add_SNo_distr x y Hx Hy.
    apply SNoLe_ref.
  + assume H2: 0 <= y. rewrite nonneg_abs_SNo y H2.
    prove abs_SNo (x + y) <= - x + y.
    apply xm (0 <= x + y).
    * assume H3. rewrite nonneg_abs_SNo (x + y) H3.
      prove x + y <= - x + y.
      apply add_SNo_Le1 x y (- x) Hx Hy Lmx.
      prove x <= - x.
      apply SNoLtLe.
      prove x < - x.
      apply SNoLt_tra x 0 (- x) Hx SNo_0 Lmx H1.
      prove 0 < - x.
      apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
      prove x < - 0.
      rewrite minus_SNo_0. exact H1.
    * assume H3. rewrite not_nonneg_abs_SNo (x + y) H3.
      prove - (x + y) <= - x + y.
      rewrite minus_add_SNo_distr x y Hx Hy.
      prove - x + - y <= - x + y.
      apply add_SNo_Le2 (- x) (- y) y Lmx Lmy Hy.
      prove - y <= y.
      claim L2: - y <= 0.
      { rewrite <- minus_SNo_0.
        exact minus_SNo_Le_contra 0 y SNo_0 Hy H2.
      }
      exact SNoLe_tra (- y) 0 y Lmy SNo_0 Hy L2 H2.
- assume H1: 0 <= x. rewrite nonneg_abs_SNo x H1.
  apply SNoLtLe_or y 0 Hy SNo_0.
  + assume H2: y < 0. rewrite neg_abs_SNo y Hy H2.
    prove abs_SNo (x + y) <= x + - y.
    apply xm (0 <= x + y).
    * assume H3. rewrite nonneg_abs_SNo (x + y) H3.
      prove x + y <= x + - y.
      apply add_SNo_Le2 x y (- y) Hx Hy Lmy.
      prove y <= - y.
      apply SNoLtLe.
      prove y < - y.
      apply SNoLt_tra y 0 (- y) Hy SNo_0 Lmy H2.
      prove 0 < - y.
      apply minus_SNo_Lt_contra2 y 0 Hy SNo_0.
      prove y < - 0.
      rewrite minus_SNo_0. exact H2.
    * assume H3. rewrite not_nonneg_abs_SNo (x + y) H3.
      prove - (x + y) <= x + - y.
      rewrite minus_add_SNo_distr x y Hx Hy.
      prove - x + - y <= x + - y.
      apply add_SNo_Le1 (- x) (- y) x Lmx Lmy Hx.
      prove - x <= x.
      claim L3: - x <= 0.
      { rewrite <- minus_SNo_0.
        exact minus_SNo_Le_contra 0 x SNo_0 Hx H1.
      }
      exact SNoLe_tra (- x) 0 x Lmx SNo_0 Hx L3 H1.
  + assume H2: 0 <= y. rewrite nonneg_abs_SNo y H2.
    prove abs_SNo (x + y) <= x + y.
    claim L1: 0 <= x + y.
    { rewrite <- add_SNo_0L 0 SNo_0.
      prove 0 + 0 <= x + y.
      exact add_SNo_Le3 0 0 x y SNo_0 SNo_0 Hx Hy H1 H2.
    }
    rewrite nonneg_abs_SNo (x + y) L1.
    apply SNoLe_ref.
Qed.

Theorem SNo_triangle2: forall x y z, SNo x -> SNo y -> SNo z -> abs_SNo (x + - z) <= abs_SNo (x + - y) + abs_SNo (y + - z).
let x y z. assume Hx Hy Hz.
claim Lmy: SNo (- y).
{ apply SNo_minus_SNo. exact Hy. }
claim Lmz: SNo (- z).
{ apply SNo_minus_SNo. exact Hz. }
claim L1: x + - z = (x + - y) + (y + - z).
{ rewrite <- add_SNo_assoc x (- y) (y + - z) Hx Lmy (SNo_add_SNo y (- z) Hy Lmz).
  prove x + - z = x + (- y + y + - z).
  f_equal. symmetry.
  exact add_SNo_minus_L2 y (- z) Hy Lmz.
}
rewrite L1.
apply SNo_triangle.
- apply SNo_add_SNo.
  + exact Hx.
  + exact Lmy.
- apply SNo_add_SNo.
  + exact Hy.
  + exact Lmz.
Qed.

End SurrealAbs.

Section SNoMaxMin.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Definition SNo_max_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> y <= x.
Definition SNo_min_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> x <= y.

Theorem minus_SNo_max_min : forall X y, (forall x :e X, SNo x) -> SNo_max_of X y -> SNo_min_of {- x|x :e X} (- y).
let X y. assume HX H1.
apply H1. assume H. apply H.
assume H1a: y :e X.
assume H1b: SNo y.
assume H1c: forall z :e X, SNo z -> z <= y.
prove - y :e {- x|x :e X} /\ SNo (- y) /\ (forall z :e {- x|x :e X}, SNo z -> - y <= z).
apply and3I.
- apply ReplI. exact H1a.
- exact SNo_minus_SNo y H1b.
- let z. assume Hz1: z :e {- x|x :e X}.
  assume Hz2: SNo z.
  apply ReplE_impred X (fun x => - x) z Hz1.
  let x. assume Hx: x :e X.
  assume Hze: z = - x.
  rewrite Hze.
  prove - y <= - x.
  apply minus_SNo_Le_contra x y (HX x Hx) H1b.
  prove x <= y. exact H1c x Hx (HX x Hx).
Qed.

Theorem minus_SNo_max_min' : forall X y, (forall x :e X, SNo x) -> SNo_max_of {- x|x :e X} y -> SNo_min_of X (- y).
let X y. assume HX H1.
claim L1: {- z|z :e {- x|x :e X}} = X.
{ apply Repl_invol_eq SNo minus_SNo.
  - prove forall x, SNo x -> - - x = x. exact minus_SNo_invol.
  - prove forall x :e X, SNo x. exact HX.
}
claim L2: forall z :e {- x|x :e X}, SNo z.
{ let z. assume Hz.
  apply ReplE_impred X (fun x => - x) z Hz.
  let x. assume Hx: x :e X.
  assume Hzx: z = - x.
  rewrite Hzx. apply SNo_minus_SNo.
  prove SNo x. exact HX x Hx.
}
rewrite <- L1.
exact minus_SNo_max_min {- x|x :e X} y L2 H1.
Qed.

Theorem minus_SNo_min_max : forall X y, (forall x :e X, SNo x) -> SNo_min_of X y -> SNo_max_of {- x|x :e X} (- y).
let X y. assume HX H1.
apply H1. assume H. apply H.
assume H1a: y :e X.
assume H1b: SNo y.
assume H1c: forall z :e X, SNo z -> y <= z.
prove - y :e {- x|x :e X} /\ SNo (- y) /\ (forall z :e {- x|x :e X}, SNo z -> z <= - y).
apply and3I.
- apply ReplI. exact H1a.
- exact SNo_minus_SNo y H1b.
- let z. assume Hz1: z :e {- x|x :e X}.
  assume Hz2: SNo z.
  apply ReplE_impred X (fun x => - x) z Hz1.
  let x. assume Hx: x :e X.
  assume Hze: z = - x.
  rewrite Hze.
  prove -x <= - y.
  apply minus_SNo_Le_contra y x H1b (HX x Hx).
  prove y <= x. exact H1c x Hx (HX x Hx).
Qed.

Theorem double_SNo_max_1 : forall x y, SNo x -> SNo_max_of (SNoL x) y -> forall z, SNo z -> x < z -> y + z < x + x -> exists w :e SNoR z, y + w = x + x.
let x y. assume Hx Hy.
apply Hy. assume H. apply H.
assume Hy1: y :e SNoL x.
assume Hy2: SNo y.
assume Hy3: forall w :e SNoL x, SNo w -> w <= y.
apply SNoL_E x Hx y Hy1.
assume Hy1a.
assume Hy1b: SNoLev y :e SNoLev x.
assume Hy1c: y < x.
apply SNoLev_ind.
let z. assume Hz: SNo z.
assume IH: forall w :e SNoS_ (SNoLev z), x < w -> y + w < x + x -> exists u :e SNoR w, y + u = x + x.
assume H1: x < z.
assume H2: y + z < x + x.
prove exists w :e SNoR z, y + w = x + x.
claim Lxx: SNo (x + x).
{ exact SNo_add_SNo x x Hx Hx. }
claim Lyz: SNo (y + z).
{ exact SNo_add_SNo y z Hy2 Hz. }
claim L1: forall w :e SNoR y, w + z <= x + x -> False.
{ let w. assume Hw.
  assume H3: w + z <= x + x.
  apply SNoR_E y Hy2 w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  assume Hw3: y < w.
  apply SNoLt_irref (x + x).
  prove x + x < x + x.
  apply SNoLtLe_tra (x + x) (w + z) (x + x) Lxx (SNo_add_SNo w z Hw1 Hz) Lxx.
  - prove x + x < w + z.
    apply add_SNo_Lt3b x x w z Hx Hx Hw1 Hz.
    + prove x <= w.
      apply SNoLtLe_or w x Hw1 Hx.
      * assume H4: w < x.
        claim L1a: w :e SNoL x.
        { apply SNoL_I x Hx w Hw1.
          - prove SNoLev w :e SNoLev x.
            exact ordinal_TransSet (SNoLev x) (SNoLev_ordinal x Hx) (SNoLev y) Hy1b (SNoLev w) Hw2.
          - prove w < x. exact H4.
        }
        apply SNoLt_irref y.
        prove y < y.
        apply SNoLtLe_tra y w y Hy2 Hw1 Hy2 Hw3.
        prove w <= y.
        exact Hy3 w L1a Hw1.
      * assume H4: x <= w. exact H4.
    + prove x < z. exact H1.
  - prove w + z <= x + x. exact H3.
}
claim L2: forall w :e SNoL x, y + z <= w + x -> False.
{ let w. assume Hw.
  assume H3: y + z <= w + x.
  apply SNoL_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: w < x.
  apply SNoLt_irref (w + x).
  prove w + x < w + x.
  apply SNoLtLe_tra (w + x) (w + z) (w + x)
                    (SNo_add_SNo w x Hw1 Hx)
                    (SNo_add_SNo w z Hw1 Hz)
                    (SNo_add_SNo w x Hw1 Hx).
  - prove w + x < w + z.
    apply add_SNo_Lt2 w x z Hw1 Hx Hz.
    prove x < z. exact H1.
  - prove w + z <= w + x.
    apply SNoLe_tra (w + z) (y + z) (w + x)
                    (SNo_add_SNo w z Hw1 Hz)
                    Lyz
                    (SNo_add_SNo w x Hw1 Hx).
    + prove w + z <= y + z.
      apply add_SNo_Le1 w z y Hw1 Hz Hy2.
      prove w <= y.
      exact Hy3 w Hw Hw1.
    + prove y + z <= w + x. exact H3.
}
claim L3: forall w :e SNoR z, y + w < x + x -> exists w :e SNoR z, y + w = x + x.
{ let w.
  assume Hw: w :e SNoR z.
  assume H4: y + w < x + x.
  apply SNoR_E z Hz w Hw.
  assume Hw1: SNo w.
  assume Hw2.
  assume Hw3: z < w.
  claim LIH: exists u :e SNoR w, y + u = x + x.
  { apply IH w (SNoR_SNoS_ z w Hw).
    - prove x < w. exact SNoLt_tra x z w Hx Hz Hw1 H1 Hw3.
    - prove y + w < x + x. exact H4.
  }
  apply LIH.
  let u. assume H. apply H.
  assume Hu1: u :e SNoR w.
  assume Hu2: y + u = x + x.
  apply SNoR_E w Hw1 u Hu1.
  assume Hu1a Hu1b Hu1c.
  witness u. apply andI.
  - prove u :e SNoR z.
    apply SNoR_I z Hz u Hu1a.
    + prove SNoLev u :e SNoLev z.
      exact ordinal_TransSet (SNoLev z) (SNoLev_ordinal z Hz) (SNoLev w) Hw2 (SNoLev u) Hu1b.
    + prove z < u. exact SNoLt_tra z w u Hz Hw1 Hu1a Hw3 Hu1c.
  - exact Hu2.
}
apply SNoLt_SNoL_or_SNoR_impred (y + z) (x + x) Lyz Lxx H2.
- let u.
  assume Hu1: u :e SNoL (x + x).
  assume Hu2: u :e SNoR (y + z).
  apply SNoL_E (x + x) Lxx u Hu1.
  assume Hu1a: SNo u.
  assume Hu1b.
  assume Hu1c: u < x + x.
  apply add_SNo_SNoR_interpolate y z Hy2 Hz u Hu2.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoR y.
    assume H4: w + z <= u.
    apply SNoR_E y Hy2 w Hw.
    assume Hw1: SNo w.
    assume Hw2.
    assume Hw3: y < w.
    prove False.
    apply L1 w Hw.
    prove w + z <= x + x.
    apply SNoLtLe.
    prove w + z < x + x.
    apply SNoLeLt_tra (w + z) u (x + x) (SNo_add_SNo w z Hw1 Hz) Hu1a Lxx H4.
    prove u < x + x.
    exact Hu1c.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoR z.
    assume H4: y + w <= u.
    apply SNoR_E z Hz w Hw.
    assume Hw1: SNo w.
    assume Hw2.
    assume Hw3: z < w.
    apply L3 w Hw.
    prove y + w < x + x.
    apply SNoLeLt_tra (y + w) u (x + x) (SNo_add_SNo y w Hy2 Hw1) Hu1a Lxx H4.
    prove u < x + x.
    exact Hu1c.
- assume H3: y + z :e SNoL (x + x). prove False.
  apply add_SNo_SNoL_interpolate x x Hx Hx (y + z) H3.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoL x.
    assume H4: y + z <= w + x.
    exact L2 w Hw H4.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoL x.
    assume H4: y + z <= x + w.
    apply SNoL_E x Hx w Hw.
    assume Hw1 Hw2 Hw3.
    apply L2 w Hw.
    prove y + z <= w + x.
    rewrite add_SNo_com w x Hw1 Hx.
    prove y + z <= x + w.
    exact H4.
- assume H3: x + x :e SNoR (y + z).
  apply add_SNo_SNoR_interpolate y z Hy2 Hz (x + x) H3.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoR y.
    assume H4: w + z <= x + x.
    prove False.
    exact L1 w Hw H4.
  + assume H. apply H.
    let w. assume H. apply H.
    assume Hw: w :e SNoR z.
    assume H4: y + w <= x + x.
    apply SNoR_E z Hz w Hw.
    assume Hw1: SNo w.
    assume Hw2: SNoLev w :e SNoLev z.
    assume Hw3: z < w.
    apply SNoLtLe_or (y + w) (x + x) (SNo_add_SNo y w Hy2 Hw1) Lxx.
    * assume H5: y + w < x + x.
      prove exists w :e SNoR z, y + w = x + x.
      apply L3 w Hw.
      prove y + w < x + x.
      exact H5.
    * { assume H5: x + x <= y + w.
        prove exists w :e SNoR z, y + w = x + x.
        witness w. apply andI.
        - exact Hw.
        - apply SNoLe_antisym (y + w) (x + x) (SNo_add_SNo y w Hy2 Hw1) Lxx.
          + exact H4.
          + exact H5.
      }
Qed.

Theorem double_SNo_min_1 : forall x y, SNo x -> SNo_min_of (SNoR x) y -> forall z, SNo z -> z < x -> x + x < y + z -> exists w :e SNoL z, y + w = x + x.
let x y. assume Hx Hy.
apply Hy. assume H. apply H.
assume Hy1: y :e SNoR x.
assume Hy2: SNo y.
assume Hy3: forall w :e SNoR x, SNo w -> y <= w.
apply SNoR_E x Hx y Hy1.
assume Hy1a.
assume Hy1b: SNoLev y :e SNoLev x.
assume Hy1c: x < y.
let z. assume Hz: SNo z.
assume H1: z < x.
assume H2: x + x < y + z.
claim Lmx: SNo (- x).
{ exact SNo_minus_SNo x Hx. }
claim Lmy: SNo (- y).
{ exact SNo_minus_SNo y Hy2. }
claim Lmz: SNo (- z).
{ exact SNo_minus_SNo z Hz. }
claim Lxx: SNo (x + x).
{ exact SNo_add_SNo x x Hx Hx. }
claim Lyz: SNo (y + z).
{ exact SNo_add_SNo y z Hy2 Hz. }
claim L1: SNo_max_of (SNoL (- x)) (- y).
{ rewrite SNoL_minus_SNoR x Hx.
  prove SNo_max_of {- w|w :e SNoR x} (- y).
  apply minus_SNo_min_max.
  - prove forall w :e SNoR x, SNo w.
    let w. assume Hw.
    apply SNoR_E x Hx w Hw.
    assume Hw1 _ _. exact Hw1.
  - prove SNo_min_of (SNoR x) y. exact Hy.
}
claim L2: - x < - z.
{ exact minus_SNo_Lt_contra z x Hz Hx H1. }
claim L3: - y + - z < - x + - x.
{ rewrite <- minus_add_SNo_distr y z Hy2 Hz.
  rewrite <- minus_add_SNo_distr x x Hx Hx.
  exact minus_SNo_Lt_contra (x + x) (y + z) Lxx Lyz H2.
}
apply double_SNo_max_1 (- x) (- y) Lmx L1 (- z) Lmz L2 L3.
let w. assume H. apply H.
assume Hw: w :e SNoR (- z).
rewrite <- minus_add_SNo_distr x x Hx Hx.
assume H3: - y + w = - (x + x).
apply SNoR_E (- z) Lmz w Hw.
assume Hw1: SNo w.
assume Hw2: SNoLev w :e SNoLev (- z).
assume Hw3: - z < w.
claim Lmw: SNo (- w).
{ exact SNo_minus_SNo w Hw1. }
witness (- w). apply andI.
- prove - w :e SNoL z.
  rewrite <- minus_SNo_invol z Hz.
  prove - w :e SNoL (- - z).
  rewrite SNoL_minus_SNoR (- z) Lmz.
  prove - w :e {- w|w :e SNoR (- z)}.
  apply ReplI.
  exact Hw.
- prove y + - w = x + x.
  rewrite <- minus_SNo_invol (x + x) Lxx.
  prove y + - w = - - (x + x).
  rewrite <- H3.
  prove y + - w = - (- y + w).
  rewrite minus_add_SNo_distr (- y) w Lmy Hw1.
  prove y + - w = - - y + - w.
  rewrite minus_SNo_invol y Hy2.
  reflexivity.
Qed.

Theorem finite_max_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_max_of X x.
claim L1: forall n, nat_p n -> forall X, (forall x :e X, SNo x) -> equip X (ordsucc n) -> exists x, SNo_max_of X x.
{ apply nat_ind.
  - let X. assume HX.
    assume H1: equip X 1.
    apply equip_sym X 1 H1.
    let f. assume Hf: bij 1 X f.
    apply bijE 1 X f Hf. assume Hf1 Hf2 Hf3.
    witness f 0.
    prove SNo_max_of X (f 0).
    prove f 0 :e X /\ SNo (f 0) /\ forall y :e X, SNo y -> y <= f 0.
    claim Lf0X: f 0 :e X.
    { exact Hf1 0 In_0_1. }
    apply and3I.
    + prove f 0 :e X. exact Lf0X.
    + exact HX (f 0) Lf0X.
    + let y. assume Hy: y :e X. assume Hy2: SNo y.
      apply Hf3 y Hy.
      let i. assume H. apply H.
      assume Hi: i :e 1.
      assume Hyi: f i = y.
      prove y <= f 0.
      rewrite <- Hyi.
      apply cases_1 i Hi.
      prove f 0 <= f 0. apply SNoLe_ref.
  - let n. assume Hn.
    assume IHn: forall X, (forall x :e X, SNo x) -> equip X (ordsucc n) -> exists x, SNo_max_of X x.
    let X. assume HX.
    assume H1: equip X (ordsucc (ordsucc n)).
    apply equip_sym X (ordsucc (ordsucc n)) H1.
    let f. assume Hf: bij (ordsucc (ordsucc n)) X f.
    apply bijE (ordsucc (ordsucc n)) X f Hf. assume Hf1 Hf2 Hf3.
    set X' := {f i|i :e ordsucc n}.
    claim LX'1: X' c= X.
    { let w. assume Hw: w :e X'.
      apply ReplE_impred (ordsucc n) f w Hw.
      let i. assume Hi: i :e ordsucc n.
      assume Hwi: w = f i. rewrite Hwi.
      prove f i :e X.
      apply Hf1 i.
      apply ordsuccI1. exact Hi.
    }
    claim LX'2: equip X' (ordsucc n).
    { apply equip_sym.
      prove exists f:set -> set, bij (ordsucc n) X' f.
      witness f.
      apply bijI.
      - let i. assume Hi: i :e ordsucc n.
        prove f i :e X'. apply ReplI. exact Hi.
      - let i. assume Hi. let j. assume Hj.
        assume Hij: f i = f j.
	apply Hf2.
	+ prove i :e ordsucc (ordsucc n). apply ordsuccI1. exact Hi.
	+ prove j :e ordsucc (ordsucc n). apply ordsuccI1. exact Hj.
	+ exact Hij.
      - let w. assume Hw: w :e X'.
        apply ReplE_impred (ordsucc n) f w Hw.
	let i. assume Hi: i :e ordsucc n.
	assume Hwi: w = f i.
	witness i. apply andI.
	+ exact Hi.
	+ symmetry. exact Hwi.
    }
    apply IHn X' (fun x' Hx' => HX x' (LX'1 x' Hx')) LX'2.
    let z. assume H. apply H. assume H. apply H.
    assume Hz1: z :e X'.
    assume Hz2: SNo z.
    assume Hz3: forall y :e X', SNo y -> y <= z.
    claim Lfn1: f (ordsucc n) :e X.
    { apply Hf1 (ordsucc n). apply ordsuccI2. }
    claim Lfn1': SNo (f (ordsucc n)).
    { apply HX (f (ordsucc n)) Lfn1. }
    apply SNoLtLe_or z (f (ordsucc n)) Hz2 Lfn1'.
    + assume H2: z < f (ordsucc n).
      witness (f (ordsucc n)).
      prove f (ordsucc n) :e X /\ SNo (f (ordsucc n)) /\ forall y :e X, SNo y -> y <= f (ordsucc n).
      apply and3I.
      * exact Lfn1.
      * exact Lfn1'.
      * { let y. assume Hy Hy2.
          apply Hf3 y Hy.
	  let i. assume H. apply H.
	  assume Hi: i :e ordsucc (ordsucc n).
	  assume Hyi: f i = y.
	  apply ordsuccE (ordsucc n) i Hi.
	  - assume H3: i :e ordsucc n.
	    prove y <= f (ordsucc n).
	    apply SNoLe_tra y z (f (ordsucc n)) Hy2 Hz2 Lfn1'.
	    + prove y <= z. apply Hz3 y.
	      * prove y :e X'. rewrite <- Hyi. prove f i :e X'. apply ReplI. exact H3.
	      * exact Hy2.
	    + prove z <= f (ordsucc n). apply SNoLtLe. exact H2.
	  - assume H3: i = ordsucc n.
	    rewrite <- Hyi. rewrite H3.
	    prove f (ordsucc n) <= f (ordsucc n).
	    apply SNoLe_ref.
        }
    + assume H2: f (ordsucc n) <= z.
      witness z.
      prove z :e X /\ SNo z /\ forall y :e X, SNo y -> y <= z.
      apply and3I.
      * exact LX'1 z Hz1.
      * exact Hz2.
      * { let y. assume Hy Hy2.
          apply Hf3 y Hy.
	  let i. assume H. apply H.
	  assume Hi: i :e ordsucc (ordsucc n).
	  assume Hyi: f i = y.
	  apply ordsuccE (ordsucc n) i Hi.
	  - assume H3: i :e ordsucc n.
	    prove y <= z.
	    apply Hz3 y.
	    + prove y :e X'. rewrite <- Hyi. prove f i :e X'. apply ReplI. exact H3.
	    + exact Hy2.
	  - assume H3: i = ordsucc n.
	    rewrite <- Hyi. rewrite H3.
	    prove f (ordsucc n) <= z. exact H2.
        }
}
let X. assume HX.
assume H1: finite X. apply H1.
let n. assume H. apply H.
assume Hn: n :e omega.
apply nat_inv n (omega_nat_p n Hn).
- assume Hn0: n = 0.
  rewrite Hn0.
  assume H2: equip X 0.
  assume H3: X <> 0.
  prove False.
  apply H2. let f. assume Hf: bij X 0 f.
  apply bijE X 0 f Hf.
  assume Hf1 _ _.
  apply H3. apply Empty_eq.
  let x. assume Hx.
  apply EmptyE (f x).
  exact Hf1 x Hx.
- assume H. apply H.
  let m. assume H. apply H.
  assume Hm: nat_p m.
  assume Hnm: n = ordsucc m.
  rewrite Hnm.
  assume H2: equip X (ordsucc m).
  assume _.
  exact L1 m Hm X HX H2.
Qed.

Theorem finite_min_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_min_of X x.
let X.
assume HX: forall x :e X, SNo x.
assume H1: finite X.
assume H2: X <> 0.
set X' := {- x|x :e X}.
claim L1: forall z :e X', SNo z.
{ let z. assume Hz.
  apply ReplE_impred X (fun x => - x) z Hz.
  let x. assume Hx: x :e X.
  assume Hzx: z = - x.
  rewrite Hzx. apply SNo_minus_SNo.
  prove SNo x. exact HX x Hx.
}
claim L2: finite X'.
{ apply H1.
  let n. assume H. apply H.
  assume Hn: n :e omega.
  assume H3: equip X n.
  prove exists n :e omega, equip X' n.
  witness n. apply andI.
  - exact Hn.
  - prove equip X' n.
    apply equip_tra X' X n.
    + prove equip X' X. apply equip_sym.
      prove equip X X'.
      prove exists f : set -> set, bij X X' f.
      witness minus_SNo.
      apply bijI.
      * let x. assume Hx: x :e X.
        prove - x :e X'. apply ReplI. exact Hx.
      * { let x. assume Hx. let x'. assume Hx'.
          assume Hxx': - x = - x'.
          prove x = x'.
	  transitivity - - x, - - x'.
	  - symmetry. exact minus_SNo_invol x (HX x Hx).
	  - f_equal. exact Hxx'.
	  - exact minus_SNo_invol x' (HX x' Hx').
        }
      * { let w. assume Hw: w :e X'.
          apply ReplE_impred X (fun x => - x) w Hw.
          let x. assume Hx.
          assume Hwx: w = - x.
          prove exists u :e X, - u = w.
          witness x.
          apply andI.
	  - exact Hx.
	  - symmetry. exact Hwx.
	}
    + prove equip X n. exact H3.
}
claim L3: X' <> 0.
{ assume H1: X' = 0.
  apply H2. prove X = 0.
  apply Empty_eq.
  let x. assume Hx: x :e X.
  apply EmptyE (- x).
  prove - x :e 0.
  rewrite <- H1. apply ReplI. exact Hx.
}
apply finite_max_exists X' L1 L2 L3.
let y.
assume Hy: SNo_max_of X' y.
witness (- y).
prove SNo_min_of X (- y).
exact minus_SNo_max_min' X y HX Hy.
Qed.

Theorem SNoS_omega_SNoL_max_exists : forall x :e SNoS_ omega, SNoL x = 0 \/ exists y, SNo_max_of (SNoL x) y.
let x. assume Hx.
apply xm (SNoL x = 0).
- assume H1: SNoL x = 0. apply orIL. exact H1.
- assume H1: SNoL x <> 0. apply orIR.
  claim L1: forall y :e SNoL x, SNo y.
  { let y. assume Hy.
    apply SNoS_E2 omega omega_ordinal x Hx.
    assume _ _ Hx3 _.
    apply SNoL_E x Hx3 y Hy.
    assume H _ _. exact H.
  }
  exact finite_max_exists (SNoL x) L1 (SNoS_omega_SNoL_finite x Hx) H1.
Qed.

Theorem SNoS_omega_SNoR_min_exists : forall x :e SNoS_ omega, SNoR x = 0 \/ exists y, SNo_min_of (SNoR x) y.
let x. assume Hx.
apply xm (SNoR x = 0).
- assume H1: SNoR x = 0. apply orIL. exact H1.
- assume H1: SNoR x <> 0. apply orIR.
  claim L1: forall y :e SNoR x, SNo y.
  { let y. assume Hy.
    apply SNoS_E2 omega omega_ordinal x Hx.
    assume _ _ Hx3 _.
    apply SNoR_E x Hx3 y Hy.
    assume H _ _. exact H.
  }
  exact finite_min_exists (SNoR x) L1 (SNoS_omega_SNoR_finite x Hx) H1.
Qed.

End SNoMaxMin.

Section DiadicRationals.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Infix ^ 342 right := exp_SNo_nat.

Theorem nonneg_diadic_rational_p_SNoS_omega: forall k :e omega, forall n, nat_p n -> eps_ k * n :e SNoS_ omega.
let k. assume Hk.
claim Lek: SNo (eps_ k).
{ exact SNo_eps_ k Hk. }
claim Lek2: eps_ k :e SNoS_ omega.
{ exact SNo_eps_SNoS_omega k Hk. }
apply nat_ind.
- prove eps_ k * 0 :e SNoS_ omega. rewrite mul_SNo_zeroR (eps_ k) Lek.
  prove 0 :e SNoS_ omega.
  exact omega_SNoS_omega 0 (nat_p_omega 0 nat_0).
- let n. assume Hn.
  assume IHn: eps_ k * n :e SNoS_ omega.
  prove eps_ k * ordsucc n :e SNoS_ omega.
  rewrite <- add_SNo_1_ordsucc n (nat_p_omega n Hn).
  prove eps_ k * (n + 1) :e SNoS_ omega.
  rewrite mul_SNo_distrL (eps_ k) n 1 Lek (omega_SNo n (nat_p_omega n Hn)) (omega_SNo 1 (nat_p_omega 1 nat_1)).
  prove eps_ k * n + eps_ k * 1 :e SNoS_ omega.
  rewrite mul_SNo_oneR (eps_ k) Lek.
  prove eps_ k * n + eps_ k :e SNoS_ omega.
  apply add_SNo_SNoS_omega.
  + exact IHn.
  + exact SNo_eps_SNoS_omega k Hk.
Qed.

Definition diadic_rational_p : set -> prop := fun x => exists k :e omega, exists m :e int, x = eps_ k * m.

Theorem diadic_rational_p_SNoS_omega: forall x, diadic_rational_p x -> x :e SNoS_ omega.
let x. 
assume H. apply H.
let k. assume H. apply H.
assume Hk: k :e omega. assume H. apply H.
let m.  assume H. apply H.
assume Hm: m :e int.
assume Hxkm: x = eps_ k * m.
rewrite Hxkm.
prove eps_ k * m :e SNoS_ omega.
claim L1: forall n :e omega, eps_ k * n :e SNoS_ omega.
{ let n. assume Hn: n :e omega.
  prove eps_ k * n :e SNoS_ omega.
  exact nonneg_diadic_rational_p_SNoS_omega k Hk n (omega_nat_p n Hn).
}
claim L2: forall n :e omega, eps_ k * (- n) :e SNoS_ omega.
{ let n. assume Hn: n :e omega.
  prove eps_ k * (- n) :e SNoS_ omega.
  rewrite mul_SNo_minus_distrR (eps_ k) n (SNo_eps_ k Hk) (omega_SNo n Hn).
  apply minus_SNo_SNoS_omega.
  exact nonneg_diadic_rational_p_SNoS_omega k Hk n (omega_nat_p n Hn).
}
exact int_SNo_cases (fun m => eps_ k * m :e SNoS_ omega) L1 L2 m Hm.
Qed.

Theorem int_diadic_rational_p : forall m :e int, diadic_rational_p m.
let m. assume Hm.
prove exists k :e omega, exists m' :e int, m = eps_ k * m'.
witness 0. apply andI.
- exact nat_p_omega 0 nat_0.
- witness m. apply andI.
  + exact Hm.
  + prove m = eps_ 0 * m.
    rewrite eps_0_1. symmetry. exact mul_SNo_oneL m (int_SNo m Hm).
Qed.

Theorem omega_diadic_rational_p : forall m :e omega, diadic_rational_p m.
let m. assume Hm. apply int_diadic_rational_p.
apply Subq_omega_int. exact Hm.
Qed.

Theorem eps_diadic_rational_p : forall k :e omega, diadic_rational_p (eps_ k).
let k. assume Hk.
prove exists k' :e omega, exists m :e int, eps_ k = eps_ k' * m.
witness k. apply andI.
- exact Hk.
- witness 1. apply andI.
  + apply Subq_omega_int. exact nat_p_omega 1 nat_1.
  + prove eps_ k = eps_ k * 1.
    symmetry.
    exact mul_SNo_oneR (eps_ k) (SNo_eps_ k Hk).
Qed.

Theorem minus_SNo_diadic_rational_p : forall x, diadic_rational_p x -> diadic_rational_p (- x).
let x. assume H. apply H.
let k. assume H. apply H.
assume Hk: k :e omega.
claim Lek: SNo (eps_ k).
{ exact SNo_eps_ k Hk. }
assume H. apply H.
let m. assume H. apply H.
assume Hm: m :e int.
assume Hxkm: x = eps_ k * m.
claim Lm: SNo m.
{ exact int_SNo m Hm. }
claim Lekm: SNo (eps_ k * m).
{ exact SNo_mul_SNo (eps_ k) m Lek Lm. }
prove exists k' :e omega, exists m' :e int, - x = eps_ k' * m'.
witness k. apply andI.
- exact Hk.
- witness (- m). apply andI.
  + apply int_minus_SNo. exact Hm.
  + prove - x = eps_ k * (- m).
    rewrite mul_SNo_minus_distrR (eps_ k) m (SNo_eps_ k Hk) Lm.
    prove - x = - eps_ k * m.
    f_equal.
    exact Hxkm.
Qed.

Theorem mul_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x * y).
let x y. assume Hx. apply Hx.
let k. assume H. apply H.
assume Hk: k :e omega.
claim Lek: SNo (eps_ k).
{ exact SNo_eps_ k Hk. }
assume H. apply H.
let m. assume H. apply H.
assume Hm: m :e int.
assume Hxkm: x = eps_ k * m.
claim Lm: SNo m.
{ exact int_SNo m Hm. }
claim Lekm: SNo (eps_ k * m).
{ exact SNo_mul_SNo (eps_ k) m Lek Lm. }
assume Hy. apply Hy.
let l. assume H. apply H.
assume Hl: l :e omega.
claim Lel: SNo (eps_ l).
{ exact SNo_eps_ l Hl. }
assume H. apply H.
let n. assume H. apply H.
assume Hn: n :e int.
claim Ln: SNo n.
{ exact int_SNo n Hn. }
claim Leln: SNo (eps_ l * n).
{ exact SNo_mul_SNo (eps_ l) n Lel Ln. }
assume Hyln: y = eps_ l * n.
prove exists k' :e omega, exists m' :e int, x * y = eps_ k' * m'.
witness (k + l). apply andI.
- exact add_SNo_In_omega k Hk l Hl.
- witness (m * n). apply andI.
  + exact int_mul_SNo m Hm n Hn.
  + prove x * y = eps_ (k + l) * (m * n).
    rewrite <- mul_SNo_eps_eps_add_SNo k Hk l Hl.
    prove x * y = (eps_ k * eps_ l) * (m * n).
    rewrite mul_SNo_com_4_inner_mid (eps_ k) (eps_ l) m n Lek Lel Lm Ln.
    prove x * y = (eps_ k * m) * (eps_ l * n).
    f_equal.
    * exact Hxkm.
    * exact Hyln.
Qed.

Theorem add_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x + y).
let x y. assume Hx. apply Hx.
let k. assume H. apply H.
assume Hk: k :e omega.
claim Lek: SNo (eps_ k).
{ exact SNo_eps_ k Hk. }
assume H. apply H.
let m. assume H. apply H.
assume Hm: m :e int.
assume Hxkm: x = eps_ k * m.
claim Lm: SNo m.
{ exact int_SNo m Hm. }
claim Lekm: SNo (eps_ k * m).
{ exact SNo_mul_SNo (eps_ k) m Lek Lm. }
assume Hy. apply Hy.
let l. assume H. apply H.
assume Hl: l :e omega.
claim Lel: SNo (eps_ l).
{ exact SNo_eps_ l Hl. }
assume H. apply H.
let n. assume H. apply H.
assume Hn: n :e int.
assume Hyln: y = eps_ l * n.
claim Ln: SNo n.
{ exact int_SNo n Hn. }
claim Leln: SNo (eps_ l * n).
{ exact SNo_mul_SNo (eps_ l) n Lel Ln. }
prove exists k' :e omega, exists m' :e int, x + y = eps_ k' * m'.
witness (k + l). apply andI.
- prove k + l :e omega. exact add_SNo_In_omega k Hk l Hl.
- witness (2 ^ l * m + 2 ^ k * n).
  claim L2l: 2 ^ l :e int.
  { apply Subq_omega_int. apply nat_p_omega.
    exact nat_exp_SNo_nat 2 nat_2 l (omega_nat_p l Hl).
  }
  claim L2lm: 2 ^ l * m :e int.
  { apply int_mul_SNo.
    - exact L2l.
    - exact Hm.
  }
  claim L2k: 2 ^ k :e int.
  { apply Subq_omega_int. apply nat_p_omega.
    exact nat_exp_SNo_nat 2 nat_2 k (omega_nat_p k Hk).
  }
  claim L2kn: 2 ^ k * n :e int.
  { apply int_mul_SNo.
    - exact L2k.
    - exact Hn.
  }
  apply andI.
  + prove 2 ^ l * m + 2 ^ k * n :e int.
    apply int_add_SNo.
    * exact L2lm.
    * exact L2kn.
  + prove x + y = eps_ (k + l) * (2 ^ l * m + 2 ^ k * n).
    rewrite <- mul_SNo_eps_eps_add_SNo k Hk l Hl.
    prove x + y = (eps_ k * eps_ l) * (2 ^ l * m + 2 ^ k * n).
    rewrite mul_SNo_distrL (eps_ k * eps_ l) (2 ^ l * m) (2 ^ k * n) (SNo_mul_SNo (eps_ k) (eps_ l) Lek Lel) (int_SNo (2 ^ l * m) L2lm) (int_SNo (2 ^ k * n) L2kn).
    prove x + y = (eps_ k * eps_ l) * 2 ^ l * m + (eps_ k * eps_ l) * 2 ^ k * n.
    f_equal.
    * prove x = (eps_ k * eps_ l) * 2 ^ l * m.
      rewrite <- mul_SNo_assoc (eps_ k) (eps_ l) (2 ^ l * m) Lek Lel (int_SNo (2 ^ l * m) L2lm).
      prove x = eps_ k * eps_ l * 2 ^ l * m.
      rewrite mul_SNo_assoc (eps_ l) (2 ^ l) m Lel (int_SNo (2 ^ l) L2l) (int_SNo m Hm).
      prove x = eps_ k * (eps_ l * 2 ^ l) * m.
      rewrite mul_SNo_eps_power_2 l (omega_nat_p l Hl).
      prove x = eps_ k * 1 * m.
      rewrite mul_SNo_oneL m (int_SNo m Hm).
      prove x = eps_ k * m. exact Hxkm.
    * prove y = (eps_ k * eps_ l) * (2 ^ k * n).
      rewrite mul_SNo_com_4_inner_mid (eps_ k) (eps_ l) (2 ^ k) n Lek Lel (int_SNo (2 ^ k) L2k) (int_SNo n Hn).
      prove y = (eps_ k * 2 ^ k) * (eps_ l * n).
      rewrite mul_SNo_eps_power_2 k (omega_nat_p k Hk).
      prove y = 1 * (eps_ l * n).
      rewrite mul_SNo_oneL (eps_ l * n) Leln.
      exact Hyln.
Qed.

Theorem SNoS_omega_diadic_rational_p_lem: forall n, nat_p n -> forall x, SNo x -> SNoLev x = n -> diadic_rational_p x.
apply nat_complete_ind.
let n. assume Hn.
assume IH: forall m :e n, forall x, SNo x -> SNoLev x = m -> diadic_rational_p x.
let x.
assume Hx: SNo x.
assume Hxn: SNoLev x = n.
prove diadic_rational_p x.
apply dneg.
assume HC: ~diadic_rational_p x.
prove False.
claim LxSo: x :e SNoS_ omega.
{ apply SNoS_I omega omega_ordinal x (SNoLev x).
  - prove SNoLev x :e omega. rewrite Hxn. exact nat_p_omega n Hn.
  - prove SNo_ (SNoLev x) x. apply SNoLev_. exact Hx.
}
claim L1: exists y, SNo_max_of (SNoL x) y.
{ apply SNoS_omega_SNoL_max_exists x LxSo.
  - assume H1: SNoL x = 0. (** x must be - n, so it is a diadic rational **)
    claim L1a: ordinal (- x).
    { apply SNo_max_ordinal (- x) (SNo_minus_SNo x Hx).
      let w.
      rewrite minus_SNo_Lev x Hx.
      assume Hw: w :e SNoS_ (SNoLev x).
      prove w < - x.
      apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) w Hw.
      assume Hw1 Hw2 Hw3 Hw4.
      apply SNoLt_trichotomy_or_impred w (- x) ?? (SNo_minus_SNo x Hx).
      - assume H2: w < - x. exact H2.
      - assume H2: w = - x. prove False. apply In_irref (SNoLev w).
        rewrite H2 at 2. rewrite minus_SNo_Lev x Hx.
        exact ??.
      - assume H2: - x < w. prove False.
        apply EmptyE (- w).
        prove - w :e 0.
        rewrite <- H1.
        prove - w :e SNoL x.
        apply SNoL_I x Hx (- w) (SNo_minus_SNo w ??).
        + prove SNoLev (- w) :e SNoLev x. rewrite minus_SNo_Lev w ??. exact ??.
        + prove - w < x. exact minus_SNo_Lt_contra1 x w Hx ?? ??.
    }
    claim L1b: - x = n.
    { rewrite <- Hxn. prove - x = SNoLev x. symmetry.
      rewrite <- minus_SNo_Lev x ??.
      exact ordinal_SNoLev (- x) L1a.
    }
    prove False.
    apply HC.
    prove diadic_rational_p x.
    rewrite <- minus_SNo_invol x ??.
    prove diadic_rational_p (- - x).
    apply minus_SNo_diadic_rational_p.
    prove diadic_rational_p (- x).
    rewrite L1b.
    prove diadic_rational_p n.
    apply omega_diadic_rational_p.
    exact nat_p_omega n Hn.
  - assume H1. exact H1.
}
claim L2: exists z, SNo_min_of (SNoR x) z.
{ apply SNoS_omega_SNoR_min_exists x LxSo.
  - assume H1: SNoR x = 0. (** x must be n, so it is a diadic rational **)
    claim L2a: ordinal x.
    { apply SNo_max_ordinal x Hx.
      let w. assume Hw: w :e SNoS_ (SNoLev x).
      prove w < x.
      apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x ??) w Hw.
      assume Hw1 Hw2 Hw3 Hw4.
      apply SNoLt_trichotomy_or_impred w x ?? ??.
      - assume H2: w < x. exact H2.
      - assume H2: w = x. prove False. apply In_irref (SNoLev x).
        rewrite <- H2 at 1. exact ??.
      - assume H2: x < w. prove False.
        apply EmptyE w.
        prove w :e 0.
        rewrite <- H1.
        prove w :e SNoR x.
        apply SNoR_I x ?? w ?? ?? ??.
    }
    claim L2b: x = n.
    { rewrite <- Hxn. prove x = SNoLev x. symmetry. exact ordinal_SNoLev x L2a. }
    prove False.
    apply HC.
    prove diadic_rational_p x.
    apply omega_diadic_rational_p.
    prove x :e omega. rewrite L2b. exact nat_p_omega n Hn.
  - assume H1. exact H1.
}
apply L1.
let y.
assume Hy: SNo_max_of (SNoL x) y.
apply Hy. assume H. apply H.
assume Hy1: y :e SNoL x.
assume Hy2: SNo y.
assume Hy3: forall w :e SNoL x, SNo w -> w <= y.
apply SNoL_E x Hx y Hy1.
assume _ Hy1b Hy1c.
apply L2.
let z.
assume Hz: SNo_min_of (SNoR x) z.
apply Hz. assume H. apply H.
assume Hz1: z :e SNoR x.
assume Hz2: SNo z.
assume Hz3: forall w :e SNoR x, SNo w -> z <= w.
apply SNoR_E x Hx z Hz1.
assume _ Hz1b Hz1c.
claim Lxx: SNo (x + x).
{ exact SNo_add_SNo x x Hx Hx. }
claim Lyz: SNo (y + z).
{ exact SNo_add_SNo y z Hy2 Hz2. }
claim Ldry: diadic_rational_p y.
{ apply IH (SNoLev y).
  - prove SNoLev y :e n. rewrite <- Hxn.
    prove SNoLev y :e SNoLev x.
    exact Hy1b.
  - prove SNo y. exact Hy2.
  - prove SNoLev y = SNoLev y. reflexivity.
}
claim Ldrz: diadic_rational_p z.
{ apply IH (SNoLev z).
  - prove SNoLev z :e n. rewrite <- Hxn.
    prove SNoLev z :e SNoLev x.
    exact Hz1b.
  - prove SNo z. exact Hz2.
  - prove SNoLev z = SNoLev z. reflexivity.
}
apply SNoLt_trichotomy_or_impred (x + x) (y + z) Lxx Lyz.
- rewrite add_SNo_com y z Hy2 Hz2.
  assume H1: x + x < z + y.
  apply double_SNo_min_1 x z Hx Hz y Hy2 Hy1c H1.
  let w. assume H. apply H.
  assume Hw: w :e SNoL y.
  assume H2: z + w = x + x.
  apply SNoL_E y Hy2 w Hw.
  assume Hw1 Hw2 Hw3.
  claim Ldrw: diadic_rational_p w.
  { apply IH (SNoLev w).
    - prove SNoLev w :e n.
      apply ordinal_TransSet n (nat_p_ordinal n Hn) (SNoLev y).
      + prove SNoLev y :e n. rewrite <- Hxn.
        exact Hy1b.
      + prove SNoLev w :e SNoLev y. exact Hw2.
    - prove SNo w. exact Hw1.
    - prove SNoLev w = SNoLev w. reflexivity.
  }
  claim Lxe: x = eps_ 1 * (z + w).
  { apply double_eps_1 x z w Hx Hz2 Hw1.
    symmetry. exact H2.
  }
  apply HC.
  prove diadic_rational_p x.
  rewrite Lxe.
  apply mul_SNo_diadic_rational_p.
  + prove diadic_rational_p (eps_ 1).
    exact eps_diadic_rational_p 1 (nat_p_omega 1 nat_1).
  + prove diadic_rational_p (z + w).
    apply add_SNo_diadic_rational_p.
    * prove diadic_rational_p z. exact Ldrz.
    * prove diadic_rational_p w. exact Ldrw.
- assume H1: x + x = y + z.
  claim Lxe: x = eps_ 1 * (y + z).
  { exact double_eps_1 x y z Hx Hy2 Hz2 H1. }
  apply HC.
  prove diadic_rational_p x.
  rewrite Lxe.
  apply mul_SNo_diadic_rational_p.
  + prove diadic_rational_p (eps_ 1).
    exact eps_diadic_rational_p 1 (nat_p_omega 1 nat_1).
  + prove diadic_rational_p (y + z).
    apply add_SNo_diadic_rational_p.
    * prove diadic_rational_p y. exact Ldry.
    * prove diadic_rational_p z. exact Ldrz.
- assume H1: y + z < x + x.
  apply double_SNo_max_1 x y Hx Hy z Hz2 Hz1c H1.
  let w. assume H. apply H.
  assume Hw: w :e SNoR z.
  assume H2: y + w = x + x.
  apply SNoR_E z Hz2 w Hw.
  assume Hw1 Hw2 Hw3.
  claim Ldrw: diadic_rational_p w.
  { apply IH (SNoLev w).
    - prove SNoLev w :e n.
      apply ordinal_TransSet n (nat_p_ordinal n Hn) (SNoLev z).
      + prove SNoLev z :e n. rewrite <- Hxn.
        exact Hz1b.
      + prove SNoLev w :e SNoLev z. exact Hw2.
    - prove SNo w. exact Hw1.
    - prove SNoLev w = SNoLev w. reflexivity.
  }
  claim Lxe: x = eps_ 1 * (y + w).
  { apply double_eps_1 x y w Hx Hy2 Hw1.
    symmetry. exact H2.
  }
  apply HC.
  prove diadic_rational_p x.
  rewrite Lxe.
  apply mul_SNo_diadic_rational_p.
  + prove diadic_rational_p (eps_ 1).
    exact eps_diadic_rational_p 1 (nat_p_omega 1 nat_1).
  + prove diadic_rational_p (y + w).
    apply add_SNo_diadic_rational_p.
    * prove diadic_rational_p y. exact Ldry.
    * prove diadic_rational_p w. exact Ldrw.
Qed.

Theorem SNoS_omega_diadic_rational_p: forall x :e SNoS_ omega, diadic_rational_p x.
let x. assume Hx: x :e SNoS_ omega.
apply SNoS_E2 omega omega_ordinal x Hx.
assume Hx1: SNoLev x :e omega.
assume Hx2: ordinal (SNoLev x).
assume Hx3: SNo x.
assume Hx4: SNo_ (SNoLev x) x.
apply SNoS_omega_diadic_rational_p_lem (SNoLev x).
- prove nat_p (SNoLev x). exact omega_nat_p (SNoLev x) Hx1.
- prove SNo x. exact Hx3.
- prove SNoLev x = SNoLev x. reflexivity.
Qed.

Theorem mul_SNo_SNoS_omega : forall x y :e SNoS_ omega, x * y :e SNoS_ omega.
let x. assume Hx. let y. assume Hy.
apply diadic_rational_p_SNoS_omega.
apply mul_SNo_diadic_rational_p.
- apply SNoS_omega_diadic_rational_p. exact Hx.
- apply SNoS_omega_diadic_rational_p. exact Hy.
Qed.

End DiadicRationals.

Opaque int.
Opaque abs_SNo.
Opaque SNo_max_of.
Opaque SNo_min_of.
Opaque diadic_rational_p.
