(** Part 9 **)

Section SurrealSqrt.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Infix ^ 342 right := exp_SNo_nat.

Definition SNoL_nonneg : set -> set := fun x => {w :e SNoL x|0 <= w}.

Theorem SNoL_nonneg_0: SNoL_nonneg 0 = 0.
prove {w :e SNoL 0|0 <= w} = 0.
rewrite SNoL_0.
exact Sep_Empty (fun w => 0 <= w).
Qed.

Theorem SNoL_nonneg_1: SNoL_nonneg 1 = 1.
prove {w :e SNoL 1|0 <= w} = 1.
rewrite SNoL_1.
prove {w :e 1|0 <= w} = 1.
apply set_ext.
- exact Sep_Subq 1 (fun w => 0 <= w).
- let w. assume Hw: w :e 1.
  apply cases_1 w Hw.
  prove 0 :e {w :e 1|0 <= w}.
  apply SepI.
  + exact In_0_1.
  + prove 0 <= 0. apply SNoLe_ref.
Qed.

Definition SNo_sqrtauxset : set -> set -> set -> set := fun Y Z x => \/_ y :e Y, {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.

Theorem SNo_sqrtauxset_I : forall Y Z x,
 forall y :e Y, forall z :e Z, 0 < y + z -> (x + y * z) :/: (y + z) :e SNo_sqrtauxset Y Z x.
let Y Z x y. assume Hy. let z. assume Hz.
assume H1.
prove (x + y * z) :/: (y + z) :e \/_ y :e Y, {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.
apply famunionI Y (fun y => {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}) y ((x + y * z) :/: (y + z)) Hy.
prove (x + y * z) :/: (y + z) :e {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.
exact ReplSepI Z (fun z => 0 < y + z) (fun z => (x + y * z) :/: (y + z)) z Hz H1.
Qed.

Theorem SNo_sqrtauxset_E : forall Y Z x,
 forall u :e SNo_sqrtauxset Y Z x, forall p:prop,
     (forall y :e Y, forall z :e Z, 0 < y + z -> u = (x + y * z) :/: (y + z) -> p)
  -> p.
let Y Z x u. assume Hu. let p. assume H1.
apply famunionE_impred Y (fun y => {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}) u Hu.
let y. assume Hy: y :e Y. assume Hu1.
apply ReplSepE_impred Z (fun z => 0 < y + z) (fun z => (x + y * z) :/: (y + z)) u Hu1.
let z. assume Hz: z :e Z.
assume Hyz: 0 < y + z.
assume Hu2: u = (x + y * z) :/: (y + z).
exact H1 y Hy z Hz Hyz Hu2.
Qed.

Theorem SNo_sqrtauxset_0: forall Z x, SNo_sqrtauxset 0 Z x = 0.
let Z x. apply Empty_eq.
let u. assume Hu.
apply SNo_sqrtauxset_E 0 Z x u Hu.
let y. assume Hy: y :e 0.
prove False. exact EmptyE y Hy.
Qed.

Theorem SNo_sqrtauxset_0': forall Y x, SNo_sqrtauxset Y 0 x = 0.
let Y x. apply Empty_eq.
let u. assume Hu.
apply SNo_sqrtauxset_E Y 0 x u Hu.
let y. assume Hy: y :e Y.
let z. assume Hz: z :e 0.
prove False. exact EmptyE z Hz.
Qed.

Definition SNo_sqrtaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x})
   (fun k p => (p 0 :\/: SNo_sqrtauxset (p 0) (p 1) x,
                p 1 :\/: SNo_sqrtauxset (p 0) (p 0) x
                    :\/: SNo_sqrtauxset (p 1) (p 1) x)).

Theorem SNo_sqrtaux_0: forall x, forall g:set -> set, SNo_sqrtaux x g 0 = ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x}).
let x g.
exact nat_primrec_0 ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x})
   (fun k p => (p 0 :\/: SNo_sqrtauxset (p 0) (p 1) x,
                p 1 :\/: SNo_sqrtauxset (p 0) (p 0) x
                    :\/: SNo_sqrtauxset (p 1) (p 1) x)).
Qed.

Theorem SNo_sqrtaux_S: forall x, forall g:set -> set, forall n, nat_p n
 -> SNo_sqrtaux x g (ordsucc n)
  = (SNo_sqrtaux x g n 0
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 1) x,
     SNo_sqrtaux x g n 1
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 0) x
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 1) (SNo_sqrtaux x g n 1) x).
let x g n. assume Hn.
exact nat_primrec_S ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x})
   (fun k p => (p 0 :\/: SNo_sqrtauxset (p 0) (p 1) x,
                p 1 :\/: SNo_sqrtauxset (p 0) (p 0) x
                    :\/: SNo_sqrtauxset (p 1) (p 1) x)) n Hn.
Qed.

Theorem SNo_sqrtaux_mon_lem: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m n) 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m n) 1.
let x g m. assume Hm.
apply nat_ind.
- prove SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m 0) 0
     /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m 0) 1.
  rewrite add_nat_0R m.
  prove SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g m 0
     /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g m 1.
  apply andI.
  + apply Subq_ref.
  + apply Subq_ref.
- let n. assume Hn IH. apply IH.
  assume IH0: SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m n) 0.
  assume IH1: SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m n) 1.
  rewrite add_nat_SR m n Hn.
  prove SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (ordsucc (add_nat m n)) 0
     /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (ordsucc (add_nat m n)) 1.
  rewrite SNo_sqrtaux_S x g (add_nat m n) (add_nat_p m Hm n Hn).
  rewrite tuple_2_0_eq.
  rewrite tuple_2_1_eq.
  apply andI.
  + prove SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m n) 0 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 1) x.
    apply Subq_tra (SNo_sqrtaux x g m 0)
                   (SNo_sqrtaux x g (add_nat m n) 0)
                   (SNo_sqrtaux x g (add_nat m n) 0 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 1) x)
                   IH0.
    apply binunion_Subq_1.
  + prove SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m n) 1 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 0) x :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 1) (SNo_sqrtaux x g (add_nat m n) 1) x.
    apply Subq_tra (SNo_sqrtaux x g m 1)
                   (SNo_sqrtaux x g (add_nat m n) 1)
                   (SNo_sqrtaux x g (add_nat m n) 1 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 0) x :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 1) (SNo_sqrtaux x g (add_nat m n) 1) x)
                   IH1.
    apply Subq_tra (SNo_sqrtaux x g (add_nat m n) 1)
                   (SNo_sqrtaux x g (add_nat m n) 1 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 0) x)
                   (SNo_sqrtaux x g (add_nat m n) 1 :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 0) (SNo_sqrtaux x g (add_nat m n) 0) x :\/: SNo_sqrtauxset (SNo_sqrtaux x g (add_nat m n) 1) (SNo_sqrtaux x g (add_nat m n) 1) x).
    * apply binunion_Subq_1.
    * apply binunion_Subq_1.
Qed.

Theorem SNo_sqrtaux_mon: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n -> m c= n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g n 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g n 1.
let x g m. assume Hm. let n. assume Hn Hmn.
apply nat_Subq_add_ex m Hm n Hn Hmn.
let k. assume H. apply H.
assume Hk: nat_p k.
rewrite add_nat_com k Hk m Hm.
assume H1: n = add_nat m k.
rewrite H1.
exact SNo_sqrtaux_mon_lem x g m Hm k Hk.
Qed.

Theorem SNo_sqrtaux_ext: forall x, SNo x -> forall g h:set -> set, (forall x' :e SNoS_ (SNoLev x), g x' = h x') -> forall k, nat_p k -> SNo_sqrtaux x g k = SNo_sqrtaux x h k.
let x. assume Hx. let g h.
assume Hgh.
apply nat_ind.
- prove SNo_sqrtaux x g 0 = SNo_sqrtaux x h 0.
  rewrite SNo_sqrtaux_0 x g.
  rewrite SNo_sqrtaux_0 x h.
  prove ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x}) = ({h w|w :e SNoL_nonneg x},{h z|z :e SNoR x}).
  claim L1: {g w|w :e SNoL_nonneg x} = {h w|w :e SNoL_nonneg x}.
  { apply ReplEq_ext (SNoL_nonneg x) g h.
    let w. assume Hw: w :e SNoL_nonneg x.
    prove g w = h w.
    apply SNoL_E x Hx w (SepE1 (SNoL x) (fun w => 0 <= w) w Hw).
    assume Hw1 Hw2 Hw3.
    apply Hgh.
    prove w :e SNoS_ (SNoLev x).
    exact SNoS_I2 w x Hw1 Hx Hw2.
  }
  claim L2: {g w|w :e SNoR x} = {h w|w :e SNoR x}.
  { apply ReplEq_ext (SNoR x) g h.
    let w. assume Hw: w :e SNoR x.
    prove g w = h w.
    apply SNoR_E x Hx w Hw.
    assume Hw1 Hw2 Hw3.
    apply Hgh.
    prove w :e SNoS_ (SNoLev x).
    exact SNoS_I2 w x Hw1 Hx Hw2.
  }
  rewrite L1. rewrite L2. reflexivity.
- let k.
  assume Hk: nat_p k.
  assume IH: SNo_sqrtaux x g k = SNo_sqrtaux x h k.
  prove SNo_sqrtaux x g (ordsucc k) = SNo_sqrtaux x h (ordsucc k).
  rewrite SNo_sqrtaux_S x g k Hk.
  rewrite SNo_sqrtaux_S x h k Hk.
  rewrite IH.
  reflexivity.
Qed.

Section sqrt_SNo_nonneg.

Let G : set -> (set -> set) -> set := fun x g => SNoCut (\/_ k :e omega, SNo_sqrtaux x g k 0) (\/_ k :e omega, SNo_sqrtaux x g k 1).

Definition sqrt_SNo_nonneg : set -> set := SNo_rec_i G.

Theorem sqrt_SNo_nonneg_eq: forall x, SNo x -> sqrt_SNo_nonneg x = G x sqrt_SNo_nonneg.
apply SNo_rec_i_eq G.
let x. assume Hx.
let g h. assume Hgh.
prove SNoCut (\/_ k :e omega, SNo_sqrtaux x g k 0) (\/_ k :e omega, SNo_sqrtaux x g k 1)
    = SNoCut (\/_ k :e omega, SNo_sqrtaux x h k 0) (\/_ k :e omega, SNo_sqrtaux x h k 1).
f_equal.
- apply famunion_ext.
  let k. assume Hk.
  prove SNo_sqrtaux x g k 0 = SNo_sqrtaux x h k 0.
  f_equal.
  apply SNo_sqrtaux_ext x Hx g h.
  + prove forall w :e SNoS_ (SNoLev x), g w = h w.
    exact Hgh.
  + exact omega_nat_p k Hk.
- apply famunion_ext.
  let k. assume Hk.
  prove SNo_sqrtaux x g k 1 = SNo_sqrtaux x h k 1.
  f_equal.
  apply SNo_sqrtaux_ext x Hx g h.
  + prove forall w :e SNoS_ (SNoLev x), g w = h w.
    exact Hgh.
  + exact omega_nat_p k Hk.
Qed.

Theorem sqrt_SNo_nonneg_prop1a: forall x, SNo x -> 0 <= x ->
    (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
 -> forall k, nat_p k ->
              (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y).
let x. assume Hx Hxnonneg IH.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
apply nat_ind.
- prove (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg 0 0, SNo y /\ 0 <= y /\ y * y < x)
     /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg 0 1, SNo y /\ 0 <= y /\ x < y * y).
  rewrite SNo_sqrtaux_0 x sqrt_SNo_nonneg. apply andI.
  + let y. rewrite tuple_2_0_eq.
    assume Hy: y :e {sqrt_SNo_nonneg w|w :e SNoL_nonneg x}.
    prove SNo y /\ 0 <= y /\ y * y < x.
    apply ReplE_impred (SNoL_nonneg x) sqrt_SNo_nonneg y Hy.
    let w. assume Hw: w :e SNoL_nonneg x.
    assume Hyw: y = sqrt_SNo_nonneg w.
    apply SepE (SNoL x) (fun w => 0 <= w) w Hw.
    assume Hw: w :e SNoL x.
    assume Hwnonneg: 0 <= w.
    apply SNoL_E x Hx w Hw.
    assume Hw1 Hw2 Hw3.
    claim Lw: w :e SNoS_ (SNoLev x).
    { exact SNoS_I2 w x Hw1 Hx Hw2. }
    apply IH w Lw Hwnonneg. assume H. apply H.
    assume IHa: SNo (sqrt_SNo_nonneg w).
    assume IHb: 0 <= sqrt_SNo_nonneg w.
    assume IHc: sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w.
    apply and3I.
    * rewrite Hyw. exact IHa.
    * rewrite Hyw. exact IHb.
    * rewrite Hyw.
      prove sqrt_SNo_nonneg w * sqrt_SNo_nonneg w < x.
      rewrite IHc.
      exact Hw3.
  + let y. rewrite tuple_2_1_eq.
    assume Hy: y :e {sqrt_SNo_nonneg z|z :e SNoR x}.
    prove SNo y /\ 0 <= y /\ x < y * y.
    apply ReplE_impred (SNoR x) sqrt_SNo_nonneg y Hy.
    let z. assume Hz: z :e SNoR x.
    assume Hyz: y = sqrt_SNo_nonneg z.
    apply SNoR_E x Hx z Hz.
    assume Hz1 Hz2 Hz3.
    claim Lz: z :e SNoS_ (SNoLev x).
    { exact SNoS_I2 z x Hz1 Hx Hz2. }
    claim Lznonneg: 0 <= z.
    { exact SNoLe_tra 0 x z SNo_0 Hx Hz1 Hxnonneg (SNoLtLe x z Hz3). }
    apply IH z Lz Lznonneg. assume H. apply H.
    assume IHa: SNo (sqrt_SNo_nonneg z).
    assume IHb: 0 <= sqrt_SNo_nonneg z.
    assume IHc: sqrt_SNo_nonneg z * sqrt_SNo_nonneg z = z.
    apply and3I.
    * rewrite Hyz. exact IHa.
    * rewrite Hyz. exact IHb.
    * rewrite Hyz.
      prove x < sqrt_SNo_nonneg z * sqrt_SNo_nonneg z.
      rewrite IHc.
      exact Hz3.
- let k. assume Hk: nat_p k.
  assume IHk: (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
  apply IHk.
  assume IHk0 IHk1.
  prove (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc k) 0, SNo y /\ 0 <= y /\ y * y < x)
     /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc k) 1, SNo y /\ 0 <= y /\ x < y * y).
  rewrite SNo_sqrtaux_S x sqrt_SNo_nonneg k Hk. apply andI.
  + let y. rewrite tuple_2_0_eq.
    apply binunionE'.
    * exact IHk0 y.
    * { assume Hy: y :e SNo_sqrtauxset (L_ k) (R_ k) x.
        apply SNo_sqrtauxset_E (L_ k) (R_ k) x y Hy.
        let w. assume Hw: w :e L_ k.
        let z. assume Hz: z :e R_ k.
        assume Hwpzpos: 0 < w + z.
        assume Hywz: y = (x + w * z) :/: (w + z).
        apply IHk0 w Hw. assume H. apply H.
        assume Hw1: SNo w.
        assume Hw2: 0 <= w.
        assume Hw3: w * w < x.
        apply IHk1 z Hz. assume H. apply H.
        assume Hz1: SNo z.
        assume Hz2: 0 <= z.
        assume Hz3: x < z * z.
        prove SNo y /\ 0 <= y /\ y * y < x.
        claim Lwz: SNo (w * z).
        { exact SNo_mul_SNo w z Hw1 Hz1. }
        claim Lxpwz: SNo (x + w * z).
        { exact SNo_add_SNo x (w * z) Hx Lwz. }
        claim Lwpz: SNo (w + z).
        { exact SNo_add_SNo w z Hw1 Hz1. }
        claim Ly: SNo y.
        { rewrite Hywz.
          exact SNo_div_SNo (x + w * z) (w + z) Lxpwz Lwpz.
        }
        claim Lxpwznonneg: 0 <= x + w * z.
        { rewrite <- add_SNo_0L 0 SNo_0.
          apply add_SNo_Le3 0 0 x (w * z) SNo_0 SNo_0 Hx Lwz Hxnonneg.
          prove 0 <= w * z.
          exact mul_SNo_nonneg_nonneg w z Hw1 Hz1 Hw2 Hz2.
        }
        claim Lynonneg: 0 <= y.
        { prove 0 <= y. rewrite Hywz.
          prove 0 <= (x + w * z) :/: (w + z).
          apply SNoLeE 0 (x + w * z) SNo_0 Lxpwz Lxpwznonneg.
          - assume H1: 0 < x + w * z.
            apply SNoLtLe.
            apply div_SNo_pos_pos (x + w * z) (w + z) Lxpwz Lwpz.
            + prove 0 < x + w * z. exact H1.
            + prove 0 < w + z. exact Hwpzpos.
          - assume H1: 0 = x + w * z. rewrite <- H1.
            prove 0 <= 0 :/: (w + z).
            rewrite div_SNo_0_num (w + z) Lwpz.
            apply SNoLe_ref.
        }
        apply and3I.
        - exact Ly.
        - exact Lynonneg.
        - prove y * y < x.
          rewrite Hywz.
          prove ((x + w * z) :/: (w + z)) * ((x + w * z) :/: (w + z)) < x.
          rewrite mul_div_SNo_both (x + w * z) (w + z) (x + w * z) (w + z) Lxpwz Lwpz Lxpwz Lwpz.
          prove ((x + w * z) * (x + w * z)) :/: ((w + z) * (w + z)) < x.
          apply div_SNo_pos_LtL ((x + w * z) * (x + w * z)) ((w + z) * (w + z)) x (SNo_mul_SNo (x + w * z) (x + w * z) Lxpwz Lxpwz) (SNo_mul_SNo (w + z) (w + z) Lwpz Lwpz) Hx.
          + prove 0 < (w + z) * (w + z).
            exact mul_SNo_pos_pos (w + z) (w + z) Lwpz Lwpz Hwpzpos Hwpzpos.
          + prove ((x + w * z) * (x + w * z)) < x * ((w + z) * (w + z)).
            rewrite SNo_foil x (w * z) x (w * z) Hx Lwz.
            rewrite SNo_foil w z w z Hw1 Hz1 Hw1 Hz1.
            prove x * x + x * w * z + (w * z) * x + (w * z) * w * z
                < x * (w * w + w * z + z * w + z * z).
            rewrite mul_SNo_com z w Hz1 Hw1.
            rewrite <- add_SNo_rotate_4_1 (w * z) (w * z) (z * z) (w * w) Lwz Lwz (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1).
            prove x * x + x * w * z + (w * z) * x + (w * z) * w * z
                < x * (w * z + w * z + z * z + w * w).
            rewrite mul_SNo_com (w * z) x Lwz Hx.
            prove x * x + x * w * z + x * w * z + (w * z) * w * z
                < x * (w * z + w * z + z * z + w * w).
            claim Lxwz: SNo (x * w * z).
            { exact SNo_mul_SNo x (w * z) Hx Lwz. }
            rewrite <- add_SNo_rotate_4_1 (x * w * z) (x * w * z) ((w * z) * w * z) (x * x) Lxwz Lxwz (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx).
            prove x * w * z + x * w * z + (w * z) * w * z + x * x
                < x * (w * z + w * z + z * z + w * w).
            rewrite mul_SNo_distrL x (w * z) (w * z + z * z + w * w) Hx Lwz (SNo_add_SNo_3 (w * z) (z * z) (w * w) Lwz (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1)).
            prove x * w * z + x * w * z + (w * z) * w * z + x * x
                < x * w * z + x * (w * z + z * z + w * w).
            rewrite mul_SNo_distrL x (w * z) (z * z + w * w) Hx Lwz (SNo_add_SNo (z * z) (w * w) (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1)).
            prove x * w * z + x * w * z + (w * z) * w * z + x * x
                < x * w * z + x * w * z + x * (z * z + w * w).
            claim Lxwz: SNo (x * w * z).
            { exact SNo_mul_SNo_3 x w z Hx Hw1 Hz1. }
            apply add_SNo_Lt2 (x * w * z) (x * w * z + (w * z) * w * z + x * x) (x * w * z + x * (z * z + w * w)) Lxwz (SNo_add_SNo_3 (x * w * z) ((w * z) * w * z) (x * x) Lxwz (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx)) (SNo_add_SNo (x * w * z) (x * (z * z + w * w)) Lxwz (SNo_mul_SNo x (z * z + w * w) Hx (SNo_add_SNo (z * z) (w * w) (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1)))).
            prove x * w * z + (w * z) * w * z + x * x
                < x * w * z + x * (z * z + w * w).
            apply add_SNo_Lt2 (x * w * z) ((w * z) * w * z + x * x) (x * (z * z + w * w)) Lxwz (SNo_add_SNo ((w * z) * w * z) (x * x) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx)) (SNo_mul_SNo x (z * z + w * w) Hx (SNo_add_SNo (z * z) (w * w) (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1))).
            prove (w * z) * w * z + x * x < x * (z * z + w * w).
            rewrite mul_SNo_distrL x (z * z) (w * w) Hx (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1).
            prove (w * z) * w * z + x * x < x * z * z + x * w * w.
            rewrite mul_SNo_com x (w * w) Hx (SNo_mul_SNo w w Hw1 Hw1).
            prove (w * z) * w * z + x * x < x * z * z + (w * w) * x.
            rewrite <- add_SNo_0L ((w * z) * w * z + x * x) (SNo_add_SNo ((w * z) * w * z) (x * x) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx)).
            prove 0 + (w * z) * w * z + x * x < x * z * z + (w * w) * x.
            apply add_SNo_minus_Lt2 (x * z * z + (w * w) * x) ((w * z) * w * z + x * x) 0 (SNo_add_SNo (x * z * z) ((w * w) * x) (SNo_mul_SNo x (z * z) Hx (SNo_mul_SNo z z Hz1 Hz1)) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx)) (SNo_add_SNo ((w * z) * w * z) (x * x) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx)) SNo_0.
            prove 0 < (x * z * z + (w * w) * x) + - ((w * z) * w * z + x * x).
            rewrite <- add_SNo_assoc (x * z * z) ((w * w) * x) (- ((w * z) * w * z + x * x)) (SNo_mul_SNo x (z * z) Hx (SNo_mul_SNo z z Hz1 Hz1)) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * z) * w * z + x * x) (SNo_add_SNo ((w * z) * w * z) (x * x) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx))).
            rewrite minus_add_SNo_distr ((w * z) * w * z) (x * x) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz) (SNo_mul_SNo x x Hx Hx).
            prove 0 < x * z * z + (w * w) * x + - (w * z) * w * z + - x * x.
            rewrite add_SNo_rotate_3_1 ((w * w) * x) (- (w * z) * w * z) (- x * x) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * z) * w * z) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz)) (SNo_minus_SNo (x * x) (SNo_mul_SNo x x Hx Hx)).
            prove 0 < x * z * z + - x * x + (w * w) * x + - (w * z) * w * z.
            rewrite add_SNo_com ((w * w) * x) (- (w * z) * w * z) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * z) * w * z) (SNo_mul_SNo (w * z) (w * z) Lwz Lwz)).
            prove 0 < x * z * z + - x * x + - (w * z) * w * z + (w * w) * x.
            rewrite <- mul_SNo_assoc w z (w * z) Hw1 Hz1 Lwz.
            prove 0 < x * z * z + - x * x + - w * z * w * z + (w * w) * x.
            rewrite mul_SNo_com_3_0_1 z w z Hz1 Hw1 Hz1.
            prove 0 < x * z * z + - x * x + - w * w * z * z + (w * w) * x.
            rewrite mul_SNo_assoc w w (z * z) Hw1 Hw1 (SNo_mul_SNo z z Hz1 Hz1).
            rewrite <- SNo_foil_mm x (w * w) (z * z) x Hx (SNo_mul_SNo w w Hw1 Hw1) (SNo_mul_SNo z z Hz1 Hz1) Hx.
            prove 0 < (x + - w * w) * (z * z + - x).
            apply mul_SNo_pos_pos (x + - w * w) (z * z + - x) (SNo_add_SNo x (- w * w) Hx (SNo_minus_SNo (w * w) (SNo_mul_SNo w w Hw1 Hw1))) (SNo_add_SNo (z * z) (- x) (SNo_mul_SNo z z Hz1 Hz1) (SNo_minus_SNo x Hx)).
            * prove 0 < x + - w * w.
              exact SNoLt_minus_pos (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx Hw3.
            * prove 0 < z * z + - x.
              exact SNoLt_minus_pos x (z * z) Hx (SNo_mul_SNo z z Hz1 Hz1) Hz3.
            * exact Hx.
            * prove SNo (w * z). exact Lwz.
      }
  + let y. rewrite tuple_2_1_eq.
    apply binunionE'.
    * { apply binunionE'.
        - exact IHk1 y.
        - assume Hy: y :e SNo_sqrtauxset (L_ k) (L_ k) x.
          prove SNo y /\ 0 <= y /\ x < y * y.
          apply SNo_sqrtauxset_E (L_ k) (L_ k) x y Hy.
          let w. assume Hw: w :e L_ k.
          let w'. assume Hw': w' :e L_ k.
          assume Hww'pos: 0 < w + w'.
          assume Hyww': y = (x + w * w') :/: (w + w').
          apply IHk0 w Hw. assume H. apply H.
          assume Hw1: SNo w.
          assume Hw2: 0 <= w.
          assume Hw3: w * w < x.
          apply IHk0 w' Hw'. assume H. apply H.
          assume Hw'1: SNo w'.
          assume Hw'2: 0 <= w'.
          assume Hw'3: w' * w' < x.
          prove SNo y /\ 0 <= y /\ x < y * y.
          claim Lww': SNo (w * w').
          { exact SNo_mul_SNo w w' Hw1 Hw'1. }
          claim Lxpww': SNo (x + w * w').
          { exact SNo_add_SNo x (w * w') Hx Lww'. }
          claim Lwpw': SNo (w + w').
          { exact SNo_add_SNo w w' Hw1 Hw'1. }
          claim Ly: SNo y.
          { rewrite Hyww'.
            exact SNo_div_SNo (x + w * w') (w + w') Lxpww' Lwpw'.
          }
          claim Lxpww'nonneg: 0 <= x + w * w'.
          { rewrite <- add_SNo_0L 0 SNo_0.
            apply add_SNo_Le3 0 0 x (w * w') SNo_0 SNo_0 Hx Lww' Hxnonneg.
            prove 0 <= w * w'.
            exact mul_SNo_nonneg_nonneg w w' Hw1 Hw'1 Hw2 Hw'2.
          }
          claim Lynonneg: 0 <= y.
          { prove 0 <= y. rewrite Hyww'.
            prove 0 <= (x + w * w') :/: (w + w').
            apply SNoLeE 0 (x + w * w') SNo_0 Lxpww' Lxpww'nonneg.
            - assume H1: 0 < x + w * w'.
              apply SNoLtLe.
              apply div_SNo_pos_pos (x + w * w') (w + w') Lxpww' Lwpw'.
              + prove 0 < x + w * w'.
                exact H1.
              + prove 0 < w + w'. exact Hww'pos.
            - assume H1: 0 = x + w * w'. rewrite <- H1.
              prove 0 <= 0 :/: (w + w').
              rewrite div_SNo_0_num (w + w') Lwpw'.
              apply SNoLe_ref.
          }
          apply and3I.
          + exact Ly.
          + exact Lynonneg.
          + prove x < y * y.
            rewrite Hyww'.
            prove x < ((x + w * w') :/: (w + w')) * ((x + w * w') :/: (w + w')).
            rewrite mul_div_SNo_both (x + w * w') (w + w') (x + w * w') (w + w') Lxpww' Lwpw' Lxpww' Lwpw'.
            prove x < ((x + w * w') * (x + w * w')) :/: ((w + w') * (w + w')).
            apply div_SNo_pos_LtR ((x + w * w') * (x + w * w')) ((w + w') * (w + w')) x (SNo_mul_SNo (x + w * w') (x + w * w') Lxpww' Lxpww') (SNo_mul_SNo (w + w') (w + w') Lwpw' Lwpw') Hx.
            * prove 0 < (w + w') * (w + w').
              exact mul_SNo_pos_pos (w + w') (w + w') Lwpw' Lwpw' Hww'pos Hww'pos.
            * { prove x * ((w + w') * (w + w')) < ((x + w * w') * (x + w * w')).
                rewrite SNo_foil x (w * w') x (w * w') Hx Lww'.
                rewrite SNo_foil w w' w w' Hw1 Hw'1 Hw1 Hw'1.
                prove x * (w * w + w * w' + w' * w + w' * w')
                    < x * x + x * w * w' + (w * w') * x + (w * w') * w * w'.
                rewrite mul_SNo_com w' w Hw'1 Hw1.
                rewrite <- add_SNo_rotate_4_1 (w * w') (w * w') (w' * w') (w * w) Lww' Lww' (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1).
                prove x * (w * w' + w * w' + w' * w' + w * w)
                    < x * x + x * w * w' + (w * w') * x + (w * w') * w * w'.
                rewrite mul_SNo_com (w * w') x Lww' Hx.
                prove x * (w * w' + w * w' + w' * w' + w * w)
                    < x * x + x * w * w' + x * w * w' + (w * w') * w * w'.
                claim Lxww': SNo (x * w * w').
                { exact SNo_mul_SNo x (w * w') Hx Lww'. }
                rewrite <- add_SNo_rotate_4_1 (x * w * w') (x * w * w') ((w * w') * w * w') (x * x) Lxww' Lxww' (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx).
                prove x * (w * w' + w * w' + w' * w' + w * w)
                    < x * w * w' + x * w * w' + (w * w') * w * w' + x * x.
                rewrite mul_SNo_distrL x (w * w') (w * w' + w' * w' + w * w) Hx Lww' (SNo_add_SNo_3 (w * w') (w' * w') (w * w) Lww' (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1)).
                prove x * w * w' + x * (w * w' + w' * w' + w * w)
                    < x * w * w' + x * w * w' + (w * w') * w * w' + x * x.
                rewrite mul_SNo_distrL x (w * w') (w' * w' + w * w) Hx Lww' (SNo_add_SNo (w' * w') (w * w) (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1)).
                prove x * w * w' + x * w * w' + x * (w' * w' + w * w)
                    < x * w * w' + x * w * w' + (w * w') * w * w' + x * x.
                claim Lxww': SNo (x * w * w').
                { exact SNo_mul_SNo_3 x w w' Hx Hw1 Hw'1. }
                apply add_SNo_Lt2 (x * w * w') (x * w * w' + x * (w' * w' + w * w)) (x * w * w' + (w * w') * w * w' + x * x) Lxww' (SNo_add_SNo (x * w * w') (x * (w' * w' + w * w)) Lxww' (SNo_mul_SNo x (w' * w' + w * w) Hx (SNo_add_SNo (w' * w') (w * w) (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1)))) (SNo_add_SNo_3 (x * w * w') ((w * w') * w * w') (x * x) Lxww' (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx)).
                prove x * w * w' + x * (w' * w' + w * w)
                    < x * w * w' + (w * w') * w * w' + x * x.
                apply add_SNo_Lt2 (x * w * w') (x * (w' * w' + w * w)) ((w * w') * w * w' + x * x) Lxww' (SNo_mul_SNo x (w' * w' + w * w) Hx (SNo_add_SNo (w' * w') (w * w) (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1))) (SNo_add_SNo ((w * w') * w * w') (x * x) (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx)).
                prove x * (w' * w' + w * w) < (w * w') * w * w' + x * x.
                rewrite mul_SNo_distrL x (w' * w') (w * w) Hx (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_mul_SNo w w Hw1 Hw1).
                prove x * w' * w' + x * w * w < (w * w') * w * w' + x * x.
                rewrite mul_SNo_com x (w * w) Hx (SNo_mul_SNo w w Hw1 Hw1).
                prove x * w' * w' + (w * w) * x < (w * w') * w * w' + x * x.
                rewrite <- add_SNo_0L ((w * w') * w * w' + x * x) (SNo_add_SNo ((w * w') * w * w') (x * x) (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx)).
                prove x * w' * w' + (w * w) * x < 0 + (w * w') * w * w' + x * x.
                apply add_SNo_minus_Lt1 (x * w' * w' + (w * w) * x) ((w * w') * w * w' + x * x) 0 (SNo_add_SNo (x * w' * w') ((w * w) * x) (SNo_mul_SNo x (w' * w') Hx (SNo_mul_SNo w' w' Hw'1 Hw'1)) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx)) (SNo_add_SNo ((w * w') * w * w') (x * x) (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx)) SNo_0.
                prove (x * w' * w' + (w * w) * x) + - ((w * w') * w * w' + x * x) < 0.
                rewrite <- add_SNo_assoc (x * w' * w') ((w * w) * x) (- ((w * w') * w * w' + x * x)) (SNo_mul_SNo x (w' * w') Hx (SNo_mul_SNo w' w' Hw'1 Hw'1)) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * w') * w * w' + x * x) (SNo_add_SNo ((w * w') * w * w') (x * x) (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx))).
                rewrite minus_add_SNo_distr ((w * w') * w * w') (x * x) (SNo_mul_SNo (w * w') (w * w') Lww' Lww') (SNo_mul_SNo x x Hx Hx).
                prove x * w' * w' + (w * w) * x + - (w * w') * w * w' + - x * x < 0.
                rewrite add_SNo_rotate_3_1 ((w * w) * x) (- (w * w') * w * w') (- x * x) (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * w') * w * w') (SNo_mul_SNo (w * w') (w * w') Lww' Lww')) (SNo_minus_SNo (x * x) (SNo_mul_SNo x x Hx Hx)).
                prove x * w' * w' + - x * x + (w * w) * x + - (w * w') * w * w' < 0.
                rewrite add_SNo_com ((w * w) * x) (- (w * w') * w * w') (SNo_mul_SNo (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx) (SNo_minus_SNo ((w * w') * w * w') (SNo_mul_SNo (w * w') (w * w') Lww' Lww')).
                prove x * w' * w' + - x * x + - (w * w') * w * w' + (w * w) * x < 0.
                rewrite <- mul_SNo_assoc w w' (w * w') Hw1 Hw'1 Lww'.
                prove x * w' * w' + - x * x + - w * w' * w * w' + (w * w) * x < 0.
                rewrite mul_SNo_com_3_0_1 w' w w' Hw'1 Hw1 Hw'1.
                prove x * w' * w' + - x * x + - w * w * w' * w' + (w * w) * x < 0.
                rewrite mul_SNo_assoc w w (w' * w') Hw1 Hw1 (SNo_mul_SNo w' w' Hw'1 Hw'1).
                rewrite <- SNo_foil_mm x (w * w) (w' * w') x Hx (SNo_mul_SNo w w Hw1 Hw1) (SNo_mul_SNo w' w' Hw'1 Hw'1) Hx.
                prove (x + - w * w) * (w' * w' + - x) < 0.
                apply mul_SNo_pos_neg (x + - w * w) (w' * w' + - x) (SNo_add_SNo x (- w * w) Hx (SNo_minus_SNo (w * w) (SNo_mul_SNo w w Hw1 Hw1))) (SNo_add_SNo (w' * w') (- x) (SNo_mul_SNo w' w' Hw'1 Hw'1) (SNo_minus_SNo x Hx)).
                - prove 0 < x + - w * w.
                  exact SNoLt_minus_pos (w * w) x (SNo_mul_SNo w w Hw1 Hw1) Hx Hw3.
                - prove w' * w' + - x < 0.
                  apply add_SNo_minus_Lt1b (w' * w') x 0 (SNo_mul_SNo w' w' Hw'1 Hw'1) Hx SNo_0.
                  prove w' * w' < 0 + x.
                  rewrite add_SNo_0L x Hx.
                  prove w' * w' < x.
                  exact Hw'3.
                - exact Hx.
                - prove SNo (w * w'). exact Lww'.
              }
      }
    * { assume Hy: y :e SNo_sqrtauxset (R_ k) (R_ k) x.
        prove SNo y /\ 0 <= y /\ x < y * y.
        apply SNo_sqrtauxset_E (R_ k) (R_ k) x y Hy.
        let z. assume Hz: z :e R_ k.
        let z'. assume Hz': z' :e R_ k.
        assume Hzz'pos: 0 < z + z'.
        assume Hyzz': y = (x + z * z') :/: (z + z').
        apply IHk1 z Hz. assume H. apply H.
        assume Hz1: SNo z.
        assume Hz2: 0 <= z.
        assume Hz3: x < z * z.
        apply IHk1 z' Hz'. assume H. apply H.
        assume Hz'1: SNo z'.
        assume Hz'2: 0 <= z'.
        assume Hz'3: x < z' * z'.
        prove SNo y /\ 0 <= y /\ x < y * y.
        claim Lzz': SNo (z * z').
        { exact SNo_mul_SNo z z' Hz1 Hz'1. }
        claim Lxpzz': SNo (x + z * z').
        { exact SNo_add_SNo x (z * z') Hx Lzz'. }
        claim Lzpz': SNo (z + z').
        { exact SNo_add_SNo z z' Hz1 Hz'1. }
        claim Ly: SNo y.
        { rewrite Hyzz'.
          exact SNo_div_SNo (x + z * z') (z + z') Lxpzz' Lzpz'.
        }
        claim Lxpzz'nonneg: 0 <= x + z * z'.
        { rewrite <- add_SNo_0L 0 SNo_0.
          apply add_SNo_Le3 0 0 x (z * z') SNo_0 SNo_0 Hx Lzz' Hxnonneg.
          prove 0 <= z * z'.
          exact mul_SNo_nonneg_nonneg z z' Hz1 Hz'1 Hz2 Hz'2.
        }
        claim Lynonneg: 0 <= y.
        { prove 0 <= y. rewrite Hyzz'.
          prove 0 <= (x + z * z') :/: (z + z').
          apply SNoLeE 0 (x + z * z') SNo_0 Lxpzz' Lxpzz'nonneg.
          - assume H1: 0 < x + z * z'.
            apply SNoLtLe.
            apply div_SNo_pos_pos (x + z * z') (z + z') Lxpzz' Lzpz'.
            + prove 0 < x + z * z'. exact H1.
            + prove 0 < z + z'. exact Hzz'pos.
          - assume H1: 0 = x + z * z'. rewrite <- H1.
            prove 0 <= 0 :/: (z + z').
            rewrite div_SNo_0_num (z + z') Lzpz'.
            apply SNoLe_ref.
        }
        apply and3I.
        - exact Ly.
        - exact Lynonneg.
        - prove x < y * y.
          rewrite Hyzz'.
          prove x < ((x + z * z') :/: (z + z')) * ((x + z * z') :/: (z + z')).
          rewrite mul_div_SNo_both (x + z * z') (z + z') (x + z * z') (z + z') Lxpzz' Lzpz' Lxpzz' Lzpz'.
          prove x < ((x + z * z') * (x + z * z')) :/: ((z + z') * (z + z')).
          apply div_SNo_pos_LtR ((x + z * z') * (x + z * z')) ((z + z') * (z + z')) x (SNo_mul_SNo (x + z * z') (x + z * z') Lxpzz' Lxpzz') (SNo_mul_SNo (z + z') (z + z') Lzpz' Lzpz') Hx.
          + prove 0 < (z + z') * (z + z').
            exact mul_SNo_pos_pos (z + z') (z + z') Lzpz' Lzpz' Hzz'pos Hzz'pos.
          + prove x * ((z + z') * (z + z')) < ((x + z * z') * (x + z * z')).
            rewrite SNo_foil x (z * z') x (z * z') Hx Lzz'.
            rewrite SNo_foil z z' z z' Hz1 Hz'1 Hz1 Hz'1.
            prove x * (z * z + z * z' + z' * z + z' * z')
                < x * x + x * z * z' + (z * z') * x + (z * z') * z * z'.
            rewrite mul_SNo_com z' z Hz'1 Hz1.
            rewrite <- add_SNo_rotate_4_1 (z * z') (z * z') (z' * z') (z * z) Lzz' Lzz' (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1).
            prove x * (z * z' + z * z' + z' * z' + z * z)
                < x * x + x * z * z' + (z * z') * x + (z * z') * z * z'.
            rewrite mul_SNo_com (z * z') x Lzz' Hx.
            prove x * (z * z' + z * z' + z' * z' + z * z)
                < x * x + x * z * z' + x * z * z' + (z * z') * z * z'.
            claim Lxzz': SNo (x * z * z').
            { exact SNo_mul_SNo x (z * z') Hx Lzz'. }
            rewrite <- add_SNo_rotate_4_1 (x * z * z') (x * z * z') ((z * z') * z * z') (x * x) Lxzz' Lxzz' (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx).
            prove x * (z * z' + z * z' + z' * z' + z * z)
                < x * z * z' + x * z * z' + (z * z') * z * z' + x * x.
            rewrite mul_SNo_distrL x (z * z') (z * z' + z' * z' + z * z) Hx Lzz' (SNo_add_SNo_3 (z * z') (z' * z') (z * z) Lzz' (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1)).
            prove x * z * z' + x * (z * z' + z' * z' + z * z)
                < x * z * z' + x * z * z' + (z * z') * z * z' + x * x.
            rewrite mul_SNo_distrL x (z * z') (z' * z' + z * z) Hx Lzz' (SNo_add_SNo (z' * z') (z * z) (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1)).
            prove x * z * z' + x * z * z' + x * (z' * z' + z * z)
                < x * z * z' + x * z * z' + (z * z') * z * z' + x * x.
            claim Lxzz': SNo (x * z * z').
            { exact SNo_mul_SNo_3 x z z' Hx Hz1 Hz'1. }
            apply add_SNo_Lt2 (x * z * z') (x * z * z' + x * (z' * z' + z * z)) (x * z * z' + (z * z') * z * z' + x * x) Lxzz' (SNo_add_SNo (x * z * z') (x * (z' * z' + z * z)) Lxzz' (SNo_mul_SNo x (z' * z' + z * z) Hx (SNo_add_SNo (z' * z') (z * z) (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1)))) (SNo_add_SNo_3 (x * z * z') ((z * z') * z * z') (x * x) Lxzz' (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx)).
            prove x * z * z' + x * (z' * z' + z * z)
                < x * z * z' + (z * z') * z * z' + x * x.
            apply add_SNo_Lt2 (x * z * z') (x * (z' * z' + z * z)) ((z * z') * z * z' + x * x) Lxzz' (SNo_mul_SNo x (z' * z' + z * z) Hx (SNo_add_SNo (z' * z') (z * z) (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1))) (SNo_add_SNo ((z * z') * z * z') (x * x) (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx)).
            prove x * (z' * z' + z * z) < (z * z') * z * z' + x * x.
            rewrite mul_SNo_distrL x (z' * z') (z * z) Hx (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_mul_SNo z z Hz1 Hz1).
            prove x * z' * z' + x * z * z < (z * z') * z * z' + x * x.
            rewrite mul_SNo_com x (z * z) Hx (SNo_mul_SNo z z Hz1 Hz1).
            prove x * z' * z' + (z * z) * x < (z * z') * z * z' + x * x.
            rewrite <- add_SNo_0L ((z * z') * z * z' + x * x) (SNo_add_SNo ((z * z') * z * z') (x * x) (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx)).
            prove x * z' * z' + (z * z) * x < 0 + (z * z') * z * z' + x * x.
            apply add_SNo_minus_Lt1 (x * z' * z' + (z * z) * x) ((z * z') * z * z' + x * x) 0 (SNo_add_SNo (x * z' * z') ((z * z) * x) (SNo_mul_SNo x (z' * z') Hx (SNo_mul_SNo z' z' Hz'1 Hz'1)) (SNo_mul_SNo (z * z) x (SNo_mul_SNo z z Hz1 Hz1) Hx)) (SNo_add_SNo ((z * z') * z * z') (x * x) (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx)) SNo_0.
            prove (x * z' * z' + (z * z) * x) + - ((z * z') * z * z' + x * x) < 0.
            rewrite <- add_SNo_assoc (x * z' * z') ((z * z) * x) (- ((z * z') * z * z' + x * x)) (SNo_mul_SNo x (z' * z') Hx (SNo_mul_SNo z' z' Hz'1 Hz'1)) (SNo_mul_SNo (z * z) x (SNo_mul_SNo z z Hz1 Hz1) Hx) (SNo_minus_SNo ((z * z') * z * z' + x * x) (SNo_add_SNo ((z * z') * z * z') (x * x) (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx))).
            rewrite minus_add_SNo_distr ((z * z') * z * z') (x * x) (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz') (SNo_mul_SNo x x Hx Hx).
            prove x * z' * z' + (z * z) * x + - (z * z') * z * z' + - x * x < 0.
            rewrite add_SNo_rotate_3_1 ((z * z) * x) (- (z * z') * z * z') (- x * x) (SNo_mul_SNo (z * z) x (SNo_mul_SNo z z Hz1 Hz1) Hx) (SNo_minus_SNo ((z * z') * z * z') (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz')) (SNo_minus_SNo (x * x) (SNo_mul_SNo x x Hx Hx)).
            prove x * z' * z' + - x * x + (z * z) * x + - (z * z') * z * z' < 0.
            rewrite add_SNo_com ((z * z) * x) (- (z * z') * z * z') (SNo_mul_SNo (z * z) x (SNo_mul_SNo z z Hz1 Hz1) Hx) (SNo_minus_SNo ((z * z') * z * z') (SNo_mul_SNo (z * z') (z * z') Lzz' Lzz')).
            prove x * z' * z' + - x * x + - (z * z') * z * z' + (z * z) * x < 0.
            rewrite <- mul_SNo_assoc z z' (z * z') Hz1 Hz'1 Lzz'.
            prove x * z' * z' + - x * x + - z * z' * z * z' + (z * z) * x < 0.
            rewrite mul_SNo_com_3_0_1 z' z z' Hz'1 Hz1 Hz'1.
            prove x * z' * z' + - x * x + - z * z * z' * z' + (z * z) * x < 0.
            rewrite mul_SNo_assoc z z (z' * z') Hz1 Hz1 (SNo_mul_SNo z' z' Hz'1 Hz'1).
            rewrite <- SNo_foil_mm x (z * z) (z' * z') x Hx (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo z' z' Hz'1 Hz'1) Hx.
            prove (x + - z * z) * (z' * z' + - x) < 0.
            apply mul_SNo_neg_pos (x + - z * z) (z' * z' + - x) (SNo_add_SNo x (- z * z) Hx (SNo_minus_SNo (z * z) (SNo_mul_SNo z z Hz1 Hz1))) (SNo_add_SNo (z' * z') (- x) (SNo_mul_SNo z' z' Hz'1 Hz'1) (SNo_minus_SNo x Hx)).
            * prove x + - z * z < 0.
              apply add_SNo_minus_Lt1b x (z * z) 0 Hx (SNo_mul_SNo z z Hz1 Hz1) SNo_0.
              prove x < 0 + z * z.
              rewrite add_SNo_0L (z * z) (SNo_mul_SNo z z Hz1 Hz1).
              prove x < z * z.
              exact Hz3.
            * prove 0 < z' * z' + - x.
              exact SNoLt_minus_pos x (z' * z') Hx (SNo_mul_SNo z' z' Hz'1 Hz'1) Hz'3.
            * exact Hx.
            * prove SNo (z * z'). exact Lzz'.
      }
Qed.

Theorem sqrt_SNo_nonneg_prop1b: forall x, SNo x -> 0 <= x
 -> (forall k, nat_p k ->
              (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y))
 -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1).
let x. assume Hx Hxnonneg.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
assume H0: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
prove (forall x :e L, SNo x)
   /\ (forall y :e R, SNo y)
   /\ (forall x :e L, forall y :e R, x < y).
apply and3I.
- let w. assume Hw: w :e L.
  apply famunionE_impred omega L_ w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e L_ k.
  apply H0 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume H3 _. apply H3. assume H3 _.
  exact H3.
- let z. assume Hz: z :e R.
  apply famunionE_impred omega R_ z Hz.
  let k. assume Hk: k :e omega.
  assume H1: z :e R_ k.
  apply H0 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 z H1.
  assume H3 _. apply H3. assume H3 _. exact H3.
- let w. assume Hw: w :e L.
  let z. assume Hz: z :e R.
  prove w < z.
  apply famunionE_impred omega L_ w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e L_ k.
  apply H0 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1. assume H. apply H.
  assume Hw1: SNo w.
  assume Hw2: 0 <= w.
  assume Hw3: w * w < x.
  apply famunionE_impred omega R_ z Hz.
  let k'. assume Hk': k' :e omega.
  assume H3: z :e R_ k'.
  apply H0 k' (omega_nat_p k' Hk').
  assume _ H4.
  apply H4 z H3. assume H. apply H.
  assume Hz1: SNo z.
  assume Hz2: 0 <= z.
  assume Hz3: x < z * z.
  prove w < z.
  apply SNoLtLe_or w z Hw1 Hz1.
  + assume H5: w < z. exact H5.
  + assume H5: z <= w. prove False.
    apply SNoLt_irref x.
    prove x < x.
    apply SNoLt_tra x (z * z) x Hx (SNo_mul_SNo z z Hz1 Hz1) Hx Hz3.
    prove z * z < x.
    apply SNoLeLt_tra (z * z) (w * w) x (SNo_mul_SNo z z Hz1 Hz1) (SNo_mul_SNo w w Hw1 Hw1) Hx.
    * prove z * z <= w * w.
      exact nonneg_mul_SNo_Le2 z z w w Hz1 Hz1 Hw1 Hw1 Hz2 Hz2 H5 H5.
    * exact Hw3.
Qed.

Theorem sqrt_SNo_nonneg_prop1c: forall x, SNo x -> 0 <= x ->
    SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
 -> (forall z :e (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1), forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p)
 -> 0 <= G x sqrt_SNo_nonneg.
let x. assume Hx Hxnonneg H1 H1R.
rewrite <- SNoCut_0_0 at 1.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
prove SNoCut 0 0 <= SNoCut L R.
apply SNoCut_Le 0 0 L R.
- prove SNoCutP 0 0. exact SNoCutP_0_0.
- exact H1.
- let w. assume Hw: w :e 0. prove False. exact EmptyE w Hw.
- let z. assume Hz: z :e R.
  prove SNoCut 0 0 < z.
  rewrite SNoCut_0_0.
  prove 0 < z.
  apply H1R z Hz.
  assume Hz1: SNo z.
  assume Hz2: 0 <= z.
  assume Hz3: x < z * z.
  apply SNoLeE 0 z SNo_0 Hz1 Hz2.
  + assume H6: 0 < z. exact H6.
  + assume H6: 0 = z. prove False.
    apply SNoLt_irref x.
    prove x < x.
    apply SNoLtLe_tra x 0 x Hx SNo_0 Hx.
    * prove x < 0.
      rewrite <- mul_SNo_zeroR 0 SNo_0.
      prove x < 0 * 0.
      rewrite H6. exact Hz3.
    * prove 0 <= x. exact Hxnonneg.
Qed.

Theorem sqrt_SNo_nonneg_prop1d: forall x, SNo x -> 0 <= x
  -> (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
  -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
  -> 0 <= G x sqrt_SNo_nonneg
  -> G x sqrt_SNo_nonneg * G x sqrt_SNo_nonneg < x
  -> False.
let x.
assume Hx Hxnonneg IH HLR.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
set y := SNoCut L R.
assume Hynn: 0 <= y.
assume H6: y * y < x.
apply HLR.
assume HLHR. apply HLHR.
assume HL: forall w :e L, SNo w.
assume HR: forall z :e R, SNo z.
assume HLR': forall w :e L, forall z :e R, w < z.
apply SNoCutP_SNoCut_impred L R HLR.
assume H1: SNo y.
assume H2: SNoLev y :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall w :e L, w < y.
assume H4: forall z :e R, y < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
claim Lyy: SNo (y * y).
{ exact SNo_mul_SNo y y H1 H1. }
claim Lyynn: 0 <= y * y.
{ exact mul_SNo_nonneg_nonneg y y H1 H1 Hynn Hynn. }
claim LL_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> L_ k c= L_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume H _. exact H.
}
claim LR_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> R_ k c= R_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume _ H. exact H.
}
claim L1: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
{ exact sqrt_SNo_nonneg_prop1a x Hx Hxnonneg IH. }
claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
{ let w. assume Hw. let p. assume Hp.
  apply famunionE_impred omega L_ w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e L_ k.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume H3. apply H3.
  exact Hp.
}
claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
{ let z. assume Hz. let p. assume Hp.
  apply famunionE_impred omega R_ z Hz.
  let k. assume Hk: k :e omega.
  assume H1: z :e R_ k.
  apply L1 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 z H1.
  assume H3. apply H3.
  exact Hp.
}
apply SNoLtE (y * y) x Lyy Hx H6.
- let u.
  assume Hu1: SNo u.
  assume Hu2: SNoLev u :e SNoLev (y * y) :/\: SNoLev x.
  assume Hu3: SNoEq_ (SNoLev u) u (y * y).
  assume Hu4: SNoEq_ (SNoLev u) u x.
  assume Hu5: y * y < u.
  assume Hu6: u < x.
  prove False.
(** In this case u is in SNoL x. And 0 <= y times y < u.
    So u is in SNoL_nonneg x.
    So sqrt u in L and sqrt u < y.
    u = sqrt u times sqrt u < y times y, contradiction to Hu5.
 **)
  claim Lunn: 0 <= u.
  { apply SNoLtLe.
    exact SNoLeLt_tra 0 (y * y) u SNo_0 Lyy Hu1 Lyynn Hu5.
  }
  claim LuSx: u :e SNoS_ (SNoLev x).
  { apply SNoS_I2 u x Hu1 Hx.
    prove SNoLev u :e SNoLev x.
    exact binintersectE2 (SNoLev (y * y)) (SNoLev x) (SNoLev u) Hu2.
  }
  apply IH u LuSx Lunn. assume H. apply H.
  assume H7: SNo (sqrt_SNo_nonneg u).
  assume H8: 0 <= sqrt_SNo_nonneg u.
  assume H9: sqrt_SNo_nonneg u * sqrt_SNo_nonneg u = u.
  claim Lsruy: sqrt_SNo_nonneg u <= y.
  { apply SNoLtLe.
    prove sqrt_SNo_nonneg u < y.
    apply H3.
    prove sqrt_SNo_nonneg u :e L.
    claim Lsruy0: sqrt_SNo_nonneg u :e L_ 0.
    { prove sqrt_SNo_nonneg u :e SNo_sqrtaux x sqrt_SNo_nonneg 0 0.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_0_eq.
      prove sqrt_SNo_nonneg u :e {sqrt_SNo_nonneg w|w :e SNoL_nonneg x}.
      apply ReplI.
      prove u :e {w :e SNoL x|0 <= w}.
      apply SepI.
      - apply SNoL_I x Hx u Hu1.
        + exact binintersectE2 (SNoLev (y * y)) (SNoLev x) (SNoLev u) Hu2.
        + prove u < x. exact Hu6.
      - exact Lunn.
    }
    exact famunionI omega L_ 0 (sqrt_SNo_nonneg u) (nat_p_omega 0 nat_0) Lsruy0.
  }
  claim Luyy: u <= y * y.
  { rewrite <- H9.
    prove sqrt_SNo_nonneg u * sqrt_SNo_nonneg u <= y * y.
    exact nonneg_mul_SNo_Le2 (sqrt_SNo_nonneg u) (sqrt_SNo_nonneg u) y y H7 H7 H1 H1 H8 H8 Lsruy Lsruy.
  }
  apply SNoLt_irref (y * y).
  prove y * y < y * y.
  exact SNoLtLe_tra (y * y) u (y * y) Lyy Hu1 Lyy Hu5 Luyy.
- assume H7: SNoLev (y * y) :e SNoLev x.
  prove False.
  (** In this case y times y is in SNoL x.
      Also 0 <= y times y so y times y is in SNoL_nonneg x.
      Hence y = sqrt (y times y) is in L giving y < y.
   **)
  claim Lsryy: sqrt_SNo_nonneg (y * y) = y.
  { apply IH (y * y) (SNoS_I2 (y * y) x Lyy Hx H7) Lyynn.
    assume H. apply H.
    assume H10: SNo (sqrt_SNo_nonneg (y * y)).
    assume H11: 0 <= sqrt_SNo_nonneg (y * y).
    assume H12: sqrt_SNo_nonneg (y * y) * sqrt_SNo_nonneg (y * y) = y * y.
    exact SNo_nonneg_sqr_uniq (sqrt_SNo_nonneg (y * y)) y H10 H1 H11 Hynn H12.
  }
  apply SNoLt_irref y.
  prove y < y.
  rewrite <- Lsryy at 1.
  prove sqrt_SNo_nonneg (y * y) < y.
  apply H3.
  prove sqrt_SNo_nonneg (y * y) :e \/_ k :e omega, L_ k.
  claim LyyL0: sqrt_SNo_nonneg (y * y) :e L_ 0.
  { prove sqrt_SNo_nonneg (y * y) :e SNo_sqrtaux x sqrt_SNo_nonneg 0 0.
    rewrite SNo_sqrtaux_0.
    rewrite tuple_2_0_eq.
    prove sqrt_SNo_nonneg (y * y) :e {sqrt_SNo_nonneg w|w :e SNoL_nonneg x}.
    apply ReplI.
    prove y * y :e SNoL_nonneg x.
    prove y * y :e {w :e SNoL x|0 <= w}.
    apply SepI.
    - exact SNoL_I x Hx (y * y) Lyy H7 H6.
    - prove 0 <= y * y. exact Lyynn.
  }
  exact famunionI omega L_ 0 (sqrt_SNo_nonneg (y * y)) (nat_p_omega 0 nat_0) LyyL0.
- assume H7: SNoLev x :e SNoLev (y * y).
  assume H8: SNoEq_ (SNoLev x) (y * y) x.
  assume H9: SNoLev x /:e y * y.
  claim L3: x :e SNoR (y * y).
  { exact SNoR_I (y * y) Lyy x Hx H7 H6. }
  claim L4: forall p:prop, (forall v :e L, forall w :e R, v * y + y * w <= x + v * w -> p) -> p.
  { let p. assume Hp.
    apply mul_SNo_SNoCut_SNoR_interpolate_impred L R L R HLR HLR y y (fun q H => H) (fun q H => H) x L3.
    - let v. assume Hv: v :e L.
      let w. assume Hw: w :e R.
      assume H10: v * y + y * w <= x + v * w.
      exact Hp v Hv w Hw H10.
    - let v. assume Hv: v :e R.
      let w. assume Hw: w :e L.
      assume H10: v * y + y * w <= x + v * w.
      apply Hp w Hw v Hv.
      prove w * y + y * v <= x + w * v.
      claim Lv1: SNo v.
      { exact HR v Hv. }
      claim Lw1: SNo w.
      { exact HL w Hw. }
      rewrite mul_SNo_com w v Lw1 Lv1.
      prove w * y + y * v <= x + v * w.
      apply mul_SNo_com w y Lw1 H1 (fun _ u => u + y * v <= x + v * w).
      prove y * w + y * v <= x + v * w.
      apply mul_SNo_com y v H1 Lv1 (fun _ u => y * w + u <= x + v * w).
      prove y * w + v * y <= x + v * w.
      apply add_SNo_com (y * w) (v * y) (SNo_mul_SNo y w H1 Lw1) (SNo_mul_SNo v y Lv1 H1) (fun _ u => u <= x + v * w).
      exact H10.
  }
  apply L4.
  let v. assume Hv: v :e L.
  let w. assume Hw: w :e R.
  assume H10: v * y + y * w <= x + v * w.
  apply L1L v Hv.
  assume Hv1: SNo v.
  assume Hv2: 0 <= v.
  assume Hv3: v * v < x.
  apply L1R w Hw.
  assume Hw1: SNo w.
  assume Hw2: 0 <= w.
  assume Hw3: x < w * w.
  claim L5: exists k, nat_p k /\ v :e L_ k /\ w :e R_ k.
  { apply famunionE omega L_ v Hv.
    let k'. assume H. apply H.
    assume Hk'1: k' :e omega.
    assume Hk'2: v :e L_ k'.
    apply famunionE omega R_ w Hw.
    let k''. assume H. apply H.
    assume Hk''1: k'' :e omega.
    assume Hk''2: w :e R_ k''.
    apply ordinal_linear k' k'' (nat_p_ordinal k' (omega_nat_p k' Hk'1)) (nat_p_ordinal k'' (omega_nat_p k'' Hk''1)).
    - assume H1: k' c= k''.
      witness k''.
      apply and3I.
      + exact omega_nat_p k'' Hk''1.
      + prove v :e L_ k''.
        exact LL_mon k' k'' (omega_nat_p k' Hk'1) (omega_nat_p k'' Hk''1) H1 v Hk'2.
      + exact Hk''2.
    - assume H1: k'' c= k'.
      witness k'.
      apply and3I.
      + exact omega_nat_p k' Hk'1.
      + exact Hk'2.
      + prove w :e R_ k'.
        exact LR_mon k'' k' (omega_nat_p k'' Hk''1) (omega_nat_p k' Hk'1) H1 w Hk''2.
  }
  apply L5. let k. assume H. apply H. assume H. apply H.
  assume Hk: nat_p k.
  assume Hvk: v :e L_ k.
  assume Hwk: w :e R_ k.
  claim Lvwpos: 0 < v + w.
  { apply SNoLeLt_tra 0 v (v + w) SNo_0 Hv1 (SNo_add_SNo v w Hv1 Hw1) Hv2.
    prove v < v + w.
    rewrite <- add_SNo_0R v Hv1 at 1.
    prove v + 0 < v + w.
    apply add_SNo_Lt2 v 0 w Hv1 SNo_0 Hw1.
    prove 0 < w.
    apply SNoLeLt_tra 0 y w SNo_0 H1 Hw1 Hynn.
    prove y < w. apply H4.
    prove w :e R.
    exact famunionI omega R_ k w (nat_p_omega k Hk) Hwk.
  }
  claim Lvw0: v + w <> 0.
  { assume H. apply SNoLt_irref 0. rewrite <- H at 2. exact Lvwpos. }
  claim L6: (x + v * w) :/: (v + w) :e L_ (ordsucc k).
  { prove (x + v * w) :/: (v + w) :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc k) 0.
    rewrite SNo_sqrtaux_S x sqrt_SNo_nonneg k Hk.
    rewrite tuple_2_0_eq.
    prove (x + v * w) :/: (v + w) :e L_ k :\/: SNo_sqrtauxset (L_ k) (R_ k) x.
    apply binunionI2.
    exact SNo_sqrtauxset_I (L_ k) (R_ k) x v Hvk w Hwk Lvwpos.
  }
  claim L7: (x + v * w) :/: (v + w) :e L.
  { exact famunionI omega L_ (ordsucc k) ((x + v * w) :/: (v + w)) (nat_p_omega (ordsucc k) (nat_ordsucc k Hk)) L6. }
  claim L8: (x + v * w) :/: (v + w) < y.
  { exact H3 ((x + v * w) :/: (v + w)) L7. }
  claim L9: v * y + y * w = y * (v + w).
  { transitivity y * v + y * w.
    - f_equal. prove v * y = y * v. exact mul_SNo_com v y Hv1 H1.
    - prove y * v + y * w = y * (v + w).
      symmetry.
      exact mul_SNo_distrL y v w H1 Hv1 Hw1.
  }
  prove False.
  apply SNoLt_irref (v * y + y * w).
  apply SNoLeLt_tra (v * y + y * w) (x + v * w) (v * y + y * w)
                    (SNo_add_SNo (v * y) (y * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo y w H1 Hw1))
                    (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                    (SNo_add_SNo (v * y) (y * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo y w H1 Hw1))
                    H10.
  prove x + v * w < v * y + y * w.
  rewrite L9.
  prove x + v * w < y * (v + w).
  rewrite <- mul_div_SNo_invL (x + v * w) (v + w)
                    (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                    (SNo_add_SNo v w Hv1 Hw1)
                    Lvw0.
  prove ((x + v * w) :/: (v + w)) * (v + w) < y * (v + w).
  exact pos_mul_SNo_Lt' ((x + v * w) :/: (v + w)) y (v + w)
                        (SNo_div_SNo (x + v * w) (v + w)
                          (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                          (SNo_add_SNo v w Hv1 Hw1))
                        H1
                        (SNo_add_SNo v w Hv1 Hw1)
                        Lvwpos
                        L8.
Qed.

Theorem sqrt_SNo_nonneg_prop1e: forall x, SNo x -> 0 <= x
  -> (forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w)
  -> SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
  -> 0 <= G x sqrt_SNo_nonneg
  -> x < G x sqrt_SNo_nonneg * G x sqrt_SNo_nonneg
  -> False.
let x.
assume Hx Hxnonneg IH HLR.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
set y := SNoCut L R.
assume Hynn: 0 <= y.
assume H6: x < y * y.
apply HLR.
assume HLHR. apply HLHR.
assume HL: forall w :e L, SNo w.
assume HR: forall z :e R, SNo z.
assume HLR': forall w :e L, forall z :e R, w < z.
apply SNoCutP_SNoCut_impred L R HLR.
assume H1: SNo y.
assume H2: SNoLev y :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall w :e L, w < y.
assume H4: forall z :e R, y < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
claim Lyy: SNo (y * y).
{ exact SNo_mul_SNo y y H1 H1. }
claim Lyynn: 0 <= y * y.
{ exact mul_SNo_nonneg_nonneg y y H1 H1 Hynn Hynn. }
claim LL_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> L_ k c= L_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume H _. exact H.
}
claim LR_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> R_ k c= R_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume _ H. exact H.
}
claim L1: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
{ exact sqrt_SNo_nonneg_prop1a x Hx Hxnonneg IH. }
claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
{ let w. assume Hw. let p. assume Hp.
  apply famunionE_impred omega L_ w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e L_ k.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume H3. apply H3.
  exact Hp.
}
claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
{ let z. assume Hz. let p. assume Hp.
  apply famunionE_impred omega R_ z Hz.
  let k. assume Hk: k :e omega.
  assume H1: z :e R_ k.
  apply L1 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 z H1.
  assume H3. apply H3.
  exact Hp.
}
apply SNoLtE x (y * y) Hx Lyy H6.
- let u.
  assume Hu1: SNo u.
  assume Hu2: SNoLev u :e SNoLev x :/\: SNoLev (y * y).
  assume Hu3: SNoEq_ (SNoLev u) u x.
  assume Hu4: SNoEq_ (SNoLev u) u (y * y).
  assume Hu5: x < u.
  assume Hu6: u < y * y.
  prove False.
  claim Lunn: 0 <= u.
  { apply SNoLtLe.
    exact SNoLeLt_tra 0 x u SNo_0 Hx Hu1 Hxnonneg Hu5.
  }
  claim LuSx: u :e SNoS_ (SNoLev x).
  { apply SNoS_I2 u x Hu1 Hx.
    prove SNoLev u :e SNoLev x.
    exact binintersectE1 (SNoLev x) (SNoLev (y * y)) (SNoLev u) Hu2.
  }
  apply IH u LuSx Lunn. assume H. apply H.
  assume H7: SNo (sqrt_SNo_nonneg u).
  assume H8: 0 <= sqrt_SNo_nonneg u.
  assume H9: sqrt_SNo_nonneg u * sqrt_SNo_nonneg u = u.
  claim Lysru: y <= sqrt_SNo_nonneg u.
  { apply SNoLtLe.
    prove y < sqrt_SNo_nonneg u.
    apply H4.
    prove sqrt_SNo_nonneg u :e R.
    claim Lysru0: sqrt_SNo_nonneg u :e R_ 0.
    { prove sqrt_SNo_nonneg u :e SNo_sqrtaux x sqrt_SNo_nonneg 0 1.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_1_eq.
      prove sqrt_SNo_nonneg u :e {sqrt_SNo_nonneg w|w :e SNoR x}.
      apply ReplI.
      apply SNoR_I x Hx u Hu1.
      - exact binintersectE1 (SNoLev x) (SNoLev (y * y)) (SNoLev u) Hu2.
      - prove x < u. exact Hu5.
    }
    exact famunionI omega R_ 0 (sqrt_SNo_nonneg u) (nat_p_omega 0 nat_0) Lysru0.
  }
  apply SNoLt_irref u.
  prove u < u.
  apply SNoLtLe_tra u (y * y) u Hu1 Lyy Hu1 Hu6.
  prove y * y <= u.
  rewrite <- H9.
  prove y * y <= sqrt_SNo_nonneg u * sqrt_SNo_nonneg u.
  exact nonneg_mul_SNo_Le2 y y (sqrt_SNo_nonneg u) (sqrt_SNo_nonneg u) H1 H1 H7 H7 Hynn Hynn Lysru Lysru.
- assume H7: SNoLev x :e SNoLev (y * y).
  assume H8: SNoEq_ (SNoLev x) x (y * y).
  assume H9: SNoLev x :e y * y.
  claim L10: x :e SNoL (y * y).
  { exact SNoL_I (y * y) Lyy x Hx H7 H6. }
  apply mul_SNo_SNoCut_SNoL_interpolate_impred L R L R HLR HLR y y (fun q H => H) (fun q H => H) x L10.
  + let v. assume Hv: v :e L.
    let w. assume Hw: w :e L.
    assume H10: x + v * w <= v * y + y * w.
    apply L1L v Hv.
    assume Hv1: SNo v.
    assume Hv2: 0 <= v.
    assume Hv3: v * v < x.
    apply L1L w Hw.
    assume Hw1: SNo w.
    assume Hw2: 0 <= w.
    assume Hw3: w * w < x.
    apply SNoLtLe_or 0 (v + w) SNo_0 (SNo_add_SNo v w Hv1 Hw1).
    * assume H11: 0 < v + w.
      claim L11: exists k, nat_p k /\ v :e L_ k /\ w :e L_ k.
      { apply famunionE omega L_ v Hv.
        let k'. assume H. apply H.
        assume Hk'1: k' :e omega.
        assume Hk'2: v :e L_ k'.
        apply famunionE omega L_ w Hw.
        let k''. assume H. apply H.
        assume Hk''1: k'' :e omega.
        assume Hk''2: w :e L_ k''.
        apply ordinal_linear k' k'' (nat_p_ordinal k' (omega_nat_p k' Hk'1)) (nat_p_ordinal k'' (omega_nat_p k'' Hk''1)).
        - assume H1: k' c= k''.
          witness k''.
          apply and3I.
          + exact omega_nat_p k'' Hk''1.
          + prove v :e L_ k''.
            exact LL_mon k' k'' (omega_nat_p k' Hk'1) (omega_nat_p k'' Hk''1) H1 v Hk'2.
          + exact Hk''2.
        - assume H1: k'' c= k'.
          witness k'.
          apply and3I.
          + exact omega_nat_p k' Hk'1.
          + exact Hk'2.
          + prove w :e L_ k'.
            exact LL_mon k'' k' (omega_nat_p k'' Hk''1) (omega_nat_p k' Hk'1) H1 w Hk''2.
      }
      apply L11. let k. assume H. apply H. assume H. apply H.
      assume Hk: nat_p k.
      assume Hvk: v :e L_ k.
      assume Hwk: w :e L_ k.
      claim Lvw0: v + w <> 0.
      { assume H. apply SNoLt_irref 0. rewrite <- H at 2. exact H11. }
      claim L12: (x + v * w) :/: (v + w) :e R_ (ordsucc k).
      { prove (x + v * w) :/: (v + w) :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc k) 1.
        rewrite SNo_sqrtaux_S x sqrt_SNo_nonneg k Hk.
        rewrite tuple_2_1_eq.
        prove (x + v * w) :/: (v + w) :e R_ k :\/: SNo_sqrtauxset (L_ k) (L_ k) x :\/: SNo_sqrtauxset (R_ k) (R_ k) x.
        apply binunionI1.
        apply binunionI2.
        exact SNo_sqrtauxset_I (L_ k) (L_ k) x v Hvk w Hwk H11.
      }
      claim L13: (x + v * w) :/: (v + w) :e R.
      { exact famunionI omega R_ (ordsucc k) ((x + v * w) :/: (v + w)) (nat_p_omega (ordsucc k) (nat_ordsucc k Hk)) L12. }
      claim L14: y < (x + v * w) :/: (v + w).
      { exact H4 ((x + v * w) :/: (v + w)) L13. }
      claim L15: v * y + y * w = y * (v + w).
      { transitivity y * v + y * w.
        - f_equal. prove v * y = y * v. exact mul_SNo_com v y Hv1 H1.
        - prove y * v + y * w = y * (v + w).
          symmetry.
          exact mul_SNo_distrL y v w H1 Hv1 Hw1.
      }
      prove False.
      apply SNoLt_irref (x + v * w).
      apply SNoLeLt_tra (x + v * w) (v * y + y * w) (x + v * w)
                        (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                        (SNo_add_SNo (v * y) (y * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo y w H1 Hw1))
                        (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                        H10.
      prove v * y + y * w < x + v * w.
      rewrite L15.
      prove y * (v + w) < x + v * w.
      rewrite <- mul_div_SNo_invL (x + v * w) (v + w)
                        (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                        (SNo_add_SNo v w Hv1 Hw1)
                        Lvw0.
      prove y * (v + w) < ((x + v * w) :/: (v + w)) * (v + w).
      exact pos_mul_SNo_Lt' y ((x + v * w) :/: (v + w)) (v + w)
                            H1
                            (SNo_div_SNo (x + v * w) (v + w)
                              (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                              (SNo_add_SNo v w Hv1 Hw1))
                            (SNo_add_SNo v w Hv1 Hw1)
                            H11
                            L14.
    * assume H11: v + w <= 0.
      claim L16: v = 0 /\ w = 0.
      { apply SNoLtLe_or 0 v SNo_0 Hv1.
        - assume H12: 0 < v. prove False.
          apply SNoLt_irref 0.
          apply SNoLtLe_tra 0 v 0 SNo_0 Hv1 SNo_0 H12.
          prove v <= 0.
          apply SNoLe_tra v (v + w) 0 Hv1 (SNo_add_SNo v w Hv1 Hw1) SNo_0.
          + prove v <= v + w.
            rewrite <- add_SNo_0R v Hv1 at 1.
            prove v + 0 <= v + w.
            exact add_SNo_Le2 v 0 w Hv1 SNo_0 Hw1 Hw2.
          + prove v + w <= 0. exact H11.
        - assume H12: v <= 0.
          apply SNoLtLe_or 0 w SNo_0 Hw1.
          + assume H13: 0 < w. prove False.
            apply SNoLt_irref 0.
            apply SNoLtLe_tra 0 w 0 SNo_0 Hw1 SNo_0 H13.
            prove w <= 0.
            apply SNoLe_tra w (v + w) 0 Hw1 (SNo_add_SNo v w Hv1 Hw1) SNo_0.
            * prove w <= v + w.
              rewrite <- add_SNo_0L w Hw1 at 1.
              prove 0 + w <= v + w.
              exact add_SNo_Le1 0 w v SNo_0 Hw1 Hv1 Hv2.
            * prove v + w <= 0. exact H11.
          + assume H13: w <= 0.
            apply andI.
            * exact SNoLe_antisym v 0 Hv1 SNo_0 H12 Hv2.
            * exact SNoLe_antisym w 0 Hw1 SNo_0 H13 Hw2.
      }
      apply L16.
      assume Hv0: v = 0.
      assume Hw0: w = 0.
      claim L17: x + v * w = x.
      { rewrite Hv0. rewrite mul_SNo_zeroL w Hw1. exact add_SNo_0R x Hx. }
      claim L18: v * y + y * w = 0.
      { rewrite Hv0.
        prove 0 * y + y * w = 0.
        apply mul_SNo_zeroL y H1 (fun _ u => u + y * w = 0).
        rewrite Hw0.
        prove 0 + y * 0 = 0.
        apply mul_SNo_zeroR y H1 (fun _ u => 0 + u = 0).
        exact add_SNo_0L 0 SNo_0.
      }
      claim L19: x <= 0.
      { rewrite <- L17. rewrite <- L18. exact H10. }
      claim L20: x = 0.
      { exact SNoLe_antisym x 0 Hx SNo_0 L19 Hxnonneg. }
      apply SNoLt_irref (v * v).
      prove v * v < v * v.
      rewrite Hv0 at 3.
      prove v * v < 0 * v.
      rewrite mul_SNo_zeroL v Hv1.
      prove v * v < 0.
      rewrite <- L20. exact Hv3.
  + let v. assume Hv: v :e R.
    let w. assume Hw: w :e R.
    assume H10: x + v * w <= v * y + y * w.
    apply L1R v Hv.
    assume Hv1: SNo v.
    assume Hv2: 0 <= v.
    assume Hv3: x < v * v.
    apply L1R w Hw.
    assume Hw1: SNo w.
    assume Hw2: 0 <= w.
    assume Hw3: x < w * w.
    claim L21: exists k, nat_p k /\ v :e R_ k /\ w :e R_ k.
    { apply famunionE omega R_ v Hv.
      let k'. assume H. apply H.
      assume Hk'1: k' :e omega.
      assume Hk'2: v :e R_ k'.
      apply famunionE omega R_ w Hw.
      let k''. assume H. apply H.
      assume Hk''1: k'' :e omega.
      assume Hk''2: w :e R_ k''.
      apply ordinal_linear k' k'' (nat_p_ordinal k' (omega_nat_p k' Hk'1)) (nat_p_ordinal k'' (omega_nat_p k'' Hk''1)).
      - assume H1: k' c= k''.
        witness k''.
        apply and3I.
        + exact omega_nat_p k'' Hk''1.
        + prove v :e R_ k''.
          exact LR_mon k' k'' (omega_nat_p k' Hk'1) (omega_nat_p k'' Hk''1) H1 v Hk'2.
        + exact Hk''2.
      - assume H1: k'' c= k'.
        witness k'.
        apply and3I.
        + exact omega_nat_p k' Hk'1.
        + exact Hk'2.
        + prove w :e R_ k'.
          exact LR_mon k'' k' (omega_nat_p k'' Hk''1) (omega_nat_p k' Hk'1) H1 w Hk''2.
    }
    apply L21. let k. assume H. apply H. assume H. apply H.
    assume Hk: nat_p k.
    assume Hvk: v :e R_ k.
    assume Hwk: w :e R_ k.
    claim Lvwpos: 0 < v + w.
    { apply SNoLeLt_tra 0 v (v + w) SNo_0 Hv1 (SNo_add_SNo v w Hv1 Hw1) Hv2.
      prove v < v + w.
      rewrite <- add_SNo_0R v Hv1 at 1.
      prove v + 0 < v + w.
      apply add_SNo_Lt2 v 0 w Hv1 SNo_0 Hw1.
      prove 0 < w.
      apply SNoLeLt_tra 0 y w SNo_0 H1 Hw1 Hynn.
      prove y < w. apply H4.
      prove w :e R.
      exact famunionI omega R_ k w (nat_p_omega k Hk) Hwk.
    }
    claim Lvw0: v + w <> 0.
    { assume H. apply SNoLt_irref 0. rewrite <- H at 2. exact Lvwpos. }
    claim L22: (x + v * w) :/: (v + w) :e R_ (ordsucc k).
    { prove (x + v * w) :/: (v + w) :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc k) 1.
      rewrite SNo_sqrtaux_S x sqrt_SNo_nonneg k Hk.
      rewrite tuple_2_1_eq.
      prove (x + v * w) :/: (v + w) :e R_ k :\/: SNo_sqrtauxset (L_ k) (L_ k) x :\/: SNo_sqrtauxset (R_ k) (R_ k) x.
      apply binunionI2.
      exact SNo_sqrtauxset_I (R_ k) (R_ k) x v Hvk w Hwk Lvwpos.
    }
    claim L23: (x + v * w) :/: (v + w) :e R.
    { exact famunionI omega R_ (ordsucc k) ((x + v * w) :/: (v + w)) (nat_p_omega (ordsucc k) (nat_ordsucc k Hk)) L22. }
    claim L24: y < (x + v * w) :/: (v + w).
    { exact H4 ((x + v * w) :/: (v + w)) L23. }
    claim L25: v * y + y * w = y * (v + w).
    { transitivity y * v + y * w.
      - f_equal. prove v * y = y * v. exact mul_SNo_com v y Hv1 H1.
      - prove y * v + y * w = y * (v + w).
        symmetry.
        exact mul_SNo_distrL y v w H1 Hv1 Hw1.
    }
    prove False.
    apply SNoLt_irref (x + v * w).
    apply SNoLeLt_tra (x + v * w) (v * y + y * w) (x + v * w)
                      (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                      (SNo_add_SNo (v * y) (y * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo y w H1 Hw1))
                      (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                      H10.
    prove v * y + y * w < x + v * w.
    rewrite L25.
    prove y * (v + w) < x + v * w.
    rewrite <- mul_div_SNo_invL (x + v * w) (v + w)
                      (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                      (SNo_add_SNo v w Hv1 Hw1)
                      Lvw0.
    prove y * (v + w) < ((x + v * w) :/: (v + w)) * (v + w).
    exact pos_mul_SNo_Lt' y ((x + v * w) :/: (v + w)) (v + w)
                          H1
                          (SNo_div_SNo (x + v * w) (v + w)
                            (SNo_add_SNo x (v * w) Hx (SNo_mul_SNo v w Hv1 Hw1))
                            (SNo_add_SNo v w Hv1 Hw1))
                          (SNo_add_SNo v w Hv1 Hw1)
                          Lvwpos
                          L24.
- assume H7: SNoLev (y * y) :e SNoLev x.
  prove False.
  claim Lsryy: sqrt_SNo_nonneg (y * y) = y.
  { apply IH (y * y) (SNoS_I2 (y * y) x Lyy Hx H7) Lyynn.
    assume H. apply H.
    assume H10: SNo (sqrt_SNo_nonneg (y * y)).
    assume H11: 0 <= sqrt_SNo_nonneg (y * y).
    assume H12: sqrt_SNo_nonneg (y * y) * sqrt_SNo_nonneg (y * y) = y * y.
    exact SNo_nonneg_sqr_uniq (sqrt_SNo_nonneg (y * y)) y H10 H1 H11 Hynn H12.
  }
  apply SNoLt_irref y.
  prove y < y.
  rewrite <- Lsryy at 2.
  prove y < sqrt_SNo_nonneg (y * y).
  apply H4.
  prove sqrt_SNo_nonneg (y * y) :e R.
  claim LyyR0: sqrt_SNo_nonneg (y * y) :e R_ 0.
  { prove sqrt_SNo_nonneg (y * y) :e SNo_sqrtaux x sqrt_SNo_nonneg 0 1.
    rewrite SNo_sqrtaux_0.
    rewrite tuple_2_1_eq.
    prove sqrt_SNo_nonneg (y * y) :e {sqrt_SNo_nonneg w|w :e SNoR x}.
    apply ReplI.
    prove y * y :e SNoR x.
    exact SNoR_I x Hx (y * y) Lyy H7 H6.
  }
  exact famunionI omega R_ 0 (sqrt_SNo_nonneg (y * y)) (nat_p_omega 0 nat_0) LyyR0.
Qed.

Theorem sqrt_SNo_nonneg_prop1: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x) /\ 0 <= sqrt_SNo_nonneg x /\ sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w.
assume Hxnonneg: 0 <= x.
prove SNo (sqrt_SNo_nonneg x) /\ 0 <= sqrt_SNo_nonneg x /\ sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
rewrite sqrt_SNo_nonneg_eq x Hx.
prove SNo (G x sqrt_SNo_nonneg) /\ 0 <= G x sqrt_SNo_nonneg /\ G x sqrt_SNo_nonneg * G x sqrt_SNo_nonneg = x.
set L_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ : set -> set := fun k => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
claim LL_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> L_ k c= L_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume H _. exact H.
}
claim LR_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> R_ k c= R_ k'.
{ let k k'. assume Hk Hk' Hkk'.
  apply SNo_sqrtaux_mon x sqrt_SNo_nonneg k Hk k' Hk' Hkk'.
  assume _ H. exact H.
}
claim L1: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
{ exact sqrt_SNo_nonneg_prop1a x Hx Hxnonneg IH. }
claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
{ let w. assume Hw. let p. assume Hp.
  apply famunionE_impred omega L_ w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e L_ k.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume H3. apply H3.
  exact Hp.
}
claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
{ let z. assume Hz. let p. assume Hp.
  apply famunionE_impred omega R_ z Hz.
  let k. assume Hk: k :e omega.
  assume H1: z :e R_ k.
  apply L1 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 z H1.
  assume H3. apply H3.
  exact Hp.
}
claim L2: SNoCutP L R.
{ exact sqrt_SNo_nonneg_prop1b x Hx Hxnonneg L1. }
apply L2.
assume HLHR. apply HLHR.
assume HL: forall w :e L, SNo w.
assume HR: forall z :e R, SNo z.
assume HLR: forall w :e L, forall z :e R, w < z.
set y := SNoCut L R.
apply SNoCutP_SNoCut_impred L R L2.
assume H1: SNo y.
assume H2: SNoLev y :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall w :e L, w < y.
assume H4: forall z :e R, y < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
claim Lynn: 0 <= y.
{ exact sqrt_SNo_nonneg_prop1c x Hx Hxnonneg L2 L1R. }
prove SNo y /\ 0 <= y /\ y * y = x.
apply and3I.
- prove SNo y. exact H1.
- prove 0 <= y. exact Lynn.
- prove y * y = x.
  claim Lyy: SNo (y * y).
  { exact SNo_mul_SNo y y H1 H1. }
  claim Lyynn: 0 <= y * y.
  { exact mul_SNo_nonneg_nonneg y y H1 H1 Lynn Lynn. }
  apply SNoLt_trichotomy_or_impred (y * y) x Lyy Hx.
  + assume H6: y * y < x. prove False.
    exact sqrt_SNo_nonneg_prop1d x Hx Hxnonneg IH L2 Lynn H6.
  + assume H6: y * y = x. exact H6.
  + assume H6: x < y * y. prove False.
    exact sqrt_SNo_nonneg_prop1e x Hx Hxnonneg IH L2 Lynn H6.
Qed.

End sqrt_SNo_nonneg.

Theorem SNo_sqrtaux_0_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
      (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
   /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y).
let x. assume Hx Hxnonneg.
apply sqrt_SNo_nonneg_prop1a x Hx Hxnonneg.
let w. assume Hw Hwnonneg.
apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) w Hw. assume Hw1 Hw2 Hw3 Hw4.
exact sqrt_SNo_nonneg_prop1 w Hw3 Hwnonneg.
Qed.

Theorem SNo_sqrtaux_0_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x.
let x. assume Hx Hxnonneg.
let k. assume Hk.
apply SNo_sqrtaux_0_1_prop x Hx Hxnonneg k Hk.
assume H _. exact H.
Qed.

Theorem SNo_sqrtaux_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y.
let x. assume Hx Hxnonneg.
let k. assume Hk.
apply SNo_sqrtaux_0_1_prop x Hx Hxnonneg k Hk.
assume _ H. exact H.
Qed.

Theorem SNo_sqrt_SNo_SNoCutP: forall x, SNo x -> 0 <= x ->
  SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0)
          (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1).
let x. assume Hx Hxnonneg.
apply sqrt_SNo_nonneg_prop1b x Hx Hxnonneg.
exact SNo_sqrtaux_0_1_prop x Hx Hxnonneg.
Qed.

Theorem SNo_sqrt_SNo_nonneg: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x).
let x. assume Hx Hxnonneg.
apply sqrt_SNo_nonneg_prop1 x Hx Hxnonneg.
assume H _. apply H. assume H _. exact H.
Qed.

Theorem sqrt_SNo_nonneg_nonneg: forall x, SNo x -> 0 <= x -> 0 <= sqrt_SNo_nonneg x.
let x. assume Hx Hxnonneg.
apply sqrt_SNo_nonneg_prop1 x Hx Hxnonneg.
assume H _. apply H. assume _ H. exact H.
Qed.

Theorem sqrt_SNo_nonneg_sqr: forall x, SNo x -> 0 <= x -> sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
let x. assume Hx Hxnonneg.
apply sqrt_SNo_nonneg_prop1 x Hx Hxnonneg.
assume _ H. exact H.
Qed.

Theorem sqrt_SNo_nonneg_0 : sqrt_SNo_nonneg 0 = 0.
rewrite sqrt_SNo_nonneg_eq 0 SNo_0.
set L_ := fun k:set => SNo_sqrtaux 0 sqrt_SNo_nonneg k 0.
set R_ := fun k:set => SNo_sqrtaux 0 sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
prove SNoCut L R = 0.
claim L1: forall k, nat_p k -> L_ k = 0 /\ R_ k = 0.
{ apply nat_ind.
  - apply andI.
    + prove L_ 0 = 0.
      prove SNo_sqrtaux 0 sqrt_SNo_nonneg 0 0 = 0.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_0_eq.
      prove {sqrt_SNo_nonneg w|w :e SNoL_nonneg 0} = 0.
      rewrite SNoL_nonneg_0.
      exact Repl_Empty sqrt_SNo_nonneg.
    + prove R_ 0 = 0.
      prove SNo_sqrtaux 0 sqrt_SNo_nonneg 0 1 = 0.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_1_eq.
      prove {sqrt_SNo_nonneg w|w :e SNoR 0} = 0.
      rewrite SNoR_0.
      exact Repl_Empty sqrt_SNo_nonneg.
  - let k. assume Hk.
    assume IHk. apply IHk.
    assume IHLk: L_ k = 0.
    assume IHRk: R_ k = 0.
    apply andI.
    + prove L_ (ordsucc k) = 0.
      prove SNo_sqrtaux 0 sqrt_SNo_nonneg (ordsucc k) 0 = 0.
      rewrite SNo_sqrtaux_S 0 sqrt_SNo_nonneg k Hk.
      rewrite tuple_2_0_eq.
      prove L_ k :\/: SNo_sqrtauxset (L_ k) (R_ k) 0 = Empty.
      rewrite IHLk.
      prove 0 :\/: SNo_sqrtauxset 0 (R_ k) 0 = Empty.
      apply SNo_sqrtauxset_0 (R_ k) 0 (fun _ u => 0 :\/: u = 0).
      prove 0 :\/: 0 = Empty.
      apply binunion_idl.
    + prove R_ (ordsucc k) = 0.
      prove SNo_sqrtaux 0 sqrt_SNo_nonneg (ordsucc k) 1 = 0.
      rewrite SNo_sqrtaux_S 0 sqrt_SNo_nonneg k Hk.
      rewrite tuple_2_1_eq.
      prove R_ k :\/: SNo_sqrtauxset (L_ k) (L_ k) 0 :\/: SNo_sqrtauxset (R_ k) (R_ k) 0 = Empty.
      rewrite IHLk. rewrite IHRk.
      prove 0 :\/: SNo_sqrtauxset 0 0 0 :\/: SNo_sqrtauxset 0 0 0 = Empty.
      rewrite SNo_sqrtauxset_0 0 0.
      prove 0 :\/: 0 :\/: 0 = Empty.
      rewrite binunion_idl 0.
      prove 0 :\/: 0 = Empty.
      apply binunion_idl.
}
claim L2: L = 0.
{ apply Empty_eq.
  let x. assume Hx: x :e L.
  apply famunionE_impred omega L_ x Hx.
  let k. assume Hk: k :e omega.
  apply L1 k (omega_nat_p k Hk).
  assume H1: L_ k = 0.
  assume _.
  prove x /:e L_ k.
  rewrite H1.
  exact EmptyE x.
}
claim L3: R = 0.
{ apply Empty_eq.
  let x. assume Hx: x :e R.
  apply famunionE_impred omega R_ x Hx.
  let k. assume Hk: k :e omega.
  apply L1 k (omega_nat_p k Hk).
  assume _.
  assume H1: R_ k = 0.
  prove x /:e R_ k.
  rewrite H1.
  exact EmptyE x.
}
rewrite L2. rewrite L3.
exact SNoCut_0_0.
Qed.

Theorem sqrt_SNo_nonneg_1 : sqrt_SNo_nonneg 1 = 1.
rewrite sqrt_SNo_nonneg_eq 1 SNo_1.
set L_ := fun k:set => SNo_sqrtaux 1 sqrt_SNo_nonneg k 0.
set R_ := fun k:set => SNo_sqrtaux 1 sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
prove SNoCut L R = 1.
claim L1: forall k, nat_p k -> L_ k = 1 /\ R_ k = 0.
{ apply nat_ind.
  - apply andI.
    + prove L_ 0 = 1.
      prove SNo_sqrtaux 1 sqrt_SNo_nonneg 0 0 = 1.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_0_eq.
      prove {sqrt_SNo_nonneg w|w :e SNoL_nonneg 1} = 1.
      rewrite SNoL_nonneg_1.
      prove {sqrt_SNo_nonneg w|w :e 1} = 1.
      apply set_ext.
      * let u. assume Hu: u :e {sqrt_SNo_nonneg w|w :e 1}.
        prove u :e 1.
        apply ReplE_impred 1 sqrt_SNo_nonneg u Hu.
        let w. assume Hw: w :e 1.
        apply cases_1 w Hw.
        rewrite sqrt_SNo_nonneg_0.
        assume Hu0: u = 0.
        rewrite Hu0. exact In_0_1.
      * let u. assume Hu: u :e 1.
        apply cases_1 u Hu.
        prove 0 :e {sqrt_SNo_nonneg w|w :e 1}.
        rewrite <- sqrt_SNo_nonneg_0 at 1.
        apply ReplI. exact In_0_1.
    + prove R_ 0 = 0.
      prove SNo_sqrtaux 1 sqrt_SNo_nonneg 0 1 = 0.
      rewrite SNo_sqrtaux_0.
      rewrite tuple_2_1_eq.
      prove {sqrt_SNo_nonneg w|w :e SNoR 1} = 0.
      rewrite SNoR_1.
      exact Repl_Empty sqrt_SNo_nonneg.
  - let k. assume Hk.
    assume IHk. apply IHk.
    assume IHLk: L_ k = 1.
    assume IHRk: R_ k = 0.
    apply andI.
    + prove L_ (ordsucc k) = 1.
      prove SNo_sqrtaux 1 sqrt_SNo_nonneg (ordsucc k) 0 = 1.
      rewrite SNo_sqrtaux_S 1 sqrt_SNo_nonneg k Hk.
      rewrite tuple_2_0_eq.
      prove L_ k :\/: SNo_sqrtauxset (L_ k) (R_ k) 1 = 1.
      rewrite IHLk. rewrite IHRk.
      prove 1 :\/: SNo_sqrtauxset 1 0 1 = 1.
      rewrite SNo_sqrtauxset_0' 1 1.
      apply binunion_idr.
    + prove R_ (ordsucc k) = 0.
      prove SNo_sqrtaux 1 sqrt_SNo_nonneg (ordsucc k) 1 = 0.
      rewrite SNo_sqrtaux_S 1 sqrt_SNo_nonneg k Hk.
      rewrite tuple_2_1_eq.
      prove R_ k :\/: SNo_sqrtauxset (L_ k) (L_ k) 1 :\/: SNo_sqrtauxset (R_ k) (R_ k) 1 = 0.
      rewrite IHLk. rewrite IHRk.
      prove 0 :\/: SNo_sqrtauxset 1 1 1 :\/: SNo_sqrtauxset 0 0 1 = 0.
      rewrite SNo_sqrtauxset_0 0 1.
      prove 0 :\/: SNo_sqrtauxset 1 1 1 :\/: 0 = 0.
      rewrite binunion_idl (SNo_sqrtauxset 1 1 1).
      rewrite binunion_idr (SNo_sqrtauxset 1 1 1).
      prove SNo_sqrtauxset 1 1 1 = 0.
      apply Empty_eq.
      let u. assume Hu: u :e SNo_sqrtauxset 1 1 1.
      apply SNo_sqrtauxset_E 1 1 1 u Hu.
      let w. assume Hw: w :e 1.
      let z. assume Hz: z :e 1.
      apply cases_1 w Hw.
      apply cases_1 z Hz.
      rewrite add_SNo_0R 0 SNo_0.
      assume H1: 0 < 0.
      prove False.
      apply SNoLt_irref 0.
      exact H1.
}
claim L2: L = 1.
{ apply set_ext.
  - prove L c= 1.
    let x. assume Hx: x :e L.
    apply famunionE_impred omega L_ x Hx.
    let k. assume Hk: k :e omega.
    apply L1 k (omega_nat_p k Hk).
    assume H1: L_ k = 1.
    assume _.
    prove x :e L_ k -> x :e 1.
    rewrite H1.
    assume H2: x :e 1.
    prove x :e 1.
    exact H2.
  - let x. assume Hx: x :e 1.
    apply cases_1 x Hx.
    prove 0 :e L.
    claim L2a: 0 :e L_ 0.
    { apply L1 0 nat_0.
      assume H1: L_ 0 = 1.
      assume _.
      rewrite H1. exact In_0_1.
    }
    prove 0 :e \/_ k :e omega, L_ k.
    exact famunionI omega L_ 0 0 (nat_p_omega 0 nat_0) L2a.
}
claim L3: R = 0.
{ apply Empty_eq.
  let x. assume Hx: x :e R.
  apply famunionE_impred omega R_ x Hx.
  let k. assume Hk: k :e omega.
  apply L1 k (omega_nat_p k Hk).
  assume _.
  assume H1: R_ k = 0.
  prove x /:e R_ k.
  rewrite H1.
  exact EmptyE x.
}
rewrite L2. rewrite L3.
prove SNoCut 1 0 = 1.
rewrite <- SNoL_1 at 1.
rewrite <- SNoR_1 at 2.
prove SNoCut (SNoL 1) (SNoR 1) = 1.
symmetry.
exact SNo_eta 1 SNo_1.
Qed.

End SurrealSqrt.

Opaque SNo_sqrtaux.
Opaque sqrt_SNo_nonneg.
