(** Part 8 **)

Section SurrealDiv.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.
Infix ^ 342 right := exp_SNo_nat.

Definition SNoL_pos : set -> set := fun x => {w :e SNoL x|0 < w}.

Theorem SNo_recip_pos_pos: forall x xi, SNo x -> SNo xi -> 0 < x -> x * xi = 1 -> 0 < xi.
let x xi. assume Hx Hxi Hxpos Hxxi.
apply SNoLt_trichotomy_or_impred 0 xi SNo_0 Hxi.
- assume H1. exact H1.
- assume H1: 0 = xi. prove False.
  apply neq_0_1.
  prove 0 = 1.
  rewrite <- Hxxi.
  prove 0 = x * xi.
  rewrite <- H1.
  prove 0 = x * 0.
  symmetry. exact mul_SNo_zeroR x Hx.
- assume H1: xi < 0. prove False.
  apply SNoLt_irref 0.
  prove 0 < 0.
  apply SNoLt_tra 0 1 0 SNo_0 SNo_1 SNo_0 SNoLt_0_1.
  prove 1 < 0.
  rewrite <- Hxxi.
  prove x * xi < 0.
  exact mul_SNo_pos_neg x xi Hx Hxi Hxpos H1.
Qed.

Theorem SNo_recip_lem1: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
let x x' x'i y y'.
assume Hx Hxpos Hx' Hx'i Hx'x'i Hy Hxy1 Hy' Hy'y.
apply SepE (SNoL x) (fun w => 0 < w) x' Hx'.
assume Hx'L: x' :e SNoL x.
assume Hx'pos: 0 < x'.
apply SNoL_E x Hx x' Hx'L.
assume Hx'1: SNo x'.
assume Hx'2: SNoLev x' :e SNoLev x.
assume Hx'3: x' < x.
claim Lxy: SNo (x * y).
{ exact SNo_mul_SNo x y Hx Hy. }
claim Lxy': SNo (x * y').
{ exact SNo_mul_SNo x y' Hx Hy'. }
claim L1: 0 < 1 + - x * y.
{ apply add_SNo_minus_Lt2b 1 (x * y) 0 SNo_1 Lxy SNo_0.
  prove 0 + x * y < 1.
  rewrite add_SNo_0L (x * y) Lxy.
  prove x * y < 1.
  exact Hxy1.
}
claim L2: (x' + - x) * x'i < 0.
{ apply mul_SNo_neg_pos (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i.
  - prove x' + - x < 0.
    apply add_SNo_minus_Lt1b x' x 0 Hx'1 Hx SNo_0.
    prove x' < 0 + x.
    rewrite add_SNo_0L x Hx.
    exact Hx'3.
  - prove 0 < x'i.
    exact SNo_recip_pos_pos x' x'i Hx'1 Hx'i Hx'pos Hx'x'i.
}
claim L3: 1 + - x * y' < 0.
{ rewrite Hy'y.
  prove (1 + - x * y) * (x' + - x) * x'i < 0.
  apply mul_SNo_pos_neg (1 + - x * y) ((x' + - x) * x'i)
                        (SNo_add_SNo 1 (- x * y) SNo_1 (SNo_minus_SNo (x * y) Lxy))
                        (SNo_mul_SNo (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i).
  - exact L1.
  - exact L2.
}
prove 1 < x * y'.
rewrite <- add_SNo_0L (x * y') Lxy'.
prove 1 < 0 + x * y'.
exact add_SNo_minus_Lt1 1 (x * y') 0 SNo_1 Lxy' SNo_0 L3.
Qed.

Theorem SNo_recip_lem2: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
let x x' x'i y y'.
assume Hx Hxpos Hx' Hx'i Hx'x'i Hy Hxy1 Hy' Hy'y.
apply SepE (SNoL x) (fun w => 0 < w) x' Hx'.
assume Hx'L: x' :e SNoL x.
assume Hx'pos: 0 < x'.
apply SNoL_E x Hx x' Hx'L.
assume Hx'1: SNo x'.
assume Hx'2: SNoLev x' :e SNoLev x.
assume Hx'3: x' < x.
claim Lxy: SNo (x * y).
{ exact SNo_mul_SNo x y Hx Hy. }
claim Lxy': SNo (x * y').
{ exact SNo_mul_SNo x y' Hx Hy'. }
claim L1: 1 + - x * y < 0.
{ apply add_SNo_minus_Lt1b 1 (x * y) 0 SNo_1 Lxy SNo_0.
  prove 1 < 0 + x * y.
  rewrite add_SNo_0L (x * y) Lxy.
  prove 1 < x * y.
  exact Hxy1.
}
claim L2: (x' + - x) * x'i < 0.
{ apply mul_SNo_neg_pos (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i.
  - prove x' + - x < 0.
    apply add_SNo_minus_Lt1b x' x 0 Hx'1 Hx SNo_0.
    prove x' < 0 + x.
    rewrite add_SNo_0L x Hx.
    exact Hx'3.
  - prove 0 < x'i.
    exact SNo_recip_pos_pos x' x'i Hx'1 Hx'i Hx'pos Hx'x'i.
}
claim L3: 0 < 1 + - x * y'.
{ rewrite Hy'y.
  prove 0 < (1 + - x * y) * (x' + - x) * x'i.
  apply mul_SNo_neg_neg (1 + - x * y) ((x' + - x) * x'i)
                        (SNo_add_SNo 1 (- x * y) SNo_1 (SNo_minus_SNo (x * y) Lxy))
                        (SNo_mul_SNo (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i).
  - exact L1.
  - exact L2.
}
prove x * y' < 1.
rewrite <- add_SNo_0L (x * y') Lxy'.
prove 0 + x * y' < 1.
exact add_SNo_minus_Lt2 1 (x * y') 0 SNo_1 Lxy' SNo_0 L3.
Qed.

Theorem SNo_recip_lem3: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
let x x' x'i y y'.
assume Hx Hxpos Hx' Hx'i Hx'x'i Hy Hxy1 Hy' Hy'y.
apply SNoR_E x Hx x' Hx'.
assume Hx'1: SNo x'.
assume Hx'2: SNoLev x' :e SNoLev x.
assume Hx'3: x < x'.
claim Lxy: SNo (x * y).
{ exact SNo_mul_SNo x y Hx Hy. }
claim Lxy': SNo (x * y').
{ exact SNo_mul_SNo x y' Hx Hy'. }
claim Lx'pos: 0 < x'.
{ exact SNoLt_tra 0 x x' SNo_0 Hx Hx'1 Hxpos Hx'3. }
claim L1: 0 < 1 + - x * y.
{ apply add_SNo_minus_Lt2b 1 (x * y) 0 SNo_1 Lxy SNo_0.
  prove 0 + x * y < 1.
  rewrite add_SNo_0L (x * y) Lxy.
  prove x * y < 1.
  exact Hxy1.
}
claim L2: 0 < (x' + - x) * x'i.
{ apply mul_SNo_pos_pos (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i.
  - prove 0 < x' + - x.
    apply add_SNo_minus_Lt2b x' x 0 Hx'1 Hx SNo_0.
    prove 0 + x < x'.
    rewrite add_SNo_0L x Hx.
    exact Hx'3.
  - prove 0 < x'i.
    exact SNo_recip_pos_pos x' x'i Hx'1 Hx'i Lx'pos Hx'x'i.
}
claim L3: 0 < 1 + - x * y'.
{ rewrite Hy'y.
  prove 0 < (1 + - x * y) * (x' + - x) * x'i.
  apply mul_SNo_pos_pos (1 + - x * y) ((x' + - x) * x'i)
                        (SNo_add_SNo 1 (- x * y) SNo_1 (SNo_minus_SNo (x * y) Lxy))
                        (SNo_mul_SNo (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i).
  - exact L1.
  - exact L2.
}
prove x * y' < 1.
rewrite <- add_SNo_0L (x * y') Lxy'.
prove 0 + x * y' < 1.
exact add_SNo_minus_Lt2 1 (x * y') 0 SNo_1 Lxy' SNo_0 L3.
Qed.

Theorem SNo_recip_lem4: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
let x x' x'i y y'.
assume Hx Hxpos Hx' Hx'i Hx'x'i Hy Hxy1 Hy' Hy'y.
apply SNoR_E x Hx x' Hx'.
assume Hx'1: SNo x'.
assume Hx'2: SNoLev x' :e SNoLev x.
assume Hx'3: x < x'.
claim Lxy: SNo (x * y).
{ exact SNo_mul_SNo x y Hx Hy. }
claim Lxy': SNo (x * y').
{ exact SNo_mul_SNo x y' Hx Hy'. }
claim Lx'pos: 0 < x'.
{ exact SNoLt_tra 0 x x' SNo_0 Hx Hx'1 Hxpos Hx'3. }
claim L1: 1 + - x * y < 0.
{ apply add_SNo_minus_Lt1b 1 (x * y) 0 SNo_1 Lxy SNo_0.
  prove 1 < 0 + x * y.
  rewrite add_SNo_0L (x * y) Lxy.
  prove 1 < x * y.
  exact Hxy1.
}
claim L2: 0 < (x' + - x) * x'i.
{ apply mul_SNo_pos_pos (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i.
  - prove 0 < x' + - x.
    apply add_SNo_minus_Lt2b x' x 0 Hx'1 Hx SNo_0.
    prove 0 + x < x'.
    rewrite add_SNo_0L x Hx.
    exact Hx'3.
  - prove 0 < x'i.
    exact SNo_recip_pos_pos x' x'i Hx'1 Hx'i Lx'pos Hx'x'i.
}
claim L3: 1 + - x * y' < 0.
{ rewrite Hy'y.
  prove (1 + - x * y) * (x' + - x) * x'i < 0.
  apply mul_SNo_neg_pos (1 + - x * y) ((x' + - x) * x'i)
                        (SNo_add_SNo 1 (- x * y) SNo_1 (SNo_minus_SNo (x * y) Lxy))
                        (SNo_mul_SNo (x' + - x) x'i (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hx'i).
  - exact L1.
  - exact L2.
}
prove 1 < x * y'.
rewrite <- add_SNo_0L (x * y') Lxy'.
prove 1 < 0 + x * y'.
exact add_SNo_minus_Lt1 1 (x * y') 0 SNo_1 Lxy' SNo_0 L3.
Qed.

Definition SNo_recipauxset : set -> set -> set -> (set -> set) -> set := fun Y x X g => \/_ y :e Y, {(1 + (x' + - x) * y) * g x'|x' :e X}.

Theorem SNo_recipauxset_I: forall Y x X, forall g:set -> set,
 forall y :e Y, forall x' :e X, (1 + (x' + - x) * y) * g x' :e SNo_recipauxset Y x X g.
let Y x X g y. assume Hy. let x'. assume Hx'.
prove (1 + (x' + - x) * y) * g x' :e \/_ y :e Y, {(1 + (x' + - x) * y) * g x'|x' :e X}.
apply famunionI Y (fun y => {(1 + (x' + - x) * y) * g x'|x' :e X}) y ((1 + (x' + - x) * y) * g x') Hy.
prove (1 + (x' + - x) * y) * g x' :e {(1 + (x' + - x) * y) * g x'|x' :e X}.
exact ReplI X (fun x' => (1 + (x' + - x) * y) * g x') x' Hx'.
Qed.

Theorem SNo_recipauxset_E : forall Y x X, forall g:set -> set, forall z :e SNo_recipauxset Y x X g, forall p:prop, (forall y :e Y, forall x' :e X, z = (1 + (x' + - x) * y) * g x' -> p) -> p.
let Y x X g z. assume Hz.
let p. assume H1.
apply famunionE_impred Y (fun y => {(1 + (x' + - x) * y) * g x'|x' :e X}) z Hz.
let y. assume Hy.
assume H2: z :e {(1 + (x' + - x) * y) * g x'|x' :e X}.
apply ReplE_impred X (fun x' => (1 + (x' + - x) * y) * g x') z H2.
let x'. assume Hx': x' :e X.
assume H3: z = (1 + (x' + - x) * y) * g x'.
exact H1 y Hy x' Hx' H3.
Qed.

Theorem SNo_recipauxset_ext: forall Y x X, forall g h:set -> set, (forall x' :e X, g x' = h x') -> SNo_recipauxset Y x X g = SNo_recipauxset Y x X h.
let Y x X g h.
assume Hgh.
prove (\/_ y :e Y, {(1 + (x' + - x) * y) * g x'|x' :e X})
    = (\/_ y :e Y, {(1 + (x' + - x) * y) * h x'|x' :e X}).
apply famunion_ext.
let y. assume Hy.
apply ReplEq_ext X (fun x' => (1 + (x' + - x) * y) * g x')
                   (fun x' => (1 + (x' + - x) * y) * h x').
let x'. assume Hx'.
prove (1 + (x' + - x) * y) * g x' = (1 + (x' + - x) * y) * h x'.
f_equal. exact Hgh x' Hx'.
Qed.

Definition SNo_recipaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({0},0)
   (fun k p => (p 0 :\/: SNo_recipauxset (p 0) x (SNoR x) g
                    :\/: SNo_recipauxset (p 1) x (SNoL_pos x) g,
                p 1 :\/: SNo_recipauxset (p 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (p 1) x (SNoR x) g)).

Theorem SNo_recipaux_0: forall x, forall g:set -> set, SNo_recipaux x g 0 = ({0},0).
let x g.
exact nat_primrec_0 ({0},0)
   (fun k p => (p 0 :\/: SNo_recipauxset (p 0) x (SNoR x) g
                    :\/: SNo_recipauxset (p 1) x (SNoL_pos x) g,
                p 1 :\/: SNo_recipauxset (p 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (p 1) x (SNoR x) g)).
Qed.

Theorem SNo_recipaux_S: forall x, forall g:set -> set, forall n, nat_p n ->
   SNo_recipaux x g (ordsucc n)
 = (SNo_recipaux x g n 0 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoR x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoL_pos x) g,
    SNo_recipaux x g n 1 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoL_pos x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoR x) g).
let x g n. assume Hn.
exact nat_primrec_S ({0},0)
   (fun k p => (p 0 :\/: SNo_recipauxset (p 0) x (SNoR x) g
                    :\/: SNo_recipauxset (p 1) x (SNoL_pos x) g,
                p 1 :\/: SNo_recipauxset (p 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (p 1) x (SNoR x) g)) n Hn.
Qed.

Theorem SNo_recipaux_lem1: forall x, SNo x -> 0 < x ->
 forall g:set -> set,
    (forall x' :e SNoS_ (SNoLev x), 0 < x' -> SNo (g x') /\ x' * g x' = 1)
 -> forall k, nat_p k ->
         (forall y :e SNo_recipaux x g k 0, SNo y /\ x * y < 1)
      /\ (forall y :e SNo_recipaux x g k 1, SNo y /\ 1 < x * y).
let x. assume Hx Hxpos.
let g. assume Hg.
set r := SNo_recipaux x g.
claim L1: forall x' :e SNoS_ (SNoLev x), 0 < x' -> forall y y', SNo y -> y' = (1 + (x' + - x) * y) * g x' -> SNo y'.
{ let x'. assume Hx' Hx'pos. let y y'. assume Hy Hy'.
  apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) x' Hx'. assume _ _ Hx'1 _.
  rewrite Hy'.
  apply SNo_mul_SNo.
  - apply SNo_add_SNo.
    + exact SNo_1.
    + apply SNo_mul_SNo.
      * { apply SNo_add_SNo.
          - exact Hx'1.
          - apply SNo_minus_SNo. exact Hx.
         }
       * exact Hy.
  - apply Hg x' Hx' Hx'pos. assume H _. exact H.
}
claim L2: forall x' :e SNoS_ (SNoLev x), 0 < x' -> forall y y', SNo y -> y' = (1 + (x' + - x) * y) * g x' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
{ let x'. assume Hx' Hx'pos. let y y'. assume Hy Hy'.
  apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) x' Hx'. assume _ _ Hx'1 _.
  prove 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
  apply Hg x' Hx' Hx'pos. assume Hgx'1 Hgx'2.
  rewrite mul_SNo_distrR x' (- x) (g x') Hx'1 (SNo_minus_SNo x Hx) Hgx'1.
  prove 1 + - x * y' = (1 + - x * y) * (x' * g x' + (- x) * g x').
  rewrite Hgx'2.
  prove 1 + - x * y' = (1 + - x * y) * (1 + (- x) * g x').
  rewrite SNo_foil 1 (- x * y) 1 ((- x) * g x') SNo_1 (SNo_minus_SNo (x * y) (SNo_mul_SNo x y Hx Hy)) SNo_1 (SNo_mul_SNo (- x) (g x') (SNo_minus_SNo x Hx) Hgx'1).
  prove 1 + - x * y' = 1 * 1 + 1 * (- x) * g x' + (- x * y) * 1 + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_oneL 1 SNo_1.
  rewrite mul_SNo_oneL ((- x) * g x') (SNo_mul_SNo (- x) (g x') (SNo_minus_SNo x Hx) Hgx'1).
  rewrite mul_SNo_oneR (- x * y) (SNo_minus_SNo (x * y) (SNo_mul_SNo x y Hx Hy)).
  prove 1 + - x * y' = 1 + (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  f_equal.
  prove - x * y' = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  rewrite Hy'.
  prove - x * ((1 + (x' + - x) * y) * g x') = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_distrR 1 ((x' + - x) * y) (g x') SNo_1 (SNo_mul_SNo (x' + - x) y (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hy) Hgx'1.
  prove - x * (1 * g x' + ((x' + - x) * y) * g x') = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_oneL (g x') Hgx'1.
  prove - x * (g x' + ((x' + - x) * y) * g x') = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  rewrite <- mul_SNo_minus_distrL x (g x' + ((x' + - x) * y) * g x') Hx (SNo_add_SNo (g x') (((x' + - x) * y) * g x') Hgx'1 (SNo_mul_SNo ((x' + - x) * y) (g x') (SNo_mul_SNo (x' + - x) y (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hy) Hgx'1)).
  prove (- x) * (g x' + ((x' + - x) * y) * g x') = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_distrL (- x) (g x') (((x' + - x) * y) * g x') (SNo_minus_SNo x Hx) Hgx'1 (SNo_mul_SNo ((x' + - x) * y) (g x') (SNo_mul_SNo (x' + - x) y (SNo_add_SNo x' (- x) Hx'1 (SNo_minus_SNo x Hx)) Hy) Hgx'1).
  prove (- x) * g x' + (- x) * (((x' + - x) * y) * g x') = (- x) * g x' + - x * y + (- x * y) * (- x) * g x'.
  f_equal.
  prove (- x) * (((x' + - x) * y) * g x') = - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_distrR x' (- x) y Hx'1 (SNo_minus_SNo x Hx) Hy.
  prove (- x) * ((x' * y + (- x) * y) * g x') = - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_distrR (x' * y) ((- x) * y) (g x') (SNo_mul_SNo x' y Hx'1 Hy) (SNo_mul_SNo (- x) y (SNo_minus_SNo x Hx) Hy) Hgx'1.
  prove (- x) * ((x' * y) * g x' + ((- x) * y) * g x') = - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_com x' y Hx'1 Hy.
  rewrite <- mul_SNo_assoc y x' (g x') Hy Hx'1 Hgx'1.
  rewrite Hgx'2.
  rewrite mul_SNo_oneR y Hy.
  prove (- x) * (y + ((- x) * y) * g x') = - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_distrL (- x) y (((- x) * y) * g x') (SNo_minus_SNo x Hx) Hy (SNo_mul_SNo ((- x) * y) (g x') (SNo_mul_SNo (- x) y (SNo_minus_SNo x Hx) Hy) Hgx'1).
  prove (- x) * y + (- x) * ((- x) * y) * g x' = - x * y + (- x * y) * (- x) * g x'.
  rewrite mul_SNo_minus_distrL x y Hx Hy at 1.
  prove - x * y + (- x) * ((- x) * y) * g x' = - x * y + (- x * y) * (- x) * g x'.
  f_equal.
  prove (- x) * ((- x) * y) * g x' = (- x * y) * (- x) * g x'.
  rewrite mul_SNo_assoc (- x) ((- x) * y) (g x') (SNo_minus_SNo x Hx) (SNo_mul_SNo (- x) y (SNo_minus_SNo x Hx) Hy) Hgx'1.
  rewrite mul_SNo_assoc (- x * y) (- x) (g x') (SNo_minus_SNo (x * y) (SNo_mul_SNo x y Hx Hy)) (SNo_minus_SNo x Hx) Hgx'1.
  f_equal.
  prove (- x) * ((- x) * y) = (- x * y) * (- x).
  rewrite mul_SNo_com (- x) y (SNo_minus_SNo x Hx) Hy.
  prove (- x) * (y * (- x)) = (- x * y) * (- x).
  rewrite <- mul_SNo_minus_distrL x y Hx Hy.
  prove (- x) * (y * (- x)) = ((- x) * y) * (- x).
  exact mul_SNo_assoc (- x) y (- x) (SNo_minus_SNo x Hx) Hy (SNo_minus_SNo x Hx).
}
apply nat_ind.
- apply andI.
  + let y.
    prove y :e r 0 0 -> SNo y /\ x * y < 1.
    rewrite SNo_recipaux_0.
    rewrite tuple_2_0_eq.
    prove y :e {0} -> SNo y /\ x * y < 1.
    assume H1: y :e {0}.
    rewrite SingE 0 y H1.
    apply andI.
    * exact SNo_0.
    * prove x * 0 < 1.
      rewrite mul_SNo_zeroR x Hx.
      exact SNoLt_0_1.
  + let y.
    prove y :e r 0 1 -> SNo y /\ 1 < x * y.
    rewrite SNo_recipaux_0.
    prove y :e ({0},0) 1 -> SNo y /\ 1 < x * y.
    rewrite tuple_2_1_eq.
    prove y :e 0 -> SNo y /\ 1 < x * y.
    assume H1: y :e 0.
    prove False. exact EmptyE y H1.
- let k.
  assume Hk: nat_p k.
  assume IH. apply IH.
  assume IH1: forall y :e r k 0, SNo y /\ x * y < 1.
  assume IH2: forall y :e r k 1, SNo y /\ 1 < x * y.
  apply andI.
  + let y'.
    prove y' :e r (ordsucc k) 0 -> SNo y' /\ x * y' < 1.
    rewrite SNo_recipaux_S.
    * { prove y' :e (r k 0 :\/: SNo_recipauxset (r k 0) x (SNoR x) g
                           :\/: SNo_recipauxset (r k 1) x (SNoL_pos x) g,
                     r k 1 :\/: SNo_recipauxset (r k 0) x (SNoL_pos x) g
                           :\/: SNo_recipauxset (r k 1) x (SNoR x) g) 0
              -> SNo y' /\ x * y' < 1.
        rewrite tuple_2_0_eq.
        prove y' :e r k 0 :\/: SNo_recipauxset (r k 0) x (SNoR x) g
                          :\/: SNo_recipauxset (r k 1) x (SNoL_pos x) g
           -> SNo y' /\ x * y' < 1.
        assume H1.
        apply binunionE (r k 0 :\/: SNo_recipauxset (r k 0) x (SNoR x) g) (SNo_recipauxset (r k 1) x (SNoL_pos x) g) y' H1.
        - assume H1.
          apply binunionE (r k 0) (SNo_recipauxset (r k 0) x (SNoR x) g) y' H1.
          + exact IH1 y'.
          + assume H1.
            apply SNo_recipauxset_E (r k 0) x (SNoR x) g y' H1.
            let y. assume Hy: y :e r k 0.
            let x'. assume Hx': x' :e SNoR x.
            assume H2: y' = (1 + (x' + - x) * y) * g x'.
            apply SNoR_E x Hx x' Hx'.
            assume Hx'1 Hx'2 Hx'3.
            claim Lx': x' :e SNoS_ (SNoLev x).
            { apply SNoS_I2 x' x Hx'1 Hx Hx'2. }
            claim Lx'pos: 0 < x'.
            { exact SNoLt_tra 0 x x' SNo_0 Hx Hx'1 Hxpos Hx'3. }
            apply IH1 y Hy.
            assume Hy1: SNo y.
            assume Hxy1: x * y < 1.
            apply Hg x' Lx' Lx'pos.
            assume Hgx'1: SNo (g x').
            assume Hgx'2: x' * g x' = 1.
            claim Ly': SNo y'.
            { exact L1 x' Lx' Lx'pos y y' Hy1 H2. }
            apply andI.
            * exact Ly'.
            * apply SNo_recip_lem3 x x' (g x') y y' Hx Hxpos Hx' Hgx'1 Hgx'2 Hy1 Hxy1 Ly'.
              prove 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
              exact L2 x' Lx' Lx'pos y y' Hy1 H2.
        - assume H1.
          apply SNo_recipauxset_E (r k 1) x (SNoL_pos x) g y' H1.
          let y. assume Hy: y :e r k 1.
          let x'. assume Hx': x' :e SNoL_pos x.
          assume H2: y' = (1 + (x' + - x) * y) * g x'.
          apply SepE (SNoL x) (fun w => 0 < w) x' Hx'.
          assume Hx'0: x' :e SNoL x.
          assume Hx'pos: 0 < x'.
          apply SNoL_E x Hx x' Hx'0.
          assume Hx'1 Hx'2 Hx'3.
          claim Lx': x' :e SNoS_ (SNoLev x).
          { apply SNoS_I2 x' x Hx'1 Hx Hx'2. }
          apply IH2 y Hy.
          assume Hy1: SNo y.
          assume Hxy1: 1 < x * y.
          apply Hg x' Lx' Hx'pos.
          assume Hgx'1: SNo (g x').
          assume Hgx'2: x' * g x' = 1.
          claim Ly': SNo y'.
          { exact L1 x' Lx' Hx'pos y y' Hy1 H2. }
          apply andI.
          + exact Ly'.
          + apply SNo_recip_lem2 x x' (g x') y y' Hx Hxpos Hx' Hgx'1 Hgx'2 Hy1 Hxy1 Ly'.
            prove 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
            exact L2 x' Lx' Hx'pos y y' Hy1 H2.
      }
    * exact Hk.
  + let y'.
    prove y' :e r (ordsucc k) 1 -> SNo y' /\ 1 < x * y'.
    rewrite SNo_recipaux_S.
    * { prove y' :e (r k 0 :\/: SNo_recipauxset (r k 0) x (SNoR x) g
                           :\/: SNo_recipauxset (r k 1) x (SNoL_pos x) g,
                     r k 1 :\/: SNo_recipauxset (r k 0) x (SNoL_pos x) g
                           :\/: SNo_recipauxset (r k 1) x (SNoR x) g) 1
            -> SNo y' /\ 1 < x * y'.
        rewrite tuple_2_1_eq.
        prove y' :e r k 1 :\/: SNo_recipauxset (r k 0) x (SNoL_pos x) g
                          :\/: SNo_recipauxset (r k 1) x (SNoR x) g
              -> SNo y' /\ 1 < x * y'.
         assume H1.
         apply binunionE (r k 1 :\/: SNo_recipauxset (r k 0) x (SNoL_pos x) g) (SNo_recipauxset (r k 1) x (SNoR x) g) y' H1.
         - assume H1. apply binunionE (r k 1) (SNo_recipauxset (r k 0) x (SNoL_pos x) g) y' H1.
           + exact IH2 y'.
           + assume H1.
            apply SNo_recipauxset_E (r k 0) x (SNoL_pos x) g y' H1.
            let y. assume Hy: y :e r k 0.
            let x'. assume Hx': x' :e SNoL_pos x.
            assume H2: y' = (1 + (x' + - x) * y) * g x'.
            apply SepE (SNoL x) (fun w => 0 < w) x' Hx'.
            assume Hx'0: x' :e SNoL x.
            assume Hx'pos: 0 < x'.
            apply SNoL_E x Hx x' Hx'0.
            assume Hx'1 Hx'2 Hx'3.
            claim Lx': x' :e SNoS_ (SNoLev x).
            { apply SNoS_I2 x' x Hx'1 Hx Hx'2. }
            apply IH1 y Hy.
            assume Hy1: SNo y.
            assume Hxy1: x * y < 1.
            apply Hg x' Lx' Hx'pos.
            assume Hgx'1: SNo (g x').
            assume Hgx'2: x' * g x' = 1.
            claim Ly': SNo y'.
            { exact L1 x' Lx' Hx'pos y y' Hy1 H2. }
            apply andI.
            * exact Ly'.
            * apply SNo_recip_lem1 x x' (g x') y y' Hx Hxpos Hx' Hgx'1 Hgx'2 Hy1 Hxy1 Ly'.
              prove 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
              exact L2 x' Lx' Hx'pos y y' Hy1 H2.
         - assume H1.
          apply SNo_recipauxset_E (r k 1) x (SNoR x) g y' H1.
          let y. assume Hy: y :e r k 1.
          let x'. assume Hx': x' :e SNoR x.
          assume H2: y' = (1 + (x' + - x) * y) * g x'.
          apply SNoR_E x Hx x' Hx'.
          assume Hx'1 Hx'2 Hx'3.
          claim Lx': x' :e SNoS_ (SNoLev x).
          { apply SNoS_I2 x' x Hx'1 Hx Hx'2. }
          claim Lx'pos: 0 < x'.
          { exact SNoLt_tra 0 x x' SNo_0 Hx Hx'1 Hxpos Hx'3. }
          apply IH2 y Hy.
          assume Hy1: SNo y.
          assume Hxy1: 1 < x * y.
          apply Hg x' Lx' Lx'pos.
          assume Hgx'1: SNo (g x').
          assume Hgx'2: x' * g x' = 1.
          claim Ly': SNo y'.
          { exact L1 x' Lx' Lx'pos y y' Hy1 H2. }
          apply andI.
          + exact Ly'.
          + apply SNo_recip_lem4 x x' (g x') y y' Hx Hxpos Hx' Hgx'1 Hgx'2 Hy1 Hxy1 Ly'.
            prove 1 + - x * y' = (1 + - x * y) * (x' + - x) * g x'.
            exact L2 x' Lx' Lx'pos y y' Hy1 H2.
      }
    * exact Hk.
Qed.

Theorem SNo_recipaux_lem2: forall x, SNo x -> 0 < x ->
 forall g:set -> set,
    (forall x' :e SNoS_ (SNoLev x), 0 < x' -> SNo (g x') /\ x' * g x' = 1)
 -> SNoCutP (\/_ k :e omega, SNo_recipaux x g k 0) (\/_ k :e omega, SNo_recipaux x g k 1).
let x. assume Hx Hxpos.
let g. assume Hg.
set L := \/_ k :e omega, SNo_recipaux x g k 0.
set R := \/_ k :e omega, SNo_recipaux x g k 1.
prove (forall x :e L, SNo x)
   /\ (forall y :e R, SNo y)
   /\ (forall x :e L, forall y :e R, x < y).
claim L1: forall k, nat_p k ->
              (forall y :e SNo_recipaux x g k 0, SNo y /\ x * y < 1)
           /\ (forall y :e SNo_recipaux x g k 1, SNo y /\ 1 < x * y).
{ exact SNo_recipaux_lem1 x Hx Hxpos g Hg. }
apply and3I.
- let y. assume Hy.
  apply famunionE_impred omega (fun k => SNo_recipaux x g k 0) y Hy.
  let k. assume Hk.
  assume H1: y :e SNo_recipaux x g k 0.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 y H1. assume H3 _. exact H3.
- let y. assume Hy.
  apply famunionE_impred omega (fun k => SNo_recipaux x g k 1) y Hy.
  let k. assume Hk.
  assume H1: y :e SNo_recipaux x g k 1.
  apply L1 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 y H1. assume H3 _. exact H3.
- let w. assume Hw. let z. assume Hz.
  apply famunionE_impred omega (fun k => SNo_recipaux x g k 0) w Hw.
  let k. assume Hk.
  assume H1: w :e SNo_recipaux x g k 0.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume H3: SNo w.
  assume H4: x * w < 1.
  apply famunionE_impred omega (fun k => SNo_recipaux x g k 1) z Hz.
  let k'. assume Hk'.
  assume H5: z :e SNo_recipaux x g k' 1.
  apply L1 k' (omega_nat_p k' Hk').
  assume _ H6.
  apply H6 z H5.
  assume H7: SNo z.
  assume H8: 1 < x * z.
  prove w < z.
  apply SNoLtLe_or w z H3 H7.
  + assume H9: w < z. exact H9.
  + assume H9: z <= w. prove False.
    apply SNoLt_irref 1.
    prove 1 < 1.
    apply SNoLt_tra 1 (x * z) 1 SNo_1 (SNo_mul_SNo x z Hx H7) SNo_1 H8.
    prove x * z < 1.
    apply SNoLeLt_tra (x * z) (x * w) 1 (SNo_mul_SNo x z Hx H7) (SNo_mul_SNo x w Hx H3) SNo_1.
    * prove x * z <= x * w.
      apply nonneg_mul_SNo_Le x z w Hx (SNoLtLe 0 x Hxpos) H7 H3 H9.
    * prove x * w < 1. exact H4.
Qed.

Theorem SNo_recipaux_ext: forall x, SNo x -> forall g h:set -> set, (forall x' :e SNoS_ (SNoLev x), g x' = h x') -> forall k, nat_p k -> SNo_recipaux x g k = SNo_recipaux x h k.
let x. assume Hx. let g h.
assume Hgh.
apply nat_ind.
- prove SNo_recipaux x g 0 = SNo_recipaux x h 0.
  rewrite SNo_recipaux_0 x h.
  exact SNo_recipaux_0 x g.
- let k.
  assume Hk: nat_p k.
  assume IH: SNo_recipaux x g k = SNo_recipaux x h k.
  prove SNo_recipaux x g (ordsucc k) = SNo_recipaux x h (ordsucc k).
  rewrite SNo_recipaux_S x g k Hk.
  rewrite SNo_recipaux_S x h k Hk.
  prove (SNo_recipaux x g k 0 :\/: SNo_recipauxset (SNo_recipaux x g k 0) x (SNoR x) g
                    :\/: SNo_recipauxset (SNo_recipaux x g k 1) x (SNoL_pos x) g,
         SNo_recipaux x g k 1 :\/: SNo_recipauxset (SNo_recipaux x g k 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (SNo_recipaux x g k 1) x (SNoR x) g)
      = (SNo_recipaux x h k 0 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) h,
         SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) h).
  rewrite IH.
  prove (SNo_recipaux x h k 0 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) g
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) g,
         SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) g)
      = (SNo_recipaux x h k 0 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) h,
         SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) h).
  claim L1: SNo_recipaux x h k 0 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) g
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) g
          = SNo_recipaux x h k 0 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) h.
  { f_equal.
    - f_equal.
      prove SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) g
          = SNo_recipauxset (SNo_recipaux x h k 0) x (SNoR x) h.
      apply SNo_recipauxset_ext.
      let w. assume Hw: w :e SNoR x.
      prove g w = h w.
      apply SNoR_E x Hx w Hw.
      assume Hw1 Hw2 Hw3.
      apply Hgh.
      prove w :e SNoS_ (SNoLev x).
      exact SNoS_I2 w x Hw1 Hx Hw2.
    - prove SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) g
          = SNo_recipauxset (SNo_recipaux x h k 1) x (SNoL_pos x) h.
      apply SNo_recipauxset_ext.
      let w. assume Hw: w :e SNoL_pos x.
      prove g w = h w.
      apply SNoL_E x Hx w (SepE1 (SNoL x) (fun w => 0 < w) w Hw).
      assume Hw1 Hw2 Hw3.
      apply Hgh.
      prove w :e SNoS_ (SNoLev x).
      exact SNoS_I2 w x Hw1 Hx Hw2.
  }
  claim L2: SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) g
          = SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) h.
  { f_equal.
    - f_equal.
      prove SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) g
          = SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) h.
      apply SNo_recipauxset_ext.
      let w. assume Hw: w :e SNoL_pos x.
      prove g w = h w.
      apply SNoL_E x Hx w (SepE1 (SNoL x) (fun w => 0 < w) w Hw).
      assume Hw1 Hw2 Hw3.
      apply Hgh.
      prove w :e SNoS_ (SNoLev x).
      exact SNoS_I2 w x Hw1 Hx Hw2.
    - prove SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) g
          = SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) h.
      apply SNo_recipauxset_ext.
      let w. assume Hw: w :e SNoR x.
      prove g w = h w.
      apply SNoR_E x Hx w Hw.
      assume Hw1 Hw2 Hw3.
      apply Hgh.
      prove w :e SNoS_ (SNoLev x).
      exact SNoS_I2 w x Hw1 Hx Hw2.
  }
  rewrite L1. rewrite L2.
  reflexivity.
Qed.

Section recip_SNo_pos.

Let G : set -> (set -> set) -> set := fun x g => SNoCut (\/_ k :e omega, SNo_recipaux x g k 0) (\/_ k :e omega, SNo_recipaux x g k 1).

Definition recip_SNo_pos : set -> set := SNo_rec_i G.

Theorem recip_SNo_pos_eq: forall x, SNo x -> recip_SNo_pos x = G x recip_SNo_pos.
apply SNo_rec_i_eq G.
let x. assume Hx.
let g h. assume Hgh.
prove SNoCut (\/_ k :e omega, SNo_recipaux x g k 0) (\/_ k :e omega, SNo_recipaux x g k 1)
    = SNoCut (\/_ k :e omega, SNo_recipaux x h k 0) (\/_ k :e omega, SNo_recipaux x h k 1).
f_equal.
- apply famunion_ext.
  let k. assume Hk.
  prove SNo_recipaux x g k 0 = SNo_recipaux x h k 0.
  f_equal.
  apply SNo_recipaux_ext x Hx g h.
  + prove forall w :e SNoS_ (SNoLev x), g w = h w.
    exact Hgh.
  + exact omega_nat_p k Hk.
- apply famunion_ext.
  let k. assume Hk.
  prove SNo_recipaux x g k 1 = SNo_recipaux x h k 1.
  f_equal.
  apply SNo_recipaux_ext x Hx g h.
  + prove forall w :e SNoS_ (SNoLev x), g w = h w.
    exact Hgh.
  + exact omega_nat_p k Hk.
Qed.

Theorem recip_SNo_pos_prop1: forall x, SNo x -> 0 < x -> SNo (recip_SNo_pos x) /\ x * recip_SNo_pos x = 1.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), 0 < w -> SNo (recip_SNo_pos w) /\ w * recip_SNo_pos w = 1.
assume Hxpos: 0 < x.
prove SNo (recip_SNo_pos x) /\ x * recip_SNo_pos x = 1.
rewrite recip_SNo_pos_eq x Hx.
prove SNo (G x recip_SNo_pos) /\ x * G x recip_SNo_pos = 1.
set L := \/_ k :e omega, SNo_recipaux x recip_SNo_pos k 0.
set R := \/_ k :e omega, SNo_recipaux x recip_SNo_pos k 1.
claim L1: forall k, nat_p k ->
              (forall y :e SNo_recipaux x recip_SNo_pos k 0, SNo y /\ x * y < 1)
           /\ (forall y :e SNo_recipaux x recip_SNo_pos k 1, SNo y /\ 1 < x * y).
{ exact SNo_recipaux_lem1 x Hx Hxpos recip_SNo_pos IH. }
claim L1L: forall w :e L, x * w < 1.
{ let w. assume Hw.
  apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 0) w Hw.
  let k. assume Hk: k :e omega.
  assume H1: w :e SNo_recipaux x recip_SNo_pos k 0.
  apply L1 k (omega_nat_p k Hk).
  assume H2 _.
  apply H2 w H1.
  assume _ H3. exact H3.
}
claim L1R: forall z :e R, 1 < x * z.
{ let z. assume Hz.
  apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 1) z Hz.
  let k. assume Hk: k :e omega.
  assume H1: z :e SNo_recipaux x recip_SNo_pos k 1.
  apply L1 k (omega_nat_p k Hk).
  assume _ H2.
  apply H2 z H1.
  assume _ H3. exact H3.
}
claim L2: SNoCutP L R.
{ exact SNo_recipaux_lem2 x Hx Hxpos recip_SNo_pos IH. }
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
claim L3: SNo (x * y).
{ exact SNo_mul_SNo x y Hx H1. }
claim L4: 0 < y.
{ apply H3.
  prove 0 :e L.
  apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 0) 0.
  - prove 0 :e omega. apply nat_p_omega. exact nat_0.
  - prove 0 :e SNo_recipaux x recip_SNo_pos 0 0.
    rewrite SNo_recipaux_0.
    prove 0 :e ({0},0) 0.
    rewrite tuple_2_0_eq. apply SingI.
}
claim L5: 0 < x * y.
{ exact mul_SNo_pos_pos x y Hx H1 Hxpos L4. }
claim L6: forall w :e SNoL y, exists w' :e L, w <= w'.
{ exact SNoL_SNoCutP_ex L R L2. }
claim L7: forall z :e SNoR y, exists z' :e R, z' <= z.
{ exact SNoR_SNoCutP_ex L R L2. }
apply andI.
- prove SNo y. exact H1.
- prove x * y = 1.
  apply dneg.
  assume HC: x * y <> 1.
  apply SNoLt_trichotomy_or_impred (x * y) 1 L3 SNo_1.
  + assume H6: x * y < 1.
    claim L8: 1 :e SNoR (x * y).
    { apply SNoR_I.
      - exact L3.
      - exact SNo_1.
      - prove SNoLev 1 :e SNoLev (x * y).
        rewrite ordinal_SNoLev 1 ordinal_1.
        prove 1 :e SNoLev (x * y).
        apply ordinal_In_Or_Subq 1 (SNoLev (x * y)) ordinal_1 (SNoLev_ordinal (x * y) L3).
        + assume H7: 1 :e SNoLev (x * y). exact H7.
        + assume H7: SNoLev (x * y) c= 1. prove False.
          apply HC.
          prove x * y = 1.
          exact pos_low_eq_one (x * y) L3 L5 H7.
      - exact H6.
    }
    claim L9: forall v w w', SNo v -> SNo w -> SNo w' -> v :e SNoS_ (SNoLev x) -> 0 < v -> v * y + x * w <= 1 + v * w -> (1 + (v + - x) * w') * recip_SNo_pos v :e L -> (- v + x) * w' <= (- v + x) * w -> False.
    { let v w w'. assume Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8.
      set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
      claim Lw''1: SNo w''.
      { exact HL w'' Hw''. }
      apply SNoLt_irref 1.
      prove 1 < 1.
      apply SNoLtLe_tra 1 (1 + v * (y + - w'')) 1 SNo_1 (SNo_add_SNo 1 (v * (y + - w'')) SNo_1 (SNo_mul_SNo v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1)))) SNo_1.
      - prove 1 < 1 + v * (y + - w'').
        rewrite <- add_SNo_0R 1 SNo_1 at 1.
        prove 1 + 0 < 1 + v * (y + - w'').
        apply add_SNo_Lt2 1 0 (v * (y + - w'')) SNo_1 SNo_0 (SNo_mul_SNo v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1))).
        prove 0 < v * (y + - w'').
        apply mul_SNo_pos_pos v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1)) Hvpos.
        prove 0 < y + - w''.
        apply SNoLt_minus_pos w'' y Lw''1 H1.
        prove w'' < y.
        exact H3 w'' Hw''.
      - prove 1 + v * (y + - w'') <= 1.
        rewrite mul_SNo_distrL v y (- w'') Hv1 H1 (SNo_minus_SNo w'' Lw''1).
        prove 1 + v * y + v * (- w'') <= 1.
        rewrite mul_SNo_minus_distrR v w'' Hv1 Lw''1.
        prove 1 + v * y + - v * w'' <= 1.
        prove 1 + v * y + - v * (1 + (v + - x) * w') * recip_SNo_pos v <= 1.
        apply IH v HvS Hvpos.
        assume Hrv1: SNo (recip_SNo_pos v).
        assume Hrv2: v * recip_SNo_pos v = 1.
        rewrite mul_SNo_com (1 + (v + - x) * w') (recip_SNo_pos v)
                            (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                            Hrv1.
        prove 1 + v * y + - v * recip_SNo_pos v * (1 + (v + - x) * w') <= 1.
        rewrite mul_SNo_assoc v (recip_SNo_pos v) (1 + (v + - x) * w')
                              Hv1 Hrv1
                              (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw')).
        prove 1 + v * y + - (v * recip_SNo_pos v) * (1 + (v + - x) * w') <= 1.
        rewrite Hrv2.
        prove 1 + v * y + - 1 * (1 + (v + - x) * w') <= 1.
        rewrite mul_SNo_oneL (1 + (v + - x) * w')
                             (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw')).
        prove 1 + v * y + - (1 + (v + - x) * w') <= 1.
        rewrite minus_add_SNo_distr 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw').
        prove 1 + v * y + - 1 + - (v + - x) * w' <= 1.
        rewrite <- add_SNo_rotate_3_1 (- 1) (- (v + - x) * w') (v * y)
                                      (SNo_minus_SNo 1 SNo_1)
                                      (SNo_minus_SNo ((v + - x) * w') (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                                      (SNo_mul_SNo v y Hv1 H1).
        prove 1 + - 1 + - (v + - x) * w' + v * y <= 1.
        rewrite add_SNo_minus_SNo_prop2 1 (- (v + - x) * w' + v * y) SNo_1
                         (SNo_add_SNo (- (v + - x) * w') (v * y)
                                      (SNo_minus_SNo ((v + - x) * w') (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                                      (SNo_mul_SNo v y Hv1 H1)).
        prove - (v + - x) * w' + v * y <= 1.
        rewrite <- mul_SNo_minus_distrL (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'.
        prove (- (v + - x)) * w' + v * y <= 1.
        rewrite minus_add_SNo_distr v (- x) Hv1 (SNo_minus_SNo x Hx).
        rewrite minus_SNo_invol x Hx.
        prove (- v + x) * w' + v * y <= 1.
        apply SNoLe_tra ((- v + x) * w' + v * y) ((- v + x) * w + v * y) 1
                        (SNo_add_SNo ((- v + x) * w') (v * y)
                         (SNo_mul_SNo (- v + x) w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw')
                         (SNo_mul_SNo v y Hv1 H1))
                        (SNo_add_SNo ((- v + x) * w) (v * y)
                         (SNo_mul_SNo (- v + x) w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw1)
                         (SNo_mul_SNo v y Hv1 H1))
                        SNo_1.
        + prove (- v + x) * w' + v * y <= (- v + x) * w + v * y.
          apply add_SNo_Le1 ((- v + x) * w') (v * y) ((- v + x) * w)
                            (SNo_mul_SNo (- v + x) w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw')
                            (SNo_mul_SNo v y Hv1 H1)
                            (SNo_mul_SNo (- v + x) w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw1).
          prove (- v + x) * w' <= (- v + x) * w.
          exact H8.
        + prove (- v + x) * w + v * y <= 1.
          rewrite mul_SNo_distrR (- v) x w (SNo_minus_SNo v Hv1) Hx Hw1.
          prove ((- v) * w + x * w) + v * y <= 1.
          rewrite mul_SNo_minus_distrL v w Hv1 Hw1.
          prove (- v * w + x * w) + v * y <= 1.
          rewrite <- add_SNo_assoc (- v * w) (x * w) (v * y)
                                  (SNo_minus_SNo (v * w) (SNo_mul_SNo v w Hv1 Hw1))
                                   (SNo_mul_SNo x w Hx Hw1)
                                   (SNo_mul_SNo v y Hv1 H1).
          prove - v * w + x * w + v * y <= 1.
          rewrite add_SNo_com (- v * w) (x * w + v * y)
                                   (SNo_minus_SNo (v * w) (SNo_mul_SNo v w Hv1 Hw1))
                                   (SNo_add_SNo (x * w) (v * y)
                                    (SNo_mul_SNo x w Hx Hw1)
                                    (SNo_mul_SNo v y Hv1 H1)).
          apply add_SNo_minus_Le2 1 (- v * w) (x * w + v * y) SNo_1
                                   (SNo_minus_SNo (v * w) (SNo_mul_SNo v w Hv1 Hw1))
                                   (SNo_add_SNo (x * w) (v * y)
                                    (SNo_mul_SNo x w Hx Hw1)
                                    (SNo_mul_SNo v y Hv1 H1)).
          prove x * w + v * y <= 1 + - - v * w.
          rewrite minus_SNo_invol (v * w) (SNo_mul_SNo v w Hv1 Hw1).
          prove x * w + v * y <= 1 + v * w.
          rewrite add_SNo_com (x * w) (v * y) (SNo_mul_SNo x w Hx Hw1) (SNo_mul_SNo v y Hv1 H1).
          prove v * y + x * w <= 1 + v * w.
          exact H7.
    }
    apply mul_SNo_SNoR_interpolate_impred x y Hx H1 1 L8.
    * { let v. assume Hv: v :e SNoL x.
        let w. assume Hw: w :e SNoR y.
        assume H7: v * y + x * w <= 1 + v * w.
        apply SNoL_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: v < x.
        apply SNoR_E y H1 w Hw.
        assume Hw1: SNo w.
        assume Hw2: SNoLev w :e SNoLev y.
        assume Hw3: y < w.
        claim LvS: v :e SNoS_ (SNoLev x).
        { exact SNoS_I2 v x Hv1 Hx Hv2. }
        claim Lxw: SNo (x * w).
        { exact SNo_mul_SNo x w Hx Hw1. }
        apply L7 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e R.
        assume Hw'2: w' <= w.
        claim Lw': SNo w'.
        { exact HR w' Hw'1. }
        claim Lxw': SNo (x * w').
        { exact SNo_mul_SNo x w' Hx Lw'. }
        claim Lvpos: 0 < v.
        { apply SNoLtLe_or 0 v SNo_0 Hv1.
          - assume H8: 0 < v. exact H8.
          - assume H8: v <= 0. prove False.
            apply SNoLt_irref 1.
            prove 1 < 1.
            apply SNoLtLe_tra 1 (x * w') 1 SNo_1 Lxw' SNo_1.
            + prove 1 < x * w'.
              exact L1R w' Hw'1.
            + prove x * w' <= 1.
              apply SNoLe_tra (x * w') (x * w) 1 Lxw' Lxw SNo_1.
              * prove x * w' <= x * w.
                exact nonneg_mul_SNo_Le x w' w Hx (SNoLtLe 0 x Hxpos) Lw' Hw1 Hw'2.  
              * { prove x * w <= 1.
                  apply SNoLe_tra (x * w) (v * (y + - w) + x * w) 1 Lxw (SNo_add_SNo (v * (y + - w)) (x * w) (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))) Lxw) SNo_1.
                  - prove x * w <= v * (y + - w) + x * w.
                    rewrite <- add_SNo_0L (x * w) Lxw at 1.
                    prove 0 + x * w <= v * (y + - w) + x * w.
                    apply add_SNo_Le1 0 (x * w) (v * (y + - w)) SNo_0 Lxw (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))).
                    prove 0 <= v * (y + - w).
                    apply mul_SNo_nonpos_neg v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1)) H8.
                    prove y + - w < 0.
                    apply add_SNo_minus_Lt1b y w 0 H1 Hw1 SNo_0.
                    prove y < 0 + w.
                    rewrite add_SNo_0L w Hw1.
                    prove y < w.
                    exact Hw3.
                  - prove v * (y + - w) + x * w <= 1.
                    rewrite mul_SNo_distrL v y (- w) Hv1 H1 (SNo_minus_SNo w Hw1).
                    prove (v * y + v * (- w)) + x * w <= 1.
                    rewrite add_SNo_com_3b_1_2 (v * y) (v * (- w)) (x * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo v (- w) Hv1 (SNo_minus_SNo w Hw1)) Lxw.
                    prove (v * y + x * w) + v * (- w) <= 1.
                    apply add_SNo_minus_Le2 1 (v * (- w)) (v * y + x * w) SNo_1 (SNo_mul_SNo v (- w) Hv1 (SNo_minus_SNo w Hw1)) (SNo_add_SNo (v * y) (x * w) (SNo_mul_SNo v y Hv1 H1) Lxw).
                    prove v * y + x * w <= 1 + - v * (- w).
                    rewrite mul_SNo_minus_distrR v w Hv1 Hw1.
                    rewrite minus_SNo_invol (v * w) (SNo_mul_SNo v w Hv1 Hw1).
                    exact H7.
                }
        }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e L.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 1) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 1.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 0) (ordsucc k) w'' (omega_ordsucc k Hk).
          prove w'' :e SNo_recipaux x recip_SNo_pos (ordsucc k) 0.
          rewrite SNo_recipaux_S x recip_SNo_pos k (omega_nat_p k Hk).
          rewrite tuple_2_0_eq.
          prove w'' :e SNo_recipaux x recip_SNo_pos k 0 :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoR x) recip_SNo_pos
                           :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoL_pos x) recip_SNo_pos.
          apply binunionI2.
          prove w'' :e SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoL_pos x) recip_SNo_pos.
          apply SNo_recipauxset_I (SNo_recipaux x recip_SNo_pos k 1) x (SNoL_pos x) recip_SNo_pos.
          - prove w' :e SNo_recipaux x recip_SNo_pos k 1.
            exact H9.
          - prove v :e SNoL_pos x.
            prove v :e {w :e SNoL x|0 < w}.
            apply SepI.
            + exact Hv.
            + prove 0 < v. exact Lvpos.
        }
        apply L9 v w w' Hv1 Hw1 Lw' LvS Lvpos H7 Lw''.
        prove (- v + x) * w' <= (- v + x) * w.
        apply nonneg_mul_SNo_Le (- v + x) w' w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx).
        - prove 0 <= - v + x.
          rewrite add_SNo_com (- v) x (SNo_minus_SNo v Hv1) Hx.
          prove 0 <= x + - v.
          apply add_SNo_minus_Le2b x v 0 Hx Hv1 SNo_0.
          prove 0 + v <= x.
          rewrite add_SNo_0L v Hv1.
          apply SNoLtLe. exact Hv3.
        - exact Lw'.
        - exact Hw1.
        - exact Hw'2.
      }
    * { let v. assume Hv: v :e SNoR x.
        let w. assume Hw: w :e SNoL y.
        assume H7: v * y + x * w <= 1 + v * w.
        apply SNoR_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: x < v.
        apply SNoL_E y H1 w Hw.
        assume Hw1: SNo w.
        assume Hw2: SNoLev w :e SNoLev y.
        assume Hw3: w < y.
        claim LvS: v :e SNoS_ (SNoLev x).
        { exact SNoS_I2 v x Hv1 Hx Hv2. }
        claim Lxw: SNo (x * w).
        { exact SNo_mul_SNo x w Hx Hw1. }
        apply L6 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e L.
        assume Hw'2: w <= w'.
        claim Lw': SNo w'.
        { exact HL w' Hw'1. }
        claim Lxw': SNo (x * w').
        { exact SNo_mul_SNo x w' Hx Lw'. }
        claim Lvpos: 0 < v.
        { exact SNoLt_tra 0 x v SNo_0 Hx Hv1 Hxpos Hv3. }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e L.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 0) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 0.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 0) (ordsucc k) w'' (omega_ordsucc k Hk).
          prove w'' :e SNo_recipaux x recip_SNo_pos (ordsucc k) 0.
          rewrite SNo_recipaux_S x recip_SNo_pos k (omega_nat_p k Hk).
          rewrite tuple_2_0_eq.
          prove w'' :e SNo_recipaux x recip_SNo_pos k 0 :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoR x) recip_SNo_pos
                           :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoL_pos x) recip_SNo_pos.
          apply binunionI1. apply binunionI2.
          prove w'' :e SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoR x) recip_SNo_pos.
          apply SNo_recipauxset_I (SNo_recipaux x recip_SNo_pos k 0) x (SNoR x) recip_SNo_pos.
          - prove w' :e SNo_recipaux x recip_SNo_pos k 0.
            exact H9.
          - prove v :e SNoR x. exact Hv.
        }
        apply L9 v w w' Hv1 Hw1 Lw' LvS Lvpos H7 Lw''.
        prove (- v + x) * w' <= (- v + x) * w.
        apply nonpos_mul_SNo_Le (- v + x) w' w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx).
        - prove - v + x <= 0.
          rewrite add_SNo_com (- v) x (SNo_minus_SNo v Hv1) Hx.
          prove x + - v <= 0.
          apply add_SNo_minus_Le2 0 (- v) x SNo_0 (SNo_minus_SNo v Hv1) Hx.
          rewrite minus_SNo_invol v Hv1.
          prove x <= 0 + v.
          rewrite add_SNo_0L v Hv1.
          apply SNoLtLe. exact Hv3.
        - exact Lw'.
        - exact Hw1.
        - exact Hw'2.
      }
  + assume H6: x * y = 1. apply HC. exact H6.
  + assume H6: 1 < x * y.
    claim L10: 1 :e SNoL (x * y).
    { apply SNoL_I.
      - exact L3.
      - exact SNo_1.
      - prove SNoLev 1 :e SNoLev (x * y).
        rewrite ordinal_SNoLev 1 ordinal_1.
        prove 1 :e SNoLev (x * y).
        apply ordinal_In_Or_Subq 1 (SNoLev (x * y)) ordinal_1 (SNoLev_ordinal (x * y) L3).
        + assume H7: 1 :e SNoLev (x * y). exact H7.
        + assume H7: SNoLev (x * y) c= 1. prove False.
          apply HC.
          prove x * y = 1.
          exact pos_low_eq_one (x * y) L3 L5 H7.
      - exact H6.
    }
    claim L11: forall v w w', SNo v -> SNo w -> SNo w' -> v :e SNoS_ (SNoLev x) -> 0 < v -> 1 + v * w <= v * y + x * w -> (1 + (v + - x) * w') * recip_SNo_pos v :e R -> (- v + x) * w <= (- v + x) * w' -> False.
    { let v w w'. assume Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8.
      set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
      claim Lw''1: SNo w''.
      { exact HR w'' Hw''. }
      apply SNoLt_irref 1.
      prove 1 < 1.
      apply SNoLeLt_tra 1 (1 + v * (y + - w'')) 1 SNo_1 (SNo_add_SNo 1 (v * (y + - w'')) SNo_1 (SNo_mul_SNo v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1)))) SNo_1.
      - prove 1 <= 1 + v * (y + - w'').
        rewrite mul_SNo_distrL v y (- w'') Hv1 H1 (SNo_minus_SNo w'' Lw''1).
        prove 1 <= 1 + v * y + v * (- w'').
        rewrite mul_SNo_minus_distrR v w'' Hv1 Lw''1.
        prove 1 <= 1 + v * y + - v * w''.
        prove 1 <= 1 + v * y + - v * (1 + (v + - x) * w') * recip_SNo_pos v.
        apply IH v HvS Hvpos.
        assume Hrv1: SNo (recip_SNo_pos v).
        assume Hrv2: v * recip_SNo_pos v = 1.
        rewrite mul_SNo_com (1 + (v + - x) * w') (recip_SNo_pos v)
                            (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                            Hrv1.
        prove 1 <= 1 + v * y + - v * recip_SNo_pos v * (1 + (v + - x) * w').
        rewrite mul_SNo_assoc v (recip_SNo_pos v) (1 + (v + - x) * w')
                              Hv1 Hrv1
                              (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw')).
        prove 1 <= 1 + v * y + - (v * recip_SNo_pos v) * (1 + (v + - x) * w').
        rewrite Hrv2.
        prove 1 <= 1 + v * y + - 1 * (1 + (v + - x) * w').
        rewrite mul_SNo_oneL (1 + (v + - x) * w')
                             (SNo_add_SNo 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw')).
        prove 1 <= 1 + v * y + - (1 + (v + - x) * w').
        rewrite minus_add_SNo_distr 1 ((v + - x) * w') SNo_1 (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw').
        prove 1 <= 1 + v * y + - 1 + - (v + - x) * w'.
        rewrite <- add_SNo_rotate_3_1 (- 1) (- (v + - x) * w') (v * y)
                                      (SNo_minus_SNo 1 SNo_1)
                                      (SNo_minus_SNo ((v + - x) * w') (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                                      (SNo_mul_SNo v y Hv1 H1).
        prove 1 <= 1 + - 1 + - (v + - x) * w' + v * y.
        rewrite add_SNo_minus_SNo_prop2 1 (- (v + - x) * w' + v * y) SNo_1
                         (SNo_add_SNo (- (v + - x) * w') (v * y)
                                      (SNo_minus_SNo ((v + - x) * w') (SNo_mul_SNo (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'))
                                      (SNo_mul_SNo v y Hv1 H1)).
        prove 1 <= - (v + - x) * w' + v * y.
        rewrite <- mul_SNo_minus_distrL (v + - x) w' (SNo_add_SNo v (- x) Hv1 (SNo_minus_SNo x Hx)) Hw'.
        prove 1 <= (- (v + - x)) * w' + v * y.
        rewrite minus_add_SNo_distr v (- x) Hv1 (SNo_minus_SNo x Hx).
        rewrite minus_SNo_invol x Hx.
        prove 1 <= (- v + x) * w' + v * y.
        apply SNoLe_tra 1 ((- v + x) * w + v * y) ((- v + x) * w' + v * y) SNo_1
                        (SNo_add_SNo ((- v + x) * w) (v * y)
                         (SNo_mul_SNo (- v + x) w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw1)
                         (SNo_mul_SNo v y Hv1 H1))
                        (SNo_add_SNo ((- v + x) * w') (v * y)
                         (SNo_mul_SNo (- v + x) w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw')
                         (SNo_mul_SNo v y Hv1 H1)).
        + prove 1 <= (- v + x) * w + v * y.
          rewrite mul_SNo_distrR (- v) x w (SNo_minus_SNo v Hv1) Hx Hw1.
          prove 1 <= ((- v) * w + x * w) + v * y.
          rewrite mul_SNo_minus_distrL v w Hv1 Hw1.
          prove 1 <= (- v * w + x * w) + v * y.
          rewrite <- add_SNo_assoc (- v * w) (x * w) (v * y)
                                  (SNo_minus_SNo (v * w) (SNo_mul_SNo v w Hv1 Hw1))
                                   (SNo_mul_SNo x w Hx Hw1)
                                   (SNo_mul_SNo v y Hv1 H1).
          prove 1 <= - v * w + x * w + v * y.
          rewrite add_SNo_com (- v * w) (x * w + v * y)
                                   (SNo_minus_SNo (v * w) (SNo_mul_SNo v w Hv1 Hw1))
                                   (SNo_add_SNo (x * w) (v * y)
                                    (SNo_mul_SNo x w Hx Hw1)
                                    (SNo_mul_SNo v y Hv1 H1)).
          prove 1 <= (x * w + v * y) + - v * w.
          apply add_SNo_minus_Le2b (x * w + v * y) (v * w) 1
                                   (SNo_add_SNo (x * w) (v * y)
                                    (SNo_mul_SNo x w Hx Hw1)
                                    (SNo_mul_SNo v y Hv1 H1))
                                   (SNo_mul_SNo v w Hv1 Hw1)
                                   SNo_1.
          prove 1 + v * w <= x * w + v * y.
          rewrite add_SNo_com (x * w) (v * y) (SNo_mul_SNo x w Hx Hw1) (SNo_mul_SNo v y Hv1 H1).
          prove 1 + v * w <= v * y + x * w.
          exact H7.
        + prove (- v + x) * w + v * y <= (- v + x) * w' + v * y.
          apply add_SNo_Le1 ((- v + x) * w) (v * y) ((- v + x) * w')
                            (SNo_mul_SNo (- v + x) w (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw1)
                            (SNo_mul_SNo v y Hv1 H1)
                            (SNo_mul_SNo (- v + x) w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx) Hw').
          prove (- v + x) * w <= (- v + x) * w'.
          exact H8.
      - prove 1 + v * (y + - w'') < 1.
        rewrite <- add_SNo_0R 1 SNo_1 at 4.
        prove 1 + v * (y + - w'') < 1 + 0.
        apply add_SNo_Lt2 1 (v * (y + - w'')) 0 SNo_1 (SNo_mul_SNo v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1))) SNo_0.
        prove v * (y + - w'') < 0.
        apply mul_SNo_pos_neg v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1)) Hvpos.
        prove y + - w'' < 0.
        apply add_SNo_minus_Lt1b y w'' 0 H1 Lw''1 SNo_0.
        prove y < 0 + w''.
        rewrite add_SNo_0L w'' Lw''1.
        prove y < w''.
        exact H4 w'' Hw''.
    }
    apply mul_SNo_SNoL_interpolate_impred x y Hx H1 1 L10.
    * { let v. assume Hv: v :e SNoL x.
        let w. assume Hw: w :e SNoL y.
        assume H7: 1 + v * w <= v * y + x * w.
        apply SNoL_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: v < x.
        apply SNoL_E y H1 w Hw.
        assume Hw1: SNo w.
        assume Hw2: SNoLev w :e SNoLev y.
        assume Hw3: w < y.
        claim LvS: v :e SNoS_ (SNoLev x).
        { exact SNoS_I2 v x Hv1 Hx Hv2. }
        claim Lxw: SNo (x * w).
        { exact SNo_mul_SNo x w Hx Hw1. }
        apply L6 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e L.
        assume Hw'2: w <= w'.
        claim Lw': SNo w'.
        { exact HL w' Hw'1. }
        claim Lxw': SNo (x * w').
        { exact SNo_mul_SNo x w' Hx Lw'. }
        claim Lvpos: 0 < v.
        { apply SNoLtLe_or 0 v SNo_0 Hv1.
          - assume H8: 0 < v. exact H8.
          - assume H8: v <= 0. prove False.
            apply SNoLt_irref 1.
            prove 1 < 1.
            apply SNoLeLt_tra 1 (x * w') 1 SNo_1 Lxw' SNo_1.
            + prove 1 <= x * w'.
              apply SNoLe_tra 1 (x * w) (x * w') SNo_1 Lxw Lxw'.
              * { prove 1 <= x * w.
                  apply SNoLe_tra 1 (v * (y + - w) + x * w) (x * w) SNo_1 (SNo_add_SNo (v * (y + - w)) (x * w) (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))) Lxw) Lxw.
                  - prove 1 <= v * (y + - w) + x * w.
                    rewrite mul_SNo_distrL v y (- w) Hv1 H1 (SNo_minus_SNo w Hw1).
                    prove 1 <= (v * y + v * (- w)) + x * w.
                    rewrite add_SNo_com_3b_1_2 (v * y) (v * (- w)) (x * w) (SNo_mul_SNo v y Hv1 H1) (SNo_mul_SNo v (- w) Hv1 (SNo_minus_SNo w Hw1)) Lxw.
                    prove 1 <= (v * y + x * w) + v * (- w).
                    rewrite mul_SNo_minus_distrR v w Hv1 Hw1.
                    prove 1 <= (v * y + x * w) + - v * w.
                    apply add_SNo_minus_Le2b (v * y + x * w) (v * w) 1 (SNo_add_SNo (v * y) (x * w) (SNo_mul_SNo v y Hv1 H1) Lxw) (SNo_mul_SNo v w Hv1 Hw1) SNo_1.
                    prove 1 + v * w <= v * y + x * w.
                    exact H7.
                  - prove v * (y + - w) + x * w <= x * w.
                    rewrite <- add_SNo_0L (x * w) Lxw at 2.
                    prove v * (y + - w) + x * w <= 0 + x * w.
                    apply add_SNo_Le1 (v * (y + - w)) (x * w) 0 (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))) Lxw SNo_0.
                    prove v * (y + - w) <= 0.
                    apply mul_SNo_nonpos_pos v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1)) H8.
                    prove 0 < y + - w.
                    apply add_SNo_minus_Lt2b y w 0 H1 Hw1 SNo_0.
                    prove 0 + w < y.
                    rewrite add_SNo_0L w Hw1.
                    prove w < y.
                    exact Hw3.
                }
              * prove x * w <= x * w'.
                exact nonneg_mul_SNo_Le x w w' Hx (SNoLtLe 0 x Hxpos) Hw1 Lw' Hw'2.
            + prove x * w' < 1.
              exact L1L w' Hw'1.
        }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e R.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 0) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 0.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 1) (ordsucc k) w'' (omega_ordsucc k Hk).
          prove w'' :e SNo_recipaux x recip_SNo_pos (ordsucc k) 1.
          rewrite SNo_recipaux_S x recip_SNo_pos k (omega_nat_p k Hk).
          rewrite tuple_2_1_eq.
          prove w'' :e SNo_recipaux x recip_SNo_pos k 1 :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoL_pos x) recip_SNo_pos
                           :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoR x) recip_SNo_pos.
          apply binunionI1. apply binunionI2.
          prove w'' :e SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoL_pos x) recip_SNo_pos.
          apply SNo_recipauxset_I (SNo_recipaux x recip_SNo_pos k 0) x (SNoL_pos x) recip_SNo_pos.
          - prove w' :e SNo_recipaux x recip_SNo_pos k 0.
            exact H9.
          - prove v :e SNoL_pos x.
            prove v :e {w :e SNoL x|0 < w}.
            apply SepI.
            + exact Hv.
            + prove 0 < v. exact Lvpos.
        }
        apply L11 v w w' Hv1 Hw1 Lw' LvS Lvpos H7 Lw''.
        prove (- v + x) * w <= (- v + x) * w'.
        apply nonneg_mul_SNo_Le (- v + x) w w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx).
        - prove 0 <= - v + x.
          rewrite add_SNo_com (- v) x (SNo_minus_SNo v Hv1) Hx.
          prove 0 <= x + - v.
          apply add_SNo_minus_Le2b x v 0 Hx Hv1 SNo_0.
          prove 0 + v <= x.
          rewrite add_SNo_0L v Hv1.
          prove v <= x.
          apply SNoLtLe. exact Hv3.
        - exact Hw1.
        - exact Lw'.
        - exact Hw'2.
      }
    * { let v. assume Hv: v :e SNoR x.
        let w. assume Hw: w :e SNoR y.
        assume H7: 1 + v * w <= v * y + x * w.
        apply SNoR_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: x < v.
        apply SNoR_E y H1 w Hw.
        assume Hw1: SNo w.
        assume Hw2: SNoLev w :e SNoLev y.
        assume Hw3: y < w.
        claim LvS: v :e SNoS_ (SNoLev x).
        { exact SNoS_I2 v x Hv1 Hx Hv2. }
        claim Lvpos: 0 < v.
        { exact SNoLt_tra 0 x v SNo_0 Hx Hv1 Hxpos Hv3. }
        claim Lxw: SNo (x * w).
        { exact SNo_mul_SNo x w Hx Hw1. }
        apply L7 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e R.
        assume Hw'2: w' <= w.
        claim Lw': SNo w'.
        { exact HR w' Hw'1. }
        claim Lxw': SNo (x * w').
        { exact SNo_mul_SNo x w' Hx Lw'. }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e R.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 1) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 1.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 1) (ordsucc k) w'' (omega_ordsucc k Hk).
          prove w'' :e SNo_recipaux x recip_SNo_pos (ordsucc k) 1.
          rewrite SNo_recipaux_S x recip_SNo_pos k (omega_nat_p k Hk).
          rewrite tuple_2_1_eq.
          prove w'' :e SNo_recipaux x recip_SNo_pos k 1 :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 0) x (SNoL_pos x) recip_SNo_pos
                           :\/: SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoR x) recip_SNo_pos.
          apply binunionI2.
          prove w'' :e SNo_recipauxset (SNo_recipaux x recip_SNo_pos k 1) x (SNoR x) recip_SNo_pos.
          apply SNo_recipauxset_I (SNo_recipaux x recip_SNo_pos k 1) x (SNoR x) recip_SNo_pos.
          - prove w' :e SNo_recipaux x recip_SNo_pos k 1.
            exact H9.
          - prove v :e SNoR x. exact Hv.
        }
        apply L11 v w w' Hv1 Hw1 Lw' LvS Lvpos H7 Lw''.
        prove (- v + x) * w <= (- v + x) * w'.
        apply L11 v w w' Hv1 Hw1 Lw' LvS Lvpos H7 Lw''.
        prove (- v + x) * w <= (- v + x) * w'.
        apply nonpos_mul_SNo_Le (- v + x) w w' (SNo_add_SNo (- v) x (SNo_minus_SNo v Hv1) Hx).
        - prove - v + x <= 0.
          rewrite add_SNo_com (- v) x (SNo_minus_SNo v Hv1) Hx.
          prove x + - v <= 0.
          apply add_SNo_minus_Le2 0 (- v) x SNo_0 (SNo_minus_SNo v Hv1) Hx.
          rewrite minus_SNo_invol v Hv1.
          prove x <= 0 + v.
          rewrite add_SNo_0L v Hv1.
          apply SNoLtLe. exact Hv3.
        - exact Hw1.
        - exact Lw'.
        - exact Hw'2.
      }
Qed.

Theorem SNo_recip_SNo_pos: forall x, SNo x -> 0 < x -> SNo (recip_SNo_pos x).
let x. assume Hx Hxpos.
apply recip_SNo_pos_prop1 x Hx Hxpos. assume H _. exact H.
Qed.

Theorem recip_SNo_pos_invR: forall x, SNo x -> 0 < x -> x * recip_SNo_pos x = 1.
let x. assume Hx Hxpos.
apply recip_SNo_pos_prop1 x Hx Hxpos. assume _ H. exact H.
Qed.

Theorem recip_SNo_pos_1: recip_SNo_pos 1 = 1.
apply mul_SNo_nonzero_cancel 1 (recip_SNo_pos 1) 1 SNo_1 neq_1_0 (SNo_recip_SNo_pos 1 SNo_1 SNoLt_0_1) SNo_1.
prove 1 * recip_SNo_pos 1 = 1 * 1.
rewrite mul_SNo_oneL 1 SNo_1.
prove 1 * recip_SNo_pos 1 = 1.
exact recip_SNo_pos_invR 1 SNo_1 SNoLt_0_1.
Qed.

Theorem recip_SNo_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
let x. assume Hx Hxpos.
claim Lrx: SNo (recip_SNo_pos x).
{ exact SNo_recip_SNo_pos x Hx Hxpos. }
apply SNoLt_trichotomy_or_impred (recip_SNo_pos x) 0 Lrx SNo_0.
- assume H1: recip_SNo_pos x < 0.
  prove False.
  apply SNoLt_irref 0.
  prove 0 < 0.
  apply SNoLt_tra 0 1 0 SNo_0 SNo_1 SNo_0 SNoLt_0_1.
  prove 1 < 0.
  rewrite <- recip_SNo_pos_invR x Hx Hxpos.
  prove x * recip_SNo_pos x < 0.
  exact mul_SNo_pos_neg x (recip_SNo_pos x) Hx Lrx Hxpos H1.
- assume H1: recip_SNo_pos x = 0.
  prove False.
  apply neq_1_0.
  prove 1 = 0.
  rewrite <- recip_SNo_pos_invR x Hx Hxpos.
  prove x * recip_SNo_pos x = 0.
  rewrite H1.
  exact mul_SNo_zeroR x Hx.
- assume H1. exact H1.
Qed.

Theorem recip_SNo_pos_invol: forall x, SNo x -> 0 < x -> recip_SNo_pos (recip_SNo_pos x) = x.
let x. assume Hx Hxpos.
claim Lrx: SNo (recip_SNo_pos x).
{ exact SNo_recip_SNo_pos x Hx Hxpos. }
claim Lrxpos: 0 < recip_SNo_pos x.
{ exact recip_SNo_pos_is_pos x Hx Hxpos. }
claim Lrrx: SNo (recip_SNo_pos (recip_SNo_pos x)).
{ exact SNo_recip_SNo_pos (recip_SNo_pos x) Lrx Lrxpos. }
claim Lrxn0: recip_SNo_pos x <> 0.
{ assume Hrx0: recip_SNo_pos x = 0.
  apply SNoLt_irref 0.
  prove 0 < 0.
  rewrite <- Hrx0 at 2.
  exact Lrxpos.
}
prove recip_SNo_pos (recip_SNo_pos x) = x.
apply mul_SNo_nonzero_cancel (recip_SNo_pos x) (recip_SNo_pos (recip_SNo_pos x)) x Lrx Lrxn0 Lrrx Hx.
prove recip_SNo_pos x * recip_SNo_pos (recip_SNo_pos x) = recip_SNo_pos x * x.
rewrite mul_SNo_com (recip_SNo_pos x) x Lrx Hx.
rewrite recip_SNo_pos_invR x Hx Hxpos.
exact recip_SNo_pos_invR (recip_SNo_pos x) Lrx Lrxpos.
Qed.

Theorem recip_SNo_pos_eps_: forall n, nat_p n -> recip_SNo_pos (eps_ n) = 2 ^ n.
let n. assume Hn.
claim Len1: SNo (eps_ n).
{ exact SNo_eps_ n (nat_p_omega n Hn). }
claim Len2: 0 < eps_ n.
{ exact SNo_eps_pos n (nat_p_omega n Hn). }
claim Len3: eps_ n <> 0.
{ assume H1: eps_ n = 0.
  apply SNoLt_irref 0.
  prove 0 < 0.
  rewrite <- H1 at 2.
  prove 0 < eps_ n.
  exact Len2.
}
apply mul_SNo_nonzero_cancel (eps_ n) (recip_SNo_pos (eps_ n)) (2 ^ n) Len1 Len3 (SNo_recip_SNo_pos (eps_ n) Len1 Len2) (SNo_exp_SNo_nat 2 SNo_2 n Hn).
prove eps_ n * recip_SNo_pos (eps_ n) = eps_ n * 2 ^ n.
rewrite mul_SNo_eps_power_2 n Hn.
prove eps_ n * recip_SNo_pos (eps_ n) = 1.
exact recip_SNo_pos_invR (eps_ n) Len1 Len2.
Qed.

Theorem recip_SNo_pos_pow_2: forall n, nat_p n -> recip_SNo_pos (2 ^ n) = eps_ n.
let n. assume Hn.
rewrite <- recip_SNo_pos_eps_ n Hn.
exact recip_SNo_pos_invol (eps_ n) (SNo_eps_ n (nat_p_omega n Hn)) (SNo_eps_pos n (nat_p_omega n Hn)).
Qed.

Theorem recip_SNo_pos_2: recip_SNo_pos 2 = eps_ 1.
rewrite <- exp_SNo_nat_1 2 SNo_2.
exact recip_SNo_pos_pow_2 1 nat_1.
Qed.

End recip_SNo_pos.

Definition recip_SNo : set -> set := fun x => if 0 < x then recip_SNo_pos x else if x < 0 then - recip_SNo_pos (- x) else 0.

Theorem recip_SNo_poscase: forall x, 0 < x -> recip_SNo x = recip_SNo_pos x.
let x. assume Hxpos.
exact If_i_1 (0 < x) (recip_SNo_pos x) (if x < 0 then - recip_SNo_pos (- x) else 0) Hxpos.
Qed.

Theorem recip_SNo_negcase: forall x, SNo x -> x < 0 -> recip_SNo x = - recip_SNo_pos (- x).
let x. assume Hx Hxneg.
claim L1: ~(0 < x).
{ assume H1. apply SNoLt_irref 0.
  prove 0 < 0.
  exact SNoLt_tra 0 x 0 SNo_0 Hx SNo_0 H1 Hxneg.
}
prove (if 0 < x then recip_SNo_pos x else if x < 0 then - recip_SNo_pos (- x) else 0) = - recip_SNo_pos (- x).
rewrite If_i_0 (0 < x) (recip_SNo_pos x) (if x < 0 then - recip_SNo_pos (- x) else 0) L1.
exact If_i_1 (x < 0) (- recip_SNo_pos (- x)) 0 Hxneg.
Qed.

Theorem recip_SNo_0: recip_SNo 0 = 0.
prove (if 0 < 0 then recip_SNo_pos 0 else if 0 < 0 then - recip_SNo_pos (- 0) else 0) = 0.
rewrite If_i_0 (0 < 0) (recip_SNo_pos 0) (if 0 < 0 then - recip_SNo_pos (- 0) else 0) (SNoLt_irref 0).
prove (if 0 < 0 then - recip_SNo_pos (- 0) else 0) = 0.
exact If_i_0 (0 < 0) (- recip_SNo_pos (- 0)) 0 (SNoLt_irref 0).
Qed.

Theorem recip_SNo_1: recip_SNo 1 = 1.
rewrite recip_SNo_poscase 1 SNoLt_0_1.
exact recip_SNo_pos_1.
Qed.

Theorem SNo_recip_SNo: forall x, SNo x -> SNo (recip_SNo x).
let x. assume Hx.
apply SNoLt_trichotomy_or_impred x 0 Hx SNo_0.
- assume H1: x < 0. rewrite recip_SNo_negcase x Hx H1.
  prove SNo (- recip_SNo_pos (- x)).
  apply SNo_minus_SNo.
  prove SNo (recip_SNo_pos (- x)).
  apply SNo_recip_SNo_pos.
  + exact SNo_minus_SNo x Hx.
  + prove 0 < - x.
    apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
    prove x < - 0.
    rewrite minus_SNo_0.
    prove x < 0.
    exact H1.
- assume H1: x = 0. rewrite H1. rewrite recip_SNo_0. exact SNo_0.
- assume H1: 0 < x. rewrite recip_SNo_poscase x H1.
  exact SNo_recip_SNo_pos x Hx H1.
Qed.

Theorem recip_SNo_invR: forall x, SNo x -> x <> 0 -> x * recip_SNo x = 1.
let x. assume Hx Hx0.
apply SNoLt_trichotomy_or_impred x 0 Hx SNo_0.
- assume H1: x < 0. rewrite recip_SNo_negcase x Hx H1.
  claim L1: 0 < - x.
  { apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
    prove x < - 0.
    rewrite minus_SNo_0.
    prove x < 0.
    exact H1.
  }
  prove x * (- recip_SNo_pos (- x)) = 1.
  rewrite mul_SNo_minus_distrR x (recip_SNo_pos (- x)) Hx (SNo_recip_SNo_pos (- x) (SNo_minus_SNo x Hx) L1).
  prove - (x * recip_SNo_pos (- x)) = 1.
  rewrite <- mul_SNo_minus_distrL x (recip_SNo_pos (- x)) Hx (SNo_recip_SNo_pos (- x) (SNo_minus_SNo x Hx) L1).
  prove (- x) * recip_SNo_pos (- x) = 1.
  exact recip_SNo_pos_invR (- x) (SNo_minus_SNo x Hx) L1.
- assume H1: x = 0. prove False. exact Hx0 H1.
- assume H1: 0 < x. rewrite recip_SNo_poscase x H1.
  exact recip_SNo_pos_invR x Hx H1.
Qed.

Theorem recip_SNo_invL: forall x, SNo x -> x <> 0 -> recip_SNo x * x = 1.
let x. assume Hx Hx0.
rewrite mul_SNo_com (recip_SNo x) x (SNo_recip_SNo x Hx) Hx.
prove x * recip_SNo x = 1.
exact recip_SNo_invR x Hx Hx0.
Qed.

Theorem recip_SNo_eps_: forall n, nat_p n -> recip_SNo (eps_ n) = 2 ^ n.
let n. assume Hn.
rewrite recip_SNo_poscase (eps_ n) (SNo_eps_pos n (nat_p_omega n Hn)).
exact recip_SNo_pos_eps_ n Hn.
Qed.

Theorem recip_SNo_pow_2 : forall n, nat_p n -> recip_SNo (2 ^ n) = eps_ n.
let n. assume Hn.
claim L1: 0 < 2 ^ n.
{ exact exp_SNo_nat_pos 2 SNo_2 SNoLt_0_2 n Hn. }
rewrite recip_SNo_poscase (2 ^ n) L1.
exact recip_SNo_pos_pow_2 n Hn.
Qed.

Theorem recip_SNo_2 : recip_SNo 2 = eps_ 1.
rewrite recip_SNo_poscase 2 SNoLt_0_2.
exact recip_SNo_pos_2.
Qed.

Theorem recip_SNo_invol: forall x, SNo x -> recip_SNo (recip_SNo x) = x.
let x. assume Hx.
apply SNoLt_trichotomy_or_impred x 0 Hx SNo_0.
- assume H1: x < 0.
  rewrite recip_SNo_negcase x Hx H1.
  claim Lmx: SNo (- x).
  { exact SNo_minus_SNo x Hx. }
  claim Lmxpos: 0 < - x.
  { apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
    prove x < - 0.
    rewrite minus_SNo_0.
    prove x < 0.
    exact H1.
  }
  claim Lrmx: SNo (recip_SNo_pos (- x)).
  { exact SNo_recip_SNo_pos (- x) Lmx Lmxpos. }
  claim Lmrmx: SNo (- recip_SNo_pos (- x)).
  { exact SNo_minus_SNo (recip_SNo_pos (- x)) Lrmx. }
  claim L1: 0 < recip_SNo_pos (- x).
  { exact recip_SNo_pos_is_pos (- x) Lmx Lmxpos. }
  claim L2: - recip_SNo_pos (- x) < 0.
  { apply minus_SNo_Lt_contra1 0 (recip_SNo_pos (- x)) SNo_0 Lrmx.
    prove - 0 < recip_SNo_pos (- x).
    rewrite minus_SNo_0. exact L1.
  }
  rewrite recip_SNo_negcase (- (recip_SNo_pos (- x))) Lmrmx L2.
  prove - recip_SNo_pos (- (- (recip_SNo_pos (- x)))) = x.
  rewrite minus_SNo_invol (recip_SNo_pos (- x)) Lrmx.
  rewrite recip_SNo_pos_invol (- x) Lmx Lmxpos.
  exact minus_SNo_invol x Hx.
- assume H1: x = 0. rewrite H1. rewrite recip_SNo_0. exact recip_SNo_0.
- assume H1: 0 < x.
  rewrite recip_SNo_poscase x H1.
  rewrite recip_SNo_poscase (recip_SNo_pos x) (recip_SNo_pos_is_pos x Hx H1).
  exact recip_SNo_pos_invol x Hx H1.
Qed.

Theorem recip_SNo_of_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo x.
let x. assume Hx Hxpos.
rewrite recip_SNo_poscase x Hxpos.
exact recip_SNo_pos_is_pos x Hx Hxpos.
Qed.

Theorem recip_SNo_neg': forall x, SNo x -> x < 0 -> recip_SNo x < 0.
let x. assume Hx Hxneg.
claim Lmx: SNo (- x).
{ exact SNo_minus_SNo x Hx. }
claim Lmxpos: 0 < - x.
{ apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
  prove x < - 0.
  rewrite minus_SNo_0.
  exact Hxneg.
}
claim Lrmx: SNo (recip_SNo_pos (- x)).
{ apply SNo_recip_SNo_pos.
  - apply SNo_minus_SNo. exact Hx.
  - exact Lmxpos.
}
rewrite recip_SNo_negcase x Hx Hxneg.
prove - recip_SNo_pos (- x) < 0.
apply minus_SNo_Lt_contra1 0 (recip_SNo_pos (- x)) SNo_0 Lrmx.
prove - 0 < recip_SNo_pos (- x).
rewrite minus_SNo_0.
prove 0 < recip_SNo_pos (- x).
apply recip_SNo_pos_is_pos (- x) Lmx.
prove 0 < - x.
exact Lmxpos.
Qed.

Definition div_SNo : set -> set -> set := fun x y => x * recip_SNo y.

Infix :/: 353 := div_SNo.

Theorem SNo_div_SNo: forall x y, SNo x -> SNo y -> SNo (x :/: y).
let x y. assume Hx Hy.
prove SNo (x * recip_SNo y).
exact SNo_mul_SNo x (recip_SNo y) Hx (SNo_recip_SNo y Hy).
Qed.

Theorem div_SNo_0_num: forall x, SNo x -> 0 :/: x = 0.
let x. assume Hx.
exact mul_SNo_zeroL (recip_SNo x) (SNo_recip_SNo x Hx).
Qed.

Theorem div_SNo_0_denum: forall x, SNo x -> x :/: 0 = 0.
let x. assume Hx.
prove x * recip_SNo 0 = 0.
rewrite recip_SNo_0.
exact mul_SNo_zeroR x Hx.
Qed.

Theorem mul_div_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x :/: y) * y = x.
let x y. assume Hx Hy Hy0.
prove (x * recip_SNo y) * y = x.
rewrite <- mul_SNo_assoc x (recip_SNo y) y Hx (SNo_recip_SNo y Hy) Hy.
prove x * (recip_SNo y * y) = x.
rewrite recip_SNo_invL y Hy Hy0.
prove x * 1 = x.
exact mul_SNo_oneR x Hx.
Qed.

Theorem mul_div_SNo_invR: forall x y, SNo x -> SNo y -> y <> 0 -> y * (x :/: y) = x.
let x y. assume Hx Hy Hy0.
rewrite mul_SNo_com y (x :/: y) Hy (SNo_div_SNo x y Hx Hy).
exact mul_div_SNo_invL x y Hx Hy Hy0.
Qed.

Theorem mul_div_SNo_R: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) * z = (x * z) :/: y.
let x y z. assume Hx Hy Hz.
apply xm (y = 0).
- assume H1: y = 0.
  rewrite H1.
  rewrite div_SNo_0_denum x Hx.
  rewrite div_SNo_0_denum (x * z) (SNo_mul_SNo x z Hx Hz).
  prove 0 * z = 0.
  exact mul_SNo_zeroL z Hz.
- assume H1: y <> 0.
  apply mul_SNo_nonzero_cancel y ((x :/: y) * z) ((x * z) :/: y) Hy H1 (SNo_mul_SNo (x :/: y) z (SNo_div_SNo x y Hx Hy) Hz) (SNo_div_SNo (x * z) y (SNo_mul_SNo x z Hx Hz) Hy).
  prove y * (x :/: y) * z = y * (x * z) :/: y.
  rewrite mul_div_SNo_invR (x * z) y (SNo_mul_SNo x z Hx Hz) Hy H1.
  prove y * (x :/: y) * z = x * z.
  rewrite mul_SNo_assoc y (x :/: y) z Hy (SNo_div_SNo x y Hx Hy) Hz.
  prove (y * (x :/: y)) * z = x * z.
  f_equal.
  prove y * (x :/: y) = x.
  exact mul_div_SNo_invR x y Hx Hy H1.
Qed.

Theorem mul_div_SNo_L: forall x y z, SNo x -> SNo y -> SNo z -> z * (x :/: y) = (z * x) :/: y.
let x y z. assume Hx Hy Hz.
transitivity (x :/: y) * z, (x * z) :/: y.
- exact mul_SNo_com z (x :/: y) Hz (SNo_div_SNo x y Hx Hy).
- exact mul_div_SNo_R x y z Hx Hy Hz.
- f_equal. exact mul_SNo_com x z Hx Hz.
Qed.

Theorem div_mul_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x * y) :/: y = x.
let x y. assume Hx Hy Hy0.
rewrite <- mul_div_SNo_R x y y Hx Hy Hy.
prove (x :/: y) * y = x.
exact mul_div_SNo_invL x y Hx Hy Hy0.
Qed.

Theorem div_div_SNo: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) :/: z = x :/: (y * z).
let x y z. assume Hx Hy Hz.
claim Lxdy: SNo (x :/: y).
{ exact SNo_div_SNo x y Hx Hy. }
claim Lxdydz: SNo ((x :/: y) :/: z).
{ exact SNo_div_SNo (x :/: y) z Lxdy Hz. }
claim Lxy: SNo (x * y).
{ exact SNo_mul_SNo x y Hx Hy. }
claim Lyz: SNo (y * z).
{ exact SNo_mul_SNo y z Hy Hz. }
claim Lxdyz: SNo (x :/: (y * z)).
{ exact SNo_div_SNo x (y * z) Hx Lyz. }
apply xm (y = 0).
- assume Hy0: y = 0.
  rewrite Hy0.
  prove (x :/: 0) :/: z = x :/: (0 * z).
  rewrite mul_SNo_zeroL z Hz.
  rewrite div_SNo_0_denum x Hx.
  prove 0 :/: z = 0.
  exact div_SNo_0_num z Hz.
- assume Hy0: y <> 0.
  apply xm (z = 0).
  + assume Hz0: z = 0.
    rewrite Hz0.
    prove (x :/: y) :/: 0 = x :/: (y * 0).
    rewrite mul_SNo_zeroR y Hy.
    prove (x :/: y) :/: 0 = x :/: 0.
    rewrite div_SNo_0_denum x Hx.
    exact div_SNo_0_denum (x :/: y) Lxdy.
  + assume Hz0: z <> 0.
    claim Lyz0: y * z <> 0.
    { assume H1: y * z = 0.
      apply Hz0.
      prove z = 0.
      apply mul_SNo_nonzero_cancel y z 0 Hy Hy0 Hz SNo_0.
      prove y * z = y * 0.
      rewrite mul_SNo_zeroR y Hy.
      exact H1.
    }
    apply mul_SNo_nonzero_cancel z ((x :/: y) :/: z) (x :/: (y * z)) Hz Hz0 Lxdydz Lxdyz.
    rewrite mul_div_SNo_invR (x :/: y) z Lxdy Hz Hz0.
    prove x :/: y = z * (x :/: (y * z)).
    apply mul_SNo_nonzero_cancel y (x :/: y) (z * (x :/: (y * z))) Hy Hy0 Lxdy (SNo_mul_SNo z (x :/: (y * z)) Hz Lxdyz).
    rewrite mul_div_SNo_invR x y Hx Hy Hy0.
    prove x = y * z * (x :/: (y * z)).
    rewrite mul_SNo_assoc y z (x :/: (y * z)) Hy Hz Lxdyz.
    symmetry.
    exact mul_div_SNo_invR x (y * z) Hx Lyz Lyz0.
Qed.

Theorem mul_div_SNo_both: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x :/: y) * (z :/: w) = (x * z) :/: (y * w).
let x y z w. assume Hx Hy Hz Hw.
rewrite mul_div_SNo_L z w (x :/: y) Hz Hw (SNo_div_SNo x y Hx Hy).
prove ((x :/: y) * z) :/: w = (x * z) :/: (y * w).
rewrite mul_div_SNo_R x y z Hx Hy Hz.
prove ((x * z) :/: y) :/: w = (x * z) :/: (y * w).
exact div_div_SNo (x * z) y w (SNo_mul_SNo x z Hx Hz) Hy Hw.
Qed.

Theorem recip_SNo_pos_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
let x. assume Hx Hxpos.
apply SNoLtLe_or 0 (recip_SNo_pos x) SNo_0 (SNo_recip_SNo_pos x Hx Hxpos).
- assume H1: 0 < recip_SNo_pos x. exact H1.
- assume H1: recip_SNo_pos x <= 0. prove False.
  apply SNoLt_irref 0.
  prove 0 < 0.
  apply SNoLtLe_tra 0 1 0 SNo_0 SNo_1 SNo_0 SNoLt_0_1.
  prove 1 <= 0.
  rewrite <- recip_SNo_pos_invR x Hx Hxpos.
  prove x * recip_SNo_pos x <= 0.
  rewrite <- mul_SNo_zeroR x Hx.
  prove x * recip_SNo_pos x <= x * 0.
  exact nonneg_mul_SNo_Le x (recip_SNo_pos x) 0 Hx (SNoLtLe 0 x Hxpos) (SNo_recip_SNo_pos x Hx Hxpos) SNo_0 H1.
Qed.

Theorem recip_SNo_of_neg_is_neg: forall x, SNo x -> x < 0 -> recip_SNo x < 0.
let x. assume Hx Hxneg.
rewrite recip_SNo_negcase x Hx Hxneg.
prove - recip_SNo_pos (- x) < 0.
claim Lmx: SNo (- x).
{ exact SNo_minus_SNo x Hx. }
claim L1: 0 < - x.
{ apply minus_SNo_Lt_contra2 x 0 Hx SNo_0.
  prove x < - 0.
  rewrite minus_SNo_0.
  exact Hxneg.
}
apply minus_SNo_Lt_contra1 0 (recip_SNo_pos (- x)) SNo_0 (SNo_recip_SNo_pos (- x) Lmx L1).
prove - 0 < recip_SNo_pos (- x).
rewrite minus_SNo_0.
prove 0 < recip_SNo_pos (- x).
apply recip_SNo_pos_pos (- x) (SNo_minus_SNo x Hx).
prove 0 < - x.
exact L1.
Qed.

Theorem div_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x :/: y.
let x y. assume Hx Hy Hxpos Hypos.
prove 0 < x * recip_SNo y.
apply mul_SNo_pos_pos x (recip_SNo y) Hx (SNo_recip_SNo y Hy) Hxpos.
prove 0 < recip_SNo y.
exact recip_SNo_of_pos_is_pos y Hy Hypos.
Qed.

Theorem div_SNo_neg_neg: forall x y, SNo x -> SNo y -> x < 0 -> y < 0 -> 0 < x :/: y.
let x y. assume Hx Hy Hxneg Hyneg.
prove 0 < x * recip_SNo y.
apply mul_SNo_neg_neg x (recip_SNo y) Hx (SNo_recip_SNo y Hy) Hxneg.
prove recip_SNo y < 0.
exact recip_SNo_neg' y Hy Hyneg.
Qed.

Theorem div_SNo_pos_neg: forall x y, SNo x -> SNo y -> 0 < x -> y < 0 -> x :/: y < 0.
let x y. assume Hx Hy Hxpos Hyneg.
prove x * recip_SNo y < 0.
apply mul_SNo_pos_neg x (recip_SNo y) Hx (SNo_recip_SNo y Hy) Hxpos.
prove recip_SNo y < 0.
exact recip_SNo_neg' y Hy Hyneg.
Qed.

Theorem div_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x :/: y < 0.
let x y. assume Hx Hy Hxneg Hypos.
prove x * recip_SNo y < 0.
apply mul_SNo_neg_pos x (recip_SNo y) Hx (SNo_recip_SNo y Hy) Hxneg.
prove 0 < recip_SNo y.
exact recip_SNo_of_pos_is_pos y Hy Hypos.
Qed.

Theorem div_SNo_pos_LtL : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x < z * y -> x :/: y < z.
let x y z. assume Hx Hy Hz Hypos.
assume H1: x < z * y.
prove x :/: y < z.
rewrite <- mul_SNo_oneR z Hz.
prove x :/: y < z * 1.
claim Ly0: y <> 0.
{ assume H2: y = 0. apply SNoLt_irref y.
  prove y < y. rewrite H2 at 1.
  exact Hypos.
}
rewrite <- recip_SNo_invR y Hy Ly0.
prove x * recip_SNo y < z * y * recip_SNo y.
rewrite mul_SNo_assoc z y (recip_SNo y) Hz Hy (SNo_recip_SNo y Hy).
prove x * recip_SNo y < (z * y) * recip_SNo y.
apply pos_mul_SNo_Lt' x (z * y) (recip_SNo y) Hx (SNo_mul_SNo z y Hz Hy) (SNo_recip_SNo y Hy).
- prove 0 < recip_SNo y.
  exact recip_SNo_of_pos_is_pos y Hy Hypos.
- prove x < z * y. exact H1.
Qed.

Theorem div_SNo_pos_LtR : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z * y < x -> z < x :/: y.
let x y z. assume Hx Hy Hz Hypos.
assume H1: z * y < x.
prove z < x :/: y.
rewrite <- mul_SNo_oneR z Hz.
prove z * 1 < x :/: y.
claim Ly0: y <> 0.
{ assume H2: y = 0. apply SNoLt_irref y.
  prove y < y. rewrite H2 at 1.
  exact Hypos.
}
rewrite <- recip_SNo_invR y Hy Ly0.
prove z * y * recip_SNo y < x * recip_SNo y.
rewrite mul_SNo_assoc z y (recip_SNo y) Hz Hy (SNo_recip_SNo y Hy).
prove (z * y) * recip_SNo y < x * recip_SNo y.
apply pos_mul_SNo_Lt' (z * y) x (recip_SNo y) (SNo_mul_SNo z y Hz Hy) Hx (SNo_recip_SNo y Hy).
- prove 0 < recip_SNo y.
  exact recip_SNo_of_pos_is_pos y Hy Hypos.
- prove z * y < x. exact H1.
Qed.

Theorem div_SNo_pos_LtL' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x :/: y < z -> x < z * y.
let x y z. assume Hx Hy Hz Hypos.
assume H1: x :/: y < z.
prove x < z * y.
rewrite <- mul_SNo_oneR x Hx.
prove x * 1 < z * y.
claim Ly0: y <> 0.
{ assume H2: y = 0. apply SNoLt_irref y.
  prove y < y. rewrite H2 at 1.
  exact Hypos.
}
rewrite <- recip_SNo_invL y Hy Ly0.
prove x * (recip_SNo y * y) < z * y.
rewrite mul_SNo_assoc x (recip_SNo y) y Hx (SNo_recip_SNo y Hy) Hy.
prove (x * recip_SNo y) * y < z * y.
prove (x :/: y) * y < z * y.
exact pos_mul_SNo_Lt' (x :/: y) z y (SNo_div_SNo x y Hx Hy) Hz Hy Hypos H1.
Qed.

Theorem div_SNo_pos_LtR' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z < x :/: y -> z * y < x.
let x y z. assume Hx Hy Hz Hypos.
assume H1: z < x :/: y.
prove z * y < x.
rewrite <- mul_SNo_oneR x Hx.
prove z * y < x * 1.
claim Ly0: y <> 0.
{ assume H2: y = 0. apply SNoLt_irref y.
  prove y < y. rewrite H2 at 1.
  exact Hypos.
}
rewrite <- recip_SNo_invL y Hy Ly0.
prove z * y < x * (recip_SNo y * y).
rewrite mul_SNo_assoc x (recip_SNo y) y Hx (SNo_recip_SNo y Hy) Hy.
prove z * y < (x * recip_SNo y) * y.
prove z * y < (x :/: y) * y.
exact pos_mul_SNo_Lt' z (x :/: y) y Hz (SNo_div_SNo x y Hx Hy) Hy Hypos H1.
Qed.

Theorem mul_div_SNo_nonzero_eq: forall x y z, SNo x -> SNo y -> SNo z -> y <> 0 -> x = y * z -> x :/: y = z.
let x y z. assume Hx Hy Hz Hy0 H1.
apply mul_SNo_nonzero_cancel y (x :/: y) z Hy Hy0 (SNo_div_SNo x y Hx Hy) Hz.
prove y * (x :/: y) = y * z.
rewrite mul_div_SNo_invR x y Hx Hy Hy0.
exact H1.
Qed.

End SurrealDiv.

Opaque SNo_recipauxset.
Opaque SNo_recipaux.
Opaque recip_SNo_pos.
Opaque recip_SNo.
