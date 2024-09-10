(** Part 5 **)
Section SurrealAdd.

Prefix - 358 := minus_SNo.

(* Parameter add_SNo "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" "127d043261bd13d57aaeb99e7d2c02cae2bd0698c0d689b03e69f1ac89b3c2c6" *)
Definition add_SNo : set -> set -> set
  := SNo_rec2 (fun x y a => SNoCut ({a w y|w :e SNoL x} :\/: {a x w|w :e SNoL y}) ({a z y|z :e SNoR x} :\/: {a x z|z :e SNoR y})).

Infix + 360 right := add_SNo.

Theorem add_SNo_eq : forall x, SNo x -> forall y, SNo y ->
    x + y = SNoCut ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
set F : set -> set -> (set -> set -> set) -> set
  := fun x y a => SNoCut ({a w y|w :e SNoL x} :\/: {a x w|w :e SNoL y}) ({a z y|z :e SNoR x} :\/: {a x z|z :e SNoR y}).
claim L1: forall x, SNo x -> forall y, SNo y ->
  forall g h:set -> set -> set,
      (forall w :e SNoS_ (SNoLev x), forall z, SNo z -> g w z = h w z)
   -> (forall z :e SNoS_ (SNoLev y), g x z = h x z)
   -> F x y g = F x y h.
{ let x. assume Hx: SNo x.
  let y. assume Hy: SNo y.
  let g h.
  assume Hgh1: forall w :e SNoS_ (SNoLev x), forall z, SNo z -> g w z = h w z.
  assume Hgh2: forall z :e SNoS_ (SNoLev y), g x z = h x z.
  prove F x y g = F x y h.
  claim L1a: {g w y|w :e SNoL x} = {h w y|w :e SNoL x}.
  { apply ReplEq_ext.
    let w. assume Hw: w :e SNoL x.
    prove g w y = h w y.
    apply Hgh1.
    - prove w :e SNoS_ (SNoLev x). exact SNoL_SNoS x Hx w Hw.
    - prove SNo y. exact Hy.
  }
  claim L1b: {g x w|w :e SNoL y} = {h x w|w :e SNoL y}.
  { apply ReplEq_ext.
    let w. assume Hw: w :e SNoL y.
    prove g x w = h x w.
    apply Hgh2.
    prove w :e SNoS_ (SNoLev y). exact SNoL_SNoS y Hy w Hw.
  }
  claim L1c: {g z y|z :e SNoR x} = {h z y|z :e SNoR x}.
  { apply ReplEq_ext.
    let z. assume Hz: z :e SNoR x.
    prove g z y = h z y.
    apply Hgh1.
    - prove z :e SNoS_ (SNoLev x). exact SNoR_SNoS x Hx z Hz.
    - prove SNo y. exact Hy.
  }
  claim L1d: {g x z|z :e SNoR y} = {h x z|z :e SNoR y}.
  { apply ReplEq_ext.
    let z. assume Hz: z :e SNoR y.
    prove g x z = h x z.
    apply Hgh2.
    prove z :e SNoS_ (SNoLev y). exact SNoR_SNoS y Hy z Hz.
  }
  prove SNoCut ({g w y|w :e SNoL x} :\/: {g x w|w :e SNoL y}) ({g z y|z :e SNoR x} :\/: {g x z|z :e SNoR y})
      = SNoCut ({h w y|w :e SNoL x} :\/: {h x w|w :e SNoL y}) ({h z y|z :e SNoR x} :\/: {h x z|z :e SNoR y}).
  rewrite L1a.
  rewrite L1b.
  rewrite L1c.
  rewrite L1d.
  reflexivity.
}
exact SNo_rec2_eq F L1.
Qed.

Theorem add_SNo_prop1 : forall x y, SNo x -> SNo y ->
    SNo (x + y)
 /\ (forall u :e SNoL x, u + y < x + y)
 /\ (forall u :e SNoR x, x + y < u + y)
 /\ (forall u :e SNoL y, x + u < x + y)
 /\ (forall u :e SNoR y, x + y < x + u)
 /\ SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
set P : set -> set -> prop
 := fun x y =>
     SNo (x + y)
 /\ (forall u :e SNoL x, u + y < x + y)
 /\ (forall u :e SNoR x, x + y < u + y)
 /\ (forall u :e SNoL y, x + u < x + y)
 /\ (forall u :e SNoR y, x + y < x + u)
 /\ SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
claim LPE: forall x y, P x y -> (** drop the SNoCut part here **)
  forall p:prop,
       (SNo (x + y)
         -> (forall u :e SNoL x, u + y < x + y)
         -> (forall u :e SNoR x, x + y < u + y)
         -> (forall u :e SNoL y, x + u < x + y)
         -> (forall u :e SNoR y, x + y < x + u)
         -> p)
    -> p.
{ let x y. assume Hxy.
  let p. assume Hp.
  apply Hxy.
  assume H. apply H. assume H. apply H.
  assume H. apply H. assume H. apply H.
  assume H1 H2 H3 H4 H5 _.
  exact Hp H1 H2 H3 H4 H5.
}
prove forall x y, SNo x -> SNo y -> P x y.
apply SNoLev_ind2.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume IHx: forall w :e SNoS_ (SNoLev x), P w y.
assume IHy: forall z :e SNoS_ (SNoLev y), P x z.
assume IHxy: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z.
claim LLx: ordinal (SNoLev x).
{ exact SNoLev_ordinal x Hx. }
claim LLxa: TransSet (SNoLev x).
{ exact ordinal_TransSet (SNoLev x) LLx. }
claim LLy: ordinal (SNoLev y).
{ exact SNoLev_ordinal y Hy. }
claim LLya: TransSet (SNoLev y).
{ exact ordinal_TransSet (SNoLev y) LLy. }
set L1 := {w + y|w :e SNoL x}.
set L2 := {x + w|w :e SNoL y}.
set L := L1 :\/: L2.
set R1 := {z + y|z :e SNoR x}.
set R2 := {x + z|z :e SNoR y}.
set R := R1 :\/: R2.
claim IHLx : forall w :e SNoL x, P w y.
{ let w. assume Hw: w :e SNoL x.
  apply SNoL_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: w < x.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  exact IHx w Lw.
}
claim IHRx : forall w :e SNoR x, P w y.
{ let w. assume Hw: w :e SNoR x.
  apply SNoR_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: x < w.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  exact IHx w Lw.
}
claim IHLy : forall w :e SNoL y, P x w.
{ let w. assume Hw: w :e SNoL y.
  apply SNoL_E y Hy w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  assume Hw3: w < y.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoS_I2 w y Hw1 Hy Hw2. }
  exact IHy w Lw.
}
claim IHRy : forall w :e SNoR y, P x w.
{ let w. assume Hw: w :e SNoR y.
  apply SNoR_E y Hy w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  assume Hw3: y < w.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoS_I2 w y Hw1 Hy Hw2. }
  exact IHy w Lw.
}
claim LLR: SNoCutP L R.
{ prove (forall w :e L, SNo w)
     /\ (forall z :e R, SNo z)
     /\ (forall w :e L, forall z :e R, w < z).
  apply and3I.
  - let w. assume Hw: w :e L1 :\/: L2.
    prove SNo w.
    apply binunionE L1 L2 w Hw.
    + assume Hw: w :e {w + y|w :e SNoL x}.
      apply ReplE_impred (SNoL x) (fun z => z + y) w Hw.
      let z.
      assume Hz: z :e SNoL x.
      assume Hwz: w = z + y.
      apply LPE z y (IHLx z Hz).
      assume H2: SNo (z + y).
      assume _ _ _ _.
      prove SNo w.
      rewrite Hwz. exact H2.
    + assume Hw: w :e {x + w|w :e SNoL y}.
      apply ReplE_impred (SNoL y) (fun z => x + z) w Hw.
      let z.
      assume Hz: z :e SNoL y.
      assume Hwz: w = x + z.
      apply LPE x z (IHLy z Hz).
      assume H2: SNo (x + z).
      assume _ _ _ _.
      prove SNo w.
      rewrite Hwz. exact H2.
  - let w. assume Hw: w :e R1 :\/: R2.
    prove SNo w.
    apply binunionE R1 R2 w Hw.
    + assume Hw: w :e {z + y|z :e SNoR x}.
      apply ReplE_impred (SNoR x) (fun z => z + y) w Hw.
      let z.
      assume Hz: z :e SNoR x.
      assume Hwz: w = z + y.
      apply LPE z y (IHRx z Hz).
      assume H2: SNo (z + y).
      assume _ _ _ _.
      prove SNo w.
      rewrite Hwz. exact H2.
    + assume Hw: w :e {x + z|z :e SNoR y}.
      apply ReplE_impred (SNoR y) (fun z => x + z) w Hw.
      let z.
      assume Hz: z :e SNoR y.
      assume Hwz: w = x + z.
      apply LPE x z (IHRy z Hz).
      assume H2: SNo (x + z).
      assume _ _ _ _.
      prove SNo w.
      rewrite Hwz. exact H2.
  - let w. assume Hw: w :e L.
    let z. assume Hz: z :e R.
    prove w < z.
    apply binunionE L1 L2 w Hw.
    + assume Hw: w :e {w + y|w :e SNoL x}.
      apply ReplE_impred (SNoL x) (fun z => z + y) w Hw.
      let u.
      assume Hu: u :e SNoL x.
      assume Hwu: w = u + y.
      apply SNoL_E x Hx u Hu.
      assume Hu1: SNo u.
      assume Hu2: SNoLev u :e SNoLev x.
      assume Hu3: u < x.
      claim Lux: u :e SNoS_ (SNoLev x).
      { exact SNoS_I2 u x Hu1 Hx Hu2. }
      apply LPE u y (IHLx u Hu).
      assume IHu1: SNo (u + y).
      assume IHu2: forall z :e SNoL u, z + y < u + y.
      assume IHu3: forall z :e SNoR u, u + y < z + y.
      assume IHu4: forall z :e SNoL y, u + z < u + y.
      assume IHu5: forall z :e SNoR y, u + y < u + z.
      prove w < z.
      rewrite Hwu.
      prove u + y < z.
      apply binunionE R1 R2 z Hz.
      * { assume Hz: z :e {z + y|z :e SNoR x}.
          apply ReplE_impred (SNoR x) (fun z => z + y) z Hz.
          let v.
          assume Hv: v :e SNoR x.
          assume Hzv: z = v + y.
          apply SNoR_E x Hx v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev x.
          assume Hv3: x < v.
          apply LPE v y (IHRx v Hv).
          assume IHv1: SNo (v + y).
          assume IHv2: forall u :e SNoL v, u + y < v + y.
          assume IHv3: forall u :e SNoR v, v + y < u + y.
          assume IHv4: forall u :e SNoL y, v + u < v + y.
          assume IHv5: forall u :e SNoR y, v + y < v + u.
          rewrite Hzv.
          prove u + y < v + y.
          claim Luv: u < v.
          { exact SNoLt_tra u x v Hu1 Hx Hv1 Hu3 Hv3. }
          apply SNoLtE u v Hu1 Hv1 Luv.
          - let q.
            assume Hq1: SNo q.
            assume Hq2: SNoLev q :e SNoLev u :/\: SNoLev v.
            assume _ _.
            assume Hq5: u < q.
            assume Hq6: q < v.
            assume _ _.
            apply binintersectE (SNoLev u) (SNoLev v) (SNoLev q) Hq2.
            assume Hq2u Hq2v.
            claim Lqx: SNoLev q :e SNoLev x.
            { exact LLxa (SNoLev u) Hu2 (SNoLev q) Hq2u. }
            claim Lqx2: q :e SNoS_ (SNoLev x).
            { exact SNoS_I2 q x Hq1 Hx Lqx. }
            claim Lqy: SNo (q + y).
            { apply LPE q y (IHx q Lqx2).
              assume IHq1 _ _ _ _. exact IHq1.
            }
            apply SNoLt_tra (u + y) (q + y) (v + y) IHu1 Lqy IHv1.
            + prove u + y < q + y.
              apply IHu3.
              prove q :e SNoR u.
              exact SNoR_I u Hu1 q Hq1 Hq2u Hq5.
            + prove q + y < v + y.
              apply IHv2.
              prove q :e SNoL v.
              exact SNoL_I v Hv1 q Hq1 Hq2v Hq6.
          - assume Huv: SNoLev u :e SNoLev v.
            assume _ _.
            prove u + y < v + y.
            apply IHv2.
            prove u :e SNoL v.
            exact SNoL_I v Hv1 u Hu1 Huv Luv.
          - assume Hvu: SNoLev v :e SNoLev u.
            assume _ _.
            prove u + y < v + y.
            apply IHu3.
            prove v :e SNoR u.
            exact SNoR_I u Hu1 v Hv1 Hvu Luv.
        }
      * { assume Hz: z :e {x + z|z :e SNoR y}.
          apply ReplE_impred (SNoR y) (fun z => x + z) z Hz.
          let v.
          assume Hv: v :e SNoR y.
          assume Hzv: z = x + v.
          apply SNoR_E y Hy v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev y.
          assume Hv3: y < v.
          claim Lvy: v :e SNoS_ (SNoLev y).
          { exact SNoS_I2 v y Hv1 Hy Hv2. }
          apply LPE x v (IHRy v Hv).
          assume IHv1: SNo (x + v).
          assume IHv2: forall u :e SNoL x, u + v < x + v.
          assume IHv3: forall u :e SNoR x, x + v < u + v.
          assume IHv4: forall u :e SNoL v, x + u < x + v.
          assume IHv5: forall u :e SNoR v, x + v < x + u.
          rewrite Hzv.
          prove u + y < x + v.
          apply LPE u v (IHxy u Lux v Lvy).
          assume IHuv1: SNo (u + v).
          assume _ _ _ _.
          prove u + y < x + v.
          apply SNoLt_tra (u + y) (u + v) (x + v) IHu1 IHuv1 IHv1.
          - prove u + y < u + v.
            apply IHu5.
            prove v :e SNoR y.
            exact SNoR_I y Hy v Hv1 Hv2 Hv3.
          - prove u + v < x + v.
            apply IHv2.
            prove u :e SNoL x.
            exact SNoL_I x Hx u Hu1 Hu2 Hu3.
        }
    + assume Hw: w :e {x + w|w :e SNoL y}.
      apply ReplE_impred (SNoL y) (fun z => x + z) w Hw.
      let u.
      assume Hu: u :e SNoL y.
      assume Hwu: w = x + u.
      apply SNoL_E y Hy u Hu.
      assume Hu1: SNo u.
      assume Hu2: SNoLev u :e SNoLev y.
      assume Hu3: u < y.
      claim Luy: u :e SNoS_ (SNoLev y).
      { exact SNoS_I2 u y Hu1 Hy Hu2. }
      apply LPE x u (IHLy u Hu).
      assume IHu1: SNo (x + u).
      assume IHu2: forall z :e SNoL x, z + u < x + u.
      assume IHu3: forall z :e SNoR x, x + u < z + u.
      assume IHu4: forall z :e SNoL u, x + z < x + u.
      assume IHu5: forall z :e SNoR u, x + u < x + z.
      prove w < z.
      rewrite Hwu.
      prove x + u < z.
      apply binunionE R1 R2 z Hz.
      * { assume Hz: z :e {z + y|z :e SNoR x}.
          apply ReplE_impred (SNoR x) (fun z => z + y) z Hz.
          let v.
          assume Hv: v :e SNoR x.
          assume Hzv: z = v + y.
          apply SNoR_E x Hx v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev x.
          assume Hv3: x < v.
          claim Lvx: v :e SNoS_ (SNoLev x).
          { exact SNoS_I2 v x Hv1 Hx Hv2. }
          apply LPE v y (IHRx v Hv).
          assume IHv1: SNo (v + y).
          assume IHv2: forall u :e SNoL v, u + y < v + y.
          assume IHv3: forall u :e SNoR v, v + y < u + y.
          assume IHv4: forall u :e SNoL y, v + u < v + y.
          assume IHv5: forall u :e SNoR y, v + y < v + u.
          rewrite Hzv.
          prove x + u < v + y.
          apply LPE v u (IHxy v Lvx u Luy).
          assume IHvu1: SNo (v + u).
          assume _ _ _ _.
          prove x + u < v + y.
          apply SNoLt_tra (x + u) (v + u) (v + y) IHu1 IHvu1 IHv1.
          - prove x + u < v + u.
            apply IHu3.
            prove v :e SNoR x.
            exact SNoR_I x Hx v Hv1 Hv2 Hv3.
          - prove v + u < v + y.
            apply IHv4.
            prove u :e SNoL y.
            exact SNoL_I y Hy u Hu1 Hu2 Hu3.
        }
      * { assume Hz: z :e {x + z|z :e SNoR y}.
          apply ReplE_impred (SNoR y) (fun z => x + z) z Hz.
          let v.
          assume Hv: v :e SNoR y.
          assume Hzv: z = x + v.
          apply SNoR_E y Hy v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev y.
          assume Hv3: y < v.
          apply LPE x v (IHRy v Hv).
          assume IHv1: SNo (x + v).
          assume IHv2: forall u :e SNoL x, u + v < x + v.
          assume IHv3: forall u :e SNoR x, x + v < u + v.
          assume IHv4: forall u :e SNoL v, x + u < x + v.
          assume IHv5: forall u :e SNoR v, x + v < x + u.
          rewrite Hzv.
          prove x + u < x + v.
          claim Luv: u < v.
          { exact SNoLt_tra u y v Hu1 Hy Hv1 Hu3 Hv3. }
          apply SNoLtE u v Hu1 Hv1 Luv.
          - let q.
            assume Hq1: SNo q.
            assume Hq2: SNoLev q :e SNoLev u :/\: SNoLev v.
            assume _ _.
            assume Hq5: u < q.
            assume Hq6: q < v.
            assume _ _.
            apply binintersectE (SNoLev u) (SNoLev v) (SNoLev q) Hq2.
            assume Hq2u Hq2v.
            claim Lqy: SNoLev q :e SNoLev y.
            { exact LLya (SNoLev v) Hv2 (SNoLev q) Hq2v. }
            claim Lqy2: q :e SNoS_ (SNoLev y).
            { exact SNoS_I2 q y Hq1 Hy Lqy. }
            claim Lxq: SNo (x + q).
            { apply LPE x q (IHy q Lqy2).
              assume IHq1 _ _ _ _. exact IHq1.
            }
            prove x + u < x + v.
            apply SNoLt_tra (x + u) (x + q) (x + v) IHu1 Lxq IHv1.
            + prove x + u < x + q.
              apply IHu5.
              prove q :e SNoR u.
              exact SNoR_I u Hu1 q Hq1 Hq2u Hq5.
            + prove x + q < x + v.
              apply IHv4.
              prove q :e SNoL v.
              exact SNoL_I v Hv1 q Hq1 Hq2v Hq6.
          - assume Huv: SNoLev u :e SNoLev v.
            assume _ _.
            prove x + u < x + v.
            apply IHv4.
            prove u :e SNoL v.
            exact SNoL_I v Hv1 u Hu1 Huv Luv.
          - assume Hvu: SNoLev v :e SNoLev u.
            assume _ _.
            prove x + u < x + v.
            apply IHu5.
            prove v :e SNoR u.
            exact SNoR_I u Hu1 v Hv1 Hvu Luv.
        }
}
prove P x y.
prove SNo (x + y)
 /\ (forall u :e SNoL x, u + y < x + y)
 /\ (forall u :e SNoR x, x + y < u + y)
 /\ (forall u :e SNoL y, x + u < x + y)
 /\ (forall u :e SNoR y, x + y < x + u)
 /\ SNoCutP L R.
claim LNLR: SNo (SNoCut L R).
{ exact SNoCutP_SNo_SNoCut L R LLR. }
apply andI.
- rewrite add_SNo_eq x Hx y Hy.
  apply and5I.
  + prove SNo (SNoCut L R). exact LNLR.
  + prove forall u :e SNoL x, u + y < SNoCut L R.
    let u. assume Hu: u :e SNoL x.
    prove u + y < SNoCut L R.
    apply SNoL_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: u < x.
    claim LuyL: u + y :e L.
    { prove u + y :e L1 :\/: L2.
      apply binunionI1.
      prove u + y :e {w + y|w :e SNoL x}.
      apply ReplI (SNoL x) (fun w => w + y) u.
      prove u :e SNoL x.
      exact Hu.
    }
    prove u + y < SNoCut L R.
    exact SNoCutP_SNoCut_L L R LLR (u + y) LuyL.
  + prove forall u :e SNoR x, SNoCut L R < u + y.
    let u. assume Hu: u :e SNoR x.
    prove SNoCut L R < u + y.
    apply SNoR_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: x < u.
    claim LuyR: u + y :e R.
    { prove u + y :e R1 :\/: R2.
      apply binunionI1.
      prove u + y :e {z + y|z :e SNoR x}.
      apply ReplI (SNoR x) (fun w => w + y) u.
      prove u :e SNoR x.
      exact Hu.
    }
    prove SNoCut L R < u + y.
    exact SNoCutP_SNoCut_R L R LLR (u + y) LuyR.
  + prove forall u :e SNoL y, x + u < SNoCut L R.
    let u. assume Hu: u :e SNoL y.
    prove x + u < SNoCut L R.
    apply SNoL_E y Hy u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev y.
    assume Hu3: u < y.
    claim LxuL: x + u :e L.
    { prove x + u :e L1 :\/: L2.
      apply binunionI2.
      prove x + u :e {x + w|w :e SNoL y}.
      apply ReplI (SNoL y) (fun w => x + w) u.
      prove u :e SNoL y.
      exact Hu.
    }
    prove x + u < SNoCut L R.
    exact SNoCutP_SNoCut_L L R LLR (x + u) LxuL.
  + prove forall u :e SNoR y, SNoCut L R < x + u.
    let u. assume Hu: u :e SNoR y.
    prove SNoCut L R < x + u.
    apply SNoR_E y Hy u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev y.
    assume Hu3: y < u.
    claim LxuR: x + u :e R.
    { prove x + u :e R1 :\/: R2.
      apply binunionI2.
      prove x + u :e {x + z|z :e SNoR y}.
      apply ReplI (SNoR y) (fun z => x + z) u.
      prove u :e SNoR y.
      exact Hu.
    }
    prove SNoCut L R < x + u.
    exact SNoCutP_SNoCut_R L R LLR (x + u) LxuR.
- exact LLR.
Qed.

Theorem SNo_add_SNo : forall x y, SNo x -> SNo y -> SNo (x + y).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
apply add_SNo_prop1 x y Hx Hy.
assume H. apply H. assume H. apply H.
assume H. apply H. assume H. apply H.
assume H _ _ _ _ _. exact H.
Qed.

Theorem SNo_add_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + z).
let x y z. assume Hx Hy Hz.
apply SNo_add_SNo.
- exact Hx.
- apply SNo_add_SNo.
  + exact Hy.
  + exact Hz.
Qed.

Theorem SNo_add_SNo_3c : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + - z).
let x y z. assume Hx Hy Hz.
apply SNo_add_SNo_3.
- exact Hx.
- exact Hy.
- apply SNo_minus_SNo. exact Hz.
Qed.

Theorem SNo_add_SNo_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> SNo (x + y + z + w).
let x y z w. assume Hx Hy Hz Hw.
exact SNo_add_SNo_3 x y (z + w) Hx Hy (SNo_add_SNo z w Hz Hw).
Qed.

Theorem add_SNo_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x < z -> x + y < z + y.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hxz: x < z.
apply add_SNo_prop1 x y Hx Hy.
assume H. apply H. assume H. apply H.
assume H. apply H. assume H. apply H.
assume H1: SNo (x + y).
assume _.
assume H2: forall u :e SNoR x, x + y < u + y.
assume _ _ _.
apply add_SNo_prop1 z y Hz Hy.
assume H. apply H. assume H. apply H.
assume H. apply H. assume H. apply H.
assume H3: SNo (z + y).
assume H4: forall u :e SNoL z, u + y < z + y.
assume _ _ _ _.
apply SNoLtE x z Hx Hz Hxz.
- let w.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x :/\: SNoLev z.
  assume _ _.
  assume Hw5: x < w.
  assume Hw6: w < z.
  assume _ _.
  apply binintersectE (SNoLev x) (SNoLev z) (SNoLev w) Hw2.
  assume Hw2x Hw2z.
  prove x + y < z + y.
  apply SNoLt_tra (x + y) (w + y) (z + y) H1 (SNo_add_SNo w y Hw1 Hy) H3.
  + prove x + y < w + y.
    apply H2.
    prove w :e SNoR x.
    apply SNoR_I x Hx w Hw1.
    * prove SNoLev w :e SNoLev x.
      exact Hw2x.
    * prove x < w. exact Hw5.
  + prove w + y < z + y.
    apply H4.
    prove w :e SNoL z.
    apply SNoL_I z Hz w Hw1.
    * prove SNoLev w :e SNoLev z.
      exact Hw2z.
    * prove w < z. exact Hw6.
- assume Hxz1: SNoLev x :e SNoLev z.
  assume _ _.
  prove x + y < z + y.
  apply H4.
  prove x :e SNoL z.
  apply SNoL_I z Hz x Hx.
  + prove SNoLev x :e SNoLev z.
    exact Hxz1.
  + prove x < z. exact Hxz.
- assume Hzx: SNoLev z :e SNoLev x.
  assume _ _.
  prove x + y < z + y.
  apply H2.
  prove z :e SNoR x.
  apply SNoR_I x Hx z Hz.
  + prove SNoLev z :e SNoLev x.
    exact Hzx.
  + prove x < z. exact Hxz.
Qed.

Theorem add_SNo_Le1 : forall x y z, SNo x -> SNo y -> SNo z -> x <= z -> x + y <= z + y.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hxz: x <= z.
prove x + y <= z + y.
apply SNoLeE x z Hx Hz Hxz.
- assume H1: x < z. apply SNoLtLe. exact add_SNo_Lt1 x y z Hx Hy Hz H1.
- assume H1: x = z. rewrite H1. apply SNoLe_ref.
Qed.

Theorem add_SNo_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> y < z -> x + y < x + z.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hyz: y < z.
apply add_SNo_prop1 x y Hx Hy.
assume H. apply H. assume H. apply H.
assume H. apply H. assume H. apply H.
assume H1: SNo (x + y).
assume _ _ _.
assume H2: forall u :e SNoR y, x + y < x + u.
assume _.
apply add_SNo_prop1 x z Hx Hz.
assume H. apply H. assume H. apply H.
assume H. apply H. assume H. apply H.
assume H3: SNo (x + z).
assume _ _.
assume H4: forall u :e SNoL z, x + u < x + z.
assume _ _.
apply SNoLtE y z Hy Hz Hyz.
- let w.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y :/\: SNoLev z.
  assume _ _.
  assume Hw5: y < w.
  assume Hw6: w < z.
  assume _ _.
  apply binintersectE (SNoLev y) (SNoLev z) (SNoLev w) Hw2.
  assume Hw2y Hw2z.
  prove x + y < x + z.
  apply SNoLt_tra (x + y) (x + w) (x + z) H1 (SNo_add_SNo x w Hx Hw1) H3.
  + prove x + y < x + w.
    apply H2.
    prove w :e SNoR y.
    apply SNoR_I y Hy w Hw1.
    * prove SNoLev w :e SNoLev y.
      exact Hw2y.
    * prove y < w. exact Hw5.
  + prove x + w < x + z.
    apply H4.
    prove w :e SNoL z.
    apply SNoL_I z Hz w Hw1.
    * prove SNoLev w :e SNoLev z.
      exact Hw2z.
    * prove w < z. exact Hw6.
- assume Hyz1: SNoLev y :e SNoLev z.
  assume _ _.
  prove x + y < x + z.
  apply H4.
  prove y :e SNoL z.
  apply SNoL_I z Hz y Hy.
  + prove SNoLev y :e SNoLev z.
    exact Hyz1.
  + prove y < z. exact Hyz.
- assume Hzy: SNoLev z :e SNoLev y.
  assume _ _.
  prove x + y < x + z.
  apply H2.
  prove z :e SNoR y.
  apply SNoR_I y Hy z Hz.
  + prove SNoLev z :e SNoLev y.
    exact Hzy.
  + prove y < z. exact Hyz.
Qed.

Theorem add_SNo_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> y <= z -> x + y <= x + z.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hyz: y <= z.
prove x + y <= x + z.
apply SNoLeE y z Hy Hz Hyz.
- assume H1: y < z. apply SNoLtLe. exact add_SNo_Lt2 x y z Hx Hy Hz H1.
- assume H1: y = z. rewrite H1. apply SNoLe_ref.
Qed.

Theorem add_SNo_Lt3a : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y <= w -> x + y < z + w.
let x y z w.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hw: SNo w.
assume Hxz: x < z.
assume Hyw: y <= w.
apply SNoLtLe_tra (x+y) (z+y) (z+w) (SNo_add_SNo x y Hx Hy) (SNo_add_SNo z y Hz Hy) (SNo_add_SNo z w Hz Hw).
- prove x+y < z+y. exact add_SNo_Lt1 x y z Hx Hy Hz Hxz.
- prove z+y <= z+w. exact add_SNo_Le2 z y w Hz Hy Hw Hyw.
Qed.

Theorem add_SNo_Lt3b : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y < w -> x + y < z + w.
let x y z w.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hw: SNo w.
assume Hxz: x <= z.
assume Hyw: y < w.
apply SNoLeLt_tra (x+y) (z+y) (z+w) (SNo_add_SNo x y Hx Hy) (SNo_add_SNo z y Hz Hy) (SNo_add_SNo z w Hz Hw).
- prove x+y <= z+y. exact add_SNo_Le1 x y z Hx Hy Hz Hxz.
- prove z+y < z+w. exact add_SNo_Lt2 z y w Hz Hy Hw Hyw.
Qed.

Theorem add_SNo_Lt3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y < w -> x + y < z + w.
let x y z w.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hw: SNo w.
assume Hxz: x < z.
assume Hyw: y < w.
apply add_SNo_Lt3a x y z w Hx Hy Hz Hw Hxz.
prove y <= w.
apply SNoLtLe.
prove y < w.
exact Hyw.
Qed.

Theorem add_SNo_Le3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y <= w -> x + y <= z + w.
let x y z w.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hw: SNo w.
assume Hxz: x <= z.
assume Hyw: y <= w.
apply SNoLe_tra (x+y) (z+y) (z+w) (SNo_add_SNo x y Hx Hy) (SNo_add_SNo z y Hz Hy) (SNo_add_SNo z w Hz Hw).
- prove x+y <= z+y. exact add_SNo_Le1 x y z Hx Hy Hz Hxz.
- prove z+y <= z+w. exact add_SNo_Le2 z y w Hz Hy Hw Hyw.
Qed.

Theorem add_SNo_SNoCutP : forall x y, SNo x -> SNo y -> SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
apply add_SNo_prop1 x y Hx Hy.
assume _ H. exact H.
Qed.

Theorem add_SNo_com : forall x y, SNo x -> SNo y -> x + y = y + x.
apply SNoLev_ind2.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume IHx: forall w :e SNoS_ (SNoLev x), w + y = y + w.
assume IHy: forall z :e SNoS_ (SNoLev y), x + z = z + x.
assume IHxy: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), w + z = z + w.
claim IHLx : forall w :e SNoL x, w + y = y + w.
{ let w. assume Hw: w :e SNoL x.
  apply SNoL_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: w < x.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  exact IHx w Lw.
}
claim IHRx : forall w :e SNoR x, w + y = y + w.
{ let w. assume Hw: w :e SNoR x.
  apply SNoR_E x Hx w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev x.
  assume Hw3: x < w.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoS_I2 w x Hw1 Hx Hw2. }
  exact IHx w Lw.
}
claim IHLy : forall w :e SNoL y, x + w = w + x.
{ let w. assume Hw: w :e SNoL y.
  apply SNoL_E y Hy w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  assume Hw3: w < y.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoS_I2 w y Hw1 Hy Hw2. }
  exact IHy w Lw.
}
claim IHRy : forall w :e SNoR y, x + w = w + x.
{ let w. assume Hw: w :e SNoR y.
  apply SNoR_E y Hy w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  assume Hw3: y < w.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoS_I2 w y Hw1 Hy Hw2. }
  exact IHy w Lw.
}
prove x + y = y + x.
set Lxy1 := {w + y|w :e SNoL x}.
set Lxy2 := {x + w|w :e SNoL y}.
set Rxy1 := {z + y|z :e SNoR x}.
set Rxy2 := {x + z|z :e SNoR y}.
rewrite add_SNo_eq x Hx y Hy.
prove (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) = y + x.
set Lyx1 := {w + x|w :e SNoL y}.
set Lyx2 := {y + w|w :e SNoL x}.
set Ryx1 := {z + x|z :e SNoR y}.
set Ryx2 := {y + z|z :e SNoR x}.
rewrite add_SNo_eq y Hy x Hx.
prove (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2))
    = (SNoCut (Lyx1 :\/: Lyx2) (Ryx1 :\/: Ryx2)).
claim Lxy1yx2: Lxy1 = Lyx2.
{ prove {w + y|w :e SNoL x} = {y + w|w :e SNoL x}.
  apply ReplEq_ext (SNoL x) (fun w => w + y) (fun w => y + w).
  let w. assume Hw: w :e SNoL x.
  prove w + y = y + w.
  exact IHLx w Hw.
}
claim Lxy2yx1: Lxy2 = Lyx1.
{ prove {x + w|w :e SNoL y} = {w + x|w :e SNoL y}.
  apply ReplEq_ext (SNoL y) (fun w => x + w) (fun w => w + x).
  let w. assume Hw: w :e SNoL y.
  prove x + w = w + x.
  exact IHLy w Hw.
}
claim Rxy1yx2: Rxy1 = Ryx2.
{ prove {w + y|w :e SNoR x} = {y + w|w :e SNoR x}.
  apply ReplEq_ext (SNoR x) (fun w => w + y) (fun w => y + w).
  let w. assume Hw: w :e SNoR x.
  prove w + y = y + w.
  exact IHRx w Hw.
}
claim Rxy2yx1: Rxy2 = Ryx1.
{ prove {x + w|w :e SNoR y} = {w + x|w :e SNoR y}.
  apply ReplEq_ext (SNoR y) (fun w => x + w) (fun w => w + x).
  let w. assume Hw: w :e SNoR y.
  prove x + w = w + x.
  exact IHRy w Hw.
}
rewrite Lxy1yx2.
rewrite Lxy2yx1.
rewrite Rxy1yx2.
rewrite Rxy2yx1.
prove (SNoCut (Lyx2 :\/: Lyx1) (Ryx2 :\/: Ryx1))
    = (SNoCut (Lyx1 :\/: Lyx2) (Ryx1 :\/: Ryx2)).
rewrite binunion_com Lyx2 Lyx1.
rewrite binunion_com Ryx2 Ryx1.
reflexivity.
Qed.

Theorem add_SNo_0L : forall x, SNo x -> 0 + x = x.
apply SNoLev_ind.
let x.
assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), 0 + w = w.
prove 0 + x = x.
rewrite add_SNo_eq 0 SNo_0 x Hx.
prove SNoCut ({w + x|w :e SNoL 0} :\/: {0 + w|w :e SNoL x}) ({w + x|w :e SNoR 0} :\/: {0 + w|w :e SNoR x}) = x.
claim L1: {w + x|w :e SNoL 0} :\/: {0 + w|w :e SNoL x} = SNoL x.
{ rewrite SNoL_0.
  prove {w + x|w :e Empty} :\/: {0 + w|w :e SNoL x} = SNoL x.
  rewrite Repl_Empty (fun w => w + x).
  prove Empty :\/: {0 + w|w :e SNoL x} = SNoL x.
  rewrite binunion_idl.
  prove {0 + w|w :e SNoL x} = SNoL x.
  apply set_ext.
  - let u. assume Hu: u :e {0 + w|w :e SNoL x}.
    apply ReplE_impred (SNoL x) (fun w => 0 + w) u Hu.
    let w. assume Hw: w :e SNoL x.
    assume H1: u = 0 + w.
    prove u :e SNoL x.
    rewrite H1.
    prove 0 + w :e SNoL x.
    rewrite IH w (SNoL_SNoS_ x w Hw).
    prove w :e SNoL x.
    exact Hw.
  - let u. assume Hu: u :e SNoL x.
    prove u :e {0 + w|w :e SNoL x}.
    rewrite <- IH u (SNoL_SNoS_ x u Hu).
    prove 0 + u :e {0 + w|w :e SNoL x}.
    exact ReplI (SNoL x) (fun w => 0 + w) u Hu.
}
claim L2: {w + x|w :e SNoR 0} :\/: {0 + w|w :e SNoR x} = SNoR x.
{ rewrite SNoR_0.
  prove {w + x|w :e Empty} :\/: {0 + w|w :e SNoR x} = SNoR x.
  rewrite Repl_Empty (fun w => w + x).
  prove Empty :\/: {0 + w|w :e SNoR x} = SNoR x.
  rewrite binunion_idl.
  prove {0 + w|w :e SNoR x} = SNoR x.
  apply set_ext.
  - let u. assume Hu: u :e {0 + w|w :e SNoR x}.
    apply ReplE_impred (SNoR x) (fun w => 0 + w) u Hu.
    let w. assume Hw: w :e SNoR x.
    assume H1: u = 0 + w.
    prove u :e SNoR x.
    rewrite H1.
    prove 0 + w :e SNoR x.
    rewrite IH w (SNoR_SNoS_ x w Hw).
    prove w :e SNoR x.
    exact Hw.
  - let u. assume Hu: u :e SNoR x.
    prove u :e {0 + w|w :e SNoR x}.
    rewrite <- IH u (SNoR_SNoS_ x u Hu).
    prove 0 + u :e {0 + w|w :e SNoR x}.
    exact ReplI (SNoR x) (fun w => 0 + w) u Hu.
}
rewrite L1.
rewrite L2.
prove SNoCut (SNoL x) (SNoR x) = x.
symmetry.
exact SNo_eta x Hx.
Qed.

Theorem add_SNo_0R : forall x, SNo x -> x + 0 = x.
let x. assume Hx: SNo x.
rewrite add_SNo_com x 0 Hx SNo_0.
exact add_SNo_0L x Hx.
Qed.

Theorem add_SNo_minus_SNo_linv : forall x, SNo x -> -x+x = 0.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), -w+w = 0.
prove -x+x = 0.
claim Lmx: SNo (-x).
{ exact SNo_minus_SNo x Hx. }
set L1 := {w + x|w :e SNoL (- x)}.
set L2 := {- x + w|w :e SNoL x}.
set R1 := {z + x|z :e SNoR (- x)}.
set R2 := {- x + z|z :e SNoR x}.
set L := L1 :\/: L2.
set R := R1 :\/: R2.
rewrite add_SNo_eq (- x) Lmx x Hx.
prove SNoCut L R = 0.
claim LLR: SNoCutP L R.
{ exact add_SNo_SNoCutP (- x) x Lmx Hx. }
claim LNLR: SNo (SNoCut L R).
{ exact SNoCutP_SNo_SNoCut L R LLR. }
claim Lfst: SNoLev (SNoCut L R) c= SNoLev 0
         /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) 0.
{ apply SNoCutP_SNoCut_fst L R LLR 0 SNo_0.
  - prove forall w :e L, w < 0.
    let w. assume Hw: w :e L.
    apply binunionE L1 L2 w Hw.
    + assume Hw: w :e {w + x|w :e SNoL (- x)}.
      apply ReplE_impred (SNoL (- x)) (fun z => z + x) w Hw.
      let u.
      assume Hu: u :e SNoL (- x).
      assume Hwu: w = u + x.
      apply SNoL_E (- x) Lmx u Hu.
      assume Hu1: SNo u.
      assume Hu2: SNoLev u :e SNoLev (- x).
      assume Hu3: u < - x.
      claim Lmu: SNo (-u).
      { apply SNo_minus_SNo. exact Hu1. }
      claim Lmuu: -u + u = 0.
      { apply IH. prove u :e SNoS_ (SNoLev x).
        apply SNoS_I2 u x Hu1 Hx.
        prove SNoLev u :e SNoLev x.
        rewrite <- minus_SNo_Lev x Hx.
        prove SNoLev u :e SNoLev (-x).
        exact Hu2.
      }
      claim Lxmu: x < -u.
      { rewrite <- minus_SNo_invol x Hx.
        prove - - x < -u.
        apply minus_SNo_Lt_contra u (- x) Hu1 Lmx.
        prove u < - x.
        exact Hu3.
      }
      prove w < 0.
      rewrite Hwu.
      prove u + x < 0.
      rewrite add_SNo_com u x Hu1 Hx.
      prove x + u < 0.
      rewrite <- Lmuu.
      prove x + u < -u + u.
      apply add_SNo_Lt1 x u (-u) Hx Hu1 Lmu.
      prove x < -u.
      exact Lxmu.
    + assume Hw: w :e {- x + w|w :e SNoL x}.
      apply ReplE_impred (SNoL x) (fun z => - x + z) w Hw.
      let u.
      assume Hu: u :e SNoL x.
      assume Hwu: w = - x + u.
      apply SNoL_E x Hx u Hu.
      assume Hu1: SNo u.
      assume Hu2: SNoLev u :e SNoLev x.
      assume Hu3: u < x.
      claim Lmu: SNo (-u).
      { apply SNo_minus_SNo. exact Hu1. }
      claim Lmuu: -u + u = 0.
      { apply IH. prove u :e SNoS_ (SNoLev x).
        apply SNoS_I2 u x Hu1 Hx.
        prove SNoLev u :e SNoLev x.
        exact Hu2.
      }
      claim Lmxmu: -x < -u.
      { apply minus_SNo_Lt_contra u x Hu1 Hx.
        prove u < x.
        exact Hu3.
      }
      prove w < 0.
      rewrite Hwu.
      prove -x + u < 0.
      rewrite <- Lmuu.
      prove -x+u < -u+u.
      apply add_SNo_Lt1 (-x) u (-u) Lmx Hu1 Lmu.
      prove -x < -u.
      exact Lmxmu.
  - prove forall z :e R, 0 < z.
    let z. assume Hz: z :e R.
    apply binunionE R1 R2 z Hz.
    + assume Hz: z :e {z + x|z :e SNoR (- x)}.
      apply ReplE_impred (SNoR (- x)) (fun z => z + x) z Hz.
      let v.
      assume Hv: v :e SNoR (- x).
      assume Hzv: z = v + x.
      apply SNoR_E (- x) Lmx v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev (- x).
      assume Hv3: - x < v.
      claim Lmv: SNo (-v).
      { apply SNo_minus_SNo. exact Hv1. }
      claim Lmvv: -v + v = 0.
      { apply IH. prove v :e SNoS_ (SNoLev x).
        apply SNoS_I2 v x Hv1 Hx.
        prove SNoLev v :e SNoLev x.
        rewrite <- minus_SNo_Lev x Hx.
        prove SNoLev v :e SNoLev (-x).
        exact Hv2.
      }
      claim Lmvx: -v < x.
      { rewrite <- minus_SNo_invol x Hx.
        prove -v < --x.
        apply minus_SNo_Lt_contra (-x) v Lmx Hv1.
        prove -x < v.
        exact Hv3.
      }
      prove 0 < z.
      rewrite Hzv.
      prove 0 < v + x.
      rewrite add_SNo_com v x Hv1 Hx.
      prove 0 < x+v.
      rewrite <- Lmvv.
      prove -v+v < x+v.
      apply add_SNo_Lt1 (-v) v x Lmv Hv1 Hx.
      prove -v < x.
      exact Lmvx.
    + assume Hz: z :e {- x + z|z :e SNoR x}.
      apply ReplE_impred (SNoR x) (fun z => - x + z) z Hz.
      let v.
      assume Hv: v :e SNoR x.
      assume Hzv: z = - x + v.
      apply SNoR_E x Hx v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev x.
      assume Hv3: x < v.
      claim Lmv: SNo (-v).
      { apply SNo_minus_SNo. exact Hv1. }
      claim Lmvv: -v + v = 0.
      { apply IH. prove v :e SNoS_ (SNoLev x).
        apply SNoS_I2 v x Hv1 Hx.
        prove SNoLev v :e SNoLev x.
        exact Hv2.
      }
      claim Lmvmx: -v < -x.
      { apply minus_SNo_Lt_contra x v Hx Hv1.
        prove x < v.
        exact Hv3.
      }
      prove 0 < z.
      rewrite Hzv.
      prove 0 < -x + v.
      rewrite <- Lmvv.
      prove -v+v < -x+v.
      apply add_SNo_Lt1 (-v) v (-x) Lmv Hv1 Lmx.
      prove -v < -x.
      exact Lmvmx.
}
apply Lfst.
assume H1: SNoLev (SNoCut L R) c= SNoLev 0.
assume H2: SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) 0.
apply SNo_eq (SNoCut L R) 0 LNLR SNo_0.
- prove SNoLev (SNoCut L R) = SNoLev 0.
  apply set_ext.
  + exact H1.
  + rewrite ordinal_SNoLev 0 ordinal_Empty.
    prove 0 c= SNoLev (SNoCut L R).
    apply Subq_Empty.
- prove SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) 0.
  exact H2.
Qed.

Theorem add_SNo_minus_SNo_rinv : forall x, SNo x -> x + -x = 0.
let x. assume Hx: SNo x.
claim Lmx: SNo (-x).
{ exact SNo_minus_SNo x Hx. }
prove x + -x = 0.
rewrite add_SNo_com x (-x) Hx Lmx.
prove -x + x = 0.
exact add_SNo_minus_SNo_linv x Hx.
Qed.

Theorem add_SNo_ordinal_SNoCutP : forall alpha, ordinal alpha -> forall beta, ordinal beta -> SNoCutP ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
set Lo1 := {x + beta | x :e SNoS_ alpha}.
set Lo2 := {alpha + x | x :e SNoS_ beta}.
prove (forall x :e Lo1 :\/: Lo2, SNo x)
   /\ (forall y :e Empty, SNo y)
   /\ (forall x :e Lo1 :\/: Lo2, forall y :e Empty, x < y).
apply and3I.
- let w. assume Hw: w :e Lo1 :\/: Lo2.
  apply binunionE Lo1 Lo2 w Hw.
  + assume H1: w :e Lo1.
    apply ReplE_impred (SNoS_ alpha) (fun x => x + beta) w H1.
    let x. assume Hx: x :e SNoS_ alpha.
    assume H2: w = x + beta.
    apply SNoS_E2 alpha Ha x Hx.
    assume _ _.
    assume Hx2: SNo x.
    assume _.
    prove SNo w.
    rewrite H2.
    prove SNo (x + beta).
    exact SNo_add_SNo x beta Hx2 (ordinal_SNo beta Hb).
  + assume H1: w :e Lo2.
    apply ReplE_impred (SNoS_ beta) (fun x => alpha + x) w H1.
    let x. assume Hx: x :e SNoS_ beta.
    assume H2: w = alpha + x.
    apply SNoS_E2 beta Hb x Hx.
    assume _ _.
    assume Hx2: SNo x.
    assume _.
    prove SNo w.
    rewrite H2.
    prove SNo (alpha + x).
    exact SNo_add_SNo alpha x (ordinal_SNo alpha Ha) Hx2.
- let y. assume Hy: y :e Empty. prove False. exact EmptyE y Hy.
- let x. assume _.
  let y. assume Hy: y :e Empty. prove False. exact EmptyE y Hy.
Qed.

Theorem add_SNo_ordinal_eq : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + beta = SNoCut ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
set Lo1 := {x + beta | x :e SNoS_ alpha}.
set Lo2 := {alpha + x | x :e SNoS_ beta}.
prove alpha + beta = SNoCut (Lo1 :\/: Lo2) Empty.
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim Lb: SNo beta.
{ exact ordinal_SNo beta Hb. }
rewrite add_SNo_eq alpha La beta Lb.
prove SNoCut ({x + beta|x :e SNoL alpha} :\/: {alpha + x|x :e SNoL beta})
             ({x + beta|x :e SNoR alpha} :\/: {alpha + x|x :e SNoR beta})
    = SNoCut (Lo1 :\/: Lo2) Empty.
rewrite ordinal_SNoL alpha Ha.
rewrite ordinal_SNoL beta Hb.
prove SNoCut (Lo1 :\/: Lo2)
             ({x + beta|x :e SNoR alpha} :\/: {alpha + x|x :e SNoR beta})
    = SNoCut (Lo1 :\/: Lo2) Empty.
rewrite ordinal_SNoR alpha Ha.
rewrite ordinal_SNoR beta Hb.
prove SNoCut (Lo1 :\/: Lo2)
             ({x + beta|x :e Empty} :\/: {alpha + x|x :e Empty})
    = SNoCut (Lo1 :\/: Lo2) Empty.
rewrite Repl_Empty.
rewrite Repl_Empty.
prove SNoCut (Lo1 :\/: Lo2) (Empty :\/: Empty)
    = SNoCut (Lo1 :\/: Lo2) Empty.
rewrite binunion_idl.
reflexivity.
Qed.

Theorem add_SNo_ordinal_ordinal : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordinal (alpha + beta).
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim Lb: SNo beta.
{ exact ordinal_SNo beta Hb. }
claim Lab1: SNo (alpha + beta).
{ exact SNo_add_SNo alpha beta La Lb. }
claim Lab2: ordinal (SNoLev (alpha + beta)).
{ exact SNoLev_ordinal (alpha + beta) Lab1. }
prove ordinal (alpha + beta).
apply SNo_max_ordinal (alpha + beta) Lab1.
prove forall y :e SNoS_ (SNoLev (alpha + beta)), y < alpha + beta.
let y. assume Hy: y :e SNoS_ (SNoLev (alpha + beta)).
apply SNoS_E2 (SNoLev (alpha + beta)) Lab2 y Hy.
assume Hy1: SNoLev y :e SNoLev (alpha + beta).
assume Hy2: ordinal (SNoLev y).
assume Hy3: SNo y.
assume Hy4: SNo_ (SNoLev y) y.
set Lo1 := {x + beta | x :e SNoS_ alpha}.
set Lo2 := {alpha + x | x :e SNoS_ beta}.
apply SNoLt_trichotomy_or y (alpha + beta) Hy3 Lab1. assume H1. apply H1.
- assume H1: y < alpha + beta. exact H1.
- assume H1: y = alpha + beta.
  prove False.
  apply In_irref (SNoLev y).
  rewrite H1 at 2. exact Hy1.
- assume H1: alpha + beta < y.
  prove False.
  apply add_SNo_ordinal_SNoCutP alpha Ha beta Hb.
  assume H2. apply H2.
  assume H2: forall x :e Lo1 :\/: Lo2, SNo x.
  assume _ _.
  apply SNoCutP_SNoCut (Lo1 :\/: Lo2) Empty
               (add_SNo_ordinal_SNoCutP alpha Ha beta Hb).
  assume H3. apply H3. assume H3. apply H3.
  assume _.
  assume H3: forall x :e Lo1 :\/: Lo2, x < SNoCut (Lo1 :\/: Lo2) Empty.
  assume _.
  assume H4: forall z, SNo z
            -> (forall x :e Lo1 :\/: Lo2, x < z)
            -> (forall y :e Empty, z < y)
            -> SNoLev (SNoCut (Lo1 :\/: Lo2) Empty) c= SNoLev z
            /\ SNoEq_ (SNoLev (SNoCut (Lo1 :\/: Lo2) Empty)) (SNoCut (Lo1 :\/: Lo2) Empty) z.
  claim L1: SNoLev (alpha + beta) c= SNoLev y
         /\ SNoEq_ (SNoLev (alpha + beta)) (alpha + beta) y.
  { rewrite add_SNo_ordinal_eq alpha Ha beta Hb.
    apply H4 y Hy3.
    - let w. assume Hw: w :e Lo1 :\/: Lo2.
      prove w < y.
      apply SNoLt_tra w (alpha + beta) y (H2 w Hw) Lab1 Hy3.
      + prove w < alpha + beta.
        rewrite add_SNo_ordinal_eq alpha Ha beta Hb.
        exact H3 w Hw.
      + prove alpha + beta < y. exact H1.
    - let w. assume Hw: w :e Empty. prove False. exact EmptyE w Hw.
  }
  apply L1.
  assume H5: SNoLev (alpha + beta) c= SNoLev y.
  assume _.
  apply In_irref (SNoLev y).
  apply H5. exact Hy1.
Qed.

Theorem add_SNo_ordinal_SL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordsucc alpha + beta = ordsucc (alpha + beta).
let alpha. assume Ha: ordinal alpha.
apply ordinal_ind.
let beta. assume Hb: ordinal beta.
assume IH: forall delta :e beta, ordsucc alpha + delta = ordsucc (alpha + delta).
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim Lb: SNo beta.
{ exact ordinal_SNo beta Hb. }
claim Lab: ordinal (alpha + beta).
{ exact add_SNo_ordinal_ordinal alpha Ha beta Hb. }
claim LSa: ordinal (ordsucc alpha).
{ apply ordinal_ordsucc. exact Ha. }
claim LSa2: SNo (ordsucc alpha).
{ apply ordinal_SNo. exact LSa. }
claim LSab: ordinal (ordsucc alpha + beta).
{ exact add_SNo_ordinal_ordinal (ordsucc alpha) LSa beta Hb. }
set Lo1 := {x + beta | x :e SNoS_ (ordsucc alpha)}.
set Lo2 := {ordsucc alpha + x | x :e SNoS_ beta}.
apply SNoCutP_SNoCut (Lo1 :\/: Lo2) Empty (add_SNo_ordinal_SNoCutP (ordsucc alpha) LSa beta Hb).
assume H1. apply H1. assume H1. apply H1.
assume _.
rewrite <- add_SNo_ordinal_eq (ordsucc alpha) LSa beta Hb.
assume H1: forall x :e Lo1 :\/: Lo2 , x < ordsucc alpha + beta.
assume _.
assume H2: forall z, SNo z -> (forall x :e Lo1 :\/: Lo2, x < z) -> (forall y :e Empty, z < y) -> SNoLev (ordsucc alpha + beta) c= SNoLev z /\ SNoEq_ (SNoLev (ordsucc alpha + beta)) (ordsucc alpha + beta) z.
claim L1: alpha + beta :e ordsucc alpha + beta.
{ apply ordinal_SNoLt_In (alpha + beta) (ordsucc alpha + beta) Lab LSab.
  prove alpha + beta < ordsucc alpha + beta.
  apply H1.
  prove alpha + beta :e Lo1 :\/: Lo2.
  apply binunionI1.
  prove alpha + beta :e {x + beta | x :e SNoS_ (ordsucc alpha)}.
  apply ReplI (SNoS_ (ordsucc alpha)) (fun x => x + beta) alpha.
  prove alpha :e SNoS_ (ordsucc alpha).
  apply SNoS_I (ordsucc alpha) LSa alpha alpha (ordsuccI2 alpha).
  prove SNo_ alpha alpha.
  exact ordinal_SNo_ alpha Ha.
}
apply ordinal_ordsucc_In_eq (ordsucc alpha + beta) (alpha + beta) LSab L1.
- assume H3: ordsucc (alpha + beta) :e ordsucc alpha + beta.
  prove False.
  set z := ordsucc (alpha + beta).
  claim Lz: ordinal z.
  { exact ordinal_ordsucc (alpha + beta) Lab. }
  claim Lz1: TransSet z.
  { exact ordinal_TransSet z Lz. }
  claim Lz2: SNo z.
  { apply ordinal_SNo. exact Lz. }
  claim L2: SNoLev (ordsucc alpha + beta) c= SNoLev z
         /\ SNoEq_ (SNoLev (ordsucc alpha + beta)) (ordsucc alpha + beta) z.
  { apply H2 z (ordinal_SNo z Lz).
    - let w. assume Hw: w :e Lo1 :\/: Lo2.
      prove w < z.
      apply binunionE Lo1 Lo2 w Hw.
      + assume H4: w :e Lo1.
        apply ReplE_impred (SNoS_ (ordsucc alpha)) (fun x => x + beta) w H4.
        let x.
        assume Hx: x :e SNoS_ (ordsucc alpha).
        assume Hwx: w = x + beta.
        apply SNoS_E2 (ordsucc alpha) LSa x Hx.
        assume Hx1: SNoLev x :e ordsucc alpha.
        assume Hx2: ordinal (SNoLev x).
        assume Hx3: SNo x.
        assume Hx4: SNo_ (SNoLev x) x.
        prove w < z.
        rewrite Hwx.
        prove x + beta < z.
        claim LLxb: ordinal (SNoLev x + beta).
        { exact add_SNo_ordinal_ordinal (SNoLev x) Hx2 beta Hb. }
        claim LLxb2: SNo (SNoLev x + beta).
        { apply ordinal_SNo. exact LLxb. }
        apply SNoLeLt_tra (x + beta) (SNoLev x + beta) z
                          (SNo_add_SNo x beta Hx3 Lb)
                          LLxb2 Lz2.
        * prove x + beta <= SNoLev x + beta.
          apply add_SNo_Le1 x beta (SNoLev x) Hx3 Lb (ordinal_SNo (SNoLev x) Hx2).
          prove x <= SNoLev x.
          exact ordinal_SNoLev_max_2 (SNoLev x) Hx2 x Hx3 (ordsuccI2 (SNoLev x)).
        * { prove SNoLev x + beta < z.
            apply SNoLeLt_tra (SNoLev x + beta) (alpha + beta) z
                              LLxb2 (ordinal_SNo (alpha + beta) Lab) Lz2.
            - prove SNoLev x + beta <= alpha + beta.
              apply add_SNo_Le1 (SNoLev x) beta alpha (ordinal_SNo (SNoLev x) Hx2) Lb La.
              prove SNoLev x <= alpha.
              apply ordinal_Subq_SNoLe (SNoLev x) alpha Hx2 Ha.
              prove SNoLev x c= alpha.
              apply ordsuccE alpha (SNoLev x) Hx1.
              + assume H5: SNoLev x :e alpha. apply Ha. assume Ha1 _. exact Ha1 (SNoLev x) H5.
              + assume H5: SNoLev x = alpha. rewrite H5. apply Subq_ref.
            - prove alpha + beta < z.
              exact ordinal_In_SNoLt z Lz (alpha + beta) (ordsuccI2 (alpha + beta)).
          }
      + assume H4: w :e Lo2.
        apply ReplE_impred (SNoS_ beta) (fun x => ordsucc alpha + x) w H4.
        let x.
        assume Hx: x :e SNoS_ beta.
        assume Hwx: w = ordsucc alpha + x.
        apply SNoS_E2 beta Hb x Hx.
        assume Hx1: SNoLev x :e beta.
        assume Hx2: ordinal (SNoLev x).
        assume Hx3: SNo x.
        assume Hx4: SNo_ (SNoLev x) x.
        prove w < z.
        rewrite Hwx.
        prove ordsucc alpha + x < z.
        claim IHLx: ordsucc alpha + SNoLev x = ordsucc (alpha + SNoLev x).
        { exact IH (SNoLev x) Hx1. }
        claim LSax: SNo (ordsucc alpha + x).
        { exact SNo_add_SNo (ordsucc alpha) x LSa2 Hx3. }
        claim LaLx: ordinal (alpha + SNoLev x).
        { exact add_SNo_ordinal_ordinal alpha Ha (SNoLev x) Hx2. }
        claim LSaLx: ordinal (ordsucc alpha + SNoLev x).
        { exact add_SNo_ordinal_ordinal (ordsucc alpha) LSa (SNoLev x) Hx2. }
        claim LSaLx2: SNo (ordsucc alpha + SNoLev x).
        { apply ordinal_SNo. exact LSaLx. }
        apply SNoLeLt_tra (ordsucc alpha + x) (ordsucc alpha + SNoLev x) z
                          LSax LSaLx2 Lz2.
        * prove ordsucc alpha + x <= ordsucc alpha + SNoLev x.
          apply add_SNo_Le2 (ordsucc alpha) x (SNoLev x)
                            LSa2 Hx3 (ordinal_SNo (SNoLev x) Hx2).
          prove x <= SNoLev x.
          exact ordinal_SNoLev_max_2 (SNoLev x) Hx2 x Hx3 (ordsuccI2 (SNoLev x)).
        * prove ordsucc alpha + SNoLev x < z.
          rewrite IHLx.
          prove ordsucc (alpha + SNoLev x) < ordsucc (alpha + beta).
          apply ordinal_In_SNoLt z Lz (ordsucc (alpha + SNoLev x)).
          prove ordsucc (alpha + SNoLev x) :e ordsucc (alpha + beta).
          apply ordinal_ordsucc_In (alpha + beta) Lab.
          prove alpha + SNoLev x :e alpha + beta.
          apply ordinal_SNoLt_In (alpha + SNoLev x) (alpha + beta) LaLx Lab.
          prove alpha + SNoLev x < alpha + beta.
          apply add_SNo_Lt2 alpha (SNoLev x) beta La (ordinal_SNo (SNoLev x) Hx2) Lb.
          prove SNoLev x < beta.
          apply ordinal_In_SNoLt beta Hb (SNoLev x).
          prove SNoLev x :e beta.
          exact Hx1.
    - let w. assume Hw: w :e Empty. prove False. exact EmptyE w Hw.
  }
  apply L2.
  rewrite ordinal_SNoLev (ordsucc alpha + beta) LSab.
  rewrite ordinal_SNoLev z Lz.
  assume H4: ordsucc alpha + beta c= z.
  assume _.
  apply In_irref z.
  apply H4.
  prove z :e ordsucc alpha + beta.
  exact H3.
- assume H3: ordsucc alpha + beta = ordsucc (alpha + beta).
  exact H3.
Qed.

Theorem add_SNo_ordinal_SR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + ordsucc beta = ordsucc (alpha + beta).
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim Lb: SNo beta.
{ exact ordinal_SNo beta Hb. }
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim LSb: ordinal (ordsucc beta).
{ apply ordinal_ordsucc. exact Hb. }
claim LSb2: SNo (ordsucc beta).
{ exact ordinal_SNo (ordsucc beta) LSb. }
rewrite add_SNo_com alpha (ordsucc beta) La LSb2.
prove ordsucc beta + alpha = ordsucc (alpha + beta).
rewrite add_SNo_ordinal_SL beta Hb alpha Ha.
prove ordsucc (beta + alpha) = ordsucc (alpha + beta).
rewrite add_SNo_com beta alpha Lb La.
reflexivity.
Qed.

Theorem add_SNo_ordinal_InL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e alpha, gamma + beta :e alpha + beta.
let alpha. assume Ha. let beta. assume Hb. let gamma. assume Hc.
claim Lc: ordinal gamma.
{ exact ordinal_Hered alpha Ha gamma Hc. }
claim Lab: ordinal (alpha + beta).
{ apply add_SNo_ordinal_ordinal.
  - exact Ha.
  - exact Hb.
}
claim Lcb: ordinal (gamma + beta).
{ apply add_SNo_ordinal_ordinal.
  - exact Lc.
  - exact Hb.
}
prove gamma + beta :e alpha + beta.
apply ordinal_SNoLt_In (gamma + beta) (alpha + beta) Lcb Lab.
prove gamma + beta < alpha + beta.
apply add_SNo_Lt1.
- apply ordinal_SNo. exact Lc.
- apply ordinal_SNo. exact Hb.
- apply ordinal_SNo. exact Ha.
- exact ordinal_In_SNoLt alpha Ha gamma Hc.
Qed.

Theorem add_SNo_ordinal_InR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e beta, alpha + gamma :e alpha + beta.
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
let gamma. assume Hc: gamma :e beta.
claim La: SNo alpha.
{ exact ordinal_SNo alpha Ha. }
claim Lb: SNo beta.
{ exact ordinal_SNo beta Hb. }
claim Lc: ordinal gamma.
{ exact ordinal_Hered beta Hb gamma Hc. }
claim Lc2: SNo gamma.
{ exact ordinal_SNo gamma Lc. }
rewrite add_SNo_com alpha gamma La Lc2.
rewrite add_SNo_com alpha beta La Lb.
exact add_SNo_ordinal_InL beta Hb alpha Ha gamma Hc.
Qed.

Theorem add_nat_add_SNo : forall n m :e omega, add_nat n m = n + m.
let n. assume Hn: n :e omega.
claim Ln1: nat_p n.
{ exact omega_nat_p n Hn. }
claim Ln2: ordinal n.
{ exact nat_p_ordinal n Ln1. }
claim Ln3: SNo n.
{ exact ordinal_SNo n Ln2. }
claim L1: forall m, nat_p m -> add_nat n m = n + m.
{ apply nat_ind.
  - prove add_nat n 0 = n + 0.
    rewrite add_SNo_0R n Ln3.
    prove add_nat n 0 = n.
    exact add_nat_0R n.
  - let m.
    assume Hm: nat_p m.
    assume IH: add_nat n m = n + m.
    prove add_nat n (ordsucc m) = n + (ordsucc m).
    rewrite add_SNo_ordinal_SR n Ln2 m (nat_p_ordinal m Hm).
    prove add_nat n (ordsucc m) = ordsucc (n + m).
    rewrite <- IH.
    prove add_nat n (ordsucc m) = ordsucc (add_nat n m).
    exact add_nat_SR n m Hm.
}
let m. assume Hm: m :e omega.
prove add_nat n m = n + m.
exact L1 m (omega_nat_p m Hm).
Qed.

Theorem add_SNo_In_omega : forall n m :e omega, n + m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- add_nat_add_SNo n Hn m Hm.
apply nat_p_omega.
apply add_nat_p.
- apply omega_nat_p. exact Hn.
- apply omega_nat_p. exact Hm.
Qed.

Theorem add_SNo_1_1_2 : 1 + 1 = 2.
rewrite <- add_nat_add_SNo 1 (nat_p_omega 1 nat_1) 1 (nat_p_omega 1 nat_1).
exact add_nat_1_1_2.
Qed.

Theorem add_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x + y), (exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x + y) -> u < x + y -> (exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v).
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x + y) -> z < x + y -> (exists v :e SNoL x, z <= v + y) \/ (exists v :e SNoL y, z <= x + v).
  assume Hu2: SNoLev u :e SNoLev (x + y).
  assume Hu3: u < x + y.
  apply dneg.
  assume HNC: ~((exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v)).
  apply SNoLt_irref u.
  prove u < u.
  apply SNoLtLe_tra u (x + y) u Hu1 Lxy Hu1 Hu3.
  prove x + y <= u.
  set Lxy1 := {w + y|w :e SNoL x}.
  set Lxy2 := {x + w|w :e SNoL y}.
  set Rxy1 := {z + y|z :e SNoR x}.
  set Rxy2 := {x + z|z :e SNoR y}.
  rewrite add_SNo_eq x Hx y Hy.
  prove SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) <= u.
  rewrite SNo_eta u Hu1.
  prove SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) <= SNoCut (SNoL u) (SNoR u).
  apply SNoCut_Le (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) (SNoL u) (SNoR u).
  - exact add_SNo_SNoCutP x y Hx Hy.
  - exact SNoCutP_SNoL_SNoR u Hu1.
  - rewrite <- SNo_eta u Hu1.
    prove forall w :e Lxy1 :\/: Lxy2, w < u.
    let w. assume Hw: w :e Lxy1 :\/: Lxy2.
    apply binunionE Lxy1 Lxy2 w Hw.
    + assume Hw2: w :e Lxy1.
      prove w < u.
      apply ReplE_impred (SNoL x) (fun w => w + y) w Hw2.
      let v.
      assume Hv: v :e SNoL x.
      assume Hwv: w = v + y.
      apply SNoL_E x Hx v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev x.
      assume Hv3: v < x.
      rewrite Hwv.
      prove v + y < u.
      claim Lvy: SNo (v + y).
      { exact SNo_add_SNo v y Hv1 Hy. }
      apply SNoLtLe_or (v+y) u Lvy Hu1.
      * assume H1: v + y < u. exact H1.
      * { assume H1: u <= v+y.
          prove False.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - prove v :e SNoL x. exact Hv.
          - prove u <= v + y. exact H1.
        }
    + assume Hw2: w :e Lxy2.
      prove w < u.
      apply ReplE_impred (SNoL y) (fun w => x + w) w Hw2.
      let v.
      assume Hv: v :e SNoL y.
      assume Hwv: w = x + v.
      apply SNoL_E y Hy v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev y.
      assume Hv3: v < y.
      rewrite Hwv.
      prove x + v < u.
      claim Lxv: SNo (x + v).
      { exact SNo_add_SNo x v Hx Hv1. }
      apply SNoLtLe_or (x+v) u Lxv Hu1.
      * assume H1: x + v < u. exact H1.
      * { assume H1: u <= x+v.
          prove False.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - prove v :e SNoL y. exact Hv.
          - prove u <= x + v. exact H1.
        }
  - rewrite <- add_SNo_eq x Hx y Hy.
    prove forall z :e SNoR u, x + y < z.
    let z. assume Hz: z :e SNoR u.
    apply SNoR_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: u < z.
    apply SNoLt_trichotomy_or (x + y) z Lxy Hz1.
    assume H1. apply H1.
    + assume H1: x + y < z. exact H1.
    + assume H1: x + y = z.
      prove False.
      apply In_no2cycle (SNoLev z) (SNoLev u) Hz2.
      prove SNoLev u :e SNoLev z.
      rewrite <- H1.
      exact Hu2.
    + assume H1: z < x + y.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { exact SNoR_SNoS_ u z Hz. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { apply SNoLev_ordinal (x+y) Lxy. assume Hxy1 _.
        exact Hxy1 (SNoLev u) Hu2 (SNoLev z) Hz2.
      }
      apply IH z Lz1 Lz2 H1.
      * { assume H2: exists v :e SNoL x, z <= v + y.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e SNoL x.
          assume H3: z <= v + y.
          apply SNoL_E x Hx v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev x.
          assume Hv3: v < x.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - exact Hv.
          - prove u <= v + y.
            apply SNoLe_tra u z (v + y) Hu1 Hz1 (SNo_add_SNo v y Hv1 Hy).
            + prove u <= z. apply SNoLtLe. exact Hz3.
            + prove z <= v + y. exact H3.
        }
      * { assume H2: exists v :e SNoL y, z <= x + v.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e SNoL y.
          assume H3: z <= x + v.
          apply SNoL_E y Hy v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev y.
          assume Hv3: v < y.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - exact Hv.
          - prove u <= x + v.
            apply SNoLe_tra u z (x + v) Hu1 Hz1 (SNo_add_SNo x v Hx Hv1).
            + prove u <= z. apply SNoLtLe. exact Hz3.
            + prove z <= x + v. exact H3.
        }
}
let u.
assume Hu: u :e SNoL (x+y).
apply SNoL_E (x+y) Lxy u Hu.
assume Hu1: SNo u.
assume Hu2: SNoLev u :e SNoLev (x + y).
assume Hu3: u < x + y.
exact LI u Hu1 Hu2 Hu3.
Qed.

Theorem add_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x + y), (exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x + y) -> x + y < u -> (exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u).
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x + y) -> x + y < z -> (exists v :e SNoR x, v + y <= z) \/ (exists v :e SNoR y, x + v <= z).
  assume Hu2: SNoLev u :e SNoLev (x + y).
  assume Hu3: x + y < u.
  apply dneg.
  assume HNC: ~((exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u)).
  apply SNoLt_irref u.
  prove u < u.
  apply (fun H: u <= x+y => SNoLeLt_tra u (x + y) u Hu1 Lxy Hu1 H Hu3).
  prove u <= x + y.
  set Lxy1 := {w + y|w :e SNoL x}.
  set Lxy2 := {x + w|w :e SNoL y}.
  set Rxy1 := {z + y|z :e SNoR x}.
  set Rxy2 := {x + z|z :e SNoR y}.
  rewrite add_SNo_eq x Hx y Hy.
  prove u <= SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  rewrite SNo_eta u Hu1.
  prove SNoCut (SNoL u) (SNoR u) <= SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  apply SNoCut_Le (SNoL u) (SNoR u) (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  - exact SNoCutP_SNoL_SNoR u Hu1.
  - exact add_SNo_SNoCutP x y Hx Hy.
  - rewrite <- add_SNo_eq x Hx y Hy.
    prove forall z :e SNoL u, z < x + y.
    let z. assume Hz: z :e SNoL u.
    apply SNoL_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: z < u.
    apply SNoLt_trichotomy_or z (x + y) Hz1 Lxy.
    assume H1. apply H1.
    + assume H1: z < x + y. exact H1.
    + assume H1: z = x + y.
      prove False.
      apply In_no2cycle (SNoLev z) (SNoLev u) Hz2.
      prove SNoLev u :e SNoLev z.
      rewrite H1.
      exact Hu2.
    + assume H1: x + y < z.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { exact SNoL_SNoS_ u z Hz. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { apply SNoLev_ordinal (x+y) Lxy. assume Hxy1 _.
        exact Hxy1 (SNoLev u) Hu2 (SNoLev z) Hz2.
      }
      apply IH z Lz1 Lz2 H1.
      * { assume H2: exists v :e SNoR x, v + y <= z.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e SNoR x.
          assume H3: v + y <= z.
          apply SNoR_E x Hx v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev x.
          assume Hv3: x < v.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - exact Hv.
          - prove v + y <= u.
            apply SNoLe_tra (v + y) z u (SNo_add_SNo v y Hv1 Hy) Hz1 Hu1.
            + prove v + y <= z. exact H3.
            + prove z <= u. apply SNoLtLe. exact Hz3.
        }
      * { assume H2: exists v :e SNoR y, x + v <= z.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e SNoR y.
          assume H3: x + v <= z.
          apply SNoR_E y Hy v Hv.
          assume Hv1: SNo v.
          assume Hv2: SNoLev v :e SNoLev y.
          assume Hv3: y < v.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - exact Hv.
          - prove x + v <= u.
            apply SNoLe_tra (x + v) z u (SNo_add_SNo x v Hx Hv1) Hz1 Hu1.
            + prove x + v <= z. exact H3.
            + prove z <= u. apply SNoLtLe. exact Hz3.
        }
  - rewrite <- SNo_eta u Hu1.
    prove forall w :e Rxy1 :\/: Rxy2, u < w.
    let w. assume Hw: w :e Rxy1 :\/: Rxy2.
    apply binunionE Rxy1 Rxy2 w Hw.
    + assume Hw2: w :e Rxy1.
      prove u < w.
      apply ReplE_impred (SNoR x) (fun w => w + y) w Hw2.
      let v.
      assume Hv: v :e SNoR x.
      assume Hwv: w = v + y.
      apply SNoR_E x Hx v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev x.
      assume Hv3: x < v.
      rewrite Hwv.
      prove u < v + y.
      claim Lvy: SNo (v + y).
      { exact SNo_add_SNo v y Hv1 Hy. }
      apply SNoLtLe_or u (v+y) Hu1 Lvy.
      * assume H1: u < v + y. exact H1.
      * { assume H1: v+y <= u.
          prove False.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - prove v :e SNoR x. exact Hv.
          - prove v + y <= u. exact H1.
        }
    + assume Hw2: w :e Rxy2.
      prove u < w.
      apply ReplE_impred (SNoR y) (fun w => x + w) w Hw2.
      let v.
      assume Hv: v :e SNoR y.
      assume Hwv: w = x + v.
      apply SNoR_E y Hy v Hv.
      assume Hv1: SNo v.
      assume Hv2: SNoLev v :e SNoLev y.
      assume Hv3: y < v.
      rewrite Hwv.
      prove u < x + v.
      claim Lxv: SNo (x + v).
      { exact SNo_add_SNo x v Hx Hv1. }
      apply SNoLtLe_or u (x+v) Hu1 Lxv.
      * assume H1: u < x + v. exact H1.
      * { assume H1: x+v <= u.
          prove False.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - prove v :e SNoR y. exact Hv.
          - prove x + v <= u. exact H1.
        }
}
let u.
assume Hu: u :e SNoR (x+y).
apply SNoR_E (x+y) Lxy u Hu.
assume Hu1: SNo u.
assume Hu2: SNoLev u :e SNoLev (x + y).
assume Hu3: x + y < u.
exact LI u Hu1 Hu2 Hu3.
Qed.

Theorem add_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z -> x + (y + z) = (x + y) + z.
set P : set -> set -> set -> prop := fun x y z => x + (y + z) = (x + y) + z.
apply SNoLev_ind3.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume IH1: forall u :e SNoS_ (SNoLev x), P u y z.
assume IH2: forall v :e SNoS_ (SNoLev y), P x v z.
assume IH3: forall w :e SNoS_ (SNoLev z), P x y w.
assume IH4: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), P u v z.
assume IH5: forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), P u y w.
assume IH6: forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P x v w.
assume IH7: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P u v w.
prove x + (y + z) = (x + y) + z.
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim Lyz: SNo (y + z).
{ exact SNo_add_SNo y z Hy Hz. }
set Lxyz1 := {w + (y + z)|w :e SNoL x}.
set Lxyz2 := {x + w|w :e SNoL (y + z)}.
set Rxyz1 := {w + (y + z)|w :e SNoR x}.
set Rxyz2 := {x + w|w :e SNoR (y + z)}.
set Lxyz3 := {w + z|w :e SNoL (x + y)}.
set Lxyz4 := {(x + y) + w|w :e SNoL z}.
set Rxyz3 := {w + z|w :e SNoR (x + y)}.
set Rxyz4 := {(x + y) + w|w :e SNoR z}.
rewrite add_SNo_eq x Hx (y+z) Lyz.
rewrite add_SNo_eq (x+y) Lxy z Hz.
prove (SNoCut (Lxyz1 :\/: Lxyz2) (Rxyz1 :\/: Rxyz2))
    = (SNoCut (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4)).
claim Lxyz12: SNoCutP (Lxyz1 :\/: Lxyz2) (Rxyz1 :\/: Rxyz2).
{ exact add_SNo_SNoCutP x (y+z) Hx Lyz. }
claim Lxyz34: SNoCutP (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4).
{ exact add_SNo_SNoCutP (x+y) z Lxy Hz. }
apply SNoCut_ext.
- exact Lxyz12.
- exact Lxyz34.
- prove forall w :e Lxyz1 :\/: Lxyz2, w < SNoCut (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4).
  rewrite <- add_SNo_eq (x+y) Lxy z Hz.
  prove forall w :e Lxyz1 :\/: Lxyz2, w < (x + y) + z.
  let w. assume Hw: w :e Lxyz1 :\/: Lxyz2.
  apply binunionE Lxyz1 Lxyz2 w Hw.
  + assume Hw: w :e Lxyz1.
    apply ReplE_impred (SNoL x) (fun w => w+(y+z)) w Hw.
    let u.
    assume Hu: u :e SNoL x.
    assume Hwu: w = u+(y+z).
    apply SNoL_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: u < x.
    prove w < (x + y) + z.
    rewrite Hwu.
    prove u + (y + z) < (x + y) + z.
    claim IH1u: u+(y+z) = (u+y)+z.
    { exact IH1 u (SNoL_SNoS_ x u Hu). }
    rewrite IH1u.
    prove (u + y) + z < (x + y) + z.
    apply add_SNo_Lt1 (u + y) z (x + y) (SNo_add_SNo u y Hu1 Hy) Hz Lxy.
    prove u + y < x + y.
    apply add_SNo_Lt1 u y x Hu1 Hy Hx.
    prove u < x.
    exact Hu3.
  + assume Hw: w :e Lxyz2.
    apply ReplE_impred (SNoL (y+z)) (fun w => x+w) w Hw.
    let u.
    assume Hu: u :e SNoL (y+z).
    assume Hwu: w = x+u.
    apply SNoL_E (y+z) Lyz u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev (y+z).
    assume Hu3: u < y+z.
    rewrite Hwu.
    prove x + u < (x + y) + z.
    apply add_SNo_SNoL_interpolate y z Hy Hz u Hu.
    * { assume H1: exists v :e SNoL y, u <= v + z.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoL y.
        assume H2: u <= v + z.
        apply SNoL_E y Hy v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev y.
        assume Hv3: v < y.
        claim IH2v: x + (v + z) = (x + v) + z.
        { exact IH2 v (SNoL_SNoS_ y v Hv). }
        prove x + u < (x + y) + z.
        apply SNoLeLt_tra (x + u) (x + (v + z)) ((x + y) + z)
                          (SNo_add_SNo x u Hx Hu1)
                          (SNo_add_SNo x (v+z) Hx (SNo_add_SNo v z Hv1 Hz))
                          (SNo_add_SNo (x+y) z Lxy Hz).
        - prove x + u <= x + (v + z).
          apply add_SNo_Le2 x u (v + z) Hx Hu1 (SNo_add_SNo v z Hv1 Hz).
          prove u <= v + z.
          exact H2.
        - prove x + (v + z) < (x + y) + z.
          rewrite IH2v.
          prove (x + v) + z < (x + y) + z.
          apply add_SNo_Lt1 (x+v) z (x+y) (SNo_add_SNo x v Hx Hv1) Hz Lxy.
          prove x + v < x + y.
          apply add_SNo_Lt2 x v y Hx Hv1 Hy.
          prove v < y.
          exact Hv3.
      }
    * { assume H1: exists v :e SNoL z, u <= y + v.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoL z.
        assume H2: u <= y + v.
        apply SNoL_E z Hz v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev z.
        assume Hv3: v < z.
        claim IH3v: x + (y + v) = (x + y) + v.
        { exact IH3 v (SNoL_SNoS_ z v Hv). }
        prove x + u < (x + y) + z.
        apply SNoLeLt_tra (x + u) (x + (y + v)) ((x + y) + z)
                          (SNo_add_SNo x u Hx Hu1)
                          (SNo_add_SNo x (y+v) Hx (SNo_add_SNo y v Hy Hv1))
                          (SNo_add_SNo (x+y) z Lxy Hz).
        - prove x + u <= x + (y + v).
          apply add_SNo_Le2 x u (y + v) Hx Hu1 (SNo_add_SNo y v Hy Hv1).
          prove u <= y + v.
          exact H2.
        - prove x + (y + v) < (x + y) + z.
          rewrite IH3v.
          prove (x + y) + v < (x + y) + z.
          apply add_SNo_Lt2 (x+y) v z Lxy Hv1 Hz.
          prove v < z.
          exact Hv3.
      }
- prove forall v :e Rxyz1 :\/: Rxyz2, SNoCut (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4) < v.
  rewrite <- add_SNo_eq (x+y) Lxy z Hz.
  prove forall v :e Rxyz1 :\/: Rxyz2, (x + y) + z < v.
  let v. assume Hv: v :e Rxyz1 :\/: Rxyz2.
  apply binunionE Rxyz1 Rxyz2 v Hv.
  + assume Hv: v :e Rxyz1.
    apply ReplE_impred (SNoR x) (fun w => w+(y+z)) v Hv.
    let u.
    assume Hu: u :e SNoR x.
    assume Hvu: v = u+(y+z).
    apply SNoR_E x Hx u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev x.
    assume Hu3: x < u.
    prove (x + y) + z < v.
    rewrite Hvu.
    prove (x + y) + z < u + (y + z).
    claim IH1u: u+(y+z) = (u+y)+z.
    { exact IH1 u (SNoR_SNoS_ x u Hu). }
    rewrite IH1u.
    prove (x + y) + z < (u + y) + z.
    apply add_SNo_Lt1 (x + y) z (u + y) Lxy Hz (SNo_add_SNo u y Hu1 Hy).
    prove x + y < u + y.
    apply add_SNo_Lt1 x y u Hx Hy Hu1.
    prove x < u.
    exact Hu3.
  + assume Hv: v :e Rxyz2.
    apply ReplE_impred (SNoR (y+z)) (fun w => x+w) v Hv.
    let u.
    assume Hu: u :e SNoR (y+z).
    assume Hvu: v = x+u.
    apply SNoR_E (y+z) Lyz u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev (y+z).
    assume Hu3: y+z < u.
    rewrite Hvu.
    prove (x + y) + z < x + u.
    apply add_SNo_SNoR_interpolate y z Hy Hz u Hu.
    * { assume H1: exists v :e SNoR y, v + z <= u.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoR y.
        assume H2: v + z <= u.
        apply SNoR_E y Hy v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev y.
        assume Hv3: y < v.
        claim IH2v: x + (v + z) = (x + v) + z.
        { exact IH2 v (SNoR_SNoS_ y v Hv). }
        prove (x + y) + z < x + u.
        apply SNoLtLe_tra ((x + y) + z) (x + (v + z)) (x + u)
                          (SNo_add_SNo (x+y) z Lxy Hz)
                          (SNo_add_SNo x (v+z) Hx (SNo_add_SNo v z Hv1 Hz))
                          (SNo_add_SNo x u Hx Hu1).
        - prove (x + y) + z < x + (v + z).
          rewrite IH2v.
          prove (x + y) + z < (x + v) + z.
          apply add_SNo_Lt1 (x+y) z (x+v) Lxy Hz (SNo_add_SNo x v Hx Hv1).
          prove x + y < x + v.
          apply add_SNo_Lt2 x y v Hx Hy Hv1.
          prove y < v.
          exact Hv3.
        - prove x + (v + z) <= x + u.
          apply add_SNo_Le2 x (v + z) u Hx (SNo_add_SNo v z Hv1 Hz) Hu1.
          prove v + z <= u.
          exact H2.
      }
    * { assume H1: exists v :e SNoR z, y + v <= u.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoR z.
        assume H2: y + v <= u.
        apply SNoR_E z Hz v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev z.
        assume Hv3: z < v.
        claim IH3v: x + (y + v) = (x + y) + v.
        { exact IH3 v (SNoR_SNoS_ z v Hv). }
        prove (x + y) + z < x + u.
        apply SNoLtLe_tra ((x + y) + z) (x + (y + v)) (x + u)
                          (SNo_add_SNo (x+y) z Lxy Hz)
                          (SNo_add_SNo x (y+v) Hx (SNo_add_SNo y v Hy Hv1))
                          (SNo_add_SNo x u Hx Hu1).
        - prove (x + y) + z < x + (y + v).
          rewrite IH3v.
          prove (x + y) + z < (x + y) + v.
          apply add_SNo_Lt2 (x+y) z v Lxy Hz Hv1.
          prove z < v.
          exact Hv3.
        - prove x + (y + v) <= x + u.
          apply add_SNo_Le2 x (y + v) u Hx (SNo_add_SNo y v Hy Hv1) Hu1.
          prove y + v <= u.
          exact H2.
      }
- prove forall w :e Lxyz3 :\/: Lxyz4, w < SNoCut (Lxyz1 :\/: Lxyz2) (Rxyz1 :\/: Rxyz2).
  rewrite <- add_SNo_eq x Hx (y+z) Lyz.
  prove forall w :e Lxyz3 :\/: Lxyz4, w < x + (y + z).
  let w. assume Hw: w :e Lxyz3 :\/: Lxyz4.
  apply binunionE Lxyz3 Lxyz4 w Hw.
  + assume Hw: w :e Lxyz3.
    apply ReplE_impred (SNoL (x+y)) (fun w => w+z) w Hw.
    let u.
    assume Hu: u :e SNoL (x+y).
    assume Hwu: w = u+z.
    apply SNoL_E (x+y) Lxy u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev (x+y).
    assume Hu3: u < x+y.
    rewrite Hwu.
    prove u + z < x + (y + z).
    apply add_SNo_SNoL_interpolate x y Hx Hy u Hu.
    * { assume H1: exists v :e SNoL x, u <= v + y.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoL x.
        assume H2: u <= v + y.
        apply SNoL_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: v < x.
        claim IH1v: v + (y + z) = (v + y) + z.
        { exact IH1 v (SNoL_SNoS_ x v Hv). }
        prove u + z < x + (y + z).
        apply SNoLeLt_tra (u + z) ((v + y) + z) (x + (y + z))
                          (SNo_add_SNo u z Hu1 Hz)
                          (SNo_add_SNo (v+y) z (SNo_add_SNo v y Hv1 Hy) Hz)
                          (SNo_add_SNo x (y+z) Hx Lyz).
        - prove u + z <= (v + y) + z.
          apply add_SNo_Le1 u z (v + y) Hu1 Hz (SNo_add_SNo v y Hv1 Hy).
          prove u <= v + y.
          exact H2.
        - prove (v + y) + z < x + (y + z).
          rewrite <- IH1v.
          prove v + (y + z) < x + (y + z).
          apply add_SNo_Lt1 v (y+z) x Hv1 Lyz Hx.
          prove v < x.
          exact Hv3.
      }
    * { assume H1: exists v :e SNoL y, u <= x + v.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoL y.
        assume H2: u <= x + v.
        apply SNoL_E y Hy v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev y.
        assume Hv3: v < y.
        claim IH2v: x + (v + z) = (x + v) + z.
        { exact IH2 v (SNoL_SNoS_ y v Hv). }
        prove u + z < x + (y + z).
        apply SNoLeLt_tra (u + z) ((x + v) + z) (x + (y + z))
                          (SNo_add_SNo u z Hu1 Hz)
                          (SNo_add_SNo (x+v) z (SNo_add_SNo x v Hx Hv1) Hz)
                          (SNo_add_SNo x (y+z) Hx Lyz).
        - prove u + z <= (x + v) + z.
          apply add_SNo_Le1 u z (x + v) Hu1 Hz (SNo_add_SNo x v Hx Hv1).
          prove u <= x + v.
          exact H2.
        - prove (x + v) + z < x + (y + z).
          rewrite <- IH2v.
          prove x + (v + z) < x + (y + z).
          apply add_SNo_Lt2 x (v+z) (y+z) Hx (SNo_add_SNo v z Hv1 Hz) Lyz.
          prove v + z < y + z.
          apply add_SNo_Lt1 v z y Hv1 Hz Hy.
          prove v < y.
          exact Hv3.
      }
  + assume Hw: w :e Lxyz4.
    apply ReplE_impred (SNoL z) (fun w => (x+y)+w) w Hw.
    let u.
    assume Hu: u :e SNoL z.
    assume Hwu: w = (x+y)+u.
    apply SNoL_E z Hz u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev z.
    assume Hu3: u < z.
    prove w < x + (y + z).
    rewrite Hwu.
    prove (x + y) + u < x + (y + z).
    claim IH3u: x + (y + u) = (x + y) + u.
    { exact IH3 u (SNoL_SNoS_ z u Hu). }
    rewrite <- IH3u.
    prove x + (y + u) < x + (y + z).
    apply add_SNo_Lt2 x (y + u) (y + z) Hx (SNo_add_SNo y u Hy Hu1) Lyz.
    prove y + u < y + z.
    apply add_SNo_Lt2 y u z Hy Hu1 Hz.
    prove u < z.
    exact Hu3.
- prove forall v :e Rxyz3 :\/: Rxyz4, SNoCut (Lxyz1 :\/: Lxyz2) (Rxyz1 :\/: Rxyz2) < v.
  rewrite <- add_SNo_eq x Hx (y+z) Lyz.
  prove forall v :e Rxyz3 :\/: Rxyz4, x + (y + z) < v.
  let v. assume Hv: v :e Rxyz3 :\/: Rxyz4.
  apply binunionE Rxyz3 Rxyz4 v Hv.
  + assume Hv: v :e Rxyz3.
    apply ReplE_impred (SNoR (x+y)) (fun w => w+z) v Hv.
    let u.
    assume Hu: u :e SNoR (x+y).
    assume Hvu: v = u+z.
    apply SNoR_E (x+y) Lxy u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev (x+y).
    assume Hu3: x+y < u.
    rewrite Hvu.
    prove x + (y + z) < u + z.
    apply add_SNo_SNoR_interpolate x y Hx Hy u Hu.
    * { assume H1: exists v :e SNoR x, v + y <= u.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoR x.
        assume H2: v + y <= u.
        apply SNoR_E x Hx v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev x.
        assume Hv3: x < v.
        claim IH1v: v + (y + z) = (v + y) + z.
        { exact IH1 v (SNoR_SNoS_ x v Hv). }
        prove x + (y + z) < u + z.
        apply SNoLtLe_tra (x + (y + z)) ((v + y) + z) (u + z)
                          (SNo_add_SNo x (y+z) Hx Lyz)
                          (SNo_add_SNo (v+y) z (SNo_add_SNo v y Hv1 Hy) Hz)
                          (SNo_add_SNo u z Hu1 Hz).
        - prove x + (y + z) < (v + y) + z.
          rewrite <- IH1v.
          prove x + (y + z) < v + (y + z).
          apply add_SNo_Lt1 x (y+z) v Hx Lyz Hv1.
          prove x < v.
          exact Hv3.
        - prove (v + y) + z <= u + z.
          apply add_SNo_Le1 (v + y) z u (SNo_add_SNo v y Hv1 Hy) Hz Hu1.
          prove v + y <= u.
          exact H2.
      }
    * { assume H1: exists v :e SNoR y, x + v <= u.
        apply H1.
        let v. assume H2. apply H2.
        assume Hv: v :e SNoR y.
        assume H2: x + v <= u.
        apply SNoR_E y Hy v Hv.
        assume Hv1: SNo v.
        assume Hv2: SNoLev v :e SNoLev y.
        assume Hv3: y < v.
        claim IH2v: x + (v + z) = (x + v) + z.
        { exact IH2 v (SNoR_SNoS_ y v Hv). }
        prove x + (y + z) < u + z.
        apply SNoLtLe_tra (x + (y + z)) ((x + v) + z) (u + z)
                          (SNo_add_SNo x (y+z) Hx Lyz)
                          (SNo_add_SNo (x+v) z (SNo_add_SNo x v Hx Hv1) Hz)
                          (SNo_add_SNo u z Hu1 Hz).
        - prove x + (y + z) < (x + v) + z.
          rewrite <- IH2v.
          prove x + (y + z) < x + (v + z).
          apply add_SNo_Lt2 x (y+z) (v+z) Hx Lyz (SNo_add_SNo v z Hv1 Hz).
          prove y + z < v + z.
          apply add_SNo_Lt1 y z v Hy Hz Hv1.
          prove y < v.
          exact Hv3.
        - prove (x + v) + z <= u + z.
          apply add_SNo_Le1 (x + v) z u (SNo_add_SNo x v Hx Hv1) Hz Hu1.
          prove x + v <= u.
          exact H2.
      }
  + assume Hv: v :e Rxyz4.
    apply ReplE_impred (SNoR z) (fun w => (x+y)+w) v Hv.
    let u.
    assume Hu: u :e SNoR z.
    assume Hvu: v = (x+y)+u.
    apply SNoR_E z Hz u Hu.
    assume Hu1: SNo u.
    assume Hu2: SNoLev u :e SNoLev z.
    assume Hu3: z < u.
    prove x + (y + z) < v.
    rewrite Hvu.
    prove x + (y + z) < (x + y) + u.
    claim IH3u: x+(y+u) = (x+y)+u.
    { exact IH3 u (SNoR_SNoS_ z u Hu). }
    rewrite <- IH3u.
    prove x + (y + z) < x + (y + u).
    apply add_SNo_Lt2 x (y + z) (y + u) Hx Lyz (SNo_add_SNo y u Hy Hu1).
    prove y + z < y + u.
    apply add_SNo_Lt2 y z u Hy Hz Hu1.
    prove z < u.
    exact Hu3.
Qed.

Theorem add_SNo_cancel_L : forall x y z, SNo x -> SNo y -> SNo z -> x + y = x + z -> y = z.
let x y z.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hz: SNo z.
assume Hxyz: x + y = x + z.
claim Lmx: SNo (-x).
{ exact SNo_minus_SNo x Hx. }
claim L1: -x + (x + y) = y.
{ rewrite add_SNo_assoc (-x) x y Lmx Hx Hy.
  prove (-x + x) + y = y.
  rewrite add_SNo_minus_SNo_linv x Hx.
  prove 0 + y = y.
  exact add_SNo_0L y Hy.
}
claim L2: -x + (x + z) = z.
{ rewrite add_SNo_assoc (-x) x z Lmx Hx Hz.
  prove (-x + x) + z = z.
  rewrite add_SNo_minus_SNo_linv x Hx.
  prove 0 + z = z.
  exact add_SNo_0L z Hz.
}
rewrite <- L1.
rewrite Hxyz.
exact L2.
Qed.

Theorem minus_SNo_0 : - 0 = 0.
apply add_SNo_cancel_L 0 (- 0) 0 SNo_0 (SNo_minus_SNo 0 SNo_0) SNo_0.
prove 0 + - 0 = 0 + 0.
transitivity 0.
- exact add_SNo_minus_SNo_rinv 0 SNo_0.
- symmetry. exact add_SNo_0L 0 SNo_0.
Qed.

Theorem minus_add_SNo_distr : forall x y, SNo x -> SNo y -> -(x+y) = (-x) + (-y).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lmx: SNo (-x).
{ exact SNo_minus_SNo x Hx. }
claim Lmy: SNo (-y).
{ exact SNo_minus_SNo y Hy. }
claim Lxy: SNo (x+y).
{ exact SNo_add_SNo x y Hx Hy. }
claim L1: (x+y) + -(x+y) = (x+y) + ((-x) + (-y)).
{ rewrite add_SNo_minus_SNo_rinv (x+y) Lxy.
  prove 0 = (x+y) + ((-x) + (-y)).
  rewrite add_SNo_assoc (x+y) (-x) (-y) Lxy Lmx Lmy.
  prove 0 = ((x+y) + (-x)) + (-y).
  rewrite add_SNo_com x y Hx Hy.
  prove 0 = ((y+x) + -x) + -y.
  rewrite <- add_SNo_assoc y x (-x) Hy Hx Lmx.
  prove 0 = (y + (x + -x)) + -y.
  rewrite add_SNo_minus_SNo_rinv x Hx.
  prove 0 = (y + 0) + -y.
  rewrite add_SNo_0R y Hy.
  prove 0 = y + -y.
  rewrite add_SNo_minus_SNo_rinv y Hy.
  prove 0 = 0.
  reflexivity.
}
exact add_SNo_cancel_L (x+y) (-(x+y)) ((-x) + (-y)) Lxy (SNo_minus_SNo (x+y) Lxy) (SNo_add_SNo (-x) (-y) Lmx Lmy) L1.
Qed.

Theorem minus_add_SNo_distr_3 : forall x y z, SNo x -> SNo y -> SNo z -> -(x + y + z) = -x + - y + -z.
let x y z. assume Hx Hy Hz.
transitivity -x + -(y + z).
- exact minus_add_SNo_distr x (y + z) Hx (SNo_add_SNo y z Hy Hz).
- f_equal. prove -(y + z) = -y + -z.
  exact minus_add_SNo_distr y z Hy Hz.
Qed.

Theorem add_SNo_Lev_bd : forall x y, SNo x -> SNo y -> SNoLev (x + y) c= SNoLev x + SNoLev y.
set P : set -> set -> prop := fun x y => SNoLev (x + y) c= SNoLev x + SNoLev y.
apply SNoLev_ind2.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim LLxLy: ordinal (SNoLev x + SNoLev y).
{ apply add_SNo_ordinal_ordinal.
  - apply SNoLev_ordinal. exact Hx.
  - apply SNoLev_ordinal. exact Hy.
}
assume IH1: forall w :e SNoS_ (SNoLev x), P w y.
assume IH2: forall z :e SNoS_ (SNoLev y), P x z.
assume IH3: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z.
prove SNoLev (x + y) c= SNoLev x + SNoLev y.
set Lxy1 := {w + y|w :e SNoL x}.
set Lxy2 := {x + w|w :e SNoL y}.
set Rxy1 := {z + y|z :e SNoR x}.
set Rxy2 := {x + z|z :e SNoR y}.
rewrite add_SNo_eq x Hx y Hy.
prove SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) c= SNoLev x + SNoLev y.
claim L1: SNoCutP (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
{ exact add_SNo_SNoCutP x y Hx Hy. }
apply SNoCutP_SNoCut_impred (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) L1.
assume H1: SNo (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)).
assume H2: SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) :e ordsucc ((\/_ x :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev x)) :\/: (\/_ y :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev y))).
assume _ _ _.
claim Lxy1E: forall u :e Lxy1, forall p:set -> prop, (forall w :e SNoS_ (SNoLev x), u = w + y -> SNo w -> SNoLev w :e SNoLev x -> w < x -> p (w + y)) -> p u.
{ let u. assume Hu. let p. assume Hp.
  apply ReplE_impred (SNoL x) (fun w => w + y) u Hu.
  let w.
  assume Hw: w :e SNoL x.
  assume Huw: u = w + y.
  rewrite Huw.
  apply SNoL_E x Hx w Hw.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoL_SNoS_ x w Hw. }
  exact Hp w Lw Huw.
}
claim Lxy2E: forall u :e Lxy2, forall p:set -> prop, (forall w :e SNoS_ (SNoLev y), u = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p u.
{ let u. assume Hu. let p. assume Hp.
  apply ReplE_impred (SNoL y) (fun w => x + w) u Hu.
  let w.
  assume Hw: w :e SNoL y.
  assume Huw: u = x + w.
  rewrite Huw.
  apply SNoL_E y Hy w Hw.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoL_SNoS_ y w Hw. }
  exact Hp w Lw Huw.
}
claim Rxy1E: forall u :e Rxy1, forall p:set -> prop, (forall w :e SNoS_ (SNoLev x), u = w + y -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y)) -> p u.
{ let u. assume Hu. let p. assume Hp.
  apply ReplE_impred (SNoR x) (fun w => w + y) u Hu.
  let w.
  assume Hw: w :e SNoR x.
  assume Huw: u = w + y.
  rewrite Huw.
  apply SNoR_E x Hx w Hw.
  claim Lw: w :e SNoS_ (SNoLev x).
  { exact SNoR_SNoS_ x w Hw. }
  exact Hp w Lw Huw.
}
claim Rxy2E: forall u :e Rxy2, forall p:set -> prop, (forall w :e SNoS_ (SNoLev y), u = x + w -> SNo w -> SNoLev w :e SNoLev y -> y < w -> p (x + w)) -> p u.
{ let u. assume Hu. let p. assume Hp.
  apply ReplE_impred (SNoR y) (fun w => x + w) u Hu.
  let w.
  assume Hw: w :e SNoR y.
  assume Huw: u = x + w.
  rewrite Huw.
  apply SNoR_E y Hy w Hw.
  claim Lw: w :e SNoS_ (SNoLev y).
  { exact SNoR_SNoS_ y w Hw. }
  exact Hp w Lw Huw.
}
claim Lxy1E2: forall u :e Lxy1, SNo u.
{ let u. assume Hu. apply Lxy1E u Hu.
  let w. assume Hw1 Hw2 Hw3 Hw4 Hw5.
  prove SNo (w + y).
  apply SNo_add_SNo.
  - exact Hw3.
  - exact Hy.
}
claim Lxy2E2: forall u :e Lxy2, SNo u.
{ let u. assume Hu. apply Lxy2E u Hu.
  let w. assume Hw1 Hw2 Hw3 Hw4 Hw5.
  prove SNo (x + w).
  apply SNo_add_SNo.
  - exact Hx.
  - exact Hw3.
}
claim Rxy1E2: forall u :e Rxy1, SNo u.
{ let u. assume Hu. apply Rxy1E u Hu.
  let w. assume Hw1 Hw2 Hw3 Hw4 Hw5.
  prove SNo (w + y).
  apply SNo_add_SNo.
  - exact Hw3.
  - exact Hy.
}
claim Rxy2E2: forall u :e Rxy2, SNo u.
{ let u. assume Hu. apply Rxy2E u Hu.
  let w. assume Hw1 Hw2 Hw3 Hw4 Hw5.
  prove SNo (x + w).
  apply SNo_add_SNo.
  - exact Hx.
  - exact Hw3.
}
claim L2: ordinal ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))).
{ apply ordinal_binunion.
  - apply ordinal_famunion (Lxy1 :\/: Lxy2) (fun u => ordsucc (SNoLev u)).
    let u. assume Hu: u :e Lxy1 :\/: Lxy2.
    prove ordinal (ordsucc (SNoLev u)).
    apply ordinal_ordsucc.
    apply SNoLev_ordinal.
    prove SNo u.
    apply binunionE Lxy1 Lxy2 u Hu.
    + assume Hu. exact Lxy1E2 u Hu.
    + assume Hu. exact Lxy2E2 u Hu.
  - apply ordinal_famunion (Rxy1 :\/: Rxy2) (fun u => ordsucc (SNoLev u)).
    let u. assume Hu: u :e Rxy1 :\/: Rxy2.
    prove ordinal (ordsucc (SNoLev u)).
    apply ordinal_ordsucc.
    apply SNoLev_ordinal.
    prove SNo u.
    apply binunionE Rxy1 Rxy2 u Hu.
    + assume Hu. exact Rxy1E2 u Hu.
    + assume Hu. exact Rxy2E2 u Hu.
}
claim L3: SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) c= (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u)).
{ apply TransSet_In_ordsucc_Subq.
  + prove TransSet ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))).
    apply L2. assume H _. exact H.
  + exact H2.
}
claim L4: ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))) c= SNoLev x + SNoLev y.
{ apply binunion_Subq_min.
  - prove (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) c= SNoLev x + SNoLev y.
    let v. assume Hv: v :e (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)).
    apply famunionE_impred (Lxy1 :\/: Lxy2) (fun u => ordsucc (SNoLev u)) v Hv.
    let u. assume Hu: u :e Lxy1 :\/: Lxy2.
    apply binunionE Lxy1 Lxy2 u Hu.
    + assume Hu: u :e Lxy1. apply Lxy1E u Hu.
      let w.
      assume Hw1: w :e SNoS_ (SNoLev x).
      assume Hw2: u = w + y.
      assume Hw3: SNo w.
      assume Hw4: SNoLev w :e SNoLev x.
      assume Hw5: w < x.
      assume Hw6: v :e ordsucc (SNoLev (w + y)).
      prove v :e SNoLev x + SNoLev y.
      claim Lv: ordinal v.
      { apply ordinal_Hered (ordsucc (SNoLev (w + y))).
        - prove ordinal (ordsucc (SNoLev (w + y))).
          apply ordinal_ordsucc. apply SNoLev_ordinal.
          apply SNo_add_SNo.
          + exact Hw3.
          + exact Hy.
        - exact Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. exact H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (w + y) c= SNoLev w + SNoLev y.
          { apply IH1. prove w :e SNoS_ (SNoLev x). exact Hw1. }
          claim L4a: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InL.
            - apply SNoLev_ordinal. exact Hx.
            - apply SNoLev_ordinal. exact Hy.
            - exact Hw4.
          }
          claim L4b: SNoLev w + SNoLev y c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. exact H (SNoLev w + SNoLev y) L4a. }
          claim L4c: v c= SNoLev (w + y).
          { apply ordinal_In_Or_Subq (SNoLev (w + y)) v (SNoLev_ordinal (w + y) (SNo_add_SNo w y Hw3 Hy)) Lv.
            - assume H2: SNoLev (w + y) :e v.
              prove False.
              apply ordsuccE (SNoLev (w + y)) v Hw6.
              + assume H3: v :e SNoLev (w + y).
                exact In_no2cycle (SNoLev (w + y)) v H2 H3.
              + assume H3: v = SNoLev (w + y).
                apply In_irref v. rewrite H3 at 1. exact H2.
            - assume H2: v c= SNoLev (w + y). exact H2.
          }
          apply In_irref (SNoLev w + SNoLev y).
          prove (SNoLev w + SNoLev y) :e (SNoLev w + SNoLev y).
          apply LIHw.
          prove (SNoLev w + SNoLev y) :e SNoLev (w + y).
          apply L4c.
          prove (SNoLev w + SNoLev y) :e v.
          apply H1.
          prove (SNoLev w + SNoLev y) :e SNoLev x + SNoLev y.
          exact L4a.
        }
    + assume Hu: u :e Lxy2. apply Lxy2E u Hu.
      let w.
      assume Hw1: w :e SNoS_ (SNoLev y).
      assume Hw2: u = x + w.
      assume Hw3: SNo w.
      assume Hw4: SNoLev w :e SNoLev y.
      assume Hw5: w < y.
      assume Hw6: v :e ordsucc (SNoLev (x + w)).
      prove v :e SNoLev x + SNoLev y.
      claim Lv: ordinal v.
      { apply ordinal_Hered (ordsucc (SNoLev (x + w))).
        - prove ordinal (ordsucc (SNoLev (x + w))).
          apply ordinal_ordsucc. apply SNoLev_ordinal.
          apply SNo_add_SNo.
          + exact Hx.
          + exact Hw3.
        - exact Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. exact H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (x + w) c= SNoLev x + SNoLev w.
          { apply IH2. prove w :e SNoS_ (SNoLev y). exact Hw1. }
          claim L4a: SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InR.
            - apply SNoLev_ordinal. exact Hx.
            - apply SNoLev_ordinal. exact Hy.
            - exact Hw4.
          }
          claim L4b: SNoLev x + SNoLev w c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. exact H (SNoLev x + SNoLev w) L4a. }
          claim L4c: v c= SNoLev (x + w).
          { apply ordinal_In_Or_Subq (SNoLev (x + w)) v (SNoLev_ordinal (x + w) (SNo_add_SNo x w Hx Hw3)) Lv.
            - assume H2: SNoLev (x + w) :e v.
              prove False.
              apply ordsuccE (SNoLev (x + w)) v Hw6.
              + assume H3: v :e SNoLev (x + w).
                exact In_no2cycle (SNoLev (x + w)) v H2 H3.
              + assume H3: v = SNoLev (x + w).
                apply In_irref v. rewrite H3 at 1. exact H2.
            - assume H2: v c= SNoLev (x + w). exact H2.
          }
          apply In_irref (SNoLev x + SNoLev w).
          prove (SNoLev x + SNoLev w) :e (SNoLev x + SNoLev w).
          apply LIHw.
          prove (SNoLev x + SNoLev w) :e SNoLev (x + w).
          apply L4c.
          prove (SNoLev x + SNoLev w) :e v.
          apply H1.
          prove (SNoLev x + SNoLev w) :e SNoLev x + SNoLev y.
          exact L4a.
        }
  - prove (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u)) c= SNoLev x + SNoLev y.
    let v. assume Hv: v :e (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u)).
    apply famunionE_impred (Rxy1 :\/: Rxy2) (fun u => ordsucc (SNoLev u)) v Hv.
    let u. assume Hu: u :e Rxy1 :\/: Rxy2.
    apply binunionE Rxy1 Rxy2 u Hu.
    + assume Hu: u :e Rxy1. apply Rxy1E u Hu.
      let w.
      assume Hw1: w :e SNoS_ (SNoLev x).
      assume Hw2: u = w + y.
      assume Hw3: SNo w.
      assume Hw4: SNoLev w :e SNoLev x.
      assume Hw5: x < w.
      assume Hw6: v :e ordsucc (SNoLev (w + y)).
      prove v :e SNoLev x + SNoLev y.
      claim Lv: ordinal v.
      { apply ordinal_Hered (ordsucc (SNoLev (w + y))).
        - prove ordinal (ordsucc (SNoLev (w + y))).
          apply ordinal_ordsucc. apply SNoLev_ordinal.
          apply SNo_add_SNo.
          + exact Hw3.
          + exact Hy.
        - exact Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. exact H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (w + y) c= SNoLev w + SNoLev y.
          { apply IH1. prove w :e SNoS_ (SNoLev x). exact Hw1. }
          claim L4a: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InL.
            - apply SNoLev_ordinal. exact Hx.
            - apply SNoLev_ordinal. exact Hy.
            - exact Hw4.
          }
          claim L4b: SNoLev w + SNoLev y c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. exact H (SNoLev w + SNoLev y) L4a. }
          claim L4c: v c= SNoLev (w + y).
          { apply ordinal_In_Or_Subq (SNoLev (w + y)) v (SNoLev_ordinal (w + y) (SNo_add_SNo w y Hw3 Hy)) Lv.
            - assume H2: SNoLev (w + y) :e v.
              prove False.
              apply ordsuccE (SNoLev (w + y)) v Hw6.
              + assume H3: v :e SNoLev (w + y).
                exact In_no2cycle (SNoLev (w + y)) v H2 H3.
              + assume H3: v = SNoLev (w + y).
                apply In_irref v. rewrite H3 at 1. exact H2.
            - assume H2: v c= SNoLev (w + y). exact H2.
          }
          apply In_irref (SNoLev w + SNoLev y).
          prove (SNoLev w + SNoLev y) :e (SNoLev w + SNoLev y).
          apply LIHw.
          prove (SNoLev w + SNoLev y) :e SNoLev (w + y).
          apply L4c.
          prove (SNoLev w + SNoLev y) :e v.
          apply H1.
          prove (SNoLev w + SNoLev y) :e SNoLev x + SNoLev y.
          exact L4a.
        }
    + assume Hu: u :e Rxy2. apply Rxy2E u Hu.
      let w.
      assume Hw1: w :e SNoS_ (SNoLev y).
      assume Hw2: u = x + w.
      assume Hw3: SNo w.
      assume Hw4: SNoLev w :e SNoLev y.
      assume Hw5: y < w.
      assume Hw6: v :e ordsucc (SNoLev (x + w)).
      prove v :e SNoLev x + SNoLev y.
      claim Lv: ordinal v.
      { apply ordinal_Hered (ordsucc (SNoLev (x + w))).
        - prove ordinal (ordsucc (SNoLev (x + w))).
          apply ordinal_ordsucc. apply SNoLev_ordinal.
          apply SNo_add_SNo.
          + exact Hx.
          + exact Hw3.
        - exact Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. exact H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (x + w) c= SNoLev x + SNoLev w.
          { apply IH2. prove w :e SNoS_ (SNoLev y). exact Hw1. }
          claim L4a: SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InR.
            - apply SNoLev_ordinal. exact Hx.
            - apply SNoLev_ordinal. exact Hy.
            - exact Hw4.
          }
          claim L4b: SNoLev x + SNoLev w c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. exact H (SNoLev x + SNoLev w) L4a. }
          claim L4c: v c= SNoLev (x + w).
          { apply ordinal_In_Or_Subq (SNoLev (x + w)) v (SNoLev_ordinal (x + w) (SNo_add_SNo x w Hx Hw3)) Lv.
            - assume H2: SNoLev (x + w) :e v.
              prove False.
              apply ordsuccE (SNoLev (x + w)) v Hw6.
              + assume H3: v :e SNoLev (x + w).
                exact In_no2cycle (SNoLev (x + w)) v H2 H3.
              + assume H3: v = SNoLev (x + w).
                apply In_irref v. rewrite H3 at 1. exact H2.
            - assume H2: v c= SNoLev (x + w). exact H2.
          }
          apply In_irref (SNoLev x + SNoLev w).
          prove (SNoLev x + SNoLev w) :e (SNoLev x + SNoLev w).
          apply LIHw.
          prove (SNoLev x + SNoLev w) :e SNoLev (x + w).
          apply L4c.
          prove (SNoLev x + SNoLev w) :e v.
          apply H1.
          prove (SNoLev x + SNoLev w) :e SNoLev x + SNoLev y.
          exact L4a.
        }
}
exact Subq_tra (SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2))) ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))) (SNoLev x + SNoLev y) L3 L4.
Qed.

Theorem add_SNo_SNoS_omega : forall x y :e SNoS_ omega, x + y :e SNoS_ omega.
let x. assume Hx. let y. assume Hy.
apply SNoS_E2 omega omega_ordinal x Hx.
assume Hx1: SNoLev x :e omega.
assume Hx2: ordinal (SNoLev x).
assume Hx3: SNo x.
assume Hx4: SNo_ (SNoLev x) x.
apply SNoS_E2 omega omega_ordinal y Hy.
assume Hy1: SNoLev y :e omega.
assume Hy2: ordinal (SNoLev y).
assume Hy3: SNo y.
assume Hy4: SNo_ (SNoLev y) y.
apply SNoS_I omega omega_ordinal (x + y) (SNoLev (x + y)).
- prove SNoLev (x + y) :e omega.
  claim LLxy: ordinal (SNoLev (x + y)).
  { apply SNoLev_ordinal. exact SNo_add_SNo x y Hx3 Hy3. }
  apply ordinal_In_Or_Subq (SNoLev (x + y)) omega LLxy omega_ordinal.
  + assume H1. exact H1.
  + assume H1: omega c= SNoLev (x + y).
    apply In_irref (SNoLev x + SNoLev y).
    prove (SNoLev x + SNoLev y) :e (SNoLev x + SNoLev y).
    apply add_SNo_Lev_bd x y Hx3 Hy3.
    prove (SNoLev x + SNoLev y) :e SNoLev (x + y).
    apply H1.
    prove (SNoLev x + SNoLev y) :e omega.
    exact add_SNo_In_omega (SNoLev x) Hx1 (SNoLev y) Hy1.
- prove SNo_ (SNoLev (x + y)) (x + y).
  apply SNoLev_. exact SNo_add_SNo x y Hx3 Hy3.
Qed.

Theorem add_SNo_minus_R2 : forall x y, SNo x -> SNo y -> (x + y) + - y = x.
let x y. assume Hx Hy.
transitivity x + (y + - y),
             x + 0.
- symmetry. exact add_SNo_assoc x y (- y) Hx Hy (SNo_minus_SNo y Hy).
- f_equal. exact add_SNo_minus_SNo_rinv y Hy.
- exact add_SNo_0R x Hx.
Qed.

Theorem add_SNo_minus_R2' : forall x y, SNo x -> SNo y -> (x + - y) + y = x.
let x y. assume Hx Hy.
rewrite <- minus_SNo_invol y Hy at 2.
exact add_SNo_minus_R2 x (- y) Hx (SNo_minus_SNo y Hy).
Qed.

Theorem add_SNo_minus_L2 : forall x y, SNo x -> SNo y -> - x + (x + y) = y.
let x y. assume Hx Hy.
rewrite add_SNo_com (- x) (x + y) (SNo_minus_SNo x Hx) (SNo_add_SNo x y Hx Hy).
prove (x + y) + - x = y.
rewrite add_SNo_com x y Hx Hy.
prove (y + x) + - x = y.
exact add_SNo_minus_R2 y x Hy Hx.
Qed.

Theorem add_SNo_minus_L2' : forall x y, SNo x -> SNo y -> x + (- x + y) = y.
let x y. assume Hx Hy.
rewrite <- minus_SNo_invol x Hx at 1.
exact add_SNo_minus_L2 (- x) y (SNo_minus_SNo x Hx) Hy.
Qed.

Theorem add_SNo_Lt1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < z + y -> x < z.
let x y z. assume Hx Hy Hz H1.
prove x < z.
claim L1: (x + y) + - y = x.
{ exact add_SNo_minus_R2 x y Hx Hy. }
claim L2: (z + y) + - y = z.
{ exact add_SNo_minus_R2 z y Hz Hy. }
rewrite <- L1. rewrite <- L2.
prove (x + y) + - y < (z + y) + - y.
exact add_SNo_Lt1 (x + y) (- y) (z + y)
                  (SNo_add_SNo x y Hx Hy)
                  (SNo_minus_SNo y Hy)
                  (SNo_add_SNo z y Hz Hy)
                  H1.
Qed.

Theorem add_SNo_Lt2_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < x + z -> y < z.
let x y z. assume Hx Hy Hz.
rewrite add_SNo_com x y Hx Hy.
rewrite add_SNo_com x z Hx Hz.
exact add_SNo_Lt1_cancel y x z Hy Hx Hz.
Qed.

Theorem add_SNo_assoc_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> x + y + z + w = (x + y + z) + w.
let x y z w. assume Hx Hy Hz Hw.
transitivity (x + y) + z + w,
             ((x + y) + z) + w.
- exact add_SNo_assoc x y (z + w) Hx Hy (SNo_add_SNo z w Hz Hw).
- exact add_SNo_assoc (x + y) z w (SNo_add_SNo x y Hx Hy) Hz Hw.
- f_equal. symmetry. exact add_SNo_assoc x y z Hx Hy Hz.
Qed.

Theorem add_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x + y + z = y + x + z.
let x y z.
assume Hx Hy Hz.
rewrite add_SNo_assoc x y z Hx Hy Hz.
rewrite add_SNo_assoc y x z Hy Hx Hz.
f_equal.
exact add_SNo_com x y Hx Hy.
Qed.

Theorem add_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) + z = (x + z) + y.
let x y z.
assume Hx Hy Hz.
rewrite <- add_SNo_assoc x y z Hx Hy Hz.
rewrite <- add_SNo_assoc x z y Hx Hz Hy.
f_equal.
exact add_SNo_com y z Hy Hz.
Qed.

Theorem add_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
let x y z w.
assume Hx Hy Hz Hw.
rewrite add_SNo_assoc (x + y) z w (SNo_add_SNo x y Hx Hy) Hz Hw.
prove ((x + y) + z) + w = (x + z) + (y + w).
rewrite add_SNo_com_3b_1_2 x y z Hx Hy Hz.
prove ((x + z) + y) + w = (x + z) + (y + w).
symmetry.
exact add_SNo_assoc (x + z) y w (SNo_add_SNo x z Hx Hz) Hy Hw.
Qed.

Theorem add_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x + y + z = z + x + y.
let x y z.
assume Hx Hy Hz.
prove x + (y + z) = z + (x + y).
transitivity x + (z + y),
             (x + z) + y,
             (z + x) + y.
- f_equal. exact add_SNo_com y z Hy Hz.
- exact add_SNo_assoc x z y Hx Hz Hy.
- f_equal. exact add_SNo_com x z Hx Hz.
- symmetry. exact add_SNo_assoc z x y Hz Hx Hy.
Qed.

Theorem add_SNo_rotate_4_1 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w ->
  x + y + z + w = w + x + y + z.
let x y z w. assume Hx Hy Hz Hw.
rewrite add_SNo_rotate_3_1 y z w Hy Hz Hw.
prove x + w + y + z = w + x + y + z.
exact add_SNo_com_3_0_1 x w (y + z) Hx Hw (SNo_add_SNo y z Hy Hz).
Qed.

Theorem add_SNo_rotate_5_1 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = v + x + y + z + w.
let x y z w v. assume Hx Hy Hz Hw Hv.
rewrite add_SNo_rotate_4_1 y z w v Hy Hz Hw Hv.
prove x + v + y + z + w = v + x + y + z + w.
exact add_SNo_com_3_0_1 x v (y + z + w) Hx Hv (SNo_add_SNo_3 y z w Hy Hz Hw).
Qed.

Theorem add_SNo_rotate_5_2 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = w + v + x + y + z.
let x y z w v. assume Hx Hy Hz Hw Hv.
transitivity (v + x + y + z + w).
- exact add_SNo_rotate_5_1 x y z w v Hx Hy Hz Hw Hv.
- exact add_SNo_rotate_5_1 v x y z w Hv Hx Hy Hz Hw.
Qed.

Theorem add_SNo_minus_SNo_prop2 : forall x y, SNo x -> SNo y -> x + - x + y = y.
let x y. assume Hx Hy.
rewrite add_SNo_assoc x (- x) y Hx (SNo_minus_SNo x Hx) Hy.
prove (x + - x) + y = y.
rewrite add_SNo_minus_SNo_rinv x Hx.
prove 0 + y = y.
exact add_SNo_0L y Hy.
Qed.

Theorem add_SNo_minus_SNo_prop3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (- z + w) = x + y + w.
let x y z w. assume Hx Hy Hz Hw.
rewrite add_SNo_assoc x y z Hx Hy Hz.
prove ((x + y) + z) + (- z + w) = x + y + w.
rewrite <- add_SNo_assoc (x + y) z (- z + w) (SNo_add_SNo x y Hx Hy) Hz (SNo_add_SNo (- z) w (SNo_minus_SNo z Hz) Hw).
prove (x + y) + (z + - z + w) = x + y + w.
rewrite add_SNo_minus_L2' z w Hz Hw.
prove (x + y) + w = x + y + w.
symmetry. exact add_SNo_assoc x y w Hx Hy Hw.
Qed.

Theorem add_SNo_minus_SNo_prop4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (w + - z) = x + y + w.
let x y z w. assume Hx Hy Hz Hw.
rewrite add_SNo_com w (- z) Hw (SNo_minus_SNo z Hz).
prove (x + y + z) + (- z + w) = x + y + w.
exact add_SNo_minus_SNo_prop3 x y z w Hx Hy Hz Hw.
Qed.

Theorem add_SNo_minus_SNo_prop5 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + - z) + (z + w) = x + y + w.
let x y z w. assume Hx Hy Hz Hw.
prove (x + y + - z) + (z + w) = x + y + w.
rewrite <- minus_SNo_invol z Hz at 2.
prove (x + y + - z) + (- - z + w) = x + y + w.
exact add_SNo_minus_SNo_prop3 x y (- z) w Hx Hy (SNo_minus_SNo z Hz) Hw.
Qed.

Theorem add_SNo_minus_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x + - y < z -> x < z + y.
let x y z. assume Hx Hy Hz H1.
apply add_SNo_Lt1_cancel x (- y) (z + y) Hx (SNo_minus_SNo y Hy) (SNo_add_SNo z y Hz Hy).
prove x + - y < (z + y) + - y.
rewrite <- add_SNo_assoc z y (- y) Hz Hy (SNo_minus_SNo y Hy).
rewrite add_SNo_minus_SNo_rinv y Hy.
rewrite add_SNo_0R z Hz.
exact H1.
Qed.

Theorem add_SNo_minus_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> z < x + - y -> z + y < x.
let x y z. assume Hx Hy Hz H1.
apply add_SNo_Lt1_cancel (z + y) (- y) x (SNo_add_SNo z y Hz Hy) (SNo_minus_SNo y Hy) Hx.
prove (z + y) + - y < x + - y.
rewrite <- add_SNo_assoc z y (- y) Hz Hy (SNo_minus_SNo y Hy).
prove z + y + - y < x + - y.
rewrite add_SNo_minus_SNo_rinv y Hy.
rewrite add_SNo_0R z Hz.
exact H1.
Qed.

Theorem add_SNo_minus_Lt1b : forall x y z, SNo x -> SNo y -> SNo z -> x < z + y -> x + - y < z.
let x y z. assume Hx Hy Hz H1.
apply add_SNo_Lt1_cancel (x + - y) y z (SNo_add_SNo x (- y) Hx (SNo_minus_SNo y Hy)) Hy Hz.
prove (x + - y) + y < z + y.
rewrite <- add_SNo_assoc x (- y) y Hx (SNo_minus_SNo y Hy) Hy.
rewrite add_SNo_minus_SNo_linv y Hy.
rewrite add_SNo_0R x Hx.
exact H1.
Qed.

Theorem add_SNo_minus_Lt2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y < x -> z < x + - y.
let x y z. assume Hx Hy Hz H1.
apply add_SNo_Lt1_cancel z y (x + - y) Hz Hy (SNo_add_SNo x (- y) Hx (SNo_minus_SNo y Hy)).
prove z + y < (x + - y) + y.
rewrite <- add_SNo_assoc x (- y) y Hx (SNo_minus_SNo y Hy) Hy.
rewrite add_SNo_minus_SNo_linv y Hy.
rewrite add_SNo_0R x Hx.
exact H1.
Qed.

Theorem add_SNo_minus_Lt1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y < w + z -> x + y + - z < w.
let x y z w. assume Hx Hy Hz Hw H1.
prove x + y + - z < w.
rewrite add_SNo_assoc x y (- z) Hx Hy (SNo_minus_SNo z Hz).
prove (x + y) + - z < w.
apply add_SNo_minus_Lt1b (x + y) z w (SNo_add_SNo x y Hx Hy) Hz Hw.
exact H1.
Qed.

Theorem add_SNo_minus_Lt2b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> w + z < x + y -> w < x + y + - z.
let x y z w. assume Hx Hy Hz Hw H1.
prove w < x + y + - z.
rewrite add_SNo_assoc x y (- z) Hx Hy (SNo_minus_SNo z Hz).
prove w < (x + y) + - z.
apply add_SNo_minus_Lt2b (x + y) z w (SNo_add_SNo x y Hx Hy) Hz Hw.
exact H1.
Qed.

Theorem add_SNo_minus_Lt_lem : forall x y z u v w, SNo x -> SNo y -> SNo z -> SNo u -> SNo v -> SNo w ->
  x + y + w < u + v + z ->
  x + y + - z < u + v + - w.
let x y z u v w. assume Hx Hy Hz Hu Hv Hw H1.
claim Lmz: SNo (- z).
{ exact SNo_minus_SNo z Hz. }
claim Lmw: SNo (- w).
{ exact SNo_minus_SNo w Hw. }
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim Luv: SNo (u + v).
{ exact SNo_add_SNo u v Hu Hv. }
rewrite add_SNo_assoc x y (- z) Hx Hy Lmz.
rewrite add_SNo_assoc u v (- w) Hu Hv Lmw.
prove (x + y) + - z < (u + v) + - w.
apply add_SNo_minus_Lt2b (u + v) w ((x + y) + - z) Luv Hw (SNo_add_SNo (x + y) (- z) Lxy Lmz).
prove ((x + y) + - z) + w < u + v.
rewrite <- add_SNo_assoc (x + y) (- z) w Lxy Lmz Hw.
prove (x + y) + - z + w < u + v.
rewrite add_SNo_com (- z) w Lmz Hw.
prove (x + y) + w + - z < u + v.
rewrite add_SNo_assoc (x + y) w (- z) Lxy Hw Lmz.
prove ((x + y) + w) + - z < u + v.
apply add_SNo_minus_Lt1b ((x + y) + w) z (u + v) (SNo_add_SNo (x + y) w Lxy Hw) Hz Luv.
prove (x + y) + w < (u + v) + z.
rewrite <- add_SNo_assoc x y w Hx Hy Hw.
rewrite <- add_SNo_assoc u v z Hu Hv Hz.
exact H1.
Qed.

Theorem add_SNo_minus_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> z <= x + - y -> z + y <= x.
let x y z. assume Hx Hy Hz H1.
apply SNoLeE z (x + - y) Hz (SNo_add_SNo x (- y) Hx (SNo_minus_SNo y Hy)) H1.
- assume H2. apply SNoLtLe.
  exact add_SNo_minus_Lt2 x y z Hx Hy Hz H2.
- assume H2: z = x + - y.
  prove z + y <= x.
  rewrite H2.
  prove (x + - y) + y <= x.
  rewrite add_SNo_minus_R2' x y Hx Hy.
  apply SNoLe_ref.
Qed.

Theorem add_SNo_minus_Le2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y <= x -> z <= x + - y.
let x y z. assume Hx Hy Hz H1.
apply SNoLeE (z + y) x (SNo_add_SNo z y Hz Hy) Hx H1.
- assume H2. apply SNoLtLe.
  exact add_SNo_minus_Lt2b x y z Hx Hy Hz H2.
- assume H2: z + y = x.
  prove z <= x + - y.
  rewrite <- H2.
  prove z <= (z + y) + - y.
  rewrite add_SNo_minus_R2 z y Hz Hy.
  apply SNoLe_ref.
Qed.

Theorem add_SNo_Lt_subprop2 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
  -> x + u < z + v
  -> y + v < w + u
  -> x + y < z + w.
let x y z w u v.
assume Hx Hy Hz Hw Hu Hv H1 H2.
apply add_SNo_Lt1_cancel (x + y) (u + v) (z + w)
           (SNo_add_SNo x y Hx Hy)
           (SNo_add_SNo u v Hu Hv)
           (SNo_add_SNo z w Hz Hw).
prove (x + y) + (u + v) < (z + w) + (u + v).
rewrite add_SNo_com_4_inner_mid x y u v Hx Hy Hu Hv.
prove (x + u) + (y + v) < (z + w) + (u + v).
claim L1: (z + w) + (u + v) = (z + v) + (w + u).
{ rewrite <- add_SNo_assoc z w (u + v) Hz Hw (SNo_add_SNo u v Hu Hv).
  rewrite <- add_SNo_assoc z v (w + u) Hz Hv (SNo_add_SNo w u Hw Hu).
  prove z + (w + (u + v)) = z + (v + (w + u)).
  f_equal.
  prove w + u + v = v + w + u.
  exact add_SNo_rotate_3_1 w u v Hw Hu Hv.
}
rewrite L1.
prove (x + u) + (y + v) < (z + v) + (w + u).
exact add_SNo_Lt3 (x + u) (y + v) (z + v) (w + u)
                       (SNo_add_SNo x u Hx Hu)
                       (SNo_add_SNo y v Hy Hv)
                       (SNo_add_SNo z v Hz Hv)
                       (SNo_add_SNo w u Hw Hu)
                       H1 H2.
Qed.

Theorem add_SNo_Lt_subprop3a : forall x y z w u a, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a
  -> x + z < w + a
  -> y + a < u
  -> x + y + z < w + u.
let x y z w u a.
assume Hx Hy Hz Hw Hu Ha H1 H2.
apply SNoLt_tra (x + y + z) (y + w + a) (w + u)
                (SNo_add_SNo x (y + z) Hx (SNo_add_SNo y z Hy Hz))
                (SNo_add_SNo y (w + a) Hy (SNo_add_SNo w a Hw Ha))
                (SNo_add_SNo w u Hw Hu).
- prove x + y + z < y + w + a.
  rewrite add_SNo_com_3_0_1 x y z Hx Hy Hz.
  prove y + x + z < y + w + a.
  apply add_SNo_Lt2 y (x + z) (w + a) Hy (SNo_add_SNo x z Hx Hz) (SNo_add_SNo w a Hw Ha).
  exact H1.
- prove y + w + a < w + u.
  rewrite <- add_SNo_rotate_3_1 w a y Hw Ha Hy.
  prove w + a + y < w + u.
  apply add_SNo_Lt2 w (a + y) u Hw (SNo_add_SNo a y Ha Hy) Hu.
  prove a + y < u.
  rewrite add_SNo_com a y Ha Hy. exact H2.
Qed.

Theorem add_SNo_Lt_subprop3b : forall x y w u v a, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a
  -> x + a < w + v
  -> y < a + u
  -> x + y < w + u + v.
let x y w u v a.
assume Hx Hy Hw Hu Hv Ha H1 H2.
rewrite add_SNo_com x y Hx Hy.
prove y + x < w + u + v.
rewrite <- add_SNo_rotate_3_1 u v w Hu Hv Hw.
prove y + x < u + v + w.
rewrite <- add_SNo_0R x Hx.
prove y + x + 0 < u + v + w.
apply add_SNo_Lt_subprop3a y x 0 u (v + w) a Hy Hx SNo_0 Hu (SNo_add_SNo v w Hv Hw) Ha.
- prove y + 0 < u + a. rewrite add_SNo_0R y Hy. rewrite add_SNo_com u a Hu Ha. exact H2.
- prove x + a < v + w. rewrite add_SNo_com v w Hv Hw. exact H1.
Qed.

Theorem add_SNo_Lt_subprop3c : forall x y z w u a b c, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a -> SNo b -> SNo c
 -> x + a < b + c
 -> y + c < u
 -> b + z < w + a
 -> x + y + z < w + u.
let x y z w u a b c.
assume Hx Hy Hz Hw Hu Ha Hb Hc H1 H2 H3.
claim L1: x + z < c + w.
{ apply add_SNo_Lt_subprop2 x z c w a b Hx Hz Hc Hw Ha Hb.
  - prove x + a < c + b. rewrite add_SNo_com c b Hc Hb. exact H1.
  - prove z + b < w + a. rewrite add_SNo_com z b Hz Hb. exact H3.
}
claim Lxz: SNo (x + z).
{ exact SNo_add_SNo x z Hx Hz. }
claim Lcw: SNo (c + w).
{ exact SNo_add_SNo c w Hc Hw. }
apply SNoLt_tra (x + y + z) (c + w + y) (w + u).
- exact SNo_add_SNo x (y + z) Hx (SNo_add_SNo y z Hy Hz).
- exact SNo_add_SNo c (w + y) Hc (SNo_add_SNo w y Hw Hy).
- exact SNo_add_SNo w u Hw Hu.
- prove x + y + z < c + w + y.
  rewrite add_SNo_com y z Hy Hz.
  prove x + z + y < c + w + y.
  rewrite add_SNo_assoc x z y Hx Hz Hy.
  rewrite add_SNo_assoc c w y Hc Hw Hy.
  exact add_SNo_Lt1 (x + z) y (c + w) Lxz Hy Lcw L1.
- prove c + w + y < w + u.
  rewrite <- add_SNo_rotate_3_1 w y c Hw Hy Hc.
  prove w + y + c < w + u.
  apply add_SNo_Lt2 w (y + c) u Hw (SNo_add_SNo y c Hy Hc) Hu.
  prove y + c < u.
  exact H2.
Qed.

Theorem add_SNo_Lt_subprop3d : forall x y w u v a b c, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a -> SNo b -> SNo c
 -> x + a < b + v
 -> y < c + u
 -> b + c < w + a
 -> x + y < w + u + v.
let x y w u v a b c.
assume Hx Hy Hw Hu Hv Ha Hb Hc H1 H2 H3.
claim L1: b + y < w + u + a.
{ exact add_SNo_Lt_subprop3b b y w u a c Hb Hy Hw Hu Ha Hc H3 H2. }
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx Hy. }
claim Lwuv: SNo (w + u + v).
{ exact SNo_add_SNo w (u + v) Hw (SNo_add_SNo u v Hu Hv). }
claim Lwua: SNo (w + u + a).
{ exact SNo_add_SNo w (u + a) Hw (SNo_add_SNo u a Hu Ha). }
claim Lby: SNo (b + y).
{ exact SNo_add_SNo b y Hb Hy. }
apply add_SNo_Lt1_cancel (x + y) b (w + u + v) Lxy Hb Lwuv.
prove (x + y) + b < (w + u + v) + b.
apply SNoLt_tra ((x + y) + b)
                (x + w + u + a)
                ((w + u + v) + b)
                (SNo_add_SNo (x + y) b Lxy Hb)
                (SNo_add_SNo x (w + u + a) Hx Lwua)
                (SNo_add_SNo (w + u + v) b Lwuv Hb).
- prove (x + y) + b < x + w + u + a.
  rewrite <- add_SNo_assoc x y b Hx Hy Hb.
  prove x + y + b < x + w + u + a.
  rewrite add_SNo_com y b Hy Hb.
  prove x + b + y < x + w + u + a.
  apply add_SNo_Lt2 x (b + y) (w + u + a) Hx Lby Lwua.
  prove b + y < w + u + a.
  exact L1.
- prove x + w + u + a < (w + u + v) + b.
  claim L2: x + w + u + a = (w + u) + (x + a).
  { transitivity (x + w + u) + a,
                 (w + u + x) + a,
                 w + u + x + a.
    - exact add_SNo_assoc_4 x w u a Hx Hw Hu Ha.
    - f_equal. symmetry. exact add_SNo_rotate_3_1 w u x Hw Hu Hx.
    - symmetry. exact add_SNo_assoc_4 w u x a Hw Hu Hx Ha.
    - prove w + u + x + a = (w + u) + (x + a).
      exact add_SNo_assoc w u (x + a) Hw Hu (SNo_add_SNo x a Hx Ha).
  }
  claim L3: (w + u + v) + b = (w + u) + b + v.
  { transitivity ((w + u) + v) + b,
                 (w + u) + (v + b).
    - f_equal. exact add_SNo_assoc w u v Hw Hu Hv.
    - symmetry. exact add_SNo_assoc (w + u) v b (SNo_add_SNo w u Hw Hu) Hv Hb.
    - f_equal. exact add_SNo_com v b Hv Hb.
  }
  rewrite L2. rewrite L3.
  prove (w + u) + (x + a) < (w + u) + (b + v).
  apply add_SNo_Lt2 (w + u) (x + a) (b + v)
                    (SNo_add_SNo w u Hw Hu)
                    (SNo_add_SNo x a Hx Ha)
                    (SNo_add_SNo b v Hb Hv).
  exact H1.
Qed.

Theorem ordinal_ordsucc_SNo_eq : forall alpha, ordinal alpha -> ordsucc alpha = 1 + alpha.
let alpha. assume Ha.
rewrite <- add_SNo_0L alpha (ordinal_SNo alpha Ha) at 1.
prove ordsucc (0 + alpha) = 1 + alpha.
symmetry.
exact add_SNo_ordinal_SL 0 ordinal_Empty alpha Ha.
Qed.

Theorem add_SNo_3a_2b: forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u
 -> (x + y + z) + (w + u) = (u + y + z) + (w + x).
let x y z w u. assume Hx Hy Hz Hw Hu.
rewrite add_SNo_com (x + y + z) (w + u)
                    (SNo_add_SNo_3 x y z Hx Hy Hz) (SNo_add_SNo w u Hw Hu).
prove (w + u) + (x + y + z) = (u + y + z) + (w + x).
rewrite add_SNo_com_4_inner_mid w u x (y + z) Hw Hu Hx (SNo_add_SNo y z Hy Hz).
prove (w + x) + (u + y + z) = (u + y + z) + (w + x).
exact add_SNo_com (w + x) (u + y + z)
                  (SNo_add_SNo w x Hw Hx)
                  (SNo_add_SNo_3 u y z Hu Hy Hz).
Qed.

Theorem add_SNo_1_ordsucc : forall n :e omega, n + 1 = ordsucc n.
let n. assume Hn.
rewrite <- add_nat_add_SNo n Hn 1 (nat_p_omega 1 nat_1).
prove add_nat n 1 = ordsucc n.
rewrite add_nat_SR n 0 nat_0.
prove ordsucc (add_nat n 0) = ordsucc n.
rewrite add_nat_0R.
reflexivity.
Qed.

Theorem add_SNo_eps_Lt : forall x, SNo x -> forall n :e omega, x < x + eps_ n.
let x. assume Hx. let n. assume Hn.
rewrite <- add_SNo_0R x Hx at 1.
prove x + 0 < x + eps_ n.
apply add_SNo_Lt2 x 0 (eps_ n) Hx SNo_0 (SNo_eps_ n Hn).
exact SNo_eps_pos n Hn.
Qed.

Theorem add_SNo_eps_Lt' : forall x y, SNo x -> SNo y -> forall n :e omega, x < y -> x < y + eps_ n.
let x y. assume Hx Hy. let n. assume Hn.
assume Hxy.
apply SNoLt_tra x y (y + eps_ n) Hx Hy (SNo_add_SNo y (eps_ n) Hy (SNo_eps_ n Hn)) Hxy.
prove y < y + eps_ n.
exact add_SNo_eps_Lt y Hy n Hn.
Qed.

Theorem SNoLt_minus_pos : forall x y, SNo x -> SNo y -> x < y -> 0 < y + - x.
let x y. assume Hx Hy Hxy.
apply add_SNo_minus_Lt2b y x 0 Hy Hx SNo_0.
prove 0 + x < y.
rewrite add_SNo_0L x Hx. exact Hxy.
Qed.

Theorem add_SNo_omega_In_cases: forall m, forall n :e omega, forall k, nat_p k -> m :e n + k -> m :e n \/ m + - n :e k.
let m n. assume Hn.
claim Ln: SNo n.
{ apply omega_SNo. exact Hn. }
apply nat_ind.
- prove m :e n + 0 -> m :e n \/ m + - n :e 0.
  rewrite add_SNo_0R n Ln.
  assume H1. apply orIL. exact H1.
- let k. assume Hk.
  assume IHk: m :e n + k -> m :e n \/ m + - n :e k.
  rewrite <- add_SNo_1_ordsucc k (nat_p_omega k Hk) at 1.
  rewrite add_SNo_assoc n k 1 Ln (nat_p_SNo k Hk) SNo_1.
  rewrite add_SNo_1_ordsucc (n + k) (add_SNo_In_omega n Hn k (nat_p_omega k Hk)).
  assume H1: m :e ordsucc (n + k).
  apply ordsuccE (n + k) m H1.
  + assume H2: m :e n + k. apply IHk H2.
    * assume H3: m :e n. apply orIL. exact H3.
    * assume H3: m + - n :e k. apply orIR.
      apply ordsuccI1. exact H3.
  + assume H2: m = n + k. apply orIR. rewrite H2.
    prove (n + k) + - n :e ordsucc k.
    rewrite add_SNo_com (n + k) (- n) (SNo_add_SNo n k Ln (nat_p_SNo k Hk)) (SNo_minus_SNo n Ln).
    rewrite add_SNo_minus_L2 n k Ln (nat_p_SNo k Hk).
    apply ordsuccI2.
Qed.

Theorem add_SNo_Lt4 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v -> x < w -> y < u -> z < v -> x + y + z < w + u + v.
let x y z w u v.
assume Hx Hy Hz Hw Hu Hv Hxw Hyu Hzv.
prove x + y + z < w + u + v.
apply add_SNo_Lt3 x (y + z) w (u + v) Hx (SNo_add_SNo y z Hy Hz) Hw (SNo_add_SNo u v Hu Hv) Hxw.
prove y + z < u + v.
exact add_SNo_Lt3 y z u v Hy Hz Hu Hv Hyu Hzv.
Qed.

Theorem add_SNo_3_3_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  x + y < z + w -> x + y + u < z + w + u.
let x y z w u. assume Hx Hy Hz Hw Hu H1.
rewrite add_SNo_assoc x y u Hx Hy Hu.
rewrite add_SNo_assoc z w u Hz Hw Hu.
prove (x + y) + u < (z + w) + u.
exact add_SNo_Lt1 (x + y) u (z + w) (SNo_add_SNo x y Hx Hy) Hu (SNo_add_SNo z w Hz Hw) H1.
Qed.

Theorem add_SNo_3_2_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  y + x < z + w -> x + u + y < z + w + u.
let x y z w u. assume Hx Hy Hz Hw Hu H1.
rewrite add_SNo_rotate_3_1 x u y Hx Hu Hy.
prove y + x + u < z + w + u.
exact add_SNo_3_3_3_Lt1 y x z w u Hy Hx Hz Hw Hu H1. 
Qed.

Theorem add_SNoCutP_lem : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> SNoCutP ({w + y|w :e Lx} :\/: {x + w|w :e Ly}) ({z + y|z :e Rx} :\/: {x + z|z :e Ry})
 /\ x + y = SNoCut ({w + y|w :e Lx} :\/: {x + w|w :e Ly}) ({z + y|z :e Rx} :\/: {x + z|z :e Ry}).
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply HLRx. assume H. apply H.
assume HLRx1: forall w :e Lx, SNo w.
assume HLRx2: forall z :e Rx, SNo z.
assume HLRx3: forall w :e Lx, forall z :e Rx, w < z.
apply HLRy. assume H. apply H.
assume HLRy1: forall w :e Ly, SNo w.
assume HLRy2: forall z :e Ry, SNo z.
assume HLRy3: forall w :e Ly, forall z :e Ry, w < z.
set Lx' := {w + y|w :e Lx}.
set Ly' := {x + w|w :e Ly}.
set Rx' := {z + y|z :e Rx}.
set Ry' := {x + z|z :e Ry}.
apply SNoCutP_SNoCut_impred Lx Rx HLRx.
rewrite <- Hxe.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc ((\/_ w :e Lx, ordsucc (SNoLev w)) :\/: (\/_ z :e Rx, ordsucc (SNoLev z))).
assume Hx3: forall w :e Lx, w < x.
assume Hx4: forall z :e Rx, x < z.
assume Hx5: (forall u, SNo u -> (forall w :e Lx, w < u) -> (forall z :e Rx, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u).
apply SNoCutP_SNoCut_impred Ly Ry HLRy.
rewrite <- Hye.
assume Hy1: SNo y.
assume Hy2: SNoLev y :e ordsucc ((\/_ w :e Ly, ordsucc (SNoLev w)) :\/: (\/_ z :e Ry, ordsucc (SNoLev z))).
assume Hy3: forall w :e Ly, w < y.
assume Hy4: forall z :e Ry, y < z.
assume Hy5: (forall u, SNo u -> (forall w :e Ly, w < u) -> (forall z :e Ry, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u).
claim L1: SNoCutP (Lx' :\/: Ly') (Rx' :\/: Ry').
{ prove (forall w :e Lx' :\/: Ly', SNo w)
     /\ (forall z :e Rx' :\/: Ry', SNo z)
     /\ (forall w :e Lx' :\/: Ly', forall z :e Rx' :\/: Ry', w < z).
  apply and3I.
  - let w. apply binunionE'.
    + assume Hw: w :e Lx'.
      apply ReplE_impred Lx (fun w => w + y) w Hw.
      let w'. assume Hw': w' :e Lx.
      assume Hwe: w = w' + y.
      rewrite Hwe.
      exact SNo_add_SNo w' y (HLRx1 w' Hw') Hy1.
    + assume Hw: w :e Ly'.
      apply ReplE_impred Ly (fun w => x + w) w Hw.
      let w'. assume Hw': w' :e Ly.
      assume Hwe: w = x + w'.
      rewrite Hwe.
      exact SNo_add_SNo x w' Hx1 (HLRy1 w' Hw').
  - let z. apply binunionE'.
    + assume Hz: z :e Rx'.
      apply ReplE_impred Rx (fun z => z + y) z Hz.
      let z'. assume Hz': z' :e Rx.
      assume Hze: z = z' + y.
      rewrite Hze.
      exact SNo_add_SNo z' y (HLRx2 z' Hz') Hy1.
    + assume Hz: z :e Ry'.
      apply ReplE_impred Ry (fun z => x + z) z Hz.
      let z'. assume Hz': z' :e Ry.
      assume Hze: z = x + z'.
      rewrite Hze.
      exact SNo_add_SNo x z' Hx1 (HLRy2 z' Hz').
  - let w. apply binunionE'.
    + assume Hw: w :e Lx'.
      apply ReplE_impred Lx (fun w => w + y) w Hw.
      let w'. assume Hw': w' :e Lx.
      claim Lw': SNo w'.
      { exact HLRx1 w' Hw'. }
      assume Hwe: w = w' + y.
      rewrite Hwe.
      let z. apply binunionE'.
      * assume Hz: z :e Rx'.
        apply ReplE_impred Rx (fun z => z + y) z Hz.
        let z'. assume Hz': z' :e Rx.
        assume Hze: z = z' + y.
        claim Lz': SNo z'.
        { exact HLRx2 z' Hz'. }
        rewrite Hze.
        prove w' + y < z' + y.
        apply add_SNo_Lt1 w' y z' Lw' Hy1 Lz'.
        prove w' < z'.
        exact SNoLt_tra w' x z' Lw' Hx1 Lz' (Hx3 w' Hw') (Hx4 z' Hz').
      * { assume Hz: z :e Ry'.
          apply ReplE_impred Ry (fun z => x + z) z Hz.
          let z'. assume Hz': z' :e Ry.
          assume Hze: z = x + z'.
          claim Lz': SNo z'.
          { exact HLRy2 z' Hz'. }
          rewrite Hze.
          prove w' + y < x + z'.
          apply add_SNo_Lt3 w' y x z' Lw' Hy1 Hx1 Lz'.
          - prove w' < x. exact Hx3 w' Hw'.
          - prove y < z'. exact Hy4 z' Hz'.
        }
    + assume Hw: w :e Ly'.
      apply ReplE_impred Ly (fun w => x + w) w Hw.
      let w'. assume Hw': w' :e Ly.
      assume Hwe: w = x + w'.
      claim Lw': SNo w'.
      { exact HLRy1 w' Hw'. }
      rewrite Hwe.
      let z. apply binunionE'.
      * { assume Hz: z :e Rx'.
          apply ReplE_impred Rx (fun z => z + y) z Hz.
          let z'. assume Hz': z' :e Rx.
          assume Hze: z = z' + y.
          claim Lz': SNo z'.
          { exact HLRx2 z' Hz'. }
          rewrite Hze.
          prove x + w' < z' + y.
          apply add_SNo_Lt3 x w' z' y Hx1 Lw' Lz' Hy1.
          - prove x < z'. exact Hx4 z' Hz'.
          - prove w' < y. exact Hy3 w' Hw'.
        }
      * assume Hz: z :e Ry'.
        apply ReplE_impred Ry (fun z => x + z) z Hz.
        let z'. assume Hz': z' :e Ry.
        assume Hze: z = x + z'.
        claim Lz': SNo z'.
        { exact HLRy2 z' Hz'. }
        rewrite Hze.
        prove x + w' < x + z'.
        apply add_SNo_Lt2 x w' z' Hx1 Lw' Lz'.
        prove w' < z'.
        exact SNoLt_tra w' y z' Lw' Hy1 Lz' (Hy3 w' Hw') (Hy4 z' Hz').
}
apply andI (SNoCutP (Lx' :\/: Ly') (Rx' :\/: Ry'))
           (x + y = SNoCut (Lx' :\/: Ly') (Rx' :\/: Ry'))
           L1.
prove x + y = SNoCut (Lx' :\/: Ly') (Rx' :\/: Ry').
rewrite add_SNo_eq x Hx1 y Hy1.
prove SNoCut ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y})
    = SNoCut (Lx' :\/: Ly') (Rx' :\/: Ry').
set v := SNoCut (Lx' :\/: Ly') (Rx' :\/: Ry').
apply SNoCutP_SNoCut_impred (Lx' :\/: Ly') (Rx' :\/: Ry') L1.
assume Hv1: SNo v.
assume Hv2: SNoLev v :e ordsucc ((\/_ w :e Lx' :\/: Ly', ordsucc (SNoLev w)) :\/: (\/_ z :e Rx' :\/: Ry', ordsucc (SNoLev z))).
assume Hv3: forall w :e Lx' :\/: Ly', w < v.
assume Hv4: forall z :e Rx' :\/: Ry', v < z.
assume Hv5: forall u, SNo u -> (forall w :e Lx' :\/: Ly', w < u) -> (forall z :e Rx' :\/: Ry', u < z) -> SNoLev v c= SNoLev u /\ SNoEq_ (SNoLev v) v u.
apply SNoCut_ext ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}) (Lx' :\/: Ly') (Rx' :\/: Ry').
- exact add_SNo_SNoCutP x y Hx1 Hy1.
- exact L1.
- prove forall w :e {w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}, w < v.
  let w. apply binunionE'.
  + assume Hw.
    apply ReplE_impred (SNoL x) (fun w => w + y) w Hw.
    let w'. assume Hw': w' :e SNoL x.
    assume Hwe: w = w' + y.
    apply SNoL_E x Hx1 w' Hw'.
    assume Hw'1: SNo w'.
    assume Hw'2: SNoLev w' :e SNoLev x.
    assume Hw'3: w' < x.
    claim L2: exists w'' :e Lx, w' <= w''.
    { apply dneg.
      assume HC.
      claim L2a: SNoLev x c= SNoLev w' /\ SNoEq_ (SNoLev x) x w'.
      { apply Hx5 w' Hw'1.
        - prove forall w'' :e Lx, w'' < w'.
          let w''. assume Hw''1.
          apply SNoLtLe_or w'' w' (HLRx1 w'' Hw''1) Hw'1.
          + assume H. exact H.
          + assume Hw''2: w' <= w''. prove False. apply HC.
            witness w''. apply andI.
            * exact Hw''1.
            * exact Hw''2.
        - prove forall z :e Rx, w' < z.
          let z. assume Hz.
          apply SNoLt_tra w' x z Hw'1 Hx1 (HLRx2 z Hz).
          + prove w' < x. exact Hw'3.
          + prove x < z. exact Hx4 z Hz.
      }
      apply L2a.
      assume Hxw': SNoLev x c= SNoLev w'. assume _.
      apply In_irref (SNoLev w').
      prove SNoLev w' :e SNoLev w'.
      apply Hxw'. exact Hw'2.
    }
    apply L2.
    let w''. assume H. apply H.
    assume Hw''1: w'' :e Lx.
    assume Hw''2: w' <= w''.
    rewrite Hwe.
    prove w' + y < v.
    apply SNoLeLt_tra (w' + y) (w'' + y) v
                      (SNo_add_SNo w' y Hw'1 Hy1)
                      (SNo_add_SNo w'' y (HLRx1 w'' Hw''1) Hy1)
                      Hv1.
    * prove w' + y <= w'' + y.
      apply add_SNo_Le1 w' y w'' Hw'1 Hy1 (HLRx1 w'' Hw''1).
      prove w' <= w''.
      exact Hw''2.
    * prove w'' + y < v.
      apply Hv3.
      prove w'' + y :e Lx' :\/: Ly'.
      apply binunionI1.
      prove w'' + y :e Lx'.
      exact ReplI Lx (fun w => w + y) w'' Hw''1.
  + assume Hw.
    apply ReplE_impred (SNoL y) (fun w => x + w) w Hw.
    let w'. assume Hw': w' :e SNoL y.
    assume Hwe: w = x + w'.
    apply SNoL_E y Hy1 w' Hw'.
    assume Hw'1: SNo w'.
    assume Hw'2: SNoLev w' :e SNoLev y.
    assume Hw'3: w' < y.
    claim L3: exists w'' :e Ly, w' <= w''.
    { apply dneg.
      assume HC.
      claim L3a: SNoLev y c= SNoLev w' /\ SNoEq_ (SNoLev y) y w'.
      { apply Hy5 w' Hw'1.
        - prove forall w'' :e Ly, w'' < w'.
          let w''. assume Hw''1.
          apply SNoLtLe_or w'' w' (HLRy1 w'' Hw''1) Hw'1.
          + assume H. exact H.
          + assume Hw''2: w' <= w''. prove False. apply HC.
            witness w''. apply andI.
            * exact Hw''1.
            * exact Hw''2.
        - prove forall z :e Ry, w' < z.
          let z. assume Hz.
          apply SNoLt_tra w' y z Hw'1 Hy1 (HLRy2 z Hz).
          + prove w' < y. exact Hw'3.
          + prove y < z. exact Hy4 z Hz.
      }
      apply L3a.
      assume Hyw': SNoLev y c= SNoLev w'. assume _.
      apply In_irref (SNoLev w').
      prove SNoLev w' :e SNoLev w'.
      apply Hyw'. exact Hw'2.
    }
    apply L3.
    let w''. assume H. apply H.
    assume Hw''1: w'' :e Ly.
    assume Hw''2: w' <= w''.
    rewrite Hwe.
    prove x + w' < v.
    apply SNoLeLt_tra (x + w') (x + w'') v
                      (SNo_add_SNo x w' Hx1 Hw'1)
                      (SNo_add_SNo x w'' Hx1 (HLRy1 w'' Hw''1))
                      Hv1.
    * prove x + w' <= x + w''.
      apply add_SNo_Le2 x w' w'' Hx1 Hw'1 (HLRy1 w'' Hw''1).
      prove w' <= w''.
      exact Hw''2.
    * prove x + w'' < v.
      apply Hv3.
      prove x + w'' :e Lx' :\/: Ly'.
      apply binunionI2.
      prove x + w'' :e Ly'.
      exact ReplI Ly (fun w => x + w) w'' Hw''1.
- prove forall z :e {z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}, v < z.
  let z. apply binunionE'.
  + assume Hz.
    apply ReplE_impred (SNoR x) (fun z => z + y) z Hz.
    let z'. assume Hz': z' :e SNoR x.
    assume Hze: z = z' + y.
    apply SNoR_E x Hx1 z' Hz'.
    assume Hz'1: SNo z'.
    assume Hz'2: SNoLev z' :e SNoLev x.
    assume Hz'3: x < z'.
    claim L4: exists z'' :e Rx, z'' <= z'.
    { apply dneg.
      assume HC.
      claim L4a: SNoLev x c= SNoLev z' /\ SNoEq_ (SNoLev x) x z'.
      { apply Hx5 z' Hz'1.
        - prove forall w :e Lx, w < z'.
          let w. assume Hw.
          apply SNoLt_tra w x z' (HLRx1 w Hw) Hx1 Hz'1.
          + prove w < x. exact Hx3 w Hw.
          + prove x < z'. exact Hz'3.
        - prove forall z'' :e Rx, z' < z''.
          let z''. assume Hz''1.
          apply SNoLtLe_or z' z'' Hz'1 (HLRx2 z'' Hz''1).
          + assume H. exact H.
          + assume Hz''2: z'' <= z'. prove False. apply HC.
            witness z''. apply andI.
            * exact Hz''1.
            * exact Hz''2.
      }
      apply L4a.
      assume Hxz': SNoLev x c= SNoLev z'. assume _.
      apply In_irref (SNoLev z').
      prove SNoLev z' :e SNoLev z'.
      apply Hxz'. exact Hz'2.
    }
    apply L4.
    let z''. assume H. apply H.
    assume Hz''1: z'' :e Rx.
    assume Hz''2: z'' <= z'.
    rewrite Hze.
    prove v < z' + y.
    apply SNoLtLe_tra v (z'' + y) (z' + y)
                      Hv1
                      (SNo_add_SNo z'' y (HLRx2 z'' Hz''1) Hy1)
                      (SNo_add_SNo z' y Hz'1 Hy1).
    * prove v < z'' + y.
      apply Hv4.
      prove z'' + y :e Rx' :\/: Ry'.
      apply binunionI1.
      prove z'' + y :e Rx'.
      exact ReplI Rx (fun z => z + y) z'' Hz''1.
    * prove z'' + y <= z' + y.
      apply add_SNo_Le1 z'' y z' (HLRx2 z'' Hz''1) Hy1 Hz'1.
      prove z'' <= z'.
      exact Hz''2.
  + assume Hz.
    apply ReplE_impred (SNoR y) (fun z => x + z) z Hz.
    let z'. assume Hz': z' :e SNoR y.
    assume Hze: z = x + z'.
    apply SNoR_E y Hy1 z' Hz'.
    assume Hz'1: SNo z'.
    assume Hz'2: SNoLev z' :e SNoLev y.
    assume Hz'3: y < z'.
    claim L5: exists z'' :e Ry, z'' <= z'.
    { apply dneg.
      assume HC.
      claim L5a: SNoLev y c= SNoLev z' /\ SNoEq_ (SNoLev y) y z'.
      { apply Hy5 z' Hz'1.
        - prove forall w :e Ly, w < z'.
          let w. assume Hw.
          apply SNoLt_tra w y z' (HLRy1 w Hw) Hy1 Hz'1.
          + prove w < y. exact Hy3 w Hw.
          + prove y < z'. exact Hz'3.
        - prove forall z'' :e Ry, z' < z''.
          let z''. assume Hz''1.
          apply SNoLtLe_or z' z'' Hz'1 (HLRy2 z'' Hz''1).
          + assume H. exact H.
          + assume Hz''2: z'' <= z'. prove False. apply HC.
            witness z''. apply andI.
            * exact Hz''1.
            * exact Hz''2.
      }
      apply L5a.
      assume Hyz': SNoLev y c= SNoLev z'. assume _.
      apply In_irref (SNoLev z').
      prove SNoLev z' :e SNoLev z'.
      apply Hyz'. exact Hz'2.
    }
    apply L5.
    let z''. assume H. apply H.
    assume Hz''1: z'' :e Ry.
    assume Hz''2: z'' <= z'.
    rewrite Hze.
    prove v < x + z'.
    apply SNoLtLe_tra v (x + z'') (x + z')
                      Hv1
                      (SNo_add_SNo x z'' Hx1 (HLRy2 z'' Hz''1))
                      (SNo_add_SNo x z' Hx1 Hz'1).
    * prove v < x + z''.
      apply Hv4.
      prove x + z'' :e Rx' :\/: Ry'.
      apply binunionI2.
      prove x + z'' :e Ry'.
      exact ReplI Ry (fun z => x + z) z'' Hz''1.
    * prove x + z'' <= x + z'.
      apply add_SNo_Le2 x z'' z' Hx1 (HLRy2 z'' Hz''1) Hz'1.
      prove z'' <= z'.
      exact Hz''2.
- rewrite <- add_SNo_eq x Hx1 y Hy1.
  prove forall w :e Lx' :\/: Ly', w < x + y.
  let w. apply binunionE'.
  + assume Hw: w :e Lx'.
    apply ReplE_impred Lx (fun w => w + y) w Hw.
    let w'. assume Hw': w' :e Lx.
    assume Hwe: w = w' + y.
    rewrite Hwe.
    prove w' + y < x + y.
    apply add_SNo_Lt1 w' y x (HLRx1 w' Hw') Hy1 Hx1.
    prove w' < x.
    exact Hx3 w' Hw'.
  + assume Hw: w :e Ly'.
    apply ReplE_impred Ly (fun w => x + w) w Hw.
    let w'. assume Hw': w' :e Ly.
    assume Hwe: w = x + w'.
    rewrite Hwe.
    prove x + w' < x + y.
    apply add_SNo_Lt2 x w' y Hx1 (HLRy1 w' Hw') Hy1.
    prove w' < y.
    exact Hy3 w' Hw'.
- rewrite <- add_SNo_eq x Hx1 y Hy1.
  prove forall z :e Rx' :\/: Ry', x + y < z.
  let z. apply binunionE'.
  + assume Hz: z :e Rx'.
    apply ReplE_impred Rx (fun z => z + y) z Hz.
    let z'. assume Hz': z' :e Rx.
    assume Hze: z = z' + y.
    rewrite Hze.
    prove x + y < z' + y.
    apply add_SNo_Lt1 x y z' Hx1 Hy1 (HLRx2 z' Hz').
    prove x < z'.
    exact Hx4 z' Hz'.
  + assume Hz: z :e Ry'.
    apply ReplE_impred Ry (fun z => x + z) z Hz.
    let z'. assume Hz': z' :e Ry.
    assume Hze: z = x + z'.
    rewrite Hze.
    prove x + y < x + z'.
    apply add_SNo_Lt2 x y z' Hx1 Hy1 (HLRy2 z' Hz').
    prove y < z'.
    exact Hy4 z' Hz'.
Qed.

Theorem add_SNoCutP_gen : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> SNoCutP ({w + y|w :e Lx} :\/: {x + w|w :e Ly}) ({z + y|z :e Rx} :\/: {x + z|z :e Ry}).
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply add_SNoCutP_lem Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
assume H _. exact H.
Qed.

Theorem add_SNoCut_eq : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> x + y = SNoCut ({w + y|w :e Lx} :\/: {x + w|w :e Ly}) ({z + y|z :e Rx} :\/: {x + z|z :e Ry}).
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply add_SNoCutP_lem Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
assume _ H. exact H.
Qed.

Theorem add_SNo_SNoCut_L_interpolate : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> forall u :e SNoL (x + y), (exists v :e Lx, u <= v + y) \/ (exists v :e Ly, u <= x + v).
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply HLRx. assume H. apply H.
assume HLRx1: forall w :e Lx, SNo w.
assume HLRx2: forall z :e Rx, SNo z.
assume HLRx3: forall w :e Lx, forall z :e Rx, w < z.
apply HLRy. assume H. apply H.
assume HLRy1: forall w :e Ly, SNo w.
assume HLRy2: forall z :e Ry, SNo z.
assume HLRy3: forall w :e Ly, forall z :e Ry, w < z.
apply SNoCutP_SNoCut_impred Lx Rx HLRx.
rewrite <- Hxe.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc ((\/_ w :e Lx, ordsucc (SNoLev w)) :\/: (\/_ z :e Rx, ordsucc (SNoLev z))).
assume Hx3: forall w :e Lx, w < x.
assume Hx4: forall z :e Rx, x < z.
assume Hx5: (forall u, SNo u -> (forall w :e Lx, w < u) -> (forall z :e Rx, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u).
apply SNoCutP_SNoCut_impred Ly Ry HLRy.
rewrite <- Hye.
assume Hy1: SNo y.
assume Hy2: SNoLev y :e ordsucc ((\/_ w :e Ly, ordsucc (SNoLev w)) :\/: (\/_ z :e Ry, ordsucc (SNoLev z))).
assume Hy3: forall w :e Ly, w < y.
assume Hy4: forall z :e Ry, y < z.
assume Hy5: (forall u, SNo u -> (forall w :e Ly, w < u) -> (forall z :e Ry, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u).
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx1 Hy1. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x + y) -> u < x + y -> (exists v :e Lx, u <= v + y) \/ (exists v :e Ly, u <= x + v).
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x + y) -> z < x + y -> (exists v :e Lx, z <= v + y) \/ (exists v :e Ly, z <= x + v).
  assume Hu2: SNoLev u :e SNoLev (x + y).
  assume Hu3: u < x + y.
  apply dneg.
  assume HNC: ~((exists v :e Lx, u <= v + y) \/ (exists v :e Ly, u <= x + v)).
  apply SNoLt_irref u.
  prove u < u.
  apply SNoLtLe_tra u (x + y) u Hu1 Lxy Hu1 Hu3.
  prove x + y <= u.
  set Lxy1 := {w + y|w :e Lx}.
  set Lxy2 := {x + w|w :e Ly}.
  set Rxy1 := {z + y|z :e Rx}.
  set Rxy2 := {x + z|z :e Ry}.
  rewrite add_SNoCut_eq Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
  prove SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) <= u.
  rewrite SNo_eta u Hu1.
  prove SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) <= SNoCut (SNoL u) (SNoR u).
  apply SNoCut_Le (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) (SNoL u) (SNoR u).
  - exact add_SNoCutP_gen Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
  - exact SNoCutP_SNoL_SNoR u Hu1.
  - rewrite <- SNo_eta u Hu1.
    prove forall w :e Lxy1 :\/: Lxy2, w < u.
    let w. assume Hw: w :e Lxy1 :\/: Lxy2.
    apply binunionE Lxy1 Lxy2 w Hw.
    + assume Hw2: w :e Lxy1.
      prove w < u.
      apply ReplE_impred Lx (fun w => w + y) w Hw2.
      let v.
      assume Hv: v :e Lx.
      assume Hwv: w = v + y.
      rewrite Hwv.
      prove v + y < u.
      claim Lvy: SNo (v + y).
      { exact SNo_add_SNo v y (HLRx1 v Hv) Hy1. }
      apply SNoLtLe_or (v+y) u Lvy Hu1.
      * assume H1: v + y < u. exact H1.
      * { assume H1: u <= v+y.
          prove False.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - prove v :e Lx. exact Hv.
          - prove u <= v + y. exact H1.
        }
    + assume Hw2: w :e Lxy2.
      prove w < u.
      apply ReplE_impred Ly (fun w => x + w) w Hw2.
      let v.
      assume Hv: v :e Ly.
      assume Hwv: w = x + v.
      rewrite Hwv.
      prove x + v < u.
      claim Lxv: SNo (x + v).
      { exact SNo_add_SNo x v Hx1 (HLRy1 v Hv). }
      apply SNoLtLe_or (x+v) u Lxv Hu1.
      * assume H1: x + v < u. exact H1.
      * { assume H1: u <= x+v.
          prove False.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - prove v :e Ly. exact Hv.
          - prove u <= x + v. exact H1.
        }
  - rewrite <- add_SNoCut_eq Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
    prove forall z :e SNoR u, x + y < z.
    let z. assume Hz: z :e SNoR u.
    apply SNoR_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: u < z.
    apply SNoLt_trichotomy_or (x + y) z Lxy Hz1.
    assume H1. apply H1.
    + assume H1: x + y < z. exact H1.
    + assume H1: x + y = z.
      prove False.
      apply In_no2cycle (SNoLev z) (SNoLev u) Hz2.
      prove SNoLev u :e SNoLev z.
      rewrite <- H1.
      exact Hu2.
    + assume H1: z < x + y.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { exact SNoR_SNoS_ u z Hz. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { apply SNoLev_ordinal (x+y) Lxy. assume Hxy1 _.
        exact Hxy1 (SNoLev u) Hu2 (SNoLev z) Hz2.
      }
      apply IH z Lz1 Lz2 H1.
      * { assume H2: exists v :e Lx, z <= v + y.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e Lx.
          assume H3: z <= v + y.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - exact Hv.
          - prove u <= v + y.
            apply SNoLe_tra u z (v + y) Hu1 Hz1 (SNo_add_SNo v y (HLRx1 v Hv) Hy1).
            + prove u <= z. apply SNoLtLe. exact Hz3.
            + prove z <= v + y. exact H3.
        }
      * { assume H2: exists v :e Ly, z <= x + v.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e Ly.
          assume H3: z <= x + v.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - exact Hv.
          - prove u <= x + v.
            apply SNoLe_tra u z (x + v) Hu1 Hz1 (SNo_add_SNo x v Hx1 (HLRy1 v Hv)).
            + prove u <= z. apply SNoLtLe. exact Hz3.
            + prove z <= x + v. exact H3.
        }
}
let u.
assume Hu: u :e SNoL (x+y).
apply SNoL_E (x+y) Lxy u Hu.
assume Hu1: SNo u.
assume Hu2: SNoLev u :e SNoLev (x + y).
assume Hu3: u < x + y.
exact LI u Hu1 Hu2 Hu3.
Qed.

Theorem add_SNo_SNoCut_R_interpolate : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> forall u :e SNoR (x + y), (exists v :e Rx, v + y <= u) \/ (exists v :e Ry, x + v <= u).
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply HLRx. assume H. apply H.
assume HLRx1: forall w :e Lx, SNo w.
assume HLRx2: forall z :e Rx, SNo z.
assume HLRx3: forall w :e Lx, forall z :e Rx, w < z.
apply HLRy. assume H. apply H.
assume HLRy1: forall w :e Ly, SNo w.
assume HLRy2: forall z :e Ry, SNo z.
assume HLRy3: forall w :e Ly, forall z :e Ry, w < z.
apply SNoCutP_SNoCut_impred Lx Rx HLRx.
rewrite <- Hxe.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc ((\/_ w :e Lx, ordsucc (SNoLev w)) :\/: (\/_ z :e Rx, ordsucc (SNoLev z))).
assume Hx3: forall w :e Lx, w < x.
assume Hx4: forall z :e Rx, x < z.
assume Hx5: (forall u, SNo u -> (forall w :e Lx, w < u) -> (forall z :e Rx, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u).
apply SNoCutP_SNoCut_impred Ly Ry HLRy.
rewrite <- Hye.
assume Hy1: SNo y.
assume Hy2: SNoLev y :e ordsucc ((\/_ w :e Ly, ordsucc (SNoLev w)) :\/: (\/_ z :e Ry, ordsucc (SNoLev z))).
assume Hy3: forall w :e Ly, w < y.
assume Hy4: forall z :e Ry, y < z.
assume Hy5: (forall u, SNo u -> (forall w :e Ly, w < u) -> (forall z :e Ry, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u).
claim Lxy: SNo (x + y).
{ exact SNo_add_SNo x y Hx1 Hy1. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x + y) -> x + y < u -> (exists v :e Rx, v + y <= u) \/ (exists v :e Ry, x + v <= u).
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x + y) -> x + y < z -> (exists v :e Rx, v + y <= z) \/ (exists v :e Ry, x + v <= z).
  assume Hu2: SNoLev u :e SNoLev (x + y).
  assume Hu3: x + y < u.
  apply dneg.
  assume HNC: ~((exists v :e Rx, v + y <= u) \/ (exists v :e Ry, x + v <= u)).
  apply SNoLt_irref u.
  prove u < u.
  apply (fun H: u <= x+y => SNoLeLt_tra u (x + y) u Hu1 Lxy Hu1 H Hu3).
  prove u <= x + y.
  set Lxy1 := {w + y|w :e Lx}.
  set Lxy2 := {x + w|w :e Ly}.
  set Rxy1 := {z + y|z :e Rx}.
  set Rxy2 := {x + z|z :e Ry}.
  rewrite add_SNoCut_eq Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
  prove u <= SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  rewrite SNo_eta u Hu1.
  prove SNoCut (SNoL u) (SNoR u) <= SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  apply SNoCut_Le (SNoL u) (SNoR u) (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
  - exact SNoCutP_SNoL_SNoR u Hu1.
  - exact add_SNoCutP_gen Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
  - rewrite <- add_SNoCut_eq Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
    prove forall z :e SNoL u, z < x + y.
    let z. assume Hz: z :e SNoL u.
    apply SNoL_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: z < u.
    apply SNoLt_trichotomy_or z (x + y) Hz1 Lxy.
    assume H1. apply H1.
    + assume H1: z < x + y. exact H1.
    + assume H1: z = x + y.
      prove False.
      apply In_no2cycle (SNoLev z) (SNoLev u) Hz2.
      prove SNoLev u :e SNoLev z.
      rewrite H1.
      exact Hu2.
    + assume H1: x + y < z.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { exact SNoL_SNoS_ u z Hz. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { apply SNoLev_ordinal (x+y) Lxy. assume Hxy1 _.
        exact Hxy1 (SNoLev u) Hu2 (SNoLev z) Hz2.
      }
      apply IH z Lz1 Lz2 H1.
      * { assume H2: exists v :e Rx, v + y <= z.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e Rx.
          assume H3: v + y <= z.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - exact Hv.
          - prove v + y <= u.
            apply SNoLe_tra (v + y) z u (SNo_add_SNo v y (HLRx2 v Hv) Hy1) Hz1 Hu1.
            + prove v + y <= z. exact H3.
            + prove z <= u. apply SNoLtLe. exact Hz3.
        }
      * { assume H2: exists v :e Ry, x + v <= z.
          apply H2.
          let v. assume H3. apply H3.
          assume Hv: v :e Ry.
          assume H3: x + v <= z.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - exact Hv.
          - prove x + v <= u.
            apply SNoLe_tra (x + v) z u (SNo_add_SNo x v Hx1 (HLRy2 v Hv)) Hz1 Hu1.
            + prove x + v <= z. exact H3.
            + prove z <= u. apply SNoLtLe. exact Hz3.
        }
  - rewrite <- SNo_eta u Hu1.
    prove forall w :e Rxy1 :\/: Rxy2, u < w.
    let w. assume Hw: w :e Rxy1 :\/: Rxy2.
    apply binunionE Rxy1 Rxy2 w Hw.
    + assume Hw2: w :e Rxy1.
      prove u < w.
      apply ReplE_impred Rx (fun w => w + y) w Hw2.
      let v.
      assume Hv: v :e Rx.
      assume Hwv: w = v + y.
      rewrite Hwv.
      prove u < v + y.
      claim Lvy: SNo (v + y).
      { exact SNo_add_SNo v y (HLRx2 v Hv) Hy1. }
      apply SNoLtLe_or u (v+y) Hu1 Lvy.
      * assume H1: u < v + y. exact H1.
      * { assume H1: v+y <= u.
          prove False.
          apply HNC.
          apply orIL.
          witness v.
          apply andI.
          - prove v :e Rx. exact Hv.
          - prove v + y <= u. exact H1.
        }
    + assume Hw2: w :e Rxy2.
      prove u < w.
      apply ReplE_impred Ry (fun w => x + w) w Hw2.
      let v.
      assume Hv: v :e Ry.
      assume Hwv: w = x + v.
      rewrite Hwv.
      prove u < x + v.
      claim Lxv: SNo (x + v).
      { exact SNo_add_SNo x v Hx1 (HLRy2 v Hv). }
      apply SNoLtLe_or u (x+v) Hu1 Lxv.
      * assume H1: u < x + v. exact H1.
      * { assume H1: x+v <= u.
          prove False.
          apply HNC.
          apply orIR.
          witness v.
          apply andI.
          - prove v :e Ry. exact Hv.
          - prove x + v <= u. exact H1.
        }
}
let u.
assume Hu: u :e SNoR (x+y).
apply SNoR_E (x+y) Lxy u Hu.
assume Hu1: SNo u.
assume Hu2: SNoLev u :e SNoLev (x + y).
assume Hu3: x + y < u.
exact LI u Hu1 Hu2 Hu3.
Qed.

Theorem add_SNo_minus_Lt12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v < w + u + z
 -> x + y + - z < w + u + - v.
let x y z w u v.
assume Hx Hy Hz Hw Hu Hv.
assume H1: x + y + v < w + u + z.
prove x + y + - z < w + u + - v.
claim Lmv: SNo (- v).
{ exact SNo_minus_SNo v Hv. }
apply add_SNo_minus_Lt1b3 x y z (w + u + - v) Hx Hy Hz (SNo_add_SNo_3 w u (- v) Hw Hu Lmv).
prove x + y < (w + u + - v) + z.
rewrite add_SNo_assoc w u (- v) Hw Hu Lmv.
prove x + y < ((w + u) + - v) + z.
rewrite add_SNo_com_3b_1_2 (w + u) (- v) z (SNo_add_SNo w u Hw Hu) Lmv Hz.
prove x + y < ((w + u) + z) + - v.
apply add_SNo_minus_Lt2b ((w + u) + z) v (x + y) (SNo_add_SNo (w + u) z (SNo_add_SNo w u Hw Hu) Hz) Hv (SNo_add_SNo x y Hx Hy).
prove (x + y) + v < (w + u) + z.
rewrite <- add_SNo_assoc x y v Hx Hy Hv.
rewrite <- add_SNo_assoc w u z Hw Hu Hz.
exact H1.
Qed.

Theorem add_SNo_Le1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y <= z + y -> x <= z.
let x y z. assume Hx Hy Hz H1.
prove x <= z.
claim L1: (x + y) + - y = x.
{ exact add_SNo_minus_R2 x y Hx Hy. }
claim L2: (z + y) + - y = z.
{ exact add_SNo_minus_R2 z y Hz Hy. }
rewrite <- L1. rewrite <- L2.
prove (x + y) + - y <= (z + y) + - y.
exact add_SNo_Le1 (x + y) (- y) (z + y)
                  (SNo_add_SNo x y Hx Hy)
                  (SNo_minus_SNo y Hy)
                  (SNo_add_SNo z y Hz Hy)
                  H1.
Qed.

Theorem add_SNo_minus_Le1b : forall x y z, SNo x -> SNo y -> SNo z -> x <= z + y -> x + - y <= z.
let x y z. assume Hx Hy Hz H1.
apply add_SNo_Le1_cancel (x + - y) y z (SNo_add_SNo x (- y) Hx (SNo_minus_SNo y Hy)) Hy Hz.
prove (x + - y) + y <= z + y.
rewrite <- add_SNo_assoc x (- y) y Hx (SNo_minus_SNo y Hy) Hy.
rewrite add_SNo_minus_SNo_linv y Hy.
rewrite add_SNo_0R x Hx.
exact H1.
Qed.

Theorem add_SNo_minus_Le1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y <= w + z -> x + y + - z <= w.
let x y z w. assume Hx Hy Hz Hw H1.
prove x + y + - z <= w.
rewrite add_SNo_assoc x y (- z) Hx Hy (SNo_minus_SNo z Hz).
prove (x + y) + - z <= w.
apply add_SNo_minus_Le1b (x + y) z w (SNo_add_SNo x y Hx Hy) Hz Hw.
exact H1.
Qed.

Theorem add_SNo_minus_Le12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v <= w + u + z
 -> x + y + - z <= w + u + - v.
let x y z w u v.
assume Hx Hy Hz Hw Hu Hv.
assume H1: x + y + v <= w + u + z.
prove x + y + - z <= w + u + - v.
claim Lmv: SNo (- v).
{ exact SNo_minus_SNo v Hv. }
apply add_SNo_minus_Le1b3 x y z (w + u + - v) Hx Hy Hz (SNo_add_SNo_3 w u (- v) Hw Hu Lmv).
prove x + y <= (w + u + - v) + z.
rewrite add_SNo_assoc w u (- v) Hw Hu Lmv.
prove x + y <= ((w + u) + - v) + z.
rewrite add_SNo_com_3b_1_2 (w + u) (- v) z (SNo_add_SNo w u Hw Hu) Lmv Hz.
prove x + y <= ((w + u) + z) + - v.
apply add_SNo_minus_Le2b ((w + u) + z) v (x + y) (SNo_add_SNo (w + u) z (SNo_add_SNo w u Hw Hu) Hz) Hv (SNo_add_SNo x y Hx Hy).
prove (x + y) + v <= (w + u) + z.
rewrite <- add_SNo_assoc x y v Hx Hy Hv.
rewrite <- add_SNo_assoc w u z Hw Hu Hz.
exact H1.
Qed.

End SurrealAdd.

Opaque add_SNo.
