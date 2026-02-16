(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.
Axiom Eps_i_ax : forall P:set->prop, forall x:set, P x -> P (Eps_i P).
Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
(* Unicode /\ "2227" *)
Infix /\ 780 left := and.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
(* Unicode \/ "2228" *)
Infix \/ 785 left := or.
Definition iff : prop -> prop -> prop := fun A B:prop => and (A -> B) (B -> A).
(* Unicode <-> "2194" *)
Infix <-> 805 := iff.
Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
Definition neq : A->A->prop := fun x y:A => ~ eq x y.
End Eq.
Infix = 502 := eq.
(* Unicode <> "2260" *)
Infix <> 502 := neq.
Section FE.
Variable A B : SType.
Axiom func_ext : forall f g : A -> B , (forall x : A , f x = g x) -> f = g.
End FE.
Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
Axiom prop_ext : forall p q:prop, iff p q -> p = q.
Parameter In:set->set->prop.
Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.
Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.
Axiom In_ind : forall P:set->prop, (forall X:set, (forall x :e X, P x) -> P X) -> forall X:set, P X.
Binder+ exists , := ex; and.
Parameter Empty : set.
Axiom EmptyAx : ~exists x:set, x :e Empty.
(* Unicode Union "22C3" *)
Parameter Union : set->set.
Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.
(* Unicode Power "1D4AB" *)
Parameter Power : set->set.
Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Axiom ReplEq : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} <-> exists x :e A, y = F x.
Definition TransSet : set->prop := fun U:set => forall x :e U, x c= U.
Definition Union_closed : set->prop := fun U:set => forall X:set, X :e U -> Union X :e U.
Definition Power_closed : set->prop := fun U:set => forall X:set, X :e U -> Power X :e U.
Definition Repl_closed : set->prop := fun U:set => forall X:set, X :e U -> forall F:set->set,
   (forall x:set, x :e X -> F x :e U) -> {F x|x :e X} :e U.
Definition ZF_closed : set->prop := fun U:set =>
   Union_closed U
/\ Power_closed U
/\ Repl_closed U.
Parameter UnivOf : set->set.
Axiom UnivOf_In : forall N:set, N :e UnivOf N.
Axiom UnivOf_TransSet : forall N:set, TransSet (UnivOf N).
Axiom UnivOf_ZF_closed : forall N:set, ZF_closed (UnivOf N).
Axiom UnivOf_Min : forall N U:set, N :e U
  -> TransSet U
  -> ZF_closed U
  -> UnivOf N c= U.

Theorem andI : forall (A B : prop), A -> B -> A /\ B.
exact (fun A B a b P H => H a b).
Qed.

Theorem orIL : forall (A B : prop), A -> A \/ B.
exact (fun A B a P H1 H2 => H1 a).
Qed.

Theorem orIR : forall (A B : prop), B -> A \/ B.
exact (fun A B b P H1 H2 => H2 b).
Qed.

Theorem iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
exact (fun A B => andI (A -> B) (B -> A)).
Qed.

Theorem pred_ext : forall P Q:set -> prop, (forall x, P x <-> Q x) -> P = Q.
let P Q. assume H1. apply func_ext set prop.
let x. apply prop_ext.
prove P x <-> Q x. exact H1 x.
Qed.

Definition nIn : set->set->prop :=
fun x X => ~In x X.
(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

Theorem EmptyE : forall x:set, x /:e Empty.
let x. assume H.
apply EmptyAx.
witness x. exact H.
Qed.

Theorem PowerI : forall X Y:set, Y c= X -> Y :e Power X.
let X Y. apply PowerEq X Y. exact (fun _ H => H).
Qed.

Theorem Subq_Empty : forall X:set, Empty c= X.
exact (fun (X x : set) (H : x :e Empty) => EmptyE x H (x :e X)).
Qed.

Theorem Empty_In_Power : forall X:set, Empty :e Power X.
exact (fun X : set => PowerI X Empty (Subq_Empty X)).
Qed.

Theorem xm : forall P:prop, P \/ ~P.
let P:prop.
set p1 := fun x : set => x = Empty \/ P.
set p2 := fun x : set => x <> Empty \/ P.
claim L1:p1 Empty.
{ prove (Empty = Empty \/ P). apply orIL. exact (fun q H => H). }
claim L2: (Eps_i p1) = Empty \/ P.
{ exact (Eps_i_ax p1 Empty L1). }
claim L3:p2 (Power Empty).
{ prove ~(Power Empty = Empty) \/ P. apply orIL.
  assume H1: Power Empty = Empty.
  apply EmptyE Empty.
  prove Empty :e Empty.
  rewrite <- H1 at 2. apply Empty_In_Power.
}
claim L4: Eps_i p2 <> Empty \/ P.
{ exact (Eps_i_ax p2 (Power Empty) L3). }
apply L2.
- assume H1: Eps_i p1 = Empty.
  apply L4.
  + assume H2: Eps_i p2 <> Empty.
    prove P \/ ~ P.
    apply orIR.
    prove ~ P.
    assume H3 : P.
    claim L5:p1 = p2.
    { apply pred_ext. let x. apply iffI.
      - assume H4.
        prove (~(x = Empty) \/ P).
        apply orIR.
        prove P.
        exact H3.
      - assume H4.
        prove (x = Empty \/ P).
        apply orIR.
        prove P.
        exact H3.
    }
    apply H2. rewrite <- L5. exact H1.
  + assume H2:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H2.
- assume H1:P.
    prove P \/ ~ P.
    apply orIL.
    prove P.
    exact H1.
Qed.

Theorem FalseE : False -> forall p:prop, p.
aby.
Qed.

Theorem andEL : forall (A B : prop), A /\ B -> A.
aby.
Qed.

Theorem andER : forall (A B : prop), A /\ B -> B.
aby.
Qed.

Section PropN.
Variable P1 P2 P3:prop.

Theorem and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
aby.
Qed.

Theorem and3E : P1 /\ P2 /\ P3 -> (forall p:prop, (P1 -> P2 -> P3 -> p) -> p).
aby.
Qed.

Theorem or3I1 : P1 -> P1 \/ P2 \/ P3.
aby.
Qed.

Theorem or3I2 : P2 -> P1 \/ P2 \/ P3.
aby.
Qed.

Theorem or3I3 : P3 -> P1 \/ P2 \/ P3.
aby.
Qed.

Theorem or3E : P1 \/ P2 \/ P3 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).
aby.
Qed.

Variable P4:prop.

Theorem and4I : P1 -> P2 -> P3 -> P4 -> P1 /\ P2 /\ P3 /\ P4.
aby and3I.
Qed.

Variable P5:prop.

Theorem and5I : P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
aby and4I.
Qed.

Variable P6:prop.

Theorem and6I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6.
aby and5I.
Qed.

Variable P7:prop.

Theorem and7I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7.
aby and6I.
Qed.

End PropN.

Theorem not_or_and_demorgan : forall A B:prop, ~(A \/ B) -> ~A /\ ~B.
aby.
Qed.

Theorem not_ex_all_demorgan_i : forall P:set->prop, (~exists x, P x) -> forall x, ~P x.
aby.
Qed.

Theorem iffEL : forall A B:prop, (A <-> B) -> A -> B.
aby.
Qed.

Theorem iffER : forall A B:prop, (A <-> B) -> B -> A.
aby.
Qed.

Theorem iff_refl : forall A:prop, A <-> A.
aby.
Qed.

Theorem iff_sym : forall A B:prop, (A <-> B) -> (B <-> A).
aby.
Qed.

Theorem iff_trans : forall A B C: prop, (A <-> B) -> (B <-> C) -> (A <-> C).
aby.
Qed.

Theorem eq_i_tra : forall x y z, x = y -> y = z -> x = z.
aby.
Qed.

Theorem neq_i_sym: forall x y, x <> y -> y <> x.
aby.
Qed.

Theorem Eps_i_ex : forall P:set -> prop, (exists x, P x) -> P (Eps_i P).
aby Eps_i_ax.
Qed.

Theorem prop_ext_2 : forall p q:prop, (p -> q) -> (q -> p) -> p = q.
aby prop_ext.
Qed.

Theorem Subq_ref : forall X:set, X c= X.
aby.
Qed.

Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
aby.
Qed.

Theorem Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
aby set_ext Subq_Empty.
Qed.

Theorem Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.
aby Empty_Subq_eq.
Qed.

Theorem UnionI : forall X x Y:set, x :e Y -> Y :e X -> x :e Union X.
aby UnionEq.
Qed.

Theorem UnionE : forall X x:set, x :e Union X -> exists Y:set, x :e Y /\ Y :e X.
aby UnionEq.
Qed.

Theorem UnionE_impred : forall X x:set, x :e Union X -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.
aby UnionE.
Qed.

Theorem PowerE : forall X Y:set, Y :e Power X -> Y c= X.
aby PowerEq.
Qed.

Theorem Self_In_Power : forall X:set, X :e Power X.
aby PowerI Subq_ref.
Qed.

Theorem dneg : forall P:prop, ~~P -> P.
aby xm.
Qed.

Theorem not_all_ex_demorgan_i : forall P:set->prop, ~(forall x, P x) -> exists x, ~P x.
aby not_ex_all_demorgan_i dneg.
Qed.

Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
aby xm prop_ext_2.
Qed.

(* Parameter exactly1of2 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "163602f90de012a7426ee39176523ca58bc964ccde619b652cb448bd678f7e21" *)
Definition exactly1of2 : prop->prop->prop := fun A B:prop =>
A /\ ~B \/ ~A /\ B.

Theorem exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
aby.
Qed.

Theorem exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
aby.
Qed.

Theorem exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.
aby.
Qed.

Theorem exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
aby exactly1of2_E.
Qed.

Theorem ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.
aby ReplEq.
Qed.

Theorem ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.
aby ReplEq.
Qed.

Theorem ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.
aby ReplE.
Qed.

Theorem ReplE' : forall X, forall f:set -> set, forall p:set -> prop, (forall x :e X, p (f x)) -> forall y :e {f x|x :e X}, p y.
aby ReplE_impred.
Qed.

Theorem Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.
aby EmptyE Empty_eq ReplE_impred.
Qed.

Theorem ReplEq_ext_sub : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} c= {G x|x :e X}.
aby ReplI ReplE_impred.
Qed.

Theorem ReplEq_ext : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} = {G x|x :e X}.
aby set_ext ReplEq_ext_sub.
Qed.

Theorem Repl_inv_eq : forall P:set -> prop, forall f g:set -> set,
    (forall x, P x -> g (f x) = x)
 -> forall X, (forall x :e X, P x) -> {g y|y :e {f x|x :e X}} = X.
aby set_ext ReplI ReplE_impred.
Qed.

Theorem Repl_invol_eq : forall P:set -> prop, forall f:set -> set,
    (forall x, P x -> f (f x) = x)
 -> forall X, (forall x :e X, P x) -> {f y|y :e {f x|x :e X}} = X.
aby Repl_inv_eq.
Qed.

(* Parameter If_i "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" "b8ff52f838d0ff97beb955ee0b26fad79602e1529f8a2854bda0ecd4193a8a3c" *)
Definition If_i : prop->set->set->set := (fun p x y => Eps_i (fun z:set => p /\ z = x \/ ~p /\ z = y)).
Notation IfThenElse If_i.

Theorem If_i_correct : forall p:prop, forall x y:set,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.
aby Eps_i_ax xm.
Qed.

Theorem If_i_0 : forall p:prop, forall x y:set,
~ p -> (if p then x else y) = y.
aby If_i_correct.
Qed.

Theorem If_i_1 : forall p:prop, forall x y:set,
p -> (if p then x else y) = x.
aby If_i_correct.
Qed.

Theorem If_i_or : forall p:prop, forall x y:set, (if p then x else y) = x \/ (if p then x else y) = y.
aby xm If_i_0 If_i_1.
Qed.

(* Parameter UPair "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" "74243828e4e6c9c0b467551f19c2ddaebf843f72e2437cc2dea41d079a31107f" *)
Definition UPair : set->set->set :=
fun y z => {if Empty :e X then y else z | X :e Power (Power Empty)}.
Notation SetEnum2 UPair.

Theorem UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.
aby ReplE If_i_or.
Qed.

Theorem UPairI1 : forall y z:set, y :e {y,z}.
aby Empty_In_Power Self_In_Power ReplI If_i_1.
Qed.

Theorem UPairI2 : forall y z:set, z :e {y,z}.
aby EmptyE Empty_In_Power ReplI If_i_0.
Qed.

(* Parameter Sing "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "bd01a809e97149be7e091bf7cbb44e0c2084c018911c24e159f585455d8e6bd0" *)
Definition Sing : set -> set := fun x => {x,x}.
Notation SetEnum1 Sing.

Theorem SingI : forall x:set, x :e {x}. 
aby UPairI1.
Qed.

Theorem SingE : forall x y:set, y :e {x} -> y = x. 
aby UPairE.
Qed.

(* Parameter binunion "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "5e1ac4ac93257583d0e9e17d6d048ff7c0d6ccc1a69875b2a505a2d4da305784" *)
Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.
(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

Theorem binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.
aby UnionI UPairI1.
Qed.

Theorem binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.
aby UnionI UPairI2.
Qed.

Theorem binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
aby UnionE_impred UPairE.
Qed.

Theorem binunionE' : forall X Y z, forall p:prop, (z :e X -> p) -> (z :e Y -> p) -> (z :e X :\/: Y -> p).
aby binunionE.
Qed.

Theorem binunion_asso:forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
aby set_ext binunionI1 binunionI2 binunionE.
Qed.

Theorem binunion_com_Subq:forall X Y:set, X :\/: Y c= Y :\/: X.
aby binunionI1 binunionI2 binunionE.
Qed.

Theorem binunion_com:forall X Y:set, X :\/: Y = Y :\/: X.
aby set_ext binunion_com_Subq.
Qed.

Theorem binunion_idl:forall X:set, Empty :\/: X = X.
aby set_ext EmptyE binunionI2 binunionE.
Qed.

Theorem binunion_idr:forall X:set, X :\/: Empty = X.
aby binunion_com binunion_idl.
Qed.

Theorem binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
aby binunionI1.
Qed.

Theorem binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
aby binunionI2.
Qed.

Theorem binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
aby binunionE.
Qed.

Theorem Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
aby set_ext prop_ext_2 Subq_ref binunion_Subq_1 binunion_Subq_2 binunion_Subq_min.
Qed.

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.
Notation SetEnum Empty Sing UPair SetAdjoin.
(* Parameter famunion "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792" "b3e3bf86a58af5d468d398d3acad61ccc50261f43c856a68f8594967a06ec07a" *)
Definition famunion:set->(set->set)->set
:= fun X F => Union {F x|x :e X}.
(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

Theorem famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.
aby UnionI ReplI.
Qed.

Theorem famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.
aby UnionE_impred ReplE_impred.
Qed.

Theorem famunionE_impred : forall X : set , forall F : (set -> set) , forall y : set , y :e (\/_ x :e X , F x) -> forall p:prop, (forall x, x :e X -> y :e F x -> p) -> p.
aby famunionE.
Qed.

Theorem famunion_Empty: forall F:set -> set, (\/_ x :e Empty, F x) = Empty.
aby EmptyE Empty_Subq_eq famunionE_impred.
Qed.

Theorem famunion_Subq: forall X, forall f g:set -> set, (forall x :e X, f x c= g x) -> famunion X f c= famunion X g.
aby famunionI famunionE_impred.
Qed.

Theorem famunion_ext: forall X, forall f g:set -> set, (forall x :e X, f x = g x) -> famunion X f = famunion X g.
aby set_ext Subq_ref famunion_Subq.
Qed.

Section SepSec.
Variable X:set.
Variable P:set->prop.
Let z : set := Eps_i (fun z => z :e X /\ P z).
Let F:set->set := fun x => if P x then x else z.
(* Parameter Sep "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f336a4ec8d55185095e45a638507748bac5384e04e0c48d008e4f6a9653e9c44" *)
Definition Sep:set
:= if (exists z :e X, P z) then {F x|x :e X} else Empty.
End SepSec.
Notation Sep Sep.

Theorem SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
aby ReplI If_i_1.
Qed.

Theorem SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
aby EmptyE xm Eps_i_ex ReplE_impred If_i_0 If_i_1.
Qed.

Theorem SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
aby SepE.
Qed.

Theorem SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.
aby SepE.
Qed.

Theorem Sep_Empty: forall P:set -> prop, {x :e Empty|P x} = Empty.
aby EmptyE Empty_eq SepE1.
Qed.

Theorem Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
aby SepE1.
Qed.

Theorem Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.
aby PowerI Sep_Subq.
Qed.

(* Parameter ReplSep "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" "ec807b205da3293041239ff9552e2912636525180ddecb3a2b285b91b53f70d8" *)
Definition ReplSep : set->(set->prop)->(set->set)->set := fun X P F => {F x|x :e {z :e X|P z}}.
Notation ReplSep ReplSep.

Theorem ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.
aby ReplI SepI.
Qed.

Theorem ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.
aby and3I ReplE SepE.
Qed.

Theorem ReplSepE_impred: forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.
aby ReplSepE.
Qed.

(* Parameter binintersect "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" "b2abd2e5215c0170efe42d2fa0fb8a62cdafe2c8fbd0d37ca14e3497e54ba729" *)
Definition binintersect:set->set->set
:= fun X Y => {x :e X |x :e Y}.
(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

Theorem binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
aby SepI.
Qed.

Theorem binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
aby SepE.
Qed.

Theorem binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
aby SepE1.
Qed.

Theorem binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
aby SepE2.
Qed.

Theorem binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
aby binintersectE1.
Qed.

Theorem binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
aby binintersectE2.
Qed.

Theorem binintersect_Subq_eq_1 : forall X Y, X c= Y -> X :/\: Y = X.
aby set_ext binintersectI binintersect_Subq_1.
Qed.

Theorem binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
aby binintersectI.
Qed.

Theorem binintersect_com_Subq: forall X Y:set, X :/\: Y c= Y :/\: X.
aby binintersect_Subq_1 binintersect_Subq_2 binintersect_Subq_max.
Qed.

Theorem binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
aby set_ext binintersect_com_Subq.
Qed.

(* Parameter setminus "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" "c68e5a1f5f57bc5b6e12b423f8c24b51b48bcc32149a86fc2c30a969a15d8881" *)
Definition setminus:set->set->set
:= fun X Y => Sep X (fun x => x /:e Y).
(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Theorem setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
aby SepI.
Qed.

Theorem setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
aby SepE.
Qed.

Theorem setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
aby SepE1.
Qed.

Theorem setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
aby SepE2.
Qed.

Theorem setminus_Subq:forall X Y:set, X :\: Y c= X.
aby setminusE1.
Qed.

Theorem setminus_In_Power : forall A U, A :\: U :e Power A.
aby PowerI setminus_Subq.
Qed.

Theorem binunion_remove1_eq: forall X, forall x :e X, X = (X :\: {x}) :\/: {x}.
aby set_ext xm SingE binunionI1 binunionI2 binunionE setminusI setminusE1.
Qed.

Theorem In_irref : forall x, x /:e x.
aby In_ind.
Qed.

Theorem In_no2cycle : forall x y, x :e y -> y :e x -> False.
aby In_ind.
Qed.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Definition ordsucc : set->set := fun x:set => x :\/: {x}.

Theorem ordsuccI1 : forall x:set, x c= ordsucc x.
aby binunionI1.
Qed.

Theorem ordsuccI2 : forall x:set, x :e ordsucc x.
aby SingI binunionI2.
Qed.

Theorem ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.
aby SingE binunionE.
Qed.

Notation Nat Empty ordsucc.

Theorem neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
aby EmptyE ordsuccI2.
Qed.

Theorem neq_ordsucc_0 : forall a:set, ordsucc a <> 0.
aby neq_i_sym neq_0_ordsucc.
Qed.

Theorem ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
aby In_no2cycle ordsuccI2 ordsuccE.
Qed.

Theorem In_0_1 : 0 :e 1.
aby ordsuccI2.
Qed.

Theorem In_0_2 : 0 :e 2.
aby ordsuccI1 In_0_1.
Qed.

Theorem In_1_2 : 1 :e 2.
aby ordsuccI2.
Qed.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

Theorem nat_0 : nat_p 0.
aby.
Qed.

Theorem nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
aby.
Qed.

Theorem nat_1 : nat_p 1.
aby nat_0 nat_ordsucc.
Qed.

Theorem nat_2 : nat_p 2.
aby nat_ordsucc nat_1.
Qed.

Theorem nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
let n.
assume H1.
apply H1 (fun n => 0 :e ordsucc n).
- aby In_0_1.
- aby ordsuccI1.
Qed.

Theorem nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
let n.
assume H1.
apply (H1 (fun n => forall m :e n, ordsucc m :e ordsucc n)).
- aby EmptyE.
- aby ordsuccI1 ordsuccI2 ordsuccE.
Qed.

Theorem nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
let p.
assume H1: p 0.
assume H2: forall n, nat_p n -> p n -> p (ordsucc n).
claim L1: nat_p 0 /\ p 0.
{ aby nat_0 H1. }
claim L2: forall n, nat_p n /\ p n -> nat_p (ordsucc n) /\ p (ordsucc n).
{ aby nat_ordsucc H2. }
aby L2 L1.
Qed.

Theorem nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
let p.
assume H1: forall n, nat_p n -> (forall m :e n, p m) -> p n.
claim L1: forall n:set, nat_p n -> forall m :e n, p m.
{ aby EmptyE ordsuccE nat_ind H1. }
aby L1 H1.
Qed.

Theorem nat_inv_impred : forall p:set->prop, p 0 -> (forall n, nat_p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
aby nat_ind.
Qed.

Theorem nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
aby nat_inv_impred.
Qed.

Theorem nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
aby EmptyE ordsuccE nat_ind.
Qed.

Theorem nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
aby EmptyE Subq_tra ordsuccI1 ordsuccE nat_ind.
Qed.

Theorem nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.
aby ordsuccE nat_trans.
Qed.

Definition surj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Theorem form100_63_surjCantor: forall A:set, forall f:set -> set, ~surj A (Power A) f.
let A f. assume H. apply H.
assume H1: forall u :e A, f u :e Power A.
aby SepI SepE2 Sep_In_Power.
Qed.

Definition inj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v).

Theorem form100_63_injCantor: forall A:set, forall f:set -> set, ~inj (Power A) A f.
let A f. assume H. apply H.
assume H1: forall X :e Power A, f X :e A.
assume H2: forall X Y :e Power A, f X = f Y -> X = Y.
set D := {f X | X :e Power A, f X /:e X}.
claim L1: D :e Power A.
{ aby PowerI ReplSepE_impred H1. }
claim L2: f D /:e D.
{ assume H3: f D :e D.
  aby ReplSepE_impred H3 L1 H2.
}
aby ReplSepI L2 L1.
Qed.

Theorem injI : forall X Y, forall f:set -> set, (forall x :e X, f x :e Y) -> (forall x z :e X, f x = f z -> x = z) -> inj X Y f.
aby.
Qed.

Theorem inj_comp : forall X Y Z:set, forall f g:set->set, inj X Y f -> inj Y Z g -> inj X Z (fun x => g (f x)).
aby injI.
Qed.

Definition bij : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Theorem bijI : forall X Y, forall f:set -> set,
    (forall u :e X, f u :e Y)
 -> (forall u v :e X, f u = f v -> u = v)
 -> (forall w :e Y, exists u :e X, f u = w)
 -> bij X Y f.
aby and3I.
Qed.

Theorem bijE : forall X Y, forall f:set -> set,
    bij X Y f
 -> forall p:prop,
      ((forall u :e X, f u :e Y)
    -> (forall u v :e X, f u = f v -> u = v)
    -> (forall w :e Y, exists u :e X, f u = w)
    -> p)
   -> p.
aby.
Qed.

Theorem bij_inj : forall X Y, forall f:set -> set, bij X Y f -> inj X Y f.
aby.
Qed.

Theorem bij_id : forall X, bij X X (fun x => x).
aby and3I.
Qed.

Theorem bij_comp : forall X Y Z:set, forall f g:set->set, bij X Y f -> bij Y Z g -> bij X Z (fun x => g (f x)).
aby and3I.
Qed.

Theorem bij_surj : forall X Y, forall f:set -> set, bij X Y f -> surj X Y f.
aby.
Qed.

Definition inv : set -> (set -> set) -> set -> set := fun X f => fun y:set => Eps_i (fun x => x :e X /\ f x = y).

Theorem surj_rinv : forall X Y, forall f:set->set, (forall w :e Y, exists u :e X, f u = w) -> forall y :e Y, inv X f y :e X /\ f (inv X f y) = y.
aby Eps_i_ax.
Qed.

Theorem inj_linv : forall X, forall f:set->set, (forall u v :e X, f u = f v -> u = v) -> forall x :e X, inv X f (f x) = x.
aby Eps_i_ax.
Qed.

Theorem bij_inv : forall X Y, forall f:set->set, bij X Y f -> bij Y X (inv X f).
aby and3I surj_rinv inj_linv.
Qed.

Definition atleastp : set -> set -> prop
 := fun X Y : set => exists f : set -> set, inj X Y f.

Theorem atleastp_tra: forall X Y Z, atleastp X Y -> atleastp Y Z -> atleastp X Z.
aby inj_comp.
Qed.

Theorem Subq_atleastp : forall X Y, X c= Y -> atleastp X Y.
aby injI.
Qed.

Definition equip : set -> set -> prop
 := fun X Y : set => exists f : set -> set, bij X Y f.

Theorem equip_atleastp: forall X Y, equip X Y -> atleastp X Y.
aby bij_inj.
Qed.

Theorem equip_ref : forall X, equip X X.
aby bij_id.
Qed.

Theorem equip_sym : forall X Y, equip X Y -> equip Y X.
aby bij_inv.
Qed.

Theorem equip_tra : forall X Y Z, equip X Y -> equip Y Z -> equip X Z.
aby bij_comp.
Qed.

Theorem equip_0_Empty : forall X, equip X 0 -> X = 0.
aby EmptyE Empty_eq bijE.
Qed.

Theorem equip_adjoin_ordsucc : forall N X y, y /:e X -> equip N X -> equip (ordsucc N) (X :\/: {y}).
let N X y.
assume H1: y /:e X.
assume H2: equip N X.
apply H2.
let f.
assume Hf: bij N X f.
apply bijE N X f Hf.
assume Hf1: forall u :e N, f u :e X.
assume Hf2: forall u v :e N, f u = f v -> u = v.
assume Hf3: forall w :e X, exists u :e N, f u = w.
claim L1: exists g:set -> set, (forall u :e N, g u = f u) /\ g N = y.
{ set g : set -> set := fun u => if u :e N then f u else y.
  aby If_i_0 If_i_1 In_irref.
}
aby SingI SingE binunionI1 binunionI2 binunionE ordsuccI1 ordsuccI2 ordsuccE bijI L1 Hf3 Hf2 Hf1 H1.
Qed.

Theorem equip_ordsucc_remove1: forall X N, forall x :e X, equip X (ordsucc N) -> equip (X :\: {x}) N.
let X N x.
assume Hx: x :e X.
assume H1: equip X (ordsucc N).
apply equip_sym X (ordsucc N) H1.
let f.
assume Hf: bij (ordsucc N) X f.
apply bijE (ordsucc N) X f Hf.
assume Hf1: forall u :e ordsucc N, f u :e X.
assume Hf2: forall u v :e ordsucc N, f u = f v -> u = v.
assume Hf3: forall y :e X, exists u :e ordsucc N, f u = y.
apply equip_sym.
prove equip N (X :\: {x}).
apply Hf3 x Hx.
let w. assume H. apply H.
assume Hw: w :e ordsucc N.
assume Hfw: f w = x.
apply ordsuccE N w Hw.
- assume H2: w :e N.
  claim L1: f N <> x.
  { assume H3: f N = x.
    aby In_irref ordsuccI1 ordsuccI2 H3 H2 Hfw Hf2.
  }
  claim L2: forall u :e N, f u <> f N.
  { aby In_irref ordsuccI1 ordsuccI2 Hf2. }
  claim L3: exists g:set->set, (forall u :e ordsucc N, u <> w -> g u = f u) /\ g w = f N.
  { set g:set->set := fun u => if u = w then f N else f u.
    aby If_i_0 If_i_1.
  }
  aby xm SingI SingE setminusI setminusE ordsuccI1 ordsuccI2 ordsuccE bijI L3 L2 L1 H2 Hfw Hw Hf3 Hf2 Hf1.
- aby SingI SingE setminusI setminusE In_irref ordsuccI1 ordsuccI2 ordsuccE bijI Hfw Hf3 Hf2 Hf1.
Qed.

Section SchroederBernstein.

Theorem KnasterTarski_set: forall A, forall F:set->set,
    (forall U :e Power A, F U :e Power A)
 -> (forall U V :e Power A, U c= V -> F U c= F V)
 -> exists Y :e Power A, F Y = Y.
let A F. assume H1 H2.
set Y : set := {u :e A|forall X :e Power A, F X c= X -> u :e X}.
claim L1: Y :e Power A.
{ aby Sep_In_Power. }
claim L2: F Y :e Power A.
{ aby H1 H2 L1. }
claim L3: forall X :e Power A, F X c= X -> Y c= X.
{ aby SepE2. }
claim L4: F Y c= Y.
{ aby PowerE SepI L3 L2 L1 H2. }
aby set_ext L4 L3 L2 L1 H2.
Qed.

Theorem image_In_Power : forall A B, forall f:set -> set, (forall x :e A, f x :e B) -> forall U :e Power A, {f x|x :e U} :e Power B.
aby PowerI PowerE ReplE_impred.
Qed.

Theorem image_monotone : forall f:set -> set, forall U V, U c= V -> {f x|x :e U} c= {f x|x :e V}.
aby ReplI ReplE_impred.
Qed.

Theorem setminus_antimonotone : forall A U V, U c= V -> A :\: V c= A :\: U.
aby setminusI setminusE.
Qed.

Theorem SchroederBernstein: forall A B, forall f g:set -> set, inj A B f -> inj B A g -> equip A B.
let A B f g. assume Hf Hg.
apply Hf. assume Hf1 Hf2.
apply Hg. assume Hg1 Hg2.
set F : set -> set := fun X => {g y|y :e B :\: {f x|x :e A :\: X}}.
claim L1: forall U :e Power A, F U :e Power A.
{ aby setminus_In_Power image_In_Power Hg1. }
claim L2: forall U V :e Power A, U c= V -> F U c= F V.
{ aby image_monotone setminus_antimonotone. }
apply KnasterTarski_set A F L1 L2.
let Y. assume H1. apply H1.
assume H1: Y :e Power A.
assume H2: F Y = Y.
set h : set -> set := fun x => if x :e Y then inv B g x else f x.
prove exists f:set -> set, bij A B f.
witness h.
apply bijI.
- let x. assume Hx.
  prove (if x :e Y then inv B g x else f x) :e B.
  apply xm (x :e Y).
  + aby ReplE_impred If_i_1 setminusE1 inj_linv H2 Hg2.
  + aby If_i_0 Hx Hf1.
- let x. assume Hx. let y. assume Hy.
  prove (if x :e Y then inv B g x else f x)
      = (if y :e Y then inv B g y else f y)
     -> x = y.
  apply xm (x :e Y).
  + assume H3: x :e Y. rewrite If_i_1 (x :e Y) (inv B g x) (f x) H3.
    prove inv B g x = (if y :e Y then inv B g y else f y)
       -> x = y.
    claim Lx: x :e F Y.
    { aby H3 H2. }
    apply ReplE_impred (B :\: {f x|x :e A :\: Y}) g x Lx.
    let z.
    assume Hz1: z :e B :\: {f x|x :e A :\: Y}.
    assume Hz2: x = g z.
    apply setminusE B {f x|x :e A :\: Y} z Hz1.
    assume Hz1a Hz1b.
    apply xm (y :e Y).
    * { assume H4: y :e Y. aby ReplE_impred If_i_1 setminusE1 inj_linv H4 Hz1a Hz2 H2 Hg2. }
    * { aby ReplI If_i_0 setminusI inj_linv Hz1b Hz1a Hz2 Hy Hg2. }
  + assume H3: x /:e Y. rewrite If_i_0 (x :e Y) (inv B g x) (f x) H3.
    prove f x = (if y :e Y then inv B g y else f y)
       -> x = y.
    apply xm (y :e Y).
    * { assume H4: y :e Y. rewrite If_i_1 (y :e Y) (inv B g y) (f y) H4.
        prove f x = inv B g y -> x = y.
        claim Ly: y :e F Y.
        { aby H4 H2. }
        apply ReplE_impred (B :\: {f x|x :e A :\: Y}) g y Ly.
        aby ReplI setminusI setminusE inj_linv H3 Hx Hg2.
      }
    * aby If_i_0 Hy Hx Hf2.
- aby xm ReplI ReplE_impred If_i_0 If_i_1 setminusI setminusE inj_linv H2 Hg2 Hg1.
Qed.

Theorem atleastp_antisym_equip: forall A B, atleastp A B -> atleastp B A -> equip A B.
aby SchroederBernstein.
Qed.

End SchroederBernstein.

Section PigeonHole.

Theorem PigeonHole_nat : forall n, nat_p n -> forall f:set -> set, (forall i :e ordsucc n, f i :e n) -> ~(forall i j :e ordsucc n, f i = f j -> i = j).
apply nat_ind (fun n => forall f:set -> set, (forall i :e ordsucc n, f i :e n) -> ~(forall i j :e ordsucc n, f i = f j -> i = j)).
- aby EmptyE In_0_1.
- let n. assume Hn: nat_p n.
  assume IH: forall f:set -> set, (forall i :e ordsucc n, f i :e n) -> ~(forall i j :e ordsucc n, f i = f j -> i = j).
  let f.
  assume H1: forall i :e ordsucc (ordsucc n), f i :e ordsucc n.
  assume H2: forall i j :e ordsucc (ordsucc n), f i = f j -> i = j.
  apply xm (exists i :e ordsucc (ordsucc n), f i = n).
  + assume H3. apply H3. let k. assume Hk. apply Hk.
    assume Hk1: k :e ordsucc (ordsucc n).
    assume Hk2: f k = n.
    set f' := fun i:set => if k c= i then f (ordsucc i) else f i.
    apply IH f'.
    * aby xm If_i_0 If_i_1 In_irref ordsuccI1 ordsuccI2 ordsuccE nat_ordsucc nat_ordsucc_in_ordsucc Hk2 Hk1 H2 H1 Hn.
    * aby xm If_i_0 If_i_1 ordsuccI1 ordsucc_inj nat_ordsucc nat_ordsucc_in_ordsucc H2 Hn.
  + aby ordsuccI1 ordsuccE H2 H1 IH.
Qed.

Theorem Pigeonhole_not_atleastp_ordsucc : forall n, nat_p n -> ~atleastp (ordsucc n) n.
aby PigeonHole_nat.
Qed.

End PigeonHole.

Theorem Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.
apply nat_complete_ind.
let n.
assume Hn: nat_p n.
assume IHn: forall m :e n, Union (ordsucc m) = m.
prove Union (ordsucc n) = n.
apply set_ext.
- aby UnionE_impred nat_ordsucc_trans Hn.
- aby UnionI ordsuccI2.
Qed.

Theorem cases_1: forall i :e 1, forall p:set->prop, p 0 -> p i.
aby EmptyE ordsuccE.
Qed.

Theorem cases_2: forall i :e 2, forall p:set->prop, p 0 -> p 1 -> p i.
aby ordsuccE cases_1.
Qed.

Theorem neq_0_1 : 0 <> 1.
aby neq_0_ordsucc.
Qed.

Theorem neq_1_0 : 1 <> 0.
aby neq_ordsucc_0.
Qed.

Theorem neq_0_2 : 0 <> 2.
aby neq_0_ordsucc.
Qed.

Theorem neq_2_0 : 2 <> 0.
aby neq_ordsucc_0.
Qed.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Theorem ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.
aby.
Qed.

Theorem ordinal_Empty : ordinal Empty.
aby EmptyE.
Qed.

Theorem ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.
aby.
Qed.

Theorem TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).
aby ordsuccI1 ordsuccE.
Qed.

Theorem ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).
aby ordsuccE TransSet_ordsucc.
Qed.

Theorem nat_p_ordinal : forall n:set, nat_p n -> ordinal n.
aby nat_ind ordinal_Empty ordinal_ordsucc.
Qed.

Theorem ordinal_1 : ordinal 1.
aby nat_1 nat_p_ordinal.
Qed.

Theorem ordinal_2 : ordinal 2.
aby nat_2 nat_p_ordinal.
Qed.

Theorem TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.
aby ordsuccE.
Qed.

Theorem ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.
aby ordinal_TransSet TransSet_ordsucc_In_Subq.
Qed.

Theorem ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
let alpha.
assume IHalpha: forall gamma :e alpha, forall beta:set, ordinal gamma -> ordinal beta -> gamma :e beta \/ gamma = beta \/ beta :e gamma.
prove forall beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.
apply In_ind.
aby set_ext xm or3I1 or3I2 or3I3 or3E ordinal_TransSet ordinal_Hered IHalpha.
Qed.    

Theorem ordinal_trichotomy_or_impred : forall alpha beta:set, ordinal alpha -> ordinal beta -> forall p:prop, (alpha :e beta -> p) -> (alpha = beta -> p) -> (beta :e alpha -> p) -> p.
aby or3E ordinal_trichotomy_or.
Qed.

Theorem ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.
aby or3E Subq_ref ordinal_TransSet ordinal_trichotomy_or.
Qed.

Theorem ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.
aby ordinal_TransSet ordinal_In_Or_Subq.
Qed.

Theorem ordinal_ordsucc_In_eq : forall alpha beta, ordinal alpha -> beta :e alpha -> ordsucc beta :e alpha \/ alpha = ordsucc beta.
aby In_irref In_no2cycle ordsuccE ordinal_Hered ordinal_ordsucc ordinal_trichotomy_or.
Qed.

Theorem ordinal_lim_or_succ : forall alpha, ordinal alpha -> (forall beta :e alpha, ordsucc beta :e alpha) \/ (exists beta :e alpha, alpha = ordsucc beta).
aby ordinal_ordsucc_In_eq.
Qed.

Theorem ordinal_ordsucc_In : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta :e ordsucc alpha.
aby set_ext ordsuccI1 ordsuccI2 ordinal_Hered ordinal_ordsucc ordinal_ordsucc_In_Subq ordinal_In_Or_Subq.
Qed.

Theorem ordinal_famunion : forall X, forall F:set -> set, (forall x :e X, ordinal (F x)) -> ordinal (\/_ x :e X, F x).
aby famunionI famunionE ordinal_Hered.
Qed.

Theorem ordinal_binintersect : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :/\: beta).
aby binintersect_Subq_eq_1 binintersect_com ordinal_In_Or_Subq.
Qed.

Theorem ordinal_binunion : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :\/: beta).
aby binunion_com Subq_binunion_eq ordinal_linear.
Qed.

Theorem ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.
aby In_ind ordinal_Hered.
Qed.

Theorem least_ordinal_ex : forall p:set -> prop, (exists alpha, ordinal alpha /\ p alpha) -> exists alpha, ordinal alpha /\ p alpha /\ forall beta :e alpha, ~p beta.
aby and3I dneg ordinal_ind.
Qed.

Theorem equip_Sing_1 : forall x, equip {x} 1.
aby SingI SingE In_0_1 bijI cases_1.
Qed.

Theorem TransSet_In_ordsucc_Subq : forall x y, TransSet y -> x :e ordsucc y -> x c= y.
aby Subq_ref ordsuccE.
Qed.

Theorem exandE_i : forall P Q:set -> prop, (exists x, P x /\ Q x) -> forall r:prop, (forall x, P x -> Q x -> r) -> r.
aby.
Qed.

Theorem exandE_ii : forall P Q:(set -> set) -> prop, (exists x:set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set, P x -> Q x -> p) -> p.
aby.
Qed.

Theorem exandE_iii : forall P Q:(set -> set -> set) -> prop, (exists x:set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set, P x -> Q x -> p) -> p.
aby.
Qed.

Theorem exandE_iiii : forall P Q:(set -> set -> set -> set) -> prop, (exists x:set -> set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set -> set, P x -> Q x -> p) -> p.
aby.
Qed.

Section Descr_ii.
Variable P : (set -> set) -> prop.
(* Parameter Descr_ii "a6e81668bfd1db6e6eb6a13bf66094509af176d9d0daccda274aa6582f6dcd7c" "3bae39e9880bbf5d70538d82bbb05caf44c2c11484d80d06dee0589d6f75178c" *)
Definition Descr_ii : set -> set := fun x:set => Eps_i (fun y => forall h:set -> set, P h -> h x = y).
Hypothesis Pex: exists f:set -> set, P f.
Hypothesis Puniq: forall f g:set -> set, P f -> P g -> f = g.

Theorem Descr_ii_prop : P Descr_ii.
aby Eps_i_ax Puniq Pex.
Qed.

End Descr_ii.
Section Descr_iii.
Variable P : (set -> set -> set) -> prop.
(* Parameter Descr_iii "dc42f3fe5d0c55512ef81fe5d2ad0ff27c1052a6814b1b27f5a5dcb6d86240bf" "ca5fc17a582fdd4350456951ccbb37275637ba6c06694213083ed9434fe3d545" *)
Definition Descr_iii : set -> set -> set := fun x y:set => Eps_i (fun z => forall h:set -> set -> set, P h -> h x y = z).
Hypothesis Pex: exists f:set -> set -> set, P f.
Hypothesis Puniq: forall f g:set -> set -> set, P f -> P g -> f = g.

Theorem Descr_iii_prop : P Descr_iii.
aby Eps_i_ax Puniq Pex.
Qed.

End Descr_iii.
Section Descr_Vo1.
Variable P : Vo 1 -> prop.
(* Parameter Descr_Vo1 "322bf09a1711d51a4512e112e1767cb2616a7708dc89d7312c8064cfee6e3315" "615c0ac7fca2b62596ed34285f29a77b39225d1deed75d43b7ae87c33ba37083" *)
Definition Descr_Vo1 : Vo 1 := fun x:set => forall h:set -> prop, P h -> h x.
Hypothesis Pex: exists f:Vo 1, P f.
Hypothesis Puniq: forall f g:Vo 1, P f -> P g -> f = g.

Theorem Descr_Vo1_prop : P Descr_Vo1.
aby prop_ext_2 Puniq Pex.
Qed.

End Descr_Vo1.
Section If_ii.
Variable p:prop.
Variable f g:set -> set.
(* Parameter If_ii "e76df3235104afd8b513a92c00d3cc56d71dd961510bf955a508d9c2713c3f29" "17057f3db7be61b4e6bd237e7b37125096af29c45cb784bb9cc29b1d52333779" *)
Definition If_ii : set -> set := fun x => if p then f x else g x.

Theorem If_ii_1 : p -> If_ii = f.
aby If_i_1.
Qed.

Theorem If_ii_0 : ~p -> If_ii = g.
aby If_i_0.
Qed.

End If_ii.
Section If_iii.
Variable p:prop.
Variable f g:set -> set -> set.
(* Parameter If_iii "53034f33cbed012c3c6db42812d3964f65a258627a765f5bede719198af1d1ca" "3314762dce5a2e94b7e9e468173b047dd4a9fac6ee2c5f553c6ea15e9c8b7542" *)
Definition If_iii : set -> set -> set := fun x y => if p then f x y else g x y.

Theorem If_iii_1 : p -> If_iii = f.
aby If_i_1.
Qed.

Theorem If_iii_0 : ~p -> If_iii = g.
aby If_i_0.
Qed.

End If_iii.
Section EpsilonRec_i.
Variable F:set -> (set -> set) -> set.
Definition In_rec_i_G : set -> set -> prop :=
fun X Y =>
forall R:set->set->prop,
(forall X:set, forall f:set->set, (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_i "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" "fac413e747a57408ad38b3855d3cde8673f86206e95ccdadff2b5babaf0c219e" *)
Definition In_rec_i : set -> set := fun X => Eps_i (In_rec_i_G X).

Theorem In_rec_i_G_c : forall X:set, forall f:set->set, (forall x :e X, In_rec_i_G x (f x)) -> In_rec_i_G X (F X f).
aby.
Qed.

Theorem In_rec_i_G_inv : forall X:set, forall Y:set, In_rec_i_G X Y -> exists f:set->set, (forall x :e X, In_rec_i_G x (f x)) /\ Y = F X f.
let X Y.
assume H1: In_rec_i_G X Y.
set R := (fun X:set => fun Y:set => exists f:set->set, (forall x :e X, In_rec_i_G x (f x)) /\ Y = F X f).
apply (H1 R).
aby exandE_ii In_rec_i_G_c.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_i_G_f : forall X:set, forall Y Z:set, In_rec_i_G X Y -> In_rec_i_G X Z -> Y = Z.
apply In_ind.
aby exandE_ii In_rec_i_G_inv Fr.
Qed.

Theorem In_rec_i_G_In_rec_i : forall X:set, In_rec_i_G X (In_rec_i X).
aby Eps_i_ax In_ind In_rec_i_G_c.
Qed.

Theorem In_rec_i_G_In_rec_i_d : forall X:set, In_rec_i_G X (F X In_rec_i).
aby In_rec_i_G_In_rec_i Fr.
Qed.

Theorem In_rec_i_eq : forall X:set, In_rec_i X = F X In_rec_i.
aby In_rec_i_G_f In_rec_i_G_In_rec_i In_rec_i_G_In_rec_i_d Fr.
Qed.

End EpsilonRec_i.
Section EpsilonRec_ii.
Variable F:set -> (set -> (set -> set)) -> (set -> set).
Definition In_rec_G_ii : set -> (set -> set) -> prop :=
fun X Y =>
forall R:set->(set -> set)->prop,
(forall X:set, forall f:set->(set -> set), (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_ii "4d137cad40b107eb0fc2c707372525f1279575e6cadb4ebc129108161af3cedb" "f3c9abbc5074c0d68e744893a170de526469426a5e95400ae7fc81f74f412f7e" *)
Definition In_rec_ii : set -> (set -> set) := fun X => Descr_ii (In_rec_G_ii X).

Theorem In_rec_G_ii_c : forall X:set, forall f:set->(set -> set), (forall x :e X, In_rec_G_ii x (f x)) -> In_rec_G_ii X (F X f).
aby.
Qed.

Theorem In_rec_G_ii_inv : forall X:set, forall Y:(set -> set), In_rec_G_ii X Y -> exists f:set->(set -> set), (forall x :e X, In_rec_G_ii x (f x)) /\ Y = F X f.
let X Y.
assume H1: In_rec_G_ii X Y.
set R := (fun X:set => fun Y:(set -> set) => exists f:set->(set -> set), (forall x :e X, In_rec_G_ii x (f x)) /\ Y = F X f).
apply (H1 R).
aby exandE_iii In_rec_G_ii_c.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_G_ii_f : forall X:set, forall Y Z:(set -> set), In_rec_G_ii X Y -> In_rec_G_ii X Z -> Y = Z.
apply In_ind.
aby exandE_iii In_rec_G_ii_inv Fr.
Qed.

Theorem In_rec_G_ii_In_rec_ii : forall X:set, In_rec_G_ii X (In_rec_ii X).
apply In_ind.
aby Descr_ii_prop In_rec_G_ii_c In_rec_G_ii_f Fr.
Qed.

Theorem In_rec_G_ii_In_rec_ii_d : forall X:set, In_rec_G_ii X (F X In_rec_ii).
aby In_rec_G_ii_In_rec_ii Fr.
Qed.

Theorem In_rec_ii_eq : forall X:set, In_rec_ii X = F X In_rec_ii.
aby In_rec_G_ii_f In_rec_G_ii_In_rec_ii In_rec_G_ii_In_rec_ii_d Fr.
Qed.

End EpsilonRec_ii.
Section EpsilonRec_iii.
Variable F:set -> (set -> (set -> set -> set)) -> (set -> set -> set).
Definition In_rec_G_iii : set -> (set -> set -> set) -> prop :=
fun X Y =>
forall R:set->(set -> set -> set)->prop,
(forall X:set, forall f:set->(set -> set -> set), (forall x :e X, R x (f x)) -> R X (F X f)) ->
R X Y.
(* Parameter In_rec_iii "222f1b8dcfb0d2e33cc4b232e87cbcdfe5c4a2bdc5326011eb70c6c9aeefa556" "9b3a85b85e8269209d0ca8bf18ef658e56f967161bf5b7da5e193d24d345dd06" *)
Definition In_rec_iii : set -> (set -> set -> set) := fun X => Descr_iii (In_rec_G_iii X).

Theorem In_rec_G_iii_c : forall X:set, forall f:set->(set -> set -> set), (forall x :e X, In_rec_G_iii x (f x)) -> In_rec_G_iii X (F X f).
aby.
Qed.

Theorem In_rec_G_iii_inv : forall X:set, forall Y:(set -> set -> set), In_rec_G_iii X Y -> exists f:set->(set -> set -> set), (forall x :e X, In_rec_G_iii x (f x)) /\ Y = F X f.
let X Y.
assume H1: In_rec_G_iii X Y.
set R := (fun X:set => fun Y:(set -> set -> set) => exists f:set->(set -> set -> set), (forall x :e X, In_rec_G_iii x (f x)) /\ Y = F X f).
apply (H1 R).
aby exandE_iiii In_rec_G_iii_c.
Qed.

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Theorem In_rec_G_iii_f : forall X:set, forall Y Z:(set -> set -> set), In_rec_G_iii X Y -> In_rec_G_iii X Z -> Y = Z.
apply In_ind.
aby exandE_iiii In_rec_G_iii_inv Fr.
Qed.

Theorem In_rec_G_iii_In_rec_iii : forall X:set, In_rec_G_iii X (In_rec_iii X).
apply In_ind.
aby Descr_iii_prop In_rec_G_iii_c In_rec_G_iii_f Fr.
Qed.

Theorem In_rec_G_iii_In_rec_iii_d : forall X:set, In_rec_G_iii X (F X In_rec_iii).
aby In_rec_G_iii_In_rec_iii Fr.
Qed.

Theorem In_rec_iii_eq : forall X:set, In_rec_iii X = F X In_rec_iii.
aby In_rec_G_iii_f In_rec_G_iii_In_rec_iii In_rec_G_iii_In_rec_iii_d Fr.
Qed.

End EpsilonRec_iii.
Section NatRec.
Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.
Definition nat_primrec : set->set := In_rec_i F.

Theorem nat_primrec_r : forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.
aby xm If_i_0.
Qed.

Theorem nat_primrec_0 : nat_primrec 0 = z.
prove (In_rec_i F 0 = z).
aby EmptyE If_i_0 In_rec_i_eq nat_primrec_r.
Qed.

Theorem nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).
let n.
assume Hn: nat_p n.
prove (In_rec_i F (ordsucc n) = f n (In_rec_i F n)).
rewrite (In_rec_i_eq F nat_primrec_r) at 1.
aby If_i_1 ordsuccI2 Union_ordsucc_eq Hn.
Qed.

End NatRec.

Section NatAdd.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.
Infix + 360 right := add_nat.

Theorem add_nat_0R : forall n:set, n + 0 = n.
aby nat_primrec_0.
Qed.

Theorem add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).
aby nat_primrec_S.
Qed.

Theorem add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby add_nat_0R Hn.
- aby nat_ordsucc add_nat_SR.
Qed.

Theorem add_nat_1_1_2 : 1 + 1 = 2.
aby nat_0 add_nat_0R add_nat_SR.
Qed.

Theorem add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).
let n. assume Hn: nat_p n.
let m. assume Hm: nat_p m.
apply nat_ind.
- aby add_nat_0R.
- aby add_nat_SR add_nat_p Hm.
Qed.

Theorem add_nat_0L : forall m:set, nat_p m -> 0+m = m.
apply nat_ind.
- aby add_nat_0R.
- aby add_nat_SR.
Qed.

Theorem add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby add_nat_0R.
- aby add_nat_SR.
Qed.

Theorem add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby add_nat_0R add_nat_0L Hn.
- aby add_nat_SR add_nat_SL Hn.
Qed.

Theorem add_nat_In_R: forall m, nat_p m -> forall k :e m, forall n, nat_p n -> k + n :e m + n.
let m. assume Hm: nat_p m.
let k. assume Hk: k :e m.
apply nat_ind.
- aby add_nat_0R Hk.
- aby nat_p_ordinal ordinal_ordsucc_In add_nat_SR add_nat_p Hm.
Qed.

Theorem add_nat_In_L: forall n, nat_p n -> forall m, nat_p m -> forall k :e m, n + k :e n + m.
aby nat_p_trans add_nat_com add_nat_In_R.
Qed.

Theorem add_nat_Subq_R: forall k, nat_p k -> forall m, nat_p m -> k c= m -> forall n, nat_p n -> k + n c= m + n.
aby set_ext Subq_ref nat_trans nat_p_ordinal ordinal_In_Or_Subq add_nat_p add_nat_In_R.
Qed.

Theorem add_nat_Subq_L: forall n, nat_p n -> forall k, nat_p k -> forall m, nat_p m -> k c= m -> n + k c= n + m.
aby add_nat_com add_nat_Subq_R.
Qed.

Theorem add_nat_Subq_R' : forall m, nat_p m -> forall n, nat_p n -> m c= m + n.
let m. assume Hm: nat_p m.
apply nat_ind.
- aby Subq_ref add_nat_0R.
- aby Subq_tra ordsuccI1 add_nat_SR.
Qed.

Theorem nat_Subq_add_ex: forall n, nat_p n -> forall m, nat_p m -> n c= m -> exists k, nat_p k /\ m = k + n.
apply nat_ind.
- aby add_nat_0R.
- let n. assume Hn.
  assume IH: forall m, nat_p m -> n c= m -> exists k, nat_p k /\ m = k + n.
  apply nat_inv_impred.
  + aby EmptyE ordsuccI2.
  + aby In_irref nat_ordsucc_in_ordsucc nat_p_ordinal ordinal_In_Or_Subq add_nat_SR IH Hn.
Qed.

Theorem add_nat_cancel_R : forall k, nat_p k -> forall m, nat_p m -> forall n, nat_p n -> k + n = m + n -> k = m.
let k. assume Hk. let m. assume Hm.
apply nat_ind.
- aby add_nat_0R.
- aby ordsucc_inj add_nat_SR.
Qed.

End NatAdd.

Section NatMul.

Infix + 360 right := add_nat.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.
Infix * 355 right := mul_nat.

Theorem mul_nat_0R : forall n:set, n * 0 = 0.
aby nat_primrec_0.
Qed.

Theorem mul_nat_SR : forall n m, nat_p m -> n * ordsucc m = n + n * m.
aby nat_primrec_S.
Qed.

Theorem mul_nat_1R: forall n, n * 1 = n.
aby nat_0 add_nat_0R mul_nat_0R mul_nat_SR.
Qed.

Theorem mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby nat_0 mul_nat_0R.
- aby add_nat_p mul_nat_SR Hn.
Qed.

Theorem mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.
apply nat_ind.
- aby mul_nat_0R.
- aby add_nat_0R mul_nat_SR.
Qed.

Theorem mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby add_nat_0R mul_nat_0R.
- aby add_nat_SR add_nat_p add_nat_asso add_nat_SL mul_nat_SR mul_nat_p Hn.
Qed.

Theorem mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.
let n.
assume Hn: nat_p n.
apply nat_ind.
- aby mul_nat_0R mul_nat_0L Hn.
- aby add_nat_com mul_nat_SR mul_nat_p mul_nat_SL Hn.
Qed.

Theorem mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.
let n.
assume Hn: nat_p n.
let m.
assume Hm: nat_p m.
apply nat_ind.
- aby add_nat_0R mul_nat_0R.
- aby add_nat_SR add_nat_p add_nat_asso add_nat_com mul_nat_SR mul_nat_p Hm Hn.
Qed.

Theorem mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).
let n.
assume Hn: nat_p n.
let m.
assume Hm: nat_p m.
apply nat_ind.
- aby mul_nat_0R.
- aby mul_nat_SR mul_nat_p mul_add_nat_distrL Hm Hn.
Qed.

Theorem mul_nat_Subq_R : forall m n, nat_p m -> nat_p n -> m c= n -> forall k, nat_p k -> m * k c= n * k.
let m n. assume Hm Hn Hmn.
apply nat_ind.
- aby Subq_ref mul_nat_0R.
- aby Subq_tra add_nat_Subq_R add_nat_Subq_L mul_nat_SR mul_nat_p Hmn Hn Hm.
Qed.

Theorem mul_nat_Subq_L : forall m n, nat_p m -> nat_p n -> m c= n -> forall k, nat_p k -> k * m c= k * n.
aby mul_nat_com mul_nat_Subq_R.
Qed.

Theorem mul_nat_0_or_Subq: forall m, nat_p m -> forall n, nat_p n -> n = 0 \/ m c= m * n.
aby nat_1 cases_1 nat_p_ordinal ordinal_In_Or_Subq mul_nat_1R mul_nat_Subq_L.
Qed.

(** If m times n = 0 for naturals m and n, then one must be 0. **)
Theorem mul_nat_0_inv : forall m, nat_p m -> forall n, nat_p n -> m * n = 0 -> m = 0 \/ n = 0.
aby neq_ordsucc_0 nat_ordsucc nat_inv_impred add_nat_SL mul_nat_SR mul_nat_p.
Qed.

Theorem mul_nat_0m_1n_In: forall m, nat_p m -> forall n, nat_p n -> 0 :e m -> 1 :e n -> m :e m * n.
apply nat_inv_impred.
- aby EmptyE.
- let m.
  assume Hm: nat_p m.
  prove forall n, nat_p n -> 0 :e ordsucc m -> 1 :e n -> ordsucc m :e ordsucc m * n.
  apply nat_inv_impred.
  + assume _.
    aby In_no2cycle In_0_1.
  + prove forall n, nat_p n -> 0 :e ordsucc m -> 1 :e ordsucc n -> ordsucc m :e ordsucc m * ordsucc n.
    apply nat_inv_impred.
    * assume _.
      aby In_irref.
    * aby nat_ordsucc nat_0_in_ordsucc add_nat_0R add_nat_SR add_nat_p add_nat_In_L mul_nat_SR mul_nat_p mul_nat_SL Hm.
Qed.

Theorem nat_le1_cases: forall m, nat_p m -> m c= 1 -> m = 0 \/ m = 1.
aby In_irref nat_ordsucc nat_0_in_ordsucc nat_ordsucc_in_ordsucc nat_inv_impred.
Qed.

Definition Pi_nat : (set -> set) -> set -> set := fun f n =>
  nat_primrec 1 (fun i r => r * f i) n.

Theorem Pi_nat_0: forall f:set -> set, Pi_nat f 0 = 1.
aby nat_primrec_0.
Qed.

Theorem Pi_nat_S: forall f:set -> set, forall n, nat_p n -> Pi_nat f (ordsucc n) = Pi_nat f n * f n.
aby nat_primrec_S.
Qed.

Theorem Pi_nat_p: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, nat_p (f i))
  -> nat_p (Pi_nat f n).
let f.
apply nat_ind.
- assume _. aby nat_1 Pi_nat_0.
- aby ordsuccI1 ordsuccI2 mul_nat_p Pi_nat_S.
Qed.

Theorem Pi_nat_0_inv: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, nat_p (f i))
   -> Pi_nat f n = 0
   -> (exists i :e n, f i = 0).
let f.
apply nat_ind.
- assume _.
  aby neq_1_0 Pi_nat_0.
- aby ordsuccI1 ordsuccI2 mul_nat_0_inv Pi_nat_S Pi_nat_p.
Qed.

Definition exp_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.

Infix ^ 342 right := exp_nat.

Theorem exp_nat_0 : forall n, n ^ 0 = 1.
aby nat_primrec_0.
Qed.

Theorem exp_nat_S : forall n m, nat_p m -> n ^ (ordsucc m) = n * n ^ m.
aby nat_primrec_S.
Qed.

Theorem exp_nat_p : forall n, nat_p n -> forall m, nat_p m -> nat_p (n ^ m).
let n. assume Hn. apply nat_ind.
- aby nat_1 exp_nat_0.
- aby mul_nat_p exp_nat_S Hn.
Qed.

Theorem exp_nat_1 : forall n, n ^ 1 = n.
aby nat_0 mul_nat_1R exp_nat_0 exp_nat_S.
Qed.

End NatMul.

Section form100_52.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.
Infix ^ 342 right := exp_nat.

Theorem Subq_Sing0_1 : {0} c= 1.
aby SingE ordsuccI2.
Qed.

Theorem Subq_1_Sing0 : 1 c= {0}.
aby EmptyE SingI ordsuccE.
Qed.

Theorem eq_1_Sing0 : 1 = {0}.
aby set_ext Subq_Sing0_1 Subq_1_Sing0.
Qed.

Theorem Power_0_Sing_0 : Power 0 = {0}.
aby set_ext Empty_In_Power Empty_Subq_eq PowerE SingI SingE.
Qed.

Theorem equip_finite_Power: forall n, nat_p n -> forall X,
  equip X n -> equip (Power X) (2 ^ n).
apply nat_ind.
- aby equip_ref equip_0_Empty exp_nat_0 eq_1_Sing0 Power_0_Sing_0.
- let n.
  assume Hn.
  assume IHn: forall X, equip X n -> equip (Power X) (2 ^ n).
  let X.
  assume H1: equip X (ordsucc n).
  prove equip (Power X) (2 ^ ordsucc n).
  rewrite exp_nat_S 2 n Hn.
  prove equip (Power X) (2 * 2 ^ n).
  claim L2nN: nat_p (2 ^ n).
  { aby nat_2 exp_nat_p Hn. }
  claim L2no: ordinal (2 ^ n).
  { aby nat_p_ordinal L2nN. }
  rewrite mul_nat_com 2 nat_2 (2 ^ n) L2nN.
  prove equip (Power X) (2 ^ n * 2).
  rewrite <- add_nat_1_1_2 at 2.
  prove equip (Power X) (2 ^ n * (1 + 1)).
  rewrite mul_add_nat_distrL (2 ^ n) L2nN 1 nat_1 1 nat_1.
  rewrite mul_nat_1R (2 ^ n).
  prove equip (Power X) (2 ^ n + 2 ^ n).
  claim L1: exists x, x :e X.
  { aby ordsuccI2 equip_sym H1. }
  apply L1.
  let x. assume Hx.
  claim L2: equip (X :\: {x}) n.
  { aby equip_ordsucc_remove1 Hx H1. }
  claim LIH: equip (Power (X :\: {x})) (2 ^ n).
  { aby L2 IHn. }
  apply LIH.
  let f.
  assume Hf: bij (Power (X :\: {x})) (2 ^ n) f.
  apply Hf. assume H. apply H.
  assume Hf1: forall Y :e Power (X :\: {x}), f Y :e 2 ^ n.
  assume Hf2: forall Y Z :e Power (X :\: {x}), f Y = f Z -> Y = Z.
  assume Hf3: forall i :e 2 ^ n, exists Y :e Power (X :\: {x}), f Y = i.
  claim LfN: forall Y :e Power (X :\: {x}), nat_p (f Y).
  { aby nat_p_trans Hf1 L2nN. }
  set g:set->set := fun Y => if x :e Y then 2 ^ n + f (Y :\: {x}) else f Y.
  prove equip (Power X) (2 ^ n + 2 ^ n).
  prove exists g:set->set, bij (Power X) (2 ^ n + 2 ^ n) g.
  witness g.
  prove bij (Power X) (2 ^ n + 2 ^ n) g.
  apply bijI.
  + let Y. assume HY: Y :e Power X.
    apply xm (x :e Y).
    * assume H2: x :e Y.
      claim LYx: Y :\: {x} :e Power (X :\: {x}).
      { aby PowerI PowerE setminusI setminusE HY. }
      aby If_i_1 nat_p_trans add_nat_com add_nat_In_R LYx H2 Hf1 L2nN.
    * assume H2: x /:e Y.
      claim LY: Y :e Power (X :\: {x}).
      { aby PowerI PowerE SingE setminusI H2 HY. }
      aby If_i_0 add_nat_Subq_R' LY H2 Hf1 L2nN.
  + let Y. assume HY: Y :e Power X.
    let Z. assume HZ: Z :e Power X.
    prove g Y = g Z -> Y = Z.
    prove (if x :e Y then 2 ^ n + f (Y :\: {x}) else f Y)
        = (if x :e Z then 2 ^ n + f (Z :\: {x}) else f Z)
       -> Y = Z.
    claim LYx: Y :\: {x} :e Power (X :\: {x}).
    { aby PowerI PowerE setminusI setminusE HY. }
    claim LZx: Z :\: {x} :e Power (X :\: {x}).
    { aby PowerI PowerE setminusI setminusE HZ. }
    claim LfYx2n: f (Y :\: {x}) :e 2 ^ n.
    { aby LYx Hf1. }
    claim LfYxN: nat_p (f (Y :\: {x})).
    { aby nat_p_trans LfYx2n L2nN. }
    claim LfZx2n: f (Z :\: {x}) :e 2 ^ n.
    { aby Hn IHn H1 L2nN L2no L1 Hx L2 LIH Hf H Hf1 Hf2 Hf3 LfN HY HZ LYx LZx LfYx2n LfYxN. }
    claim LfZxN: nat_p (f (Z :\: {x})).
    { aby nat_p_trans LfZx2n L2nN. }
    apply xm (x :e Y).
    * { assume H2: x :e Y.
        rewrite If_i_1 (x :e Y) (2 ^ n + f (Y :\: {x})) (f Y) H2.
        apply xm (x :e Z).
        - aby set_ext xm If_i_1 SingE setminusI setminusE1 add_nat_com add_nat_cancel_R H2 LfZxN LfYxN LZx LYx Hf2 L2nN.
        - assume H3: x /:e Z.
          claim LZ: Z :e Power (X :\: {x}).
          { aby PowerI PowerE SingE setminusI H3 HZ. }
          aby If_i_0 In_irref add_nat_Subq_R' LZ H3 LfYxN Hf1 L2nN.
      }
    * { assume H2: x /:e Y.
        claim LY: Y :e Power (X :\: {x}).
        { aby PowerI PowerE SingE setminusI H2 HY. }
        rewrite If_i_0 (x :e Y) (2 ^ n + f (Y :\: {x})) (f Y) H2.
        apply xm (x :e Z).
        - aby If_i_1 In_irref add_nat_Subq_R' LY LfZxN Hf1 L2nN.
        - aby PowerI PowerE If_i_0 SingE setminusI H2 HZ HY Hf2.
      }
  + let i. assume Hi: i :e 2 ^ n + 2 ^ n.
    prove exists Y :e Power X, g Y = i.
    claim LiN: nat_p i.
    { aby nat_p_trans add_nat_p Hi L2nN. }
    apply ordinal_In_Or_Subq i (2 ^ n) (nat_p_ordinal i LiN) L2no.
    * aby PowerI PowerE If_i_0 SingI setminusE1 setminusE2 Hf3.
    * { assume H2: 2 ^ n c= i.
        apply nat_Subq_add_ex (2 ^ n) L2nN i LiN H2.
        let k. assume H. apply H.
        assume Hk: nat_p k.
        assume Hik2n: i = k + 2 ^ n.
        claim L3: k :e 2 ^ n.
        { aby In_irref nat_p_ordinal ordinal_In_Or_Subq add_nat_Subq_R Hik2n Hk Hi L2no L2nN. }
        apply Hf3 k L3.
        let Y. assume H. apply H.
        assume HY: Y :e Power (X :\: {x}).
        assume HYk: f Y = k.
        claim LxnY: x /:e Y.
        { assume H3: x :e Y.
          aby PowerE SingI setminusE2 H3 HY.
        }
        claim LxYx: x :e Y :\/: {x}.
        { aby SingI binunionI2. }
        claim LYxxY: (Y :\/: {x}) :\: {x} = Y.
        { aby set_ext SingE binunionI1 binunionE setminusI setminusE LxnY. }
        aby PowerI Subq_tra PowerE If_i_1 SingE binunion_Subq_min setminus_Subq add_nat_com LYxxY LxYx HYk HY Hik2n Hk Hx L2nN.
      }
Qed.

End form100_52.

Theorem ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.
aby.
Qed.

Theorem ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.
aby ZF_closed_E.
Qed.

Theorem ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.
aby ZF_closed_E.
Qed.

Theorem ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.
aby ZF_closed_E.
Qed.

Theorem ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.
let U.
assume C: ZF_closed U.
let x.
assume Hx: x :e U.
let y.
assume Hy: y :e U.
prove {x,y} :e U.
claim L1: {if x :e X then x else y|X :e Power (Power x)} = {x,y}.
{
  apply set_ext.
  - aby xm ReplE_impred If_i_0 If_i_1 UPairI1 UPairI2.
  - aby EmptyE Empty_In_Power Self_In_Power ReplI If_i_0 If_i_1 UPairE.
}
aby xm If_i_0 If_i_1 ZF_Power_closed ZF_Repl_closed L1 Hy Hx C.
Qed.

Theorem ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.
aby ZF_UPair_closed.
Qed.

Theorem ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.
aby ZF_Union_closed ZF_UPair_closed. 
Qed.

Theorem ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.
aby ZF_Sing_closed ZF_binunion_closed.
Qed.

Theorem nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.
aby UnivOf_In UnivOf_ZF_closed nat_ind ZF_ordsucc_closed.
Qed.

(* Unicode omega "3c9" *)
(* Parameter omega "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "6fc30ac8f2153537e397b9ff2d9c981f80c151a73f96cf9d56ae2ee27dfd1eb2" *)
Definition omega : set := {n :e UnivOf Empty|nat_p n}.

Theorem omega_nat_p : forall n :e omega, nat_p n.
aby SepE2.
Qed.

Theorem nat_p_omega : forall n:set, nat_p n -> n :e omega.
aby SepI nat_p_UnivOf_Empty.
Qed.

Theorem omega_ordsucc : forall n :e omega, ordsucc n :e omega.
aby nat_ordsucc omega_nat_p nat_p_omega.
Qed.

Theorem form100_22_v2: forall f:set -> set, ~inj (Power omega) omega f.
aby form100_63_injCantor.
Qed.

Theorem form100_22_v3: forall g:set -> set, ~surj omega (Power omega) g.
let g. assume H1. apply H1.
assume H1: forall n :e omega, g n :e Power omega.
assume H2: forall X :e Power omega, exists n :e omega, g n = X.
set D := {n :e omega | n /:e g n}.
claim L1: D :e Power omega.
{ aby PowerI SepE1. }
aby SepI SepE2 L1 H2.
Qed.

Theorem form100_22_v1: ~equip omega (Power omega).
aby bij_surj form100_22_v3.
Qed.

Theorem omega_TransSet : TransSet omega.
aby nat_p_trans omega_nat_p nat_p_omega.
Qed.

Theorem omega_ordinal : ordinal omega.
aby ordinal_TransSet nat_p_ordinal omega_nat_p omega_TransSet.
Qed.

Theorem ordsucc_omega_ordinal: ordinal (ordsucc omega).
aby ordinal_ordsucc omega_ordinal.
Qed.

Definition finite : set -> prop := fun X => exists n :e omega, equip X n.

Theorem nat_finite: forall n, nat_p n -> finite n.
aby equip_ref nat_p_omega.
Qed.

Theorem finite_ind : forall p:set -> prop,
    p Empty
 -> (forall X y, finite X -> y /:e X -> p X -> p (X :\/: {y}))
 -> forall X, finite X -> p X.
let p. assume H1 H2.
claim L1: forall n, nat_p n -> forall X, equip X n -> p X.
{ apply nat_ind.
  - aby equip_0_Empty H1.
  - let n. assume Hn.
    assume IHn: forall X, equip X n -> p X.
    let X. assume H3: equip X (ordsucc n).
    apply equip_sym X (ordsucc n) H3.
    let f. assume Hf: bij (ordsucc n) X f.
    apply bijE (ordsucc n) X f Hf.
    assume Hf1: forall i :e ordsucc n, f i :e X.
    assume Hf2: forall i j :e ordsucc n, f i = f j -> i = j.
    assume Hf3: forall x :e X, exists i :e ordsucc n, f i = x.
    set Z := {f i|i :e n}.
    set y := f n.
    claim L1a: X = Z :\/: {y}.
    { apply set_ext.
      - aby ReplI SingI binunionI1 binunionI2 ordsuccE Hf3.
      - aby ReplE_impred SingE binunionE ordsuccI1 ordsuccI2 Hf1.
    }
    claim L1b: equip Z n.
    { aby ReplI ReplE' ordsuccI1 bijI equip_sym Hf2. }
    aby ReplE_impred In_irref ordsuccI1 ordsuccI2 nat_p_omega L1b L1a Hf2 IHn Hn H2.
}
aby omega_nat_p L1.
Qed.

Theorem finite_Empty: finite 0.
aby nat_0 equip_ref nat_p_omega.
Qed.

Theorem Sing_finite: forall x, finite {x}.
aby nat_1 equip_Sing_1 nat_p_omega.
Qed.

Theorem adjoin_finite: forall X y, finite X -> finite (X :\/: {y}).
let X y. assume H1. apply H1.
let n. assume H. apply H.
assume Hn: n :e omega.
assume H2: equip X n.
apply equip_sym X n H2.
let f. assume Hf: bij n X f.
apply bijE n X f Hf.
assume Hf1: forall i :e n, f i :e X.
assume Hf2: forall i j :e n, f i = f j -> i = j.
assume Hf3: forall x :e X, exists i :e n, f i = x.
apply xm (y :e X).
- aby set_ext SingE binunionE binunion_Subq_1 H1.
- assume H3: y /:e X.
  prove exists m :e omega, equip (X :\/: {y}) m.
  witness ordsucc n. apply andI.
  + aby omega_ordsucc Hn.
  + prove equip (X :\/: {y}) (ordsucc n).
    apply equip_sym.
    prove exists g:set -> set, bij (ordsucc n) (X :\/: {y}) g.
    claim Lg: exists g:set -> set, (forall i :e n, g i = f i) /\ g n = y.
    { aby If_i_0 If_i_1 In_irref. }
    aby SingI SingE binunionI1 binunionI2 binunionE ordsuccI1 ordsuccI2 ordsuccE bijI Lg H3 Hf3 Hf2 Hf1.
Qed.

Theorem binunion_finite: forall X, finite X -> forall Y, finite Y -> finite (X :\/: Y).
let X. assume HX.
aby binunion_asso binunion_idr finite_ind adjoin_finite HX.
Qed.

Theorem famunion_nat_finite : forall X:set -> set, forall n, nat_p n -> (forall i :e n, finite (X i)) -> finite (\/_ i :e n, X i).
let X. apply nat_ind.
- assume _.
  aby famunion_Empty finite_Empty.
- let n. assume Hn.
  assume IHn: (forall i :e n, finite (X i)) -> finite (\/_ i :e n, X i).
  assume H1: forall i :e ordsucc n, finite (X i).
  prove finite (\/_ i :e ordsucc n, X i).
  claim L1: (\/_ i :e ordsucc n, X i) = (\/_ i :e n, X i) :\/: X n.
  { apply set_ext.
    - aby binunionI1 binunionI2 famunionI famunionE_impred ordsuccE.
    - aby binunionE' famunionI famunionE_impred ordsuccI1 ordsuccI2.
  }
  aby ordsuccI1 ordsuccI2 binunion_finite L1 H1 IHn.
Qed.

Theorem Subq_finite : forall X, finite X -> forall Y, Y c= X -> finite Y.
apply finite_ind.
- aby Empty_Subq_eq finite_Empty.
- let X z.
  assume HX: finite X.
  assume Hz: z /:e X.
  assume IH: forall Y, Y c= X -> finite Y.
  let Y.
  assume H1: Y c= X :\/: {z}.
  prove finite Y.
  apply xm (z :e Y).
  + assume H2: z :e Y.
    claim L1: Y = (Y :\: {z}) :\/: {z}.
    { aby set_ext xm SingE binunionI1 binunionI2 binunionE setminusI setminusE1 H2. }
    rewrite L1.
    aby binunionE setminusE adjoin_finite H1 IH.
  + aby SingE binunionE H1 IH.
Qed.

Definition infinite : set -> prop := fun A => ~finite A.

Section InfinitePrimes.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Definition divides_nat : set -> set -> prop :=
  fun m n => m :e omega /\ n :e omega /\ exists k :e omega, m * k = n.

Theorem divides_nat_ref: forall n, nat_p n -> divides_nat n n.
aby and3I nat_1 mul_nat_1R nat_p_omega.
Qed.

Theorem divides_nat_tra: forall k m n, divides_nat k m -> divides_nat m n -> divides_nat k n.
aby and3I mul_nat_p mul_nat_asso omega_nat_p nat_p_omega.
Qed.

Definition prime_nat : set -> prop :=
  fun n => n :e omega /\ 1 :e n /\ forall k :e omega, divides_nat k n -> k = 1 \/ k = n.

Theorem divides_nat_mulR: forall m n :e omega, divides_nat m (m * n).
aby and3I mul_nat_p omega_nat_p nat_p_omega.
Qed.

Theorem divides_nat_mulL: forall m n :e omega, divides_nat n (m * n).
aby mul_nat_com omega_nat_p divides_nat_mulR.
Qed.

Theorem Pi_nat_divides: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, nat_p (f i))
   -> (forall i :e n, divides_nat (f i) (Pi_nat f n)).
let f.
apply nat_ind.
- assume _. aby EmptyE.
- let n. assume Hn: nat_p n.
  assume IHn: (forall i :e n, nat_p (f i))
           -> (forall i :e n, divides_nat (f i) (Pi_nat f n)).
  assume Hf: forall i :e ordsucc n, nat_p (f i).
  claim L1: forall i :e n, nat_p (f i).
  { aby ordsuccI1 Hf. }
  aby ordsuccI2 ordsuccE Pi_nat_S Pi_nat_p nat_p_omega divides_nat_tra divides_nat_mulR divides_nat_mulL L1 Hf IHn Hn.
Qed.

Definition composite_nat : set -> prop :=
  fun n => n :e omega /\ exists k m :e omega, 1 :e k /\ 1 :e m /\ k * m = n.

Theorem prime_nat_or_composite_nat: forall n :e omega, 1 :e n -> prime_nat n \/ composite_nat n.
let n. assume Hn.
assume H1: 1 :e n.
apply xm (composite_nat n).
- aby.
- assume H2: ~composite_nat n.
  apply orIL.
  prove n :e omega /\ 1 :e n /\ forall k :e omega, divides_nat k n -> k = 1 \/ k = n.
  aby and3I dneg In_no2cycle In_0_1 nat_1 nat_p_ordinal ordinal_In_Or_Subq mul_nat_0R mul_nat_1R mul_nat_0L nat_le1_cases omega_nat_p H2 H1 Hn.
Qed.

Theorem prime_nat_divisor_ex: forall n, nat_p n -> 1 :e n -> exists p, prime_nat p /\ divides_nat p n.
apply nat_complete_ind.
let n. assume Hn.
assume IHn: forall k :e n, 1 :e k -> exists p, prime_nat p /\ divides_nat p k.
assume H1: 1 :e n.
apply prime_nat_or_composite_nat n (nat_p_omega n Hn) H1.
- aby divides_nat_ref Hn.
- assume H1: composite_nat n.
  apply H1.
  assume _ H. aby In_0_1 nat_trans mul_nat_0m_1n_In omega_nat_p divides_nat_tra divides_nat_mulR H IHn.
Qed.

Theorem nat_1In_not_divides_ordsucc: forall m n, 1 :e m -> divides_nat m n -> ~divides_nat m (ordsucc n).
let m n.
assume H1m: 1 :e m.
assume H1: divides_nat m n.
assume H2: divides_nat m (ordsucc n).
apply H1. assume H. apply H.
assume Hm: m :e omega.
assume Hn: n :e omega.
assume H. apply H.
let k. assume H. apply H.
assume Hk: k :e omega.
assume Hmk: m * k = n.
apply H2. assume _ H. apply H.
let k'. assume H. apply H.
assume Hk': k' :e omega.
assume Hmk': m * k' = ordsucc n.
claim Lm: nat_p m.
{ aby omega_nat_p Hm. }
claim Ln: nat_p n.
{ aby omega_nat_p Hn. }
claim Lk: nat_p k.
{ aby omega_nat_p Hk. }
claim Lk': nat_p k'.
{ aby omega_nat_p Hk'. }
claim L1: 1 + n = ordsucc n.
{ aby nat_0 add_nat_0L add_nat_SL Ln. }
aby In_irref ordsuccI2 nat_ordsucc nat_p_ordinal ordinal_ordsucc_In_Subq ordinal_In_Or_Subq add_nat_In_R mul_nat_SR mul_nat_Subq_L L1 Lk' Lk Ln Lm Hmk' Hmk H1m.
Qed.

Definition primes : set := {n :e omega|prime_nat n}.

Theorem form100_11_infinite_primes: infinite primes.
assume H1: finite primes.
apply H1.
let n. assume H. apply H.
assume Hn: n :e omega.
assume H2: equip primes n.
apply equip_sym primes n H2.
let f. assume H. apply H. assume H. apply H.
assume Hf1: forall i :e n, f i :e primes.
assume Hf2: forall i j :e n, f i = f j -> i = j.
assume Hf3: forall p :e primes, exists i :e n, f i = p.
set p := ordsucc (Pi_nat f n).
claim L1: forall i :e n, nat_p (f i).
{ aby SepE1 omega_nat_p Hf1. }
claim L2: 0 /:e primes.
{ assume H1: 0 :e primes.
  aby SepE2 In_no2cycle In_0_1 H1.
}
claim LPN: nat_p (Pi_nat f n).
{ aby Pi_nat_p omega_nat_p H1 H Hn H2 H H Hf1 Hf2 Hf3 L1 L2. }
claim LpN: nat_p p.
{ aby nat_ordsucc LPN. }
claim Lpo: p :e omega.
{ aby nat_p_omega LpN. }
claim L3: forall q, prime_nat q -> ~divides_nat q p.
{ aby SepI SepE omega_nat_p Pi_nat_divides nat_1In_not_divides_ordsucc L1 Hf3 Hf1 Hn. }
aby and3I Empty_Subq_eq In_no2cycle In_0_1 nat_1 nat_ordsucc_in_ordsucc ordinal_Empty nat_p_ordinal ordinal_In_Or_Subq mul_nat_0L nat_le1_cases Pi_nat_0_inv omega_nat_p divides_nat_ref divides_nat_tra prime_nat_divisor_ex L3 Lpo LpN LPN L2 L1 Hf1 Hn.
Qed.

End InfinitePrimes.

Section InfiniteRamsey.

Infix + 360 right := add_nat.

Theorem atleastp_omega_infinite: forall X, atleastp omega X -> infinite X.
aby nat_ordsucc nat_p_trans atleastp_tra Subq_atleastp equip_atleastp Pigeonhole_not_atleastp_ordsucc omega_nat_p nat_p_omega.
Qed.

Theorem infinite_remove1: forall X, infinite X -> forall y, infinite (X :\: {y}).
let X. assume HX. let y.
assume H1: finite (X :\: {y}).
apply xm (y :e X).
- aby binunion_remove1_eq Sing_finite binunion_finite H1 HX.
- aby set_ext SingE setminusI setminus_Subq H1 HX.
Qed.

Theorem infinite_Finite_Subq_ex: forall X, infinite X ->
  forall n, nat_p n -> exists Y c= X, equip Y n.
let X. assume HX.
apply nat_ind.
- aby Subq_Empty equip_ref.
- let n. assume Hn.
  assume IHn: exists Y c= X, equip Y n.
  prove exists Y c= X, equip Y (ordsucc n).
  apply IHn.
  let Y. assume H. apply H.
  assume HY: Y c= X.
  assume HYn: equip Y n.
  apply HYn.
  let f.
  assume Hf: bij Y n f.
  apply Hf. assume H. apply H.
  assume Hf1: forall y :e Y, f y :e n.
  assume Hf2: forall y y' :e Y, f y = f y' -> y = y'.
  assume Hf3: forall i :e n, exists y :e Y, f y = i.
  claim L1: exists z :e X, z /:e Y.
  { aby set_ext dneg nat_p_omega HYn HY Hn HX. }
  apply L1.
  let z. assume H. apply H.
  assume HzX: z :e X.
  assume HzY: z /:e Y.
  witness Y :\/: {z}.
  apply andI.
  + aby SingE binunion_Subq_min HzX HY.
  + prove equip (Y :\/: {z}) (ordsucc n).
    claim Lg: exists g:set->set, (forall y :e Y, g y = f y) /\ g z = n.
    { set g : set -> set := fun y => if y :e Y then f y else n.
      aby If_i_0 If_i_1 HzY.
    }
    aby and3I SingI SingE binunionI1 binunionI2 binunionE In_irref ordsuccI1 ordsuccI2 ordsuccE Lg Hf3 Hf2 Hf1.
Qed.

Theorem infiniteRamsey_lem: forall X, forall f g f':set -> set,
    infinite X
 -> (forall Z c= X, infinite Z -> f Z c= Z /\ infinite (f Z))
 -> (forall Z c= X, infinite Z -> g Z :e Z /\ g Z /:e f Z)
 -> f' 0 = f X
 -> (forall m, nat_p m -> f' (ordsucc m) = f (f' m))
 -> (forall m, nat_p m -> f' m c= X /\ infinite (f' m))
 /\ (forall m m' :e omega, m c= m' -> f' m' c= f' m)
 /\ (forall m m' :e omega, g (f' m) = g (f' m') -> m = m').
let X f g f'.
assume HX: infinite X.
assume Hf1: forall Z c= X, infinite Z -> f Z c= Z /\ infinite (f Z).
assume Hg1: forall Z c= X, infinite Z -> g Z :e Z /\ g Z /:e f Z.
assume Hf'0: f' 0 = f X.
assume Hf'S: forall m, nat_p m -> f' (ordsucc m) = f (f' m).
claim Lf'1: forall m, nat_p m -> f' m c= X /\ infinite (f' m).
{ apply nat_ind.
  - aby Hf'0 Hf1 HX.
  - aby Subq_tra Hf'S Hf1.
}
claim Lgf'mm'addSubq: forall m :e omega, forall m', nat_p m' -> f' (m + m') c= f' m.
{ let m. assume Hm.
  apply nat_ind.
  - aby Subq_ref add_nat_0R.
  - aby Subq_tra add_nat_SR add_nat_p omega_nat_p Hm Lf'1 Hf'S Hf1.
}
claim Lgf'mm'Subq: forall m m' :e omega, m c= m' -> f' m' c= f' m.
{ aby add_nat_com nat_Subq_add_ex omega_nat_p Lgf'mm'addSubq.
}
claim Lgf'injlem: forall m :e omega, forall m' :e m, g (f' m') <> g (f' m).
{ aby nat_p_trans nat_p_ordinal ordinal_ordsucc_In_Subq omega_nat_p nat_p_omega omega_ordsucc Lgf'mm'Subq Lf'1 Hf'S Hg1.
}
aby and3I nat_p_ordinal ordinal_trichotomy_or_impred omega_nat_p Lgf'injlem Lgf'mm'Subq Lf'1.
Qed.

Theorem infiniteRamsey: forall c, nat_p c -> forall n, nat_p n ->
  forall X, infinite X -> forall C:set -> set,
    (forall Y c= X, equip Y n -> C Y :e c)
 -> exists H c= X, exists i :e c, infinite H /\ forall Y c= H, equip Y n -> C Y = i.
apply nat_ind.
- aby EmptyE infinite_Finite_Subq_ex.
- let c. assume Hc: nat_p c.
  assume IHc: forall n, nat_p n ->
        forall X, infinite X
     -> forall C:set -> set,
        (forall Y c= X, equip Y n -> C Y :e c)
     -> exists H c= X, exists i :e c, infinite H /\ forall Y c= H, equip Y n -> C Y = i.
  prove forall n, nat_p n ->
        forall X, infinite X
     -> forall C:set -> set,
        (forall Y c= X, equip Y n -> C Y :e ordsucc c)
     -> exists H c= X, exists i :e ordsucc c, infinite H /\ forall Y c= H, equip Y n -> C Y = i.
  apply nat_ind.
  + aby Subq_Empty Subq_ref equip_ref equip_0_Empty.
  + let n.
    assume Hn: nat_p n.
    assume IHn: forall X, infinite X -> forall C:set -> set,
        (forall Y c= X, equip Y n -> C Y :e ordsucc c)
     -> exists H c= X, exists i :e ordsucc c, infinite H /\ forall Y c= H, equip Y n -> C Y = i.
    let X.
    assume HX: infinite X.
    let C.
    assume H1: forall Y c= X, equip Y (ordsucc n) -> C Y :e ordsucc c.
    prove exists H c= X, exists i :e ordsucc c, infinite H /\ forall Y c= H, equip Y (ordsucc n) -> C Y = i.
    apply dneg.
    assume H2: ~exists H c= X, exists i :e ordsucc c, infinite H /\ forall Y c= H, equip Y (ordsucc n) -> C Y = i.
    claim L1: forall X' c= X, infinite X' ->
              exists X'' c= X', exists x :e X', x /:e X'' /\ infinite X'' /\ forall Y c= X'', equip Y n -> C (Y :\/: {x}) = c.
    { let X'.
      assume HX'X: X' c= X.
      assume HX': infinite X'.
      apply dneg.
      assume H2': ~exists X'' c= X', exists x :e X', x /:e X'' /\ infinite X'' /\ forall Y c= X'', equip Y n -> C (Y :\/: {x}) = c.
      claim L1a: exists x, x :e X'.
      { aby Empty_eq dneg finite_Empty HX'. }
      apply L1a.
      let x.
      assume Hx: x :e X'.
      claim LX'xinf: infinite (X' :\: {x}).
      { aby infinite_remove1 HX'. }
      set C' : set->set := fun Y => C (Y :\/: {x}).
      claim LC'Sc: forall Y c= X' :\: {x}, equip Y n -> C' Y :e ordsucc c.
      { aby Subq_tra SingI SingE binunion_Subq_min setminusE2 setminus_Subq equip_sym equip_adjoin_ordsucc Hx HX'X H1. }
      claim L1b: forall Z c= X', infinite Z -> exists Z' c= Z, exists y :e Z, y /:e Z' /\ infinite Z' /\ forall Y c= Z', equip Y n -> C (Y :\/: {y}) :e c.
      { apply dneg.
        assume H3: ~forall Z c= X', infinite Z -> exists Z' c= Z, exists y :e Z, y /:e Z' /\ infinite Z' /\ forall Y c= Z', equip Y n -> C (Y :\/: {y}) :e c.
        apply IHn (X' :\: {x}) LX'xinf C' LC'Sc.
        let H'. assume H. apply H.
        assume HH'X': H' c= X' :\: {x}.
        assume H. apply H.
        let i. assume H. apply H.
        assume Hi: i :e ordsucc c. assume H. apply H.
        assume HH'inf: infinite H'.
        assume HH'hom: forall Y c= H', equip Y n -> C (Y :\/: {x}) = i.
        apply ordsuccE c i Hi.
        - assume H4: i :e c.
          apply H3.
          let Z.
          assume HZX': Z c= X'.
          assume HZ: infinite Z.
          apply dneg.
          assume H5: ~exists Z' c= Z, exists y :e Z, y /:e Z' /\ infinite Z' /\ forall Y c= Z', equip Y n -> C (Y :\/: {y}) :e c.
          claim L1b1: exists y, y :e Z.
          { aby Empty_eq dneg finite_Empty HZ. }
          apply L1b1.
          let y. assume Hy: y :e Z.
          claim LZyinf: infinite (Z :\: {y}).
          { aby infinite_remove1 HZ. }
          claim LZyX': Z :\: {y} c= X'.
          { aby Subq_tra setminus_Subq HZX'. }
          claim LZyX: Z :\: {y} c= X.
          { aby Subq_tra LZyX' HX'X. }
          set C'' : set->set := fun Y => C (Y :\/: {y}).
          claim LC''Sc: forall Y c= Z :\: {y}, equip Y n -> C'' Y :e ordsucc c.
          { aby Subq_tra SingI SingE binunion_Subq_min setminusE2 equip_sym equip_adjoin_ordsucc LZyX Hy HZX' HX'X H1. }
          apply IHn (Z :\: {y}) LZyinf C'' LC''Sc.
          let H'. assume H. aby and3I Subq_tra SingI setminusE2 setminus_Subq ordsuccE H LZyX' Hy H5 HZX' H2'.
        - aby and3I Subq_tra SingI setminusE2 setminus_Subq HH'hom HH'inf HH'X' Hx H2'.
        }
        set f:set->set := fun Z => Eps_i (fun Z' => Z' c= Z /\ exists y :e Z, y /:e Z' /\ infinite Z' /\ forall Y c= Z', equip Y n -> C (Y :\/: {y}) :e c).
        claim Lf1: forall Z c= X', infinite Z -> f Z c= Z /\ exists y :e Z, y /:e f Z /\ infinite (f Z) /\ forall Y c= f Z, equip Y n -> C (Y :\/: {y}) :e c.
        { let Z. assume HZ1 HZ2.
          exact Eps_i_ex (fun Z' => Z' c= Z /\ exists y :e Z, y /:e Z' /\ infinite Z' /\ forall Y c= Z', equip Y n -> C (Y :\/: {y}) :e c) (L1b Z HZ1 HZ2).
        }
        claim Lf1a: forall Z c= X', infinite Z -> f Z c= Z /\ infinite (f Z).
        { aby Lf1. }
        set g:set->set := fun Z => Eps_i (fun y => y :e Z /\ (y /:e f Z /\ forall Y c= f Z, equip Y n -> C (Y :\/: {y}) :e c)).
        claim Lg1: forall Z c= X', infinite Z -> g Z :e Z /\ (g Z /:e f Z /\ forall Y c= f Z, equip Y n -> C (Y :\/: {g Z}) :e c).
        { aby Eps_i_ax Lf1. }
        claim Lg1a: forall Z c= X', infinite Z -> g Z :e Z /\ g Z /:e f Z.
	{ aby Lg1. }
        claim Lf': exists f':set -> set, f' 0 = f X' /\ forall m, nat_p m -> f' (ordsucc m) = f (f' m).
        { witness nat_primrec (f X') (fun _ Z => f Z).
          apply andI.
          - aby nat_primrec_0 Hc IHc Hn IHn HX H1 H2 HX'X HX' H2' L1a Hx LX'xinf LC'Sc L1b Lf1 Lf1a Lg1 Lg1a.
          - exact nat_primrec_S (f X') (fun _ Z => f Z). }
        apply Lf'.
        let f'. assume H. apply H.
        assume Hf'0 Hf'S.
	apply infiniteRamsey_lem X' f g f' HX' Lf1a Lg1a Hf'0 Hf'S.
	assume H. apply H.
	assume Hf'1: forall m, nat_p m -> f' m c= X' /\ infinite (f' m).
	assume Hgf'mm'Subq: forall m m' :e omega, m c= m' -> f' m' c= f' m.
        assume Hgf'inj: forall m m' :e omega, g (f' m) = g (f' m') -> m = m'.
        set H' := {g (f' n)|n :e omega}.
        claim LH'X: H' c= X.
        { let u. assume Hu: u :e H'.
          apply ReplE_impred omega (fun n => g (f' n)) u Hu.
          aby omega_nat_p Hf'1 Lg1 HX'X.
        }
        claim LH'inf: infinite H'.
        { apply atleastp_omega_infinite.
          aby ReplI Hgf'inj.
        }
        claim LCSnlem: forall m, nat_p m
              -> forall Y c= H', equip Y (ordsucc n)
              -> g (f' m) :e Y -> (forall k :e m, g (f' k) /:e Y)
              -> C Y :e c.
        { let m. assume Hm. let Y.
          assume HYH': Y c= H'.
          assume HYSn: equip Y (ordsucc n).
          assume Hgf'mY: g (f' m) :e Y.
          assume Hgf'kY: forall k :e m, g (f' k) /:e Y.
          apply Hf'1 m Hm.
          assume Hf'mX': f' m c= X'.
          assume Hf'minf: infinite (f' m).
          apply Lg1 (f' m) Hf'mX' Hf'minf.
          assume Hgf'mf'm: g (f' m) :e f' m.
          assume H. apply H.
          assume Hgf'mff'm: g (f' m) /:e f (f' m).
          assume Hgf'mc: forall Y c= f (f' m), equip Y n -> C (Y :\/: {g (f' m)}) :e c.
          claim Lmo: ordinal m.
          { aby nat_p_ordinal Hm. }
          prove C Y :e c.
          rewrite binunion_remove1_eq Y (g (f' m)) Hgf'mY.
          prove C ((Y :\: {g (f' m)}) :\/: {g (f' m)}) :e c.
          apply Hgf'mc.
          - prove Y :\: {g (f' m)} c= f (f' m).
            let u. assume Hu: u :e Y :\: {g (f' m)}.
            claim Luf'Sm: u :e f' (ordsucc m).
            { apply setminusE Y {g (f' m)} u Hu.
              assume Hu1: u :e Y.
              assume Hu2: u /:e {g (f' m)}.
              apply ReplE_impred omega (fun n => g (f' n)) u (HYH' u Hu1).
              let k.
              assume Hk: k :e omega.
              assume Huk: u = g (f' k).
              prove u :e f' (ordsucc m).
              claim Lko: ordinal k.
              { aby nat_p_ordinal omega_nat_p Hk. }
              apply ordinal_trichotomy_or_impred k m Lko Lmo.
              - aby Huk Hu1 Hgf'kY.
              - aby SingI Huk Hu2.
              - aby ordinal_ordsucc_In_Subq omega_nat_p nat_p_omega omega_ordsucc Lko Huk Hk Hm Hgf'mm'Subq Hf'1 Lg1.
            }
                aby Luf'Sm Hm Hf'S.
          - aby equip_ordsucc_remove1 Hgf'mY HYSn.
        }
        claim LCSn: forall Y c= H', equip Y (ordsucc n) -> C Y :e c.
        { let Y.
          assume HYH': Y c= H'.
          assume HYSn: equip Y (ordsucc n).
          prove C Y :e c.
          set p : set -> prop := fun m => m :e omega /\ g (f' m) :e Y.
          claim Lpne: exists m, ordinal m /\ p m.
          { apply equip_sym Y (ordsucc n) HYSn.
            let h.
            assume Hh: bij (ordsucc n) Y h.
            apply Hh. assume H _. apply H.
            assume Hh1: forall i :e ordsucc n, h i :e Y.
            assume _.
            claim LhnY: h n :e Y.
            { aby ordsuccI2 Hh1. }
            apply ReplE_impred omega (fun n => g (f' n)) (h n) (HYH' (h n) LhnY).
            aby nat_p_ordinal omega_nat_p LhnY.
          }
          apply least_ordinal_ex p Lpne.
          let m. assume H. apply H. assume H. apply H.
          assume Hmo: ordinal m.
          assume Hpm: m :e omega /\ g (f' m) :e Y.
          assume Hpk: forall k :e m, ~(k :e omega /\ g (f' k) :e Y).
          apply Hpm.
          assume Hm: m :e omega.
          assume Hgf'm: g (f' m) :e Y.
          prove C Y :e c.
          apply LCSnlem m (omega_nat_p m Hm) Y HYH' HYSn Hgf'm.
          aby nat_p_trans omega_nat_p nat_p_omega Hm Hpk.
        }
        apply IHc (ordsucc n) (nat_ordsucc n Hn) H' LH'inf C LCSn.
        aby Subq_tra ordsuccI1 LH'X H2.
    }
    set f:set->set := fun X' => Eps_i (fun X'' => X'' c= X' /\ exists x :e X', x /:e X'' /\ infinite X'' /\ forall Y c= X'', equip Y n -> C (Y :\/: {x}) = c).
    claim Lf1: forall X' c= X, infinite X' -> f X' c= X' /\ exists x :e X', x /:e f X' /\ infinite (f X') /\ forall Y c= f X', equip Y n -> C (Y :\/: {x}) = c.
    { aby Eps_i_ex L1. }
    claim Lf1a: forall Z c= X, infinite Z -> f Z c= Z /\ infinite (f Z).
    { aby Lf1. }
    set g:set->set := fun X' => Eps_i (fun x => x :e X' /\ (x /:e f X' /\ forall Y c= f X', equip Y n -> C (Y :\/: {x}) = c)).
    claim Lg1: forall X' c= X, infinite X' -> g X' :e X' /\ (g X' /:e f X' /\ forall Y c= f X', equip Y n -> C (Y :\/: {g X'}) = c).
    { aby Eps_i_ax Lf1. }
    claim Lg1a: forall Z c= X, infinite Z -> g Z :e Z /\ g Z /:e f Z.
    { aby Lg1. }
    claim Lf': exists f':set -> set, f' 0 = f X /\ forall m, nat_p m -> f' (ordsucc m) = f (f' m).
    { witness nat_primrec (f X) (fun _ Z => f Z).
      apply andI.
      - aby nat_primrec_0 Hc IHc Hn IHn HX H1 H2 L1 Lf1 Lf1a Lg1 Lg1a.
      - exact nat_primrec_S (f X) (fun _ Z => f Z). }
    apply Lf'.
    let f'. assume H. apply H.
    assume Hf'0 Hf'S.
    apply infiniteRamsey_lem X f g f' HX Lf1a Lg1a Hf'0 Hf'S.
    assume H. apply H.
    assume Hf'1: forall m, nat_p m -> f' m c= X /\ infinite (f' m).
    assume Hgf'mm'Subq: forall m m' :e omega, m c= m' -> f' m' c= f' m.
    assume Hgf'inj: forall m m' :e omega, g (f' m) = g (f' m') -> m = m'.
    set H' := {g (f' n)|n :e omega}.
    claim Lf'1: forall m, nat_p m -> f' m c= X /\ infinite (f' m).
    { apply nat_ind.
      - aby Hf'0 Lf1 HX.
      - aby Subq_tra Hf'S Lf1.
    }
    claim Lgf'mm'addSubq: forall m :e omega, forall m', nat_p m' -> f' (m + m') c= f' m.
    { let m. assume Hm.
      apply nat_ind.
      - aby Subq_ref add_nat_0R.
      - aby Subq_tra add_nat_SR add_nat_p omega_nat_p Hm Lf'1 Hf'S Lf1.
    }
    claim Lgf'mm'Subq: forall m m' :e omega, m c= m' -> f' m' c= f' m.
    { aby add_nat_com nat_Subq_add_ex omega_nat_p Lgf'mm'addSubq. }
    claim Lgf'injlem: forall m :e omega, forall m' :e m, g (f' m') <> g (f' m).
    { let m. assume Hm: m :e omega.
      let m'. assume Hm': m' :e m.
      assume H3: g (f' m') = g (f' m).
      claim LmN: nat_p m.
      { apply omega_nat_p. aby Hc IHc Hn IHn HX H1 H2 L1 Lf1 Lf1a Lg1 Lg1a Lf' H Hf'0 Hf'S H Hf'1 Hgf'mm'Subq Hgf'inj Lf'1 Lgf'mm'addSubq Lgf'mm'Subq Hm Hm' H3. }
      claim Lmo: ordinal m.
      { apply nat_p_ordinal. aby Hc IHc Hn IHn HX H1 H2 L1 Lf1 Lf1a Lg1 Lg1a Lf' H Hf'0 Hf'S H Hf'1 Hgf'mm'Subq Hgf'inj Lf'1 Lgf'mm'addSubq Lgf'mm'Subq Hm Hm' H3 LmN. }
      claim Lm'N: nat_p m'.
      { aby nat_p_trans omega_nat_p Hc IHc Hn IHn HX H1 H2 L1 Lf1 Lf1a Lg1 Lg1a Lf' H Hf'0 Hf'S H Hf'1 Hgf'mm'Subq Hgf'inj Lf'1 Lgf'mm'addSubq Lgf'mm'Subq Hm Hm' H3 LmN Lmo. }
      claim Lf'mff'm': f' m c= f (f' m').
      { apply Hf'S m' Lm'N (fun u _ => f' m c= u).
        prove f' m c= f' (ordsucc m').
        apply Lgf'mm'Subq (ordsucc m') (omega_ordsucc m' (nat_p_omega m' Lm'N)) m Hm.
        prove ordsucc m' c= m.
        aby ordinal_ordsucc_In_Subq Hc IHc Hn IHn HX H1 H2 L1 Lf1 Lf1a Lg1 Lg1a Lf' H Hf'0 Hf'S H Hf'1 Hgf'mm'Subq Hgf'inj Lf'1 Lgf'mm'addSubq Lgf'mm'Subq Hm Hm' H3 LmN Lmo Lm'N.
      }
      apply Lf'1 m (omega_nat_p m Hm).
      assume H4: f' m c= X.
      assume H5: infinite (f' m).
      apply Lg1 (f' m) H4 H5.
      assume H6: g (f' m) :e f' m.
      assume _.
      apply Lf'1 m' Lm'N.
      assume H7: f' m' c= X.
      assume H8: infinite (f' m').
      apply Lg1 (f' m') H7 H8.
      assume _ H. apply H.
      assume H9: g (f' m') /:e f (f' m').
      assume _.
      apply H9.
      prove g (f' m') :e f (f' m').
      rewrite H3.
      prove g (f' m) :e f (f' m').
      exact Lf'mff'm' (g (f' m)) H6.
    }
    claim Lgf'inj: forall m m' :e omega, g (f' m) = g (f' m') -> m = m'.
    { let m. assume Hm: m :e omega.
      let m'. assume Hm': m' :e omega.
      assume Hgf'mm': g (f' m) = g (f' m').
      apply ordinal_trichotomy_or_impred m m' (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal m' (omega_nat_p m' Hm')).
      - aby Hgf'mm' Hm' Lgf'injlem.
      - aby.
      - aby Hgf'mm' Hm Lgf'injlem.
    }
    claim LH'X: H' c= X.
    { let u. assume Hu: u :e H'.
      apply ReplE_impred omega (fun n => g (f' n)) u Hu.
      aby omega_nat_p Lf'1 Lg1.
    }
    claim LH'inf: infinite H'.
    { apply atleastp_omega_infinite.
      aby ReplI Lgf'inj.
    }
    claim LCSnlem: forall m, nat_p m
          -> forall Y c= H', equip Y (ordsucc n)
          -> g (f' m) :e Y -> (forall k :e m, g (f' k) /:e Y)
          -> C Y = c.
    { let m. assume Hm. let Y.
      assume HYH': Y c= H'.
      assume HYSn: equip Y (ordsucc n).
      assume Hgf'mY: g (f' m) :e Y.
      assume Hgf'kY: forall k :e m, g (f' k) /:e Y.
      apply Lf'1 m Hm.
      assume Hf'mX: f' m c= X.
      assume Hf'minf: infinite (f' m).
      apply Lg1 (f' m) Hf'mX Hf'minf.
      assume Hgf'mf'm: g (f' m) :e f' m.
      assume H. apply H.
      assume Hgf'mff'm: g (f' m) /:e f (f' m).
      assume Hgf'mc: forall Y c= f (f' m), equip Y n -> C (Y :\/: {g (f' m)}) = c.
      claim Lmo: ordinal m.
      { aby nat_p_ordinal Hm. }
      prove C Y = c.
      rewrite binunion_remove1_eq Y (g (f' m)) Hgf'mY.
      prove C ((Y :\: {g (f' m)}) :\/: {g (f' m)}) = c.
      apply Hgf'mc.
      - prove Y :\: {g (f' m)} c= f (f' m).
        let u. assume Hu: u :e Y :\: {g (f' m)}.
        claim Luf'Sm: u :e f' (ordsucc m).
        { apply setminusE Y {g (f' m)} u Hu.
          assume Hu1: u :e Y.
          assume Hu2: u /:e {g (f' m)}.
          apply ReplE_impred omega (fun n => g (f' n)) u (HYH' u Hu1).
          let k.
          assume Hk: k :e omega.
          assume Huk: u = g (f' k).
          prove u :e f' (ordsucc m).
          claim Lko: ordinal k.
          { aby nat_p_ordinal omega_nat_p Hk. }
          apply ordinal_trichotomy_or_impred k m Lko Lmo.
          - aby Huk Hu1 Hgf'kY.
          - aby SingI Huk Hu2.
          - aby ordinal_ordsucc_In_Subq omega_nat_p nat_p_omega omega_ordsucc Lko Huk Hk Hm Lgf'mm'Subq Lf'1 Lg1.
        }
        aby Luf'Sm Hm Hf'S.
      - aby equip_ordsucc_remove1 Hgf'mY HYSn.
    }
    claim LCSn: forall Y c= H', equip Y (ordsucc n) -> C Y = c.
    { let Y.
      assume HYH': Y c= H'.
      assume HYSn: equip Y (ordsucc n).
      prove C Y = c.
      set p : set -> prop := fun m => m :e omega /\ g (f' m) :e Y.
      claim Lpne: exists m, ordinal m /\ p m.
      { apply equip_sym Y (ordsucc n) HYSn.
        let h.
        assume Hh: bij (ordsucc n) Y h.
        apply Hh. assume H _. apply H.
        assume Hh1: forall i :e ordsucc n, h i :e Y.
        assume _.
        claim LhnY: h n :e Y.
        { aby ordsuccI2 Hh1. }
        apply ReplE_impred omega (fun n => g (f' n)) (h n) (HYH' (h n) LhnY).
        aby nat_p_ordinal omega_nat_p LhnY.
      }
      apply least_ordinal_ex p Lpne.
      let m. assume H. apply H. assume H. apply H.
      assume Hmo: ordinal m.
      assume Hpm: m :e omega /\ g (f' m) :e Y.
      assume Hpk: forall k :e m, ~(k :e omega /\ g (f' k) :e Y).
      apply Hpm.
      assume Hm: m :e omega.
      assume Hgf'm: g (f' m) :e Y.
      prove C Y = c.
      apply LCSnlem m (omega_nat_p m Hm) Y HYH' HYSn Hgf'm.
      aby nat_p_trans omega_nat_p nat_p_omega Hm Hpk.
    }
    aby ordsuccI2 LCSn LH'inf LH'X H2.
Qed.

End InfiniteRamsey.

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec_i (fun X f => {0} :\/: {f x|x :e X}).

Theorem Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
aby ReplEq_ext In_rec_i_eq.
Qed.

Theorem Inj1I1 : forall X:set, 0 :e Inj1 X.
aby SingI binunionI1 Inj1_eq.
Qed.

Theorem Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
aby ReplI binunionI2 Inj1_eq.
Qed.

Theorem Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
aby ReplE SingE binunionE Inj1_eq.
Qed.

Theorem Inj1NE1 : forall x:set, Inj1 x <> 0.
aby EmptyE Inj1I1.
Qed.

Theorem Inj1NE2 : forall x:set, Inj1 x /:e {0}.
aby SingE Inj1NE1.
Qed.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

Theorem Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
aby ReplI.
Qed.

Theorem Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.
aby ReplE.
Qed.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec_i (fun X f => {f x|x :e X :\: {0}}).

Theorem Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
claim L1: forall X:set, forall g h:set->set, (forall x :e X, g x = h x) -> {g x|x :e X :\: {0}} = {h x|x :e X :\: {0}}.
{
  aby ReplEq_ext setminusE1.
}
aby In_rec_i_eq L1.
Qed.

Theorem Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
apply In_ind.
let X.
assume IH: forall x :e X, Unj (Inj1 x) = x.
prove Unj (Inj1 X) = X.
rewrite Unj_eq.
prove {Unj x|x :e Inj1 X :\: {0}} = X.
apply set_ext.
- aby ReplE_impred SingI setminusE exandE_i Inj1E IH.
- aby ReplI setminusI Inj1I2 Inj1NE2 IH.
Qed.

Theorem Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
aby Unj_Inj1_eq.
Qed.

Theorem Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
let X.
rewrite (Unj_eq (Inj0 X)).
prove {Unj x|x :e Inj0 X :\: {0}} = X.
apply set_ext.
- aby ReplE_impred setminusE Unj_Inj1_eq.
- aby ReplI setminusI Inj1NE2 Unj_Inj1_eq.
Qed.

Theorem Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
aby Unj_Inj0_eq.
Qed.

Theorem Inj0_0 : Inj0 0 = 0.
aby Repl_Empty.
Qed.

Theorem Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.
aby Inj1I1 Inj1NE1 Inj0E.
Qed.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.
(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

Theorem Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
aby ReplI binunionI1.
Qed.

Theorem Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
aby ReplI binunionI2.
Qed.

Theorem setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).
aby ReplE binunionE.
Qed.

Theorem Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
aby set_ext EmptyE exandE_i Inj0I Inj0E Inj1_setsum setsum_Inj_inv.
Qed.

Theorem Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
let X. apply set_ext.
- aby SingE exandE_i Subq_1_Sing0 Inj1I1 Inj1I2 Inj0_0 setsum_Inj_inv.
- aby In_0_1 exandE_i Inj1E Inj0_0 Inj0_setsum Inj1_setsum.
Qed.

Section pair_setsum.
Let pair := setsum.
Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.
Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

Theorem Inj0_pair_0_eq : Inj0 = pair 0.
aby Inj0_setsum_0L.
Qed.

Theorem Inj1_pair_1_eq : Inj1 = pair 1.
aby Inj1_setsum_1L.
Qed.

Theorem pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
aby Inj0_setsum Inj0_pair_0_eq.
Qed.

Theorem pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
aby Inj1_setsum Inj1_pair_1_eq.
Qed.

Theorem pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
aby setsum_Inj_inv Inj0_pair_0_eq Inj1_pair_1_eq.
Qed.

Theorem pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
aby exandE_i Inj0_inj Inj0_Inj1_neq Inj0_pair_0_eq Inj1_pair_1_eq pairE.
Qed.

Theorem pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
aby exandE_i Inj1_inj Inj0_Inj1_neq Inj0_pair_0_eq Inj1_pair_1_eq pairE.
Qed.

Theorem proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
aby ReplSepI Unj_Inj0_eq Inj0_pair_0_eq.
Qed.

Theorem proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
aby ReplSepE_impred Unj_Inj0_eq Inj0_pair_0_eq.
Qed.

Theorem proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
aby ReplSepI Unj_Inj1_eq Inj1_pair_1_eq.
Qed.

Theorem proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
aby ReplSepE_impred Unj_Inj1_eq Inj1_pair_1_eq.
Qed.

Theorem proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
aby set_ext pairI0 pairE0 proj0I proj0E.
Qed.

Theorem proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
aby set_ext pairI1 pairE1 proj1I proj1E.
Qed.

Opaque add_nat mul_nat omega ordsucc setminus binintersect ReplSep Sep famunion binunion Sing UPair exactly1of2 If_i If_ii If_iii Descr_Vo1 Descr_iii Descr_ii inv In_rec_i In_rec_ii In_rec_iii.

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.
(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

Theorem Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).
aby and3I ReplE_impred famunionE exandE_i proj0_pair_eq proj1_pair_eq.
Qed.

Theorem proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.
aby and3E Sigma_eta_proj0_proj1.
Qed.

Theorem proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).
aby and3E Sigma_eta_proj0_proj1.
Qed.

Theorem pair_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, pair x y :e Sigma_ x :e X, Y x.
aby ReplI famunionI.
Qed.

Theorem pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.
aby proj0_pair_eq proj1_pair_eq proj1_Sigma.
Qed.

Theorem Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.
aby and3E Sigma_eta_proj0_proj1.
Qed.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.
(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.
(*** lam X F = {(x,y) | x :e X, y :e F x} = \/_{x :e X} {(x,y) | y :e (F x)} = Sigma X F ***)
Let lam : set -> (set -> set) -> set := Sigma.
(***  ap f x = {proj1 z | z :e f,  exists y, z = pair x y}} ***)
Definition ap : set -> set -> set := fun f x => {proj1 z|z :e f, exists y:set, z = pair x y}.
Notation SetImplicitOp ap.
Notation SetLam Sigma.

Theorem lamI : forall X:set, forall F:set->set, forall x :e X, forall y :e F x, pair x y :e fun x :e X => F x.
aby pair_Sigma.
Qed.

Theorem lamE : forall X:set, forall F:set->set, forall z:set, z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = pair x y.
aby Sigma_E.
Qed.

Theorem apI : forall f x y, pair x y :e f -> y :e f x.
aby ReplSepI proj1_pair_eq.
Qed.

Theorem apE : forall f x y, y :e f x -> pair x y :e f.
aby ReplSepE_impred proj1_pair_eq.
Qed.

Theorem beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.
aby set_ext pair_Sigma pair_Sigma_E1 lamI apI apE.
Qed.

Theorem proj0_ap_0 : forall u, proj0 u = u 0.
aby set_ext proj0I proj0E apI apE.
Qed.

Theorem proj1_ap_1 : forall u, proj1 u = u 1.
aby set_ext proj1I proj1E apI apE.
Qed.

Theorem pair_ap_0 : forall x y:set, (pair x y) 0 = x.
aby proj0_pair_eq proj0_ap_0.
Qed.

Theorem pair_ap_1 : forall x y:set, (pair x y) 1 = y.
aby proj1_pair_eq proj1_ap_1.
Qed.

Theorem ap0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 0) :e X.
aby proj0_Sigma proj0_ap_0.
Qed.

Theorem ap1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 1) :e (Y (z 0)).
aby proj1_Sigma proj0_ap_0 proj1_ap_1.
Qed.

Definition pair_p:set->prop
:= fun u:set => pair (u 0) (u 1) = u.

Theorem pair_p_I : forall x y, pair_p (pair x y).
aby pair_ap_0 pair_ap_1.
Qed.

Theorem Subq_2_UPair01 : 2 c= {0,1}.
aby UPairI1 UPairI2 SingE ordsuccE Subq_1_Sing0.
Qed.

Theorem tuple_pair : forall x y:set, pair x y = (x,y).
let x y. apply set_ext.
- aby If_i_0 If_i_1 In_0_2 In_1_2 neq_1_0 exandE_i pairE pair_Sigma lamI.
- aby If_i_0 If_i_1 UPairE neq_1_0 exandE_i pairI0 pairI1 Sigma_E lamE Subq_2_UPair01.
Qed.

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.
(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Theorem PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.
let X Y f.
assume H1: forall u :e f, pair_p u /\ u 0 :e X.
assume H2: forall x :e X, f x :e Y x.
aby PowerI UnionI SepI pair_Sigma lamI apI H2 H1.
Qed.

Theorem lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).
aby exandE_i Sigma_E lamE beta pair_ap_0 pair_p_I PiI.
Qed.

Theorem ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.
aby SepE2.
Qed.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.
(* Superscript :^: *)
Infix :^: 430 left := setexp.

Theorem pair_tuple_fun : pair = (fun x y => (x,y)).
aby tuple_pair.
Qed.

Section Tuples.
Variable x0 x1: set.

Theorem tuple_2_0_eq: (x0,x1) 0 = x0.
aby If_i_1 In_0_2 beta.
Qed.

Theorem tuple_2_1_eq: (x0,x1) 1 = x1.
aby If_i_0 In_1_2 neq_1_0 beta.
Qed.

End Tuples.

Theorem ReplEq_setprod_ext : forall X Y, forall F G:set -> set -> set, (forall x :e X, forall y :e Y, F x y = G x y) -> {F (w 0) (w 1)|w :e X :*: Y} = {G (w 0) (w 1)|w :e X :*: Y}.
aby ReplEq_ext ap0_Sigma ap1_Sigma.
Qed.

Theorem lamI2 : forall X, forall F:set->set, forall x :e X, forall y :e F x, (x,y) :e fun x :e X => F x.
aby pair_Sigma lamI pair_tuple_fun.
Qed.

Theorem tuple_2_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, (x,y) :e Sigma_ x :e X, Y x.
aby lamI2.
Qed.

Theorem tuple_2_setprod : forall X:set, forall Y:set, forall x :e X, forall y :e Y, (x,y) :e X :*: Y.
aby lamI2 tuple_2_Sigma.
Qed.

End pair_setsum.
(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.
(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.
(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.
(* Superscript :^: *)
Infix :^: 430 left := setexp.
(* Parameter DescrR_i_io_1 "1f005fdad5c6f98763a15a5e5539088f5d43b7d1be866b0b204fda1ce9ed9248" "1d3fd4a14ef05bd43f5c147d7966cf05fd2fed808eea94f56380454b9a6044b2" *)
Definition DescrR_i_io_1 : (set->(set->prop)->prop) -> set := fun R => Eps_i (fun x => (exists y:set -> prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)).
(* Parameter DescrR_i_io_2 "28d8599686476258c12dcc5fc5f5974335febd7d5259e1a8e5918b7f9b91ca03" "768eb2ad186988375e6055394e36e90c81323954b8a44eb08816fb7a84db2272" *)
Definition DescrR_i_io_2 : (set->(set->prop)->prop) -> set->prop := fun R => Descr_Vo1 (fun y => R (DescrR_i_io_1 R) y).

Theorem DescrR_i_io_12 : forall R:set->(set->prop)->prop, (exists x, (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)) -> R (DescrR_i_io_1 R) (DescrR_i_io_2 R).
aby Eps_i_ex Descr_Vo1_prop.
Qed.

(** Conway describes this way of formalizing in ZF in an appendix to Part Zero of his book,
    but rejects formalization in favor of "Mathematician's Liberation."
 **)
Definition PNoEq_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => forall beta :e alpha, p beta <-> q beta.

Theorem PNoEq_ref_ : forall alpha, forall p:set -> prop, PNoEq_ alpha p p.
aby.
Qed.

Theorem PNoEq_sym_ : forall alpha, forall p q:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q p.
aby iff_sym.
Qed.

Theorem PNoEq_tra_ : forall alpha, forall p q r:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q r -> PNoEq_ alpha p r.
aby iff_trans.
Qed.

Theorem PNoEq_antimon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoEq_ alpha p q -> PNoEq_ beta p q.
aby.
Qed.

Definition PNoLt_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.

Theorem PNoLt_E_ : forall alpha, forall p q:set -> prop, PNoLt_ alpha p q ->
  forall R:prop, (forall beta, beta :e alpha -> PNoEq_ beta p q -> ~p beta -> q beta -> R) -> R.
aby.
Qed.

Theorem PNoLt_irref_ : forall alpha, forall p:set -> prop, ~PNoLt_ alpha p p.
aby.
Qed.

Theorem PNoLt_mon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoLt_ beta p q -> PNoLt_ alpha p q.
aby.
Qed.

Theorem PNoLt_trichotomy_or_ : forall p q:set -> prop, forall alpha, ordinal alpha
  -> PNoLt_ alpha p q \/ PNoEq_ alpha p q \/ PNoLt_ alpha q p.
let p q.
apply ordinal_ind.
aby xm and3I not_all_ex_demorgan_i PNoEq_sym_ PNoLt_mon_.
Qed.

(* Parameter PNoLt "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "8f57a05ce4764eff8bc94b278352b6755f1a46566cd7220a5488a4a595a47189" *)
Definition PNoLt : set -> (set -> prop) -> set -> (set -> prop) -> prop
 := fun alpha p beta q =>
        PNoLt_ (alpha :/\: beta) p q
     \/ alpha :e beta /\ PNoEq_ alpha p q /\ q alpha
     \/ beta :e alpha /\ PNoEq_ beta p q /\ ~p beta.

Theorem PNoLtI1 : forall alpha beta, forall p q:set -> prop,
  PNoLt_ (alpha :/\: beta) p q -> PNoLt alpha p beta q.
aby or3I1.
Qed.

Theorem PNoLtI2 : forall alpha beta, forall p q:set -> prop,
  alpha :e beta -> PNoEq_ alpha p q -> q alpha -> PNoLt alpha p beta q.
aby and3I or3I2.
Qed.

Theorem PNoLtI3 : forall alpha beta, forall p q:set -> prop,
  beta :e alpha -> PNoEq_ beta p q -> ~p beta -> PNoLt alpha p beta q.
aby and3I or3I3.
Qed.

Theorem PNoLtE : forall alpha beta, forall p q:set -> prop,
  PNoLt alpha p beta q ->
  forall R:prop,
      (PNoLt_ (alpha :/\: beta) p q -> R)
   -> (alpha :e beta -> PNoEq_ alpha p q -> q alpha -> R)
   -> (beta :e alpha -> PNoEq_ beta p q -> ~p beta -> R)
   -> R.
aby.
Qed.

Theorem PNoLt_irref : forall alpha, forall p:set -> prop, ~PNoLt alpha p alpha p.
aby In_irref PNoLt_irref_ PNoLtE.
Qed.

Theorem PNoLt_trichotomy_or : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q \/ PNoLt beta q alpha p.
aby xm or3I1 or3I2 or3I3 Subq_ref binintersect_Subq_eq_1 binintersect_com ordinal_trichotomy_or ordinal_binintersect PNoEq_sym_ PNoLt_trichotomy_or_ PNoLtI1 PNoLtI2 PNoLtI3.
Qed.

Theorem PNoLtEq_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoEq_ beta q r -> PNoLt alpha p beta r.
aby and3I binintersectE PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI2 PNoLtI3 PNoLtE.
Qed.

Theorem PNoEqLt_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLt alpha q beta r -> PNoLt alpha p beta r.
aby and3I binintersectE PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI2 PNoLtI3 PNoLtE.
Qed.

Theorem PNoLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
aby and3I binintersectI binintersectE ordinal_Hered ordinal_trichotomy_or PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI2 PNoLtI3 PNoLtE.
Qed.

Definition PNoLe : set -> (set -> prop) -> set -> (set -> prop) -> prop
   := fun alpha p beta q => PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.

Theorem PNoLeI1 : forall alpha beta, forall p q:set -> prop,
   PNoLt alpha p beta q -> PNoLe alpha p beta q.
aby.
Qed.

Theorem PNoLeI2 : forall alpha, forall p q:set -> prop,
   PNoEq_ alpha p q -> PNoLe alpha p alpha q.
aby.
Qed.

Theorem PNoLe_ref : forall alpha, forall p:set -> prop, PNoLe alpha p alpha p.
aby PNoEq_ref_ PNoLeI2.
Qed.

Theorem PNoLe_antisym : forall alpha beta, ordinal alpha -> ordinal beta ->
 forall p q:set -> prop,
 PNoLe alpha p beta q -> PNoLe beta q alpha p -> alpha = beta /\ PNoEq_ alpha p q.
aby binintersectE In_irref PNoLtE PNoLt_irref PNoLt_tra.
Qed.

Theorem PNoLtLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLe beta q gamma r -> PNoLt alpha p gamma r.
aby PNoLtEq_tra PNoLt_tra.
Qed.

Theorem PNoLeLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.
aby PNoEqLt_tra PNoLt_tra.
Qed.

Theorem PNoEqLe_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLe alpha q beta r -> PNoLe alpha p beta r.
aby PNoEq_tra_ PNoEqLt_tra.
Qed.

Theorem PNoLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLe beta q gamma r -> PNoLe alpha p gamma r.
aby PNoLtLe_tra PNoEqLe_tra.
Qed.

Definition PNo_downc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun L alpha p => exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe alpha p beta q.
Definition PNo_upc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun R alpha p => exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q alpha p.

Theorem PNoLe_downc : forall L:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_downc L alpha p -> PNoLe beta q alpha p -> PNo_downc L beta q.
aby PNoLe_tra.
Qed.

Theorem PNo_downc_ref : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, L alpha p -> PNo_downc L alpha p.
aby PNoLe_ref.
Qed.

Theorem PNo_upc_ref : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, R alpha p -> PNo_upc R alpha p.
aby PNoLe_ref.
Qed.

Theorem PNoLe_upc : forall R:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_upc R alpha p -> PNoLe alpha p beta q -> PNo_upc R beta q.
aby PNoLe_tra.
Qed.

Definition PNoLt_pwise : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> prop
  := fun L R => forall gamma, ordinal gamma -> forall p:set -> prop, L gamma p -> forall delta, ordinal delta -> forall q:set -> prop, R delta q -> PNoLt gamma p delta q.

Theorem PNoLt_pwise_downc_upc : forall L R:set -> (set -> prop) -> prop,
    PNoLt_pwise L R -> PNoLt_pwise (PNo_downc L) (PNo_upc R).
aby PNoLt_irref PNoLt_trichotomy_or PNoLt_tra PNoLtLe_tra PNoLeLt_tra.
Qed.

Definition PNo_rel_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_downc L beta q -> PNoLt beta q alpha p.
Definition PNo_rel_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_upc R beta q -> PNoLt alpha p beta q.
Definition PNo_rel_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_upperbd L alpha p /\ PNo_rel_strict_lowerbd R alpha p.

Theorem PNoEq_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L alpha q.
aby ordinal_Hered PNoLtEq_tra.
Qed.

Theorem PNo_rel_strict_upperbd_antimon : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
aby binintersect_Subq_eq_1 In_no2cycle ordinal_Hered PNoLtI1 PNoLtI2 PNoLtE.
Qed.

Theorem PNoEq_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R alpha q.
aby ordinal_Hered PNoEq_sym_ PNoEqLt_tra.
Qed.

Theorem PNo_rel_strict_lowerbd_antimon : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
aby binintersect_Subq_eq_1 binintersect_com In_no2cycle ordinal_Hered PNoLtI1 PNoLtI3 PNoLtE.
Qed.

Theorem PNoEq_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R alpha q.
aby PNoEq_rel_strict_upperbd PNoEq_rel_strict_lowerbd.
Qed.

Theorem PNo_rel_strict_imv_antimon : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
aby PNo_rel_strict_upperbd_antimon PNo_rel_strict_lowerbd_antimon.
Qed.

Definition PNo_rel_strict_uniq_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_imv L R alpha p /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha p q.
Definition PNo_rel_strict_split_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p =>
         PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha)
      /\ PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).

Theorem PNo_extend0_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta /\ delta <> alpha).
aby In_irref.
Qed.

Theorem PNo_extend1_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta \/ delta = alpha).
aby In_irref.
Qed.

Theorem PNo_rel_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha ->
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
let L R. assume HLR.
claim LLR: PNoLt_pwise (PNo_downc L) (PNo_upc R).
{ aby PNoLt_pwise_downc_upc HLR. }
apply ordinal_ind.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume IH: forall gamma :e alpha,
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R gamma p)
   \/ (exists tau :e gamma, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
apply dneg.
assume HNC: ~((exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p)).
apply not_or_and_demorgan (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p) (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p) HNC.
assume HNC1: ~(exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p).
assume HNC2: ~(exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).
claim LIH: forall gamma :e alpha, exists p:set -> prop, PNo_rel_strict_uniq_imv L R gamma p.
{ aby HNC2 IH Ha1. }
apply ordinal_lim_or_succ alpha Ha.
- assume H1: forall beta :e alpha, ordsucc beta :e alpha.
  set pl : set -> prop := fun delta => forall p:set -> prop, PNo_rel_strict_imv L R (ordsucc delta) p -> p delta.
  claim Lpl1 : forall gamma, ordinal gamma -> gamma :e alpha -> PNo_rel_strict_uniq_imv L R gamma pl.
  { apply ordinal_ind.
    let gamma.
    assume Hc: ordinal gamma.
    assume IH2: forall delta :e gamma, delta :e alpha -> PNo_rel_strict_uniq_imv L R delta pl.
    assume Hc1: gamma :e alpha.
    apply LIH gamma Hc1.
    let p. assume Hp. apply Hp.
    assume Hp1: PNo_rel_strict_imv L R gamma p.
    apply Hp1. assume Hp1a Hp1b.
    assume Hp2: forall q:set -> prop, PNo_rel_strict_imv L R gamma q -> PNoEq_ gamma p q.
    claim Lplpe: PNoEq_ gamma pl p.
    { let delta. assume Hd: delta :e gamma.
      apply ordinal_ordsucc_In_eq gamma delta Hc Hd.
      - assume Hsd: ordsucc delta :e gamma.
        claim Lsda: ordsucc delta :e alpha.
        { aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Hc IH2 Hc1 Hp Hp1 Hp1a Hp1b Hp2 Hd Hsd. }
        aby ordsuccI2 PNo_rel_strict_imv_antimon Lsda Hsd Hp1 IH2 Hc.
      - aby Hd Hp2 Hp1.
    }
    aby ordinal_Hered PNoEq_sym_ PNoEq_tra_ PNoLtEq_tra PNoEqLt_tra Lplpe Hp2 Hp1b Hp1a Hc.
  }
  claim Lpl2 : forall gamma :e alpha, PNo_rel_strict_uniq_imv L R gamma pl.
  { aby ordinal_Hered Lpl1 Ha. }
  apply HNC1.
  witness pl.
  prove PNo_rel_strict_uniq_imv L R alpha pl.
  prove PNo_rel_strict_imv L R alpha pl /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha pl q.
  apply andI.
  + prove PNo_rel_strict_imv L R alpha pl.
    prove PNo_rel_strict_upperbd L alpha pl /\ PNo_rel_strict_lowerbd R alpha pl.
    apply andI.
    * { prove PNo_rel_strict_upperbd L alpha pl.
        let beta. assume Hb: beta :e alpha.
        let q. assume Hq: PNo_downc L beta q.
        claim Lb: ordinal beta.
        { aby ordinal_Hered Hb Ha. }
        claim Lsb: ordinal (ordsucc beta).
        { aby ordinal_ordsucc Lb. }
        prove PNoLt beta q alpha pl.
        apply PNoLt_trichotomy_or beta alpha q pl Lb Ha.
	- assume H2. aby In_irref H2 Hb.
        - assume H2: PNoLt alpha pl beta q.
          apply PNoLtE alpha beta pl q H2.
          + assume H3: PNoLt_ (alpha :/\: beta) pl q.
            apply H3.
            let gamma. assume H4. apply H4.
            assume Hc: gamma :e alpha :/\: beta.
            apply binintersectE alpha beta gamma Hc.
            assume Hc1 Hc2.
            assume H5. apply H5. assume H5. apply H5.
            assume H5: PNoEq_ gamma pl q.
            assume H6: ~pl gamma.
            assume H7: q gamma.
            claim Lc: ordinal gamma.
            { aby ordinal_Hered Hc2 Lb. }
            claim Lsc: ordinal (ordsucc gamma).
            { aby ordinal_ordsucc Lc. }
            prove False.
            apply H6.
            prove pl gamma.
            let p.
            assume Hp: PNo_rel_strict_imv L R (ordsucc gamma) p.
            prove p gamma.
            apply Hp. assume Hp1 Hp2.
            claim Lqp: PNoLt gamma q (ordsucc gamma) p.
            { aby ordsuccI2 PNoEq_ref_ PNoLtI2 PNoLeI1 PNoLe_downc Hp1 Lc H7 Hc2 Lb Hq. }
            apply PNoLtE gamma (ordsucc gamma) q p Lqp.
            * aby binintersectE ordsuccI2 ordinal_Hered ordinal_ordsucc_In PNo_rel_strict_imv_antimon Hp Lsc Lc H5 Hc1 Lpl2 H1 Ha1.
            * aby.
            * aby In_no2cycle ordsuccI2.
          + aby In_no2cycle Hb.
          + assume H3: beta :e alpha.
            assume H4: PNoEq_ beta pl q.
            assume H5: ~pl beta.
            prove False.
            apply H5.
            prove pl beta.
            let p.
            assume Hp: PNo_rel_strict_imv L R (ordsucc beta) p.
            prove p beta.
            apply Hp. assume Hp1 Hp2.
            claim Lqp: PNoLt beta q (ordsucc beta) p.
            { aby ordsuccI2 HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb H2 H3 H4 H5 Hp Hp1 Hp2. }
            apply PNoLtE beta (ordsucc beta) q p Lqp.
            * aby binintersectE ordsuccI2 ordinal_Hered ordinal_ordsucc_In PNo_rel_strict_imv_antimon Hp H4 Lsb Lb Hb Lpl2 H1 Ha1.
            * aby.
            * aby In_no2cycle ordsuccI2.
      }
    * { prove PNo_rel_strict_lowerbd R alpha pl.
        let beta. assume Hb: beta :e alpha.
        let q. assume Hq: PNo_upc R beta q.
        claim Lb: ordinal beta.
        { aby ordinal_Hered Hb Ha. }
        claim Lsb: ordinal (ordsucc beta).
        { aby ordinal_ordsucc Lb. }
        claim Lsba: ordsucc beta :e alpha.
        { aby Hb H1. }
        prove PNoLt alpha pl beta q.
        apply PNoLt_trichotomy_or alpha beta pl q Ha Lb.
	- assume H2. aby In_irref H2 Hb.
        - assume H2: PNoLt beta q alpha pl.
          apply PNoLtE beta alpha q pl H2.
          + assume H3: PNoLt_ (beta :/\: alpha) q pl.
            apply H3.
            let gamma. assume H4. apply H4.
            assume Hc: gamma :e beta :/\: alpha.
            apply binintersectE beta alpha gamma Hc.
            assume Hc2 Hc1.
            assume H5. apply H5. assume H5. apply H5.
            assume H5: PNoEq_ gamma q pl.
            assume H6: ~q gamma.
            assume H7: pl gamma.
            claim Lc: ordinal gamma.
            { aby ordinal_Hered HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7. }
            claim Lsc: ordinal (ordsucc gamma).
            { aby ordinal_ordsucc HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc. }
            claim Lsca: ordsucc gamma :e alpha.
            { aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc. }
            prove False.
            apply Lpl2 (ordsucc gamma) Lsca.
            assume Hpl2: PNo_rel_strict_imv L R (ordsucc gamma) pl.
            assume _.
            apply Hpl2.
            assume _.
            assume Hpl2b: PNo_rel_strict_lowerbd R (ordsucc gamma) pl.
            claim Lplq: PNoLt (ordsucc gamma) pl gamma q.
            { apply Hpl2b gamma (ordsuccI2 gamma) q.
              prove PNo_upc R gamma q.
              apply PNoLe_upc R beta gamma q q Lb Lc.
              - prove PNo_upc R beta q. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b.
              - prove PNoLe beta q gamma q.
                apply PNoLeI1 beta gamma q q.
                prove PNoLt beta q gamma q.
                apply PNoLtI3.
                + prove gamma :e beta. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b.
                + prove PNoEq_ gamma q q. apply PNoEq_ref_.
                + prove ~q gamma. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b.
            }
            claim Lqpl: PNoLt gamma q (ordsucc gamma) pl.
            { apply PNoLtI2.
              - prove gamma :e ordsucc gamma. apply ordsuccI2.
              - prove PNoEq_ gamma q pl. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b Lplq.
              - prove pl gamma. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b Lplq.
            }
            prove False.
            apply PNoLt_irref gamma q.
            aby PNoLt_tra HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 Lpl1 Lpl2 Hb Hq Lb Lsb Lsba H2 H3 H4 Hc Hc2 Hc1 H5 H5 H5 H6 H7 Lc Lsc Lsca Hpl2 Hpl2b Lplq Lqpl.
          + assume H3: beta :e alpha.
            assume H4: PNoEq_ beta q pl.
            assume H5: pl beta.
            apply Lpl2 (ordsucc beta) Lsba.
            assume Hpl2: PNo_rel_strict_imv L R (ordsucc beta) pl.
            assume _.
            aby ordsuccI2 PNoLtI2 PNoLt_irref PNoLt_tra Hpl2 H5 H4 Lsb Lb Hq.
          + aby In_no2cycle Hb.
      }
  + aby ordsuccI2 PNo_rel_strict_imv_antimon Lpl2 H1 Ha.
- assume H1: exists beta :e alpha, alpha = ordsucc beta.
  apply H1.
  let beta. assume H1. apply H1.
  assume Hb: beta :e alpha.
  assume Hab: alpha = ordsucc beta.
  claim Lb: ordinal beta.
  { aby ordinal_Hered Hb Ha. }
  claim Lsb: ordinal (ordsucc beta).
  { aby Hab Ha. }
  claim Lbsb1: beta :/\: ordsucc beta = beta.
  { aby binintersect_Subq_eq_1 ordsuccI1. }
  claim Lbsb2: ordsucc beta :/\: beta = beta.
  { aby binintersect_com Lbsb1. }
  apply LIH beta Hb.
  let p.
  assume Hp: PNo_rel_strict_uniq_imv L R beta p.
  apply Hp.
  assume Hp0: PNo_rel_strict_imv L R beta p.
  apply Hp0.
  assume Hp1: forall gamma :e beta, forall q:set -> prop, PNo_downc L gamma q -> PNoLt gamma q beta p.
  assume Hp2: forall gamma :e beta, forall q:set -> prop, PNo_upc R gamma q -> PNoLt beta p gamma q.
  assume Hp3: forall q:set -> prop, PNo_rel_strict_imv L R beta q -> PNoEq_ beta p q.
  set p0 : set -> prop := fun delta => p delta /\ delta <> beta.
  set p1 : set -> prop := fun delta => p delta \/ delta = beta.
  claim Lp0e: PNoEq_ beta p0 p.
  { aby In_irref. }
  claim Lp0b: ~p0 beta.
  { assume H2: p beta /\ beta <> beta. aby H2. }
  claim Lp0p: PNoLt (ordsucc beta) p0 beta p.
  { aby ordsuccI2 PNoLtI3 Lp0b Lp0e. }
  claim Lp1e: PNoEq_ beta p p1.
  { aby In_irref. }
  claim Lp1b: p1 beta.
  { aby. }
  claim Lpp1: PNoLt beta p (ordsucc beta) p1.
  { aby ordsuccI2 PNoLtI2 Lp1b Lp1e. }
  claim Lnotboth: ~(PNo_rel_strict_imv L R alpha p0 /\ PNo_rel_strict_imv L R alpha p1).
  { aby Hab Hb HNC2. }
  claim Lcases : (forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q)
              \/ (forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q).
  { rewrite eq_or_nand.
     assume H2. apply H2.
     assume H2: ~(forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q).
     assume H3: ~(forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q).
     apply H2.
     let q0.
     assume H4: PNo_downc L beta q0.
     assume H5: PNoEq_ beta p q0.
     apply H3.
     let q1.
     assume H6: PNo_upc R beta q1.
     assume H7: PNoEq_ beta p q1.
     claim L2: PNoLt beta q0 beta q1.
     { aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth H2 H2 H3 H4 H5 H6 H7. }
     apply PNoLt_irref beta q0.
     apply PNoLtLe_tra beta beta beta Lb Lb Lb q0 q1 q0 L2.
     prove PNoLe beta q1 beta q0.
     prove PNoLt beta q1 beta q0 \/ beta = beta /\ PNoEq_ beta q1 q0.
     apply orIR.
     apply andI.
     - reflexivity.
     - prove PNoEq_ beta q1 q0. apply PNoEq_tra_ beta q1 p q0.      
       + prove PNoEq_ beta q1 p. apply PNoEq_sym_. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth H2 H2 H3 H4 H5 H6 H7 L2.
       + prove PNoEq_ beta p q0. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth H2 H2 H3 H4 H5 H6 H7 L2. }
  prove False.
  apply Lcases.
  + assume H2: forall q:set -> prop, PNo_downc L beta q -> ~PNoEq_ beta p q.
    claim Lp0imv: PNo_rel_strict_imv L R (ordsucc beta) p0.
    { prove PNo_rel_strict_upperbd L (ordsucc beta) p0
         /\ PNo_rel_strict_lowerbd R (ordsucc beta) p0.
      apply andI.
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_downc L gamma q.
        claim Lc: ordinal gamma.
        { aby ordinal_Hered Hc Lsb. }
        prove PNoLt gamma q (ordsucc beta) p0.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          claim L1: PNoLt gamma q beta p.
          { aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4. }
          aby and3I binintersectI binintersectE In_irref In_no2cycle ordsuccI1 PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI2 PNoLtE L1 H4 Lp0e Lb.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt beta q (ordsucc beta) p0.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p0 Lb Lsb.
	  * assume H5. aby In_irref ordsuccI2 H5.
          * { assume H5: PNoLt (ordsucc beta) p0 beta q.
              apply PNoLtE (ordsucc beta) beta p0 q H5.
              - rewrite Lbsb2.
                assume H6: PNoLt_ beta p0 q.
                apply H6.
                let delta. assume H7. apply H7.
                assume Hd: delta :e beta.
                assume H7. apply H7. assume H7. apply H7.
                assume H7: PNoEq_ delta p0 q.
                assume H8: ~p0 delta.
                assume H9: q delta.
                claim Ld: ordinal delta.
                { aby ordinal_Hered HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9. }
                claim L2: PNoLt beta p delta q.
                { apply PNoLtI3.
                  - prove delta :e beta. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld.
                  - prove PNoEq_ delta p q. apply PNoEq_tra_ delta p p0 q.
                    + prove PNoEq_ delta p p0. apply PNoEq_sym_.
                      apply PNoEq_antimon_ p0 p beta Lb delta Hd.
                      aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld.
                    + prove PNoEq_ delta p0 q. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld.
                  - prove ~p delta.
                    assume H10: p delta.
                    apply H8.
                    prove p delta /\ delta <> beta.
                    apply andI.
                    + aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld H10.
                    + assume H11: delta = beta. apply In_irref beta. rewrite <- H11 at 1.
                      aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld H10 H11.
                }
                claim L3: PNoLt delta q beta p.
                { apply Hp1 delta Hd q.
                  prove PNo_downc L delta q. (** This is where I need to use PNo_downc L instead of just L since all I know is PNo_downc L gamma q where gamma=beta here. **)
                  apply PNoLe_downc L gamma delta q q Lc Ld H3.
                  prove PNoLe delta q gamma q.
                  apply PNoLeI1.
                  prove PNoLt delta q gamma q.
                  apply PNoLtI2.
                  - prove delta :e gamma. rewrite H4. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld L2.
                  - prove PNoEq_ delta q q. apply PNoEq_ref_.
                  - prove q delta. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld L2.
                }
              apply PNoLt_irref delta q.
              prove PNoLt delta q delta q.
              aby PNoLt_tra HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5 H6 H7 Hd H7 H7 H7 H8 H9 Ld L2 L3.
              - aby In_no2cycle ordsuccI2.
              - aby PNoEq_sym_ PNoEq_tra_ H4 H3 H2 Lp0e.
            }
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_upc R gamma q.
        claim Lc: ordinal gamma.
        { aby ordinal_Hered Hc Lsb. }
        prove PNoLt (ordsucc beta) p0 gamma q.
        apply ordsuccE beta gamma Hc.
        + aby PNoLt_tra Lc H3 Lp0p Hp2 Lsb Lb.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt (ordsucc beta) p0 beta q.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p0 Lb Lsb. assume H5. apply H5.
          * { assume H5: PNoLt beta q (ordsucc beta) p0.
              apply PNoLtE beta (ordsucc beta) q p0 H5.
              - rewrite Lbsb1.
                assume H6: PNoLt_ beta q p0.
                apply H6.
                aby ordinal_Hered PNoEq_ref_ PNoEq_tra_ PNoEq_antimon_ PNoLtI2 PNoLtI3 PNoLt_irref PNoLt_tra PNoLeI1 PNoLe_upc H4 Lc H3 Lp0e Hp2 Lb.
              - aby.
              - aby In_no2cycle ordsuccI2.
            }
          * assume H5. aby In_irref ordsuccI2 H5.
          * aby.
    }
    apply HNC1.
    witness p0.
    rewrite Hab.
    prove PNo_rel_strict_uniq_imv L R (ordsucc beta) p0.
    prove PNo_rel_strict_imv L R (ordsucc beta) p0
       /\ forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc beta) q -> PNoEq_ (ordsucc beta) p0 q.
    apply andI.
    * aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Lp0imv.
    * { let q. assume Hq: PNo_rel_strict_imv L R (ordsucc beta) q.
        prove PNoEq_ (ordsucc beta) p0 q.
        aby xm In_irref ordsuccI2 ordsuccE PNoEq_rel_strict_imv PNo_rel_strict_imv_antimon Hq Lp0imv Lnotboth Hp3 Lsb Hab.
      }
  + assume H2: forall q:set -> prop, PNo_upc R beta q -> ~PNoEq_ beta p q.
    claim Lp1imv: PNo_rel_strict_imv L R (ordsucc beta) p1.
    { prove PNo_rel_strict_upperbd L (ordsucc beta) p1
         /\ PNo_rel_strict_lowerbd R (ordsucc beta) p1.
      apply andI.
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_downc L gamma q.
        claim Lc: ordinal gamma.
        { aby ordinal_Hered Hc Lsb. }
        prove PNoLt gamma q (ordsucc beta) p1.
        apply ordsuccE beta gamma Hc.
        + aby PNoLt_tra Lc H3 Lpp1 Hp1 Lsb Lb.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt beta q (ordsucc beta) p1.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p1 Lb Lsb.
	  * assume H5. aby In_irref ordsuccI2 H5.
          * { assume H5: PNoLt (ordsucc beta) p1 beta q.
              apply PNoLtE (ordsucc beta) beta p1 q H5.
              - aby ordinal_Hered PNoEq_ref_ PNoEq_tra_ PNoEq_antimon_ PNoLtI2 PNoLtI3 PNoLt_irref PNoLt_tra PNoLeI1 PNoLe_downc H4 Lc H3 Lp1e Hp1 Lbsb2 Lb.
              - aby In_no2cycle ordsuccI2.
              - aby.
            }
      - let gamma. assume Hc: gamma :e ordsucc beta. let q.
        assume H3: PNo_upc R gamma q.
        claim Lc: ordinal gamma.
        { aby ordinal_Hered Hc Lsb. }
        prove PNoLt (ordsucc beta) p1 gamma q.
        apply ordsuccE beta gamma Hc.
        + assume H4: gamma :e beta.
          claim L1: PNoLt beta p gamma q.
          { aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4. }
          aby and3I binintersectI binintersectE In_irref In_no2cycle ordsuccI1 PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI3 PNoLtE L1 H4 Lp1e Lb.
        + assume H4: gamma = beta.
          rewrite H4.
          prove PNoLt (ordsucc beta) p1 beta q.
          apply PNoLt_trichotomy_or beta (ordsucc beta) q p1 Lb Lsb. assume H5. apply H5.
          * { assume H5: PNoLt beta q (ordsucc beta) p1.
              apply PNoLtE beta (ordsucc beta) q p1 H5.
              - rewrite Lbsb1.
                assume H6: PNoLt_ beta q p1.
                apply H6.
                aby In_irref ordinal_Hered PNoEq_ref_ PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNoLtI2 PNoLtI3 PNoLt_irref PNoLt_tra PNoLeI1 PNoLe_upc H4 Lc H3 Lp1e Hp2 Lb.
              - aby PNoEq_sym_ PNoEq_tra_ H4 H3 H2 Lp1e.
              - aby In_no2cycle ordsuccI2.
            }
          * assume H5. aby In_irref ordsuccI2 H5.
          * assume H5. aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Hc H3 Lc H4 H5.
    }
    apply HNC1.
    witness p1.
    rewrite Hab.
    prove PNo_rel_strict_uniq_imv L R (ordsucc beta) p1.
    prove PNo_rel_strict_imv L R (ordsucc beta) p1
       /\ forall q:set -> prop, PNo_rel_strict_imv L R (ordsucc beta) q -> PNoEq_ (ordsucc beta) p1 q.
    apply andI.
    * aby HLR LLR Ha Ha1 IH HNC HNC1 HNC2 LIH H1 H1 Hb Hab Lb Lsb Lbsb1 Lbsb2 Hp Hp0 Hp1 Hp2 Hp3 Lp0e Lp0b Lp0p Lp1e Lp1b Lpp1 Lnotboth Lcases H2 Lp1imv.
    * aby xm In_irref ordsuccI2 ordsuccE PNoEq_rel_strict_imv PNo_rel_strict_imv_antimon Lp1imv Lnotboth Hp3 Lsb Hab.
Qed.

Definition PNo_lenbdd : set -> (set -> (set -> prop) -> prop) -> prop
  := fun alpha L => forall beta, forall p:set -> prop, L beta p -> beta :e alpha.

Theorem PNo_lenbdd_strict_imv_extend0 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha).
let L R.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume HaL HaR.
let p.
assume Hp1: PNo_rel_strict_imv L R alpha p.
apply Hp1.
assume Hp1a Hp1b.
set p0 : set -> prop := fun delta => p delta /\ delta <> alpha.
claim Lsa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
claim Lpp0e: PNoEq_ alpha p p0.
{ aby PNo_extend0_eq Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa. }
prove PNo_rel_strict_upperbd L (ordsucc alpha) p0 /\ PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
apply andI.
- prove PNo_rel_strict_upperbd L (ordsucc alpha) p0.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_downc L gamma q.
  claim Lc: ordinal gamma.
  { aby ordinal_Hered Hc Lsa. }
  prove PNoLt gamma q (ordsucc alpha) p0.
  apply Hq.
  let delta. assume Hq1. apply Hq1.
  assume Hd: ordinal delta. assume Hq1. apply Hq1.
  let r. assume Hq1. apply Hq1.
  assume Hr: L delta r.
  assume Hqr: PNoLe gamma q delta r.
  apply PNoLeLt_tra gamma delta (ordsucc alpha) Lc Hd Lsa q r p0 Hqr.
  prove PNoLt delta r (ordsucc alpha) p0.
  claim Lda: delta :e alpha.
  { aby Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa Lpp0e Hc Hq Lc Hq1 Hd Hq1 Hq1 Hr Hqr. }
  claim Ldsa: delta :e ordsucc alpha.
  { aby ordsuccI1 Lda. }
  claim Ldr: PNo_downc L delta r.
  { aby PNo_downc_ref Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa Lpp0e Hc Hq Lc Hq1 Hd Hq1 Hq1 Hr Hqr Lda Ldsa. }
  claim Lrp : PNoLt delta r alpha p.
  { aby Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa Lpp0e Hc Hq Lc Hq1 Hd Hq1 Hq1 Hr Hqr Lda Ldsa Ldr. }
  aby and3I binintersectI binintersectE In_irref In_no2cycle PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI3 PNoLtE PNoLt_irref PNoLt_trichotomy_or PNoLt_tra Lrp Ldsa Lda Hd Lpp0e Lsa Ha1 Ha.
- prove PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_upc R gamma q.
  claim Lc: ordinal gamma.
  { aby ordinal_Hered Hc Lsa. }
  prove PNoLt (ordsucc alpha) p0 gamma q.
  apply PNoLt_tra (ordsucc alpha) alpha gamma Lsa Ha Lc p0 p q.
  + aby ordsuccI2 PNoEq_sym_ PNoLtI3 Lpp0e.
  + prove PNoLt alpha p gamma q.
    apply Hq.
    let delta. assume Hq1. aby PNoLtLe_tra PNo_upc_ref Hq1 Lc Hp1b HaR Ha.
Qed.

Theorem PNo_lenbdd_strict_imv_extend1 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).
let L R.
let alpha. assume Ha. apply Ha. assume Ha1 _.
assume HaL HaR.
let p.
assume Hp1: PNo_rel_strict_imv L R alpha p.
apply Hp1.
assume Hp1a Hp1b.
set p1 : set -> prop := fun delta => p delta \/ delta = alpha.
claim Lsa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
claim Lpp1e: PNoEq_ alpha p p1.
{ aby PNo_extend1_eq Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa. }
prove PNo_rel_strict_upperbd L (ordsucc alpha) p1 /\ PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
apply andI.
- aby ordsuccI2 ordinal_Hered PNoLtI2 PNoLt_tra PNoLe_ref PNoLeLt_tra Lpp1e Lsa Hp1a HaL Ha.
- prove PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
  let gamma. assume Hc: gamma :e ordsucc alpha.
  let q. assume Hq: PNo_upc R gamma q.
  claim Lc: ordinal gamma.
  { aby ordinal_Hered Hc Lsa. }
  prove PNoLt (ordsucc alpha) p1 gamma q.
  apply Hq.
  let delta. assume Hq1. apply Hq1.
  assume Hd: ordinal delta. assume Hq1. apply Hq1.
  let r. assume Hq1. apply Hq1.
  assume Hr: R delta r.
  assume Hrq: PNoLe delta r gamma q.
  apply (fun H:PNoLt (ordsucc alpha) p1 delta r => PNoLtLe_tra (ordsucc alpha) delta gamma Lsa Hd Lc p1 r q H Hrq).
  prove PNoLt (ordsucc alpha) p1 delta r.
  claim Lda: delta :e alpha.
  { aby Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa Lpp1e Hc Hq Lc Hq1 Hd Hq1 Hq1 Hr Hrq. }
  claim Ldsa: delta :e ordsucc alpha.
  { aby ordsuccI1 Lda. }
  claim Ldr: PNo_upc R delta r.
  { aby PNoLe_ref Hr Hd. }
  claim Lpr : PNoLt alpha p delta r.
  { aby Ha Ha1 HaL HaR Hp1 Hp1a Hp1b Lsa Lpp1e Hc Hq Lc Hq1 Hd Hq1 Hq1 Hr Hrq Lda Ldsa Ldr. }
  aby and3I binintersectI binintersectE In_irref In_no2cycle PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNoLtI1 PNoLtI2 PNoLtE PNoLt_irref PNoLt_trichotomy_or PNoLt_tra Lpr Ldsa Lda Hd Lpp1e Lsa Ha1 Ha.
Qed.

Theorem PNo_lenbdd_strict_imv_split : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_split_imv L R alpha p.
aby PNo_lenbdd_strict_imv_extend0 PNo_lenbdd_strict_imv_extend1.
Qed.

Theorem PNo_rel_imv_bdd_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_rel_strict_split_imv L R beta p.
aby ordsuccI1 ordsuccI2 ordinal_ordsucc PNo_rel_imv_ex PNo_lenbdd_strict_imv_split.
Qed.

Definition PNo_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, L beta q -> PNoLt beta q alpha p.
Definition PNo_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, R beta q -> PNoLt alpha p beta q.
Definition PNo_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_strict_upperbd L alpha p /\ PNo_strict_lowerbd R alpha p.

Theorem PNoEq_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_upperbd L alpha p -> PNo_strict_upperbd L alpha q.
aby PNoLtEq_tra.
Qed.

Theorem PNoEq_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_lowerbd R alpha p -> PNo_strict_lowerbd R alpha q.
aby PNoEq_sym_ PNoEqLt_tra.
Qed.

Theorem PNoEq_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_imv L R alpha p -> PNo_strict_imv L R alpha q.
aby PNoEq_strict_upperbd PNoEq_strict_lowerbd.
Qed.

Theorem PNo_strict_upperbd_imp_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.
let L alpha.
assume Ha: ordinal alpha.
let beta.
assume Hb: beta :e ordsucc alpha.
let p.
assume H1: PNo_strict_upperbd L alpha p.
let gamma. assume Hc: gamma :e beta.
let q. assume Hq: PNo_downc L gamma q.
apply Ha. assume Ha1 _.
claim Lsa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
claim Lb: ordinal beta.
{ aby ordinal_Hered Lsa Hb. }
claim Lb1: TransSet beta.
{ aby Lb. }
claim Lc: ordinal gamma.
{ aby ordinal_Hered Lb Hc. }
claim Lcb: gamma c= beta.
{ aby Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc. }
prove PNoLt gamma q beta p.
apply Hq.
let delta. assume H2. apply H2.
assume Hd: ordinal delta. assume H2. apply H2.
let r. assume H2. apply H2.
assume H2: L delta r.
assume H3: PNoLe gamma q delta r.
claim L1: PNoLt delta r alpha p.
{ aby Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc Lcb H2 Hd H2 H2 H2 H3. }
claim L2: PNoLt gamma q alpha p.
{ aby PNoLeLt_tra Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc Lcb H2 Hd H2 H2 H2 H3 L1. }
aby binintersect_Subq_eq_1 binintersect_com In_irref In_no2cycle ordsuccE PNoLtI1 PNoLtI3 PNoLtE PNoLt_irref PNoLt_trichotomy_or PNoLt_tra L2 Lcb Lc Lb Ha1 Hc Hb Ha.
Qed.

Theorem PNo_strict_lowerbd_imp_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.
let R alpha.
assume Ha: ordinal alpha.
let beta.
assume Hb: beta :e ordsucc alpha.
let p.
assume H1: PNo_strict_lowerbd R alpha p.
let gamma. assume Hc: gamma :e beta.
let q. assume Hq: PNo_upc R gamma q.
apply Ha. assume Ha1 _.
claim Lsa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
claim Lb: ordinal beta.
{ aby ordinal_Hered Lsa Hb. }
claim Lb1: TransSet beta.
{ aby Lb. }
claim Lc: ordinal gamma.
{ aby ordinal_Hered Lb Hc. }
claim Lcb: gamma c= beta.
{ aby Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc. }
prove PNoLt beta p gamma q.
apply Hq.
let delta. assume H2. apply H2.
assume Hd: ordinal delta. assume H2. apply H2.
let r. assume H2. apply H2.
assume H2: R delta r.
assume H3: PNoLe delta r gamma q.
claim L1: PNoLt alpha p delta r.
{ aby Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc Lcb H2 Hd H2 H2 H2 H3. }
claim L2: PNoLt alpha p gamma q.
{ aby PNoLtLe_tra Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc Lcb H2 Hd H2 H2 H2 H3 L1. }
claim Lca: gamma :e alpha.
{ aby ordsuccE Ha1 Hc Hb. }
claim Lca2: gamma c= alpha.
{ aby Ha Hb H1 Hc Hq Ha1 Lsa Lb Lb1 Lc Lcb H2 Hd H2 H2 H2 H3 L1 L2 Lca. }
aby binintersect_Subq_eq_1 In_irref In_no2cycle PNoLtI1 PNoLtI2 PNoLtE PNoLt_irref PNoLt_trichotomy_or PNoLt_tra Lca2 Lca L2 Lcb Lc Lb Hc Ha.
Qed.

Theorem PNo_strict_imv_imp_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.
aby PNo_strict_upperbd_imp_rel_strict_upperbd PNo_strict_lowerbd_imp_rel_strict_lowerbd.
Qed.

Theorem PNo_rel_split_imv_imp_strict_imv : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> forall p:set -> prop,
       PNo_rel_strict_split_imv L R alpha p
    -> PNo_strict_imv L R alpha p.
let L R.
let alpha.
assume Ha: ordinal alpha.
let p.
assume Hp: PNo_rel_strict_split_imv L R alpha p.
claim Lsa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
set p0 : set -> prop := fun delta => p delta /\ delta <> alpha.
set p1 : set -> prop := fun delta => p delta \/ delta = alpha.
apply Hp.
assume Hp0: PNo_rel_strict_imv L R (ordsucc alpha) p0.
assume Hp1: PNo_rel_strict_imv L R (ordsucc alpha) p1.
apply Hp0.
assume Hp0a: PNo_rel_strict_upperbd L (ordsucc alpha) p0.
assume Hp0b: PNo_rel_strict_lowerbd R (ordsucc alpha) p0.
apply Hp1.
assume Hp1a: PNo_rel_strict_upperbd L (ordsucc alpha) p1.
assume Hp1b: PNo_rel_strict_lowerbd R (ordsucc alpha) p1.
claim Lnp0a: ~p0 alpha.
{ assume H10. aby H10. }
claim Lp1a: p1 alpha.
{ aby. }
claim Lap0p: PNoLt (ordsucc alpha) p0 alpha p.
{ aby ordsuccI2 PNoEq_sym_ PNoLtI3 PNo_extend0_eq Lnp0a. }
claim Lapp1: PNoLt alpha p (ordsucc alpha) p1.
{ aby ordsuccI2 PNoLtI2 PNo_extend1_eq Lp1a. }
aby dneg binintersectE ordsuccI1 ordsuccI2 ordsuccE ordinal_Hered PNoEq_ref_ PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNoLtI2 PNoLtI3 PNoLtE PNoLt_irref PNoLt_trichotomy_or PNoLt_tra PNoLeI1 PNo_downc_ref PNo_upc_ref PNo_extend0_eq PNo_extend1_eq Lapp1 Lap0p Lp1a Lnp0a Hp1b Hp0a Lsa Ha.
Qed.

Theorem PNo_lenbdd_strict_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_strict_imv L R beta p.
aby ordinal_Hered ordinal_ordsucc PNo_rel_imv_bdd_ex PNo_rel_split_imv_imp_strict_imv.
Qed.

Definition PNo_least_rep : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => ordinal beta
       /\ PNo_strict_imv L R beta p
       /\ forall gamma :e beta,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.
Definition PNo_least_rep2 : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => PNo_least_rep L R beta p /\ forall x, x /:e beta -> ~p x.

Theorem PNo_strict_imv_pred_eq : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha -> forall p q:set -> prop,
     PNo_least_rep L R alpha p
  -> PNo_strict_imv L R alpha q
  -> forall beta :e alpha, p beta <-> q beta.
let L R. assume HLR. let alpha. assume Ha. let p q.
assume Hp.
assume Hq.
apply Ha. assume Ha1 _.
apply Hp. assume Hp1. apply Hp1.
assume _.
assume Hp1: PNo_strict_imv L R alpha p.
assume Hp2: forall beta :e alpha, forall r:set -> prop, ~PNo_strict_imv L R beta r.
apply Hp1.
assume Hp1a: PNo_strict_upperbd L alpha p.
assume Hp1b: PNo_strict_lowerbd R alpha p.
apply Hq.
assume Hq1: PNo_strict_upperbd L alpha q.
assume Hq2: PNo_strict_lowerbd R alpha q.
claim L1: forall beta, ordinal beta -> beta :e alpha -> (p beta <-> q beta).
{ apply ordinal_ind.
  let beta. assume Hb1: ordinal beta.
  assume IH: forall gamma :e beta, gamma :e alpha -> (p gamma <-> q gamma).
  assume Hb2: beta :e alpha.
  claim Lbpq: PNoEq_ beta p q.
  { aby Hb2 IH Ha1. }
  aby dneg PNoEq_ref_ PNoEq_sym_ PNoLtI2 PNoLtI3 PNoLt_tra Lbpq Hb2 Hb1 Hq2 Hq1 Hp1b Hp1a Hp2 Ha.
}
aby ordinal_Hered L1 Ha.
Qed.

Theorem PNo_lenbdd_least_rep2_exuniq2 : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta,
        (exists p:set -> prop, PNo_least_rep2 L R beta p)
     /\ (forall p q:set -> prop, PNo_least_rep2 L R beta p -> PNo_least_rep2 L R beta q -> p = q).
let L R. assume HLR. let alpha. assume Ha HaL HaR.
claim L1: exists beta, ordinal beta /\ (exists p:set -> prop, PNo_strict_imv L R beta p) /\ forall gamma :e beta, ~(exists p:set -> prop, PNo_strict_imv L R gamma p).
{ apply least_ordinal_ex (fun beta => exists p:set -> prop, PNo_strict_imv L R beta p).
  aby ordinal_Hered ordinal_ordsucc PNo_lenbdd_strict_imv_ex HaR HaL Ha HLR.
}
apply L1.
let beta. assume H1. apply H1. assume H1. apply H1.
assume H1: ordinal beta.
assume H2: exists p:set -> prop, PNo_strict_imv L R beta p.
assume H3: forall gamma :e beta, ~exists p:set -> prop, PNo_strict_imv L R gamma p.
apply H2.
let p. assume Hp: PNo_strict_imv L R beta p.
witness beta.
apply andI.
- witness (fun x => x :e beta /\ p x).
  prove PNo_least_rep L R beta (fun x => x :e beta /\ p x) /\ forall x, x /:e beta -> ~(x :e beta /\ p x).
  apply andI.
  + prove ordinal beta
     /\ PNo_strict_imv L R beta (fun x => x :e beta /\ p x)
     /\ forall gamma :e beta,
         forall q:set -> prop, ~PNo_strict_imv L R gamma q.
    aby and3I PNoEq_strict_imv Hp H3 H1.
  + aby.
- aby pred_ext xm PNo_strict_imv_pred_eq H1 HLR.
Qed.

(* Parameter PNo_bd "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" "ed76e76de9b58e621daa601cca73b4159a437ba0e73114924cb92ec8044f2aa2" *)
Definition PNo_bd : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set
 := fun L R => DescrR_i_io_1 (PNo_least_rep2 L R).
(* Parameter PNo_pred "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" "b2d51dcfccb9527e9551b0d0c47d891c9031a1d4ee87bba5a9ae5215025d107a" *)
Definition PNo_pred : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> prop
 := fun L R => DescrR_i_io_2 (PNo_least_rep2 L R).

Theorem PNo_bd_pred_lem : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep2 L R (PNo_bd L R) (PNo_pred L R).
aby DescrR_i_io_12 PNo_lenbdd_least_rep2_exuniq2.
Qed.

Theorem PNo_bd_pred : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep L R (PNo_bd L R) (PNo_pred L R).
aby PNo_bd_pred_lem.
Qed.

Theorem PNo_bd_In : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_bd L R :e ordsucc alpha.
let L R. assume HLR. let alpha. assume Ha HaL HaR.
apply PNo_bd_pred L R HLR alpha Ha HaL HaR.
assume H1. aby ordinal_ordsucc ordinal_In_Or_Subq PNo_lenbdd_strict_imv_ex H1 HaR HaL Ha HLR.
Qed.

Opaque Sigma Pi ap PNo_pred PNo_bd PNoLt DescrR_i_io_1 DescrR_i_io_2.

Section TaggedSets.
Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Theorem not_TransSet_Sing1 : ~TransSet {1}.
aby SingI SingE In_0_1 neq_0_1.
Qed.

Theorem not_ordinal_Sing1 : ~ordinal {1}.
aby not_TransSet_Sing1.
Qed.

Theorem tagged_not_ordinal : forall y, ~ordinal (y ').
aby SingI binunionI2 ordinal_Hered not_ordinal_Sing1.
Qed.

Theorem tagged_notin_ordinal : forall alpha y, ordinal alpha -> (y ') /:e alpha.
aby ordinal_Hered tagged_not_ordinal.
Qed.

Theorem tagged_eqE_Subq : forall alpha beta, ordinal alpha -> alpha ' = beta ' -> alpha c= beta.
aby SingE binunionI1 binunionE ordinal_Hered not_ordinal_Sing1.
Qed.

Theorem tagged_eqE_eq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha ' = beta ' -> alpha = beta.
aby set_ext tagged_eqE_Subq.
Qed.

Theorem tagged_ReplE : forall alpha beta, ordinal alpha -> ordinal beta -> beta ' :e {gamma '|gamma :e alpha} -> beta :e alpha.
aby ReplE_impred ordinal_Hered tagged_eqE_eq.
Qed.

Theorem ordinal_notin_tagged_Repl : forall alpha Y, ordinal alpha -> alpha /:e {y '|y :e Y}.
aby ReplE_impred tagged_not_ordinal.
Qed.

Definition SNoElts_ : set -> set := fun alpha => alpha :\/: {beta '|beta :e alpha}.

Theorem SNoElts_mon : forall alpha beta, alpha c= beta -> SNoElts_ alpha c= SNoElts_ beta.
aby ReplI ReplE_impred binunionI1 binunionI2 binunionE.
Qed.

Definition SNo_ : set -> set -> prop := fun alpha x =>
    x c= SNoElts_ alpha
 /\ forall beta :e alpha, exactly1of2 (beta ' :e x) (beta :e x).
Definition PSNo : set -> (set -> prop) -> set :=
  fun alpha p => {beta :e alpha|p beta} :\/: {beta '|beta :e alpha, ~p beta}.

Theorem PNoEq_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, PNoEq_ alpha (fun beta => beta :e PSNo alpha p) p.
aby binunionI1 binunionE SepI SepE2 ReplSepE_impred tagged_notin_ordinal.
Qed.

Theorem SNo_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNo_ alpha (PSNo alpha p).
let alpha. assume Ha. let p.
prove PSNo alpha p c= SNoElts_ alpha
 /\ forall beta :e alpha, exactly1of2 (beta ' :e PSNo alpha p) (beta :e PSNo alpha p).
apply andI.
- aby ReplI binunionI1 binunionI2 binunionE SepE ReplSepE_impred.
- let beta. assume H1: beta :e alpha.
  claim Lbeta: ordinal beta.
  { aby ordinal_Hered H1 Ha. }
  prove exactly1of2 (beta ' :e PSNo alpha p) (beta :e PSNo alpha p).
  apply xm (p beta).
  + aby exactly1of2_I2 binunionI1 binunionE SepI SepE ReplSepE_impred ordinal_Hered tagged_not_ordinal tagged_eqE_eq Lbeta H1 Ha.
  + aby exactly1of2_I1 binunionI2 binunionE SepE ReplSepI ReplSepE_impred tagged_not_ordinal Lbeta H1.
Qed.

Theorem SNo_PSNo_eta_ : forall alpha x, ordinal alpha -> SNo_ alpha x -> x = PSNo alpha (fun beta => beta :e x).
let alpha x. assume Ha Hx.
apply Hx.
assume Hx1: x c= SNoElts_ alpha.
assume Hx2: forall beta :e alpha, exactly1of2 (beta ' :e x) (beta :e x).
apply set_ext.
- prove x c= PSNo alpha (fun beta => beta :e x).
  let u. assume Hu: u :e x.
  apply binunionE alpha {beta '|beta :e alpha} u (Hx1 u Hu).
  + aby binunionI1 SepI Hu.
  + aby exactly1of2_E ReplE_impred binunionI2 ReplSepI Hu Hx2.
- aby exactly1of2_E binunionE SepE ReplSepE_impred Hx2.
Qed.

(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "11faa7a742daf8e4f9aaf08e90b175467e22d0e6ad3ed089af1be90cfc17314b" *)
Definition SNo : set -> prop := fun x => exists alpha, ordinal alpha /\ SNo_ alpha x.

Theorem SNo_SNo : forall alpha, ordinal alpha -> forall z, SNo_ alpha z -> SNo z.
aby.
Qed.

(* Parameter SNoLev "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" "293b77d05dab711767d698fb4484aab2a884304256765be0733e6bd5348119e8" *)
Definition SNoLev : set -> set := fun x => Eps_i (fun alpha => ordinal alpha /\ SNo_ alpha x).

Theorem SNoLev_uniq_Subq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha c= beta.
aby exactly1of2_or binunionE ordinal_Hered tagged_notin_ordinal tagged_ReplE ordinal_notin_tagged_Repl.
Qed.

Theorem SNoLev_uniq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha = beta.
aby set_ext SNoLev_uniq_Subq.
Qed.

Theorem SNoLev_prop : forall x, SNo x -> ordinal (SNoLev x) /\ SNo_ (SNoLev x) x.
aby Eps_i_ex.
Qed.

Theorem SNoLev_ordinal : forall x, SNo x -> ordinal (SNoLev x).
aby SNoLev_prop.
Qed.

Theorem SNoLev_ : forall x, SNo x -> SNo_ (SNoLev x) x.
aby SNoLev_prop.
Qed.

Theorem SNo_PSNo_eta : forall x, SNo x -> x = PSNo (SNoLev x) (fun beta => beta :e x).
aby SNo_PSNo_eta_ SNoLev_prop.
Qed.

Theorem SNoLev_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNoLev (PSNo alpha p) = alpha.
aby SNo_PSNo SNoLev_uniq SNoLev_prop.
Qed.

Theorem SNo_Subq : forall x y, SNo x -> SNo y -> SNoLev x c= SNoLev y -> (forall alpha :e SNoLev x, alpha :e x <-> alpha :e y) -> x c= y.
let x y.
assume Hx Hy H1 H2.
apply SNoLev_ x Hx.
aby exactly1of2_E ReplE_impred binunionE SNoLev_ H2 H1 Hy.
Qed.

Definition SNoEq_ : set -> set -> set -> prop
 := fun alpha x y => PNoEq_ alpha (fun beta => beta :e x) (fun beta => beta :e y).

Theorem SNoEq_I : forall alpha x y, (forall beta :e alpha, beta :e x <-> beta :e y) -> SNoEq_ alpha x y.
aby.
Qed.

Theorem SNo_eq : forall x y, SNo x -> SNo y -> SNoLev x = SNoLev y -> SNoEq_ (SNoLev x) x y -> x = y.
aby set_ext iff_sym Subq_ref SNo_Subq.
Qed.

End TaggedSets.
Definition SNoLt : set -> set -> prop :=
  fun x y => PNoLt (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).
Infix < 490 := SNoLt.
Definition SNoLe : set -> set -> prop :=
  fun x y => PNoLe (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem SNoLtLe : forall x y, x < y -> x <= y.
aby PNoLeI1.
Qed.

Theorem SNoLeE : forall x y, SNo x -> SNo y -> x <= y -> x < y \/ x = y.
aby SNo_eq.
Qed.

Theorem SNoEq_sym_ : forall alpha x y, SNoEq_ alpha x y -> SNoEq_ alpha y x.
aby PNoEq_sym_.
Qed.

Theorem SNoEq_tra_ : forall alpha x y z, SNoEq_ alpha x y -> SNoEq_ alpha y z -> SNoEq_ alpha x z.
aby PNoEq_tra_.
Qed.

Theorem SNoLtE : forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z, SNo z -> SNoLev z :e SNoLev x :/\: SNoLev y -> SNoEq_ (SNoLev z) z x -> SNoEq_ (SNoLev z) z y -> x < z -> z < y -> SNoLev z /:e x -> SNoLev z :e y -> p)
 -> (SNoLev x :e SNoLev y -> SNoEq_ (SNoLev x) x y -> SNoLev x :e y -> p)
 -> (SNoLev y :e SNoLev x -> SNoEq_ (SNoLev y) x y -> SNoLev y /:e x -> p)
 -> p.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume Hxy: PNoLt (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).
let p.
assume Hp1 Hp2 Hp3.
claim LLx: ordinal (SNoLev x).
{ aby SNoLev_ordinal Hx. }
claim LLy: ordinal (SNoLev y).
{ aby SNoLev_ordinal Hy. }
apply PNoLtE (SNoLev x) (SNoLev y) (fun beta => beta :e x) (fun beta => beta :e y) Hxy.
- assume H1: PNoLt_ (SNoLev x :/\: SNoLev y) (fun beta => beta :e x) (fun beta => beta :e y).
  aby binintersectE ordinal_Hered PNoEq_sym_ PNoLt_E_ PNoLtI2 PNoLtI3 PNoEq_PSNo SNo_PSNo SNoLev_uniq SNoLev_prop SNoEq_tra_ H1 LLx Hp1.
- aby Hp2.
- aby Hp3.
Qed.

(** The analogous thm to PNoLtI1 can be recovered by SNoLt_tra (transitivity) and SNoLtI2 and SNoLtI3. **)
Theorem SNoLtI2 : forall x y,
     SNoLev x :e SNoLev y
  -> SNoEq_ (SNoLev x) x y
  -> SNoLev x :e y
  -> x < y.
aby PNoLtI2.
Qed.

Theorem SNoLtI3 : forall x y,
     SNoLev y :e SNoLev x
  -> SNoEq_ (SNoLev y) x y
  -> SNoLev y /:e x
  -> x < y.
aby PNoLtI3.
Qed.

Theorem SNoLt_irref : forall x, ~SNoLt x x.
aby PNoLt_irref.
Qed.

Theorem SNoLt_trichotomy_or : forall x y, SNo x -> SNo y -> x < y \/ x = y \/ y < x.
aby or3I1 or3I2 or3I3 PNoLt_trichotomy_or SNoLev_ordinal SNo_eq.
Qed.

Theorem SNoLt_trichotomy_or_impred : forall x y, SNo x -> SNo y ->
  forall p:prop,
      (x < y -> p)
   -> (x = y -> p)
   -> (y < x -> p)
   -> p.
aby SNoLt_trichotomy_or.
Qed.

Theorem SNoLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y < z -> x < z.
aby PNoLt_tra SNoLev_ordinal.
Qed.

Theorem SNoLe_ref : forall x, SNoLe x x.
aby PNoLe_ref.
Qed.

Theorem SNoLe_antisym : forall x y, SNo x -> SNo y -> x <= y -> y <= x -> x = y.
aby PNoLe_antisym SNoLev_ordinal SNo_eq.
Qed.

Theorem SNoLtLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y <= z -> x < z.
aby PNoLtLe_tra SNoLev_ordinal.
Qed.

Theorem SNoLeLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y < z -> x < z.
aby PNoLeLt_tra SNoLev_ordinal.
Qed.

Theorem SNoLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y <= z -> x <= z.
aby PNoLe_tra SNoLev_ordinal.
Qed.

Theorem SNoLtLe_or : forall x y, SNo x -> SNo y -> x < y \/ y <= x.
aby SNoLtLe SNoLt_trichotomy_or SNoLe_ref.
Qed.

Theorem SNoLt_PSNo_PNoLt : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PSNo alpha p < PSNo beta q -> PNoLt alpha p beta q.
aby PNoEq_sym_ PNoLtEq_tra PNoEqLt_tra PNoEq_PSNo SNoLev_PSNo.
Qed.

Theorem PNoLt_SNoLt_PSNo : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q -> PSNo alpha p < PSNo beta q.
aby PNoEq_sym_ PNoLtEq_tra PNoEqLt_tra PNoEq_PSNo SNoLev_PSNo.
Qed.

Definition SNoCut : set -> set -> set :=
  fun L R => PSNo (PNo_bd (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)) (PNo_pred (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)).
Definition SNoCutP : set -> set -> prop :=
 fun L R =>
      (forall x :e L, SNo x)
   /\ (forall y :e R, SNo y)
   /\ (forall x :e L, forall y :e R, x < y).

Theorem SNoCutP_SNoCut : forall L R, SNoCutP L R
 -> SNo (SNoCut L R)
 /\ SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
 /\ (forall x :e L, x < SNoCut L R)
 /\ (forall y :e R, SNoCut L R < y)
 /\ (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z).
let L R.
assume HC: SNoCutP L R.
apply HC. assume HC. apply HC.
assume HL: forall x :e L, SNo x.
assume HR: forall y :e R, SNo y.
assume HLR: forall x :e L, forall y :e R, x < y.
set L' : set -> (set -> prop) -> prop := fun alpha p => ordinal alpha /\ PSNo alpha p :e L.
set R' : set -> (set -> prop) -> prop := fun alpha p => ordinal alpha /\ PSNo alpha p :e R.
set tau := PNo_bd L' R'.
set w := PNo_pred L' R'.
set alpha := \/_ x :e L, ordsucc (SNoLev x).
set beta := \/_ y :e R, ordsucc (SNoLev y).
prove SNo (SNoCut L R)
 /\ SNoLev (SNoCut L R) :e ordsucc (alpha :\/: beta)
 /\ (forall x :e L, x < SNoCut L R)
 /\ (forall y :e R, SNoCut L R < y)
 /\ (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ PNoEq_ (SNoLev (SNoCut L R)) (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z)).
claim LLR: PNoLt_pwise L' R'.
{ aby SNoLt_PSNo_PNoLt HLR. }
claim La: ordinal alpha.
{ aby ordinal_ordsucc ordinal_famunion SNoLev_ordinal HL. }
claim Lb: ordinal beta.
{ aby ordinal_ordsucc ordinal_famunion SNoLev_ordinal HR. }
claim Lab: ordinal (alpha :\/: beta).
{ aby binunion_com Subq_binunion_eq ordinal_linear Lb La. }
claim LLab: PNo_lenbdd (alpha :\/: beta) L'.
{ aby binunionI1 famunionI ordsuccI2 SNoLev_PSNo. }
claim LRab: PNo_lenbdd (alpha :\/: beta) R'.
{ aby binunionI2 famunionI ordsuccI2 SNoLev_PSNo. }
apply PNo_bd_pred L' R' LLR (alpha :\/: beta) Lab LLab LRab.
assume H1. apply H1.
assume H1: ordinal tau.
assume H2: PNo_strict_imv L' R' tau w.
assume H3: forall gamma :e tau,
           forall q:set -> prop, ~PNo_strict_imv L' R' gamma q.
apply H2.
assume H4: PNo_strict_upperbd L' tau w.
assume H5: PNo_strict_lowerbd R' tau w.
claim LNoC: SNo (SNoCut L R).
{ aby SNo_PSNo H1. }
claim LLleveqtau: SNoLev (SNoCut L R) = tau.
{ aby SNoLev_PSNo HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC. }
claim LLbdtau: tau :e ordsucc (alpha :\/: beta).
{ aby PNo_bd_In HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau. }
claim LLbd: SNoLev (SNoCut L R) :e ordsucc (alpha :\/: beta).
{ aby LLbdtau LLleveqtau. }
claim LLecw: PNoEq_ tau (fun gamma => gamma :e SNoCut L R) w.
{ aby PNoEq_PSNo H1. }
claim LLC: ordinal (SNoLev (SNoCut L R)).
{ aby SNoLev_ordinal LNoC. }
claim LL: forall x :e L, x < SNoCut L R.
{ aby SNoLev_ordinal SNo_PSNo_eta PNoLt_SNoLt_PSNo H4 H1 HL. }
claim LR: forall y :e R, SNoCut L R < y.
{ aby SNoLev_ordinal SNo_PSNo_eta PNoLt_SNoLt_PSNo H5 H1 HR. }
apply and5I.
- aby LNoC.
- aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR.
- aby LL.
- aby LR.
- prove forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ PNoEq_ (SNoLev (SNoCut L R)) (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
  let z. assume Hz: SNo z.
  assume H10: forall x :e L, x < z.
  assume H11: forall y :e R, z < y.
  claim LLz: ordinal (SNoLev z).
  { aby SNoLev_ordinal Hz. }
  claim Lzimv: PNo_strict_imv L' R' (SNoLev z) (fun gamma => gamma :e z).
  { aby SNo_PSNo_eta SNoLt_PSNo_PNoLt LLz H11 H10 Hz. }
  claim LLznt: SNoLev z /:e tau.
  { assume H12: SNoLev z :e tau.
    aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv H12.
  }
  claim LLzlet : tau c= SNoLev z.
  { aby ordinal_In_Or_Subq LLznt LLz H1. }
  prove SNoLev (SNoCut L R) c= SNoLev z /\ PNoEq_ (SNoLev (SNoCut L R)) (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
  rewrite LLleveqtau.
  prove tau c= SNoLev z /\ PNoEq_ tau (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
  apply andI.
  + aby LLzlet.
  + prove PNoEq_ tau (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
    apply PNoLt_trichotomy_or_ w (fun gamma => gamma :e z) tau H1. assume H12. apply H12.
    * { assume H12: PNoLt_ tau w (fun gamma => gamma :e z).
        prove False.
        apply H12.
        let delta. assume H13. apply H13.
        assume Hd: delta :e tau.
        assume H13. apply H13. assume H13. apply H13.
        assume H13: PNoEq_ delta w (fun gamma => gamma :e z).
        assume H14: ~w delta.
        assume H15: delta :e z.
        claim Ld: ordinal delta.
        { aby ordinal_Hered HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15. }
        claim Lsd: ordinal (ordsucc delta).
        { aby ordinal_ordsucc Ld. }
        set z0 : set -> prop := fun eps => eps :e z /\ eps <> delta.
        set z1 : set -> prop := fun eps => eps :e z \/ eps = delta.
        claim Lnz0d: ~z0 delta.
        { assume H10. aby H10. }
        claim Lz1d: z1 delta.
        { aby. }
        apply H3 delta Hd (fun gamma => gamma :e z).
        prove PNo_strict_imv L' R' delta (fun gamma => gamma :e z).
        apply PNo_rel_split_imv_imp_strict_imv L' R' delta Ld (fun gamma => gamma :e z).
        prove PNo_rel_strict_split_imv L' R' delta (fun gamma => gamma :e z).
        prove PNo_rel_strict_imv L' R' (ordsucc delta) z0
           /\ PNo_rel_strict_imv L' R' (ordsucc delta) z1.
        apply andI.
        - prove PNo_rel_strict_imv L' R' (ordsucc delta) z0.
          apply PNoEq_rel_strict_imv L' R' (ordsucc delta) Lsd w z0.
          + aby iff_trans ordsuccE PNo_extend0_eq Lnz0d H14 H13.
          + aby ordinal_ordsucc_In PNo_strict_imv_imp_rel_strict_imv Hd H2 H1.
        - prove PNo_rel_strict_imv L' R' (ordsucc delta) z1.
          apply PNoEq_rel_strict_imv L' R' (ordsucc delta) Lsd (fun gamma => gamma :e z) z1.
          + prove PNoEq_ (ordsucc delta) (fun gamma => gamma :e z) z1.
            let eps. assume He: eps :e ordsucc delta.
            apply ordsuccE delta eps He.
            * assume He1: eps :e delta.
              aby PNo_extend1_eq HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15 Ld Lsd Lnz0d Lz1d He He1.
            * { assume He1: eps = delta.
                prove eps :e z <-> z1 eps.
                rewrite He1.
                prove delta :e z <-> z1 delta.
                apply iffI.
                - assume _. aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15 Ld Lsd Lnz0d Lz1d He He1.
                - assume _. aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15 Ld Lsd Lnz0d Lz1d He He1.
              }
          + prove PNo_rel_strict_imv L' R' (ordsucc delta) (fun gamma => gamma :e z).
            apply PNo_strict_imv_imp_rel_strict_imv L' R' (SNoLev z) LLz (ordsucc delta).
            * prove ordsucc delta :e ordsucc (SNoLev z).
              apply ordinal_ordsucc_In (SNoLev z) LLz.
              prove delta :e SNoLev z.
              apply LLzlet.
              prove delta :e tau. aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15 Ld Lsd Lnz0d Lz1d.
            * prove PNo_strict_imv L' R' (SNoLev z) (fun gamma => gamma :e z).
              aby HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H12 H13 Hd H13 H13 H13 H14 H15 Ld Lsd Lnz0d Lz1d.
      }
    * aby PNoEq_tra_ LLecw.
    * { assume H12: PNoLt_ tau (fun gamma => gamma :e z) w.
        prove False.
        apply H12.
        let delta. assume H13. apply H13.
        assume Hd: delta :e tau.
        assume H13. apply H13. assume H13. apply H13.
        assume H13: PNoEq_ delta (fun gamma => gamma :e z) w.
        assume H14: delta /:e z.
        assume H15: w delta.
        claim Ld: ordinal delta.
        { aby ordinal_Hered HC HC HL HR HLR LLR La Lb Lab LLab LRab H1 H1 H2 H3 H4 H5 LNoC LLleveqtau LLbdtau LLbd LLecw LLC LL LR Hz H10 H11 LLz Lzimv LLznt LLzlet H12 H13 Hd H13 H13 H13 H14 H15. }
        claim Lsd: ordinal (ordsucc delta).
        { aby ordinal_ordsucc Ld. }
        set z0 : set -> prop := fun eps => eps :e z /\ eps <> delta.
        set z1 : set -> prop := fun eps => eps :e z \/ eps = delta.
        claim Lnz0d: ~z0 delta.
        { assume H10. aby H10. }
        claim Lz1d: z1 delta.
        { aby. }
        apply H3 delta Hd (fun gamma => gamma :e z).
        prove PNo_strict_imv L' R' delta (fun gamma => gamma :e z).
        apply PNo_rel_split_imv_imp_strict_imv L' R' delta Ld (fun gamma => gamma :e z).
        prove PNo_rel_strict_split_imv L' R' delta (fun gamma => gamma :e z).
        prove PNo_rel_strict_imv L' R' (ordsucc delta) z0
           /\ PNo_rel_strict_imv L' R' (ordsucc delta) z1.
        apply andI.
        - aby ordsuccE ordinal_ordsucc_In PNoEq_rel_strict_imv PNo_extend0_eq PNo_strict_imv_imp_rel_strict_imv Lnz0d Lsd H14 Hd LLzlet Lzimv LLz.
        - prove PNo_rel_strict_imv L' R' (ordsucc delta) z1.
          apply PNoEq_rel_strict_imv L' R' (ordsucc delta) Lsd w z1.
          + aby iff_sym iff_trans ordsuccE PNo_extend1_eq Lz1d H15 H13.
          + aby ordinal_ordsucc_In PNo_strict_imv_imp_rel_strict_imv Hd H2 H1.
      }
Qed.

Theorem SNoCutP_SNoCut_impred : forall L R, SNoCutP L R
 -> forall p:prop,
      (SNo (SNoCut L R)
    -> SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
    -> (forall x :e L, x < SNoCut L R)
    -> (forall y :e R, SNoCut L R < y)
    -> (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z)
    -> p)
   -> p.
aby SNoCutP_SNoCut.
Qed.

Theorem SNoCutP_L_0: forall L, (forall x :e L, SNo x) -> SNoCutP L 0.
aby EmptyE and3I.
Qed.

Theorem SNoCutP_0_0: SNoCutP 0 0.
aby EmptyE SNoCutP_L_0.
Qed.

Definition SNoS_ : set -> set := fun alpha => {x :e Power (SNoElts_ alpha)|exists beta :e alpha, SNo_ beta x}.

Theorem SNoS_E : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, exists beta :e alpha, SNo_ beta x.
aby SepE2.
Qed.

Section TaggedSets2.
Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Theorem SNoS_I : forall alpha, ordinal alpha -> forall x, forall beta :e alpha, SNo_ beta x -> x :e SNoS_ alpha.
aby PowerI Subq_tra SepI SNoElts_mon.
Qed.

Theorem SNoS_I2 : forall x y, SNo x -> SNo y -> SNoLev x :e SNoLev y -> x :e SNoS_ (SNoLev y).
aby SNoLev_ordinal SNoLev_ SNoS_I.
Qed.  

Theorem SNoS_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> SNoS_ alpha c= SNoS_ beta.
aby SNoS_E SNoS_I.
Qed.

Theorem SNoLev_uniq2 : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNoLev x = alpha.
aby SNo_SNo SNoLev_uniq SNoLev_prop.
Qed.

Theorem SNoS_E2 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha,
 forall p:prop,
     (SNoLev x :e alpha -> ordinal (SNoLev x) -> SNo x -> SNo_ (SNoLev x) x -> p)
  -> p.
aby ordinal_Hered SNo_SNo SNoLev_prop SNoS_E SNoLev_uniq2.
Qed.

Theorem SNoS_In_neq : forall w, SNo w -> forall x :e SNoS_ (SNoLev w), x <> w.
aby In_irref SNoLev_prop SNoS_E2.
Qed.

Theorem SNoS_SNoLev : forall z, SNo z -> z :e SNoS_ (ordsucc (SNoLev z)).
aby ordsuccI2 ordinal_ordsucc SNoLev_prop SNoS_I.
Qed.

Definition SNoL : set -> set := fun z => {x :e SNoS_ (SNoLev z) | x < z}.
Definition SNoR : set -> set := fun z => {y :e SNoS_ (SNoLev z) | z < y}.

Theorem SNoCutP_SNoL_SNoR: forall z, SNo z -> SNoCutP (SNoL z) (SNoR z).
aby and3I SepE1 SepE2 ordinal_Hered SNoLev_ordinal SNoLt_tra SNoS_E.
Qed.

Theorem SNoL_E : forall x, SNo x -> forall w :e SNoL x,
  forall p:prop,
       (SNo w -> SNoLev w :e SNoLev x -> w < x -> p)
    -> p.
aby SepE SNoLev_ordinal SNoS_E2.
Qed.

Theorem SNoR_E : forall x, SNo x -> forall z :e SNoR x,
  forall p:prop,
       (SNo z -> SNoLev z :e SNoLev x -> x < z -> p)
    -> p.
aby SepE SNoLev_ordinal SNoS_E2.
Qed.

Theorem SNoL_SNoS_ : forall z, SNoL z c= SNoS_ (SNoLev z).
aby Sep_Subq.
Qed.

Theorem SNoR_SNoS_ : forall z, SNoR z c= SNoS_ (SNoLev z).
aby Sep_Subq.
Qed.

Theorem SNoL_SNoS : forall x, SNo x -> forall w :e SNoL x, w :e SNoS_ (SNoLev x).
aby SNoS_I2 SNoL_E.
Qed.

Theorem SNoR_SNoS : forall x, SNo x -> forall z :e SNoR x, z :e SNoS_ (SNoLev x).
aby SNoS_I2 SNoR_E.
Qed.

Theorem SNoL_I : forall z, SNo z -> forall x, SNo x -> SNoLev x :e SNoLev z -> x < z -> x :e SNoL z.
aby SepI SNoS_I2.
Qed.

Theorem SNoR_I : forall z, SNo z -> forall y, SNo y -> SNoLev y :e SNoLev z -> z < y -> y :e SNoR z.
aby SepI SNoS_I2.
Qed.

Theorem SNo_eta : forall z, SNo z -> z = SNoCut (SNoL z) (SNoR z).
let z. assume Hz: SNo z.
set L := SNoL z.
set R := SNoR z.
claim LLz: ordinal (SNoLev z).
{ aby SNoLev_ordinal Hz. }
claim LC: SNoCutP L R.
{ aby SNoCutP_SNoL_SNoR Hz. }
apply SNoCutP_SNoCut L R LC.
assume H1. apply H1. assume H1. apply H1. assume H1. apply H1.
assume H1: SNo (SNoCut L R).
assume H2: SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall x :e L, x < SNoCut L R.
assume H4: forall y :e R, SNoCut L R < y.
assume H5: forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ PNoEq_ (SNoLev (SNoCut L R)) (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
claim L4: ordinal (SNoLev (SNoCut L R)).
{ aby SNoLev_ordinal H1. }
claim L5: forall x :e L, x < z.
{ aby SepE2. }
claim L6: forall y :e R, z < y.
{ aby SepE2. }
apply H5 z Hz L5 L6.
assume H6: SNoLev (SNoCut L R) c= SNoLev z.
assume H7: PNoEq_ (SNoLev (SNoCut L R)) (fun gamma => gamma :e SNoCut L R) (fun gamma => gamma :e z).
claim L7: SNoLev (SNoCut L R) = SNoLev z.
{ apply ordinal_trichotomy_or (SNoLev (SNoCut L R)) (SNoLev z) L4 LLz.
  - assume H8. aby SepI In_irref SNoLev_ SNoLt_irref SNoLt_trichotomy_or SNoS_I H8 H4 H3 H1 LLz Hz.
  - aby In_irref H6.
}
aby SNo_eq L7 H7 H1 Hz.
Qed.

Theorem SNoCutP_SNo_SNoCut : forall L R, SNoCutP L R -> SNo (SNoCut L R).
aby SNoCutP_SNoCut.
Qed.

Theorem SNoCutP_SNoCut_L : forall L R, SNoCutP L R -> forall x :e L, x < SNoCut L R.
aby SNoCutP_SNoCut.
Qed.

Theorem SNoCutP_SNoCut_R : forall L R, SNoCutP L R -> forall y :e R, SNoCut L R < y.
aby SNoCutP_SNoCut.
Qed.

Theorem SNoCutP_SNoCut_fst : forall L R, SNoCutP L R ->
 forall z, SNo z
   -> (forall x :e L, x < z)
   -> (forall y :e R, z < y)
   -> SNoLev (SNoCut L R) c= SNoLev z
   /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z.
aby SNoCutP_SNoCut.
Qed.

Theorem SNoCut_Le : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 <= SNoCut L2 R2.
let L1 R1 L2 R2.
assume HLR1 HLR2.
assume H1: forall w :e L1, w < SNoCut L2 R2.
assume H2: forall z :e R2, SNoCut L1 R1 < z.
apply HLR1. assume HLR1a. apply HLR1a.
assume HLR1a: forall x :e L1, SNo x.
assume HLR1b: forall y :e R1, SNo y.
assume HLR1c: forall x :e L1, forall y :e R1, x < y.
apply HLR2. assume HLR2a. apply HLR2a.
assume HLR2a: forall x :e L2, SNo x.
assume HLR2b: forall y :e R2, SNo y.
assume HLR2c: forall x :e L2, forall y :e R2, x < y.
set alpha := \/_ x :e L1, ordsucc (SNoLev x).
set beta := \/_ y :e R1, ordsucc (SNoLev y).
set gamma := \/_ x :e L2, ordsucc (SNoLev x).
set delta := \/_ y :e R2, ordsucc (SNoLev y).
apply SNoCutP_SNoCut L1 R1 HLR1.
assume H3. apply H3. assume H3. apply H3. assume H3. apply H3.
assume H3: SNo (SNoCut L1 R1).
assume H4: SNoLev (SNoCut L1 R1) :e ordsucc (alpha :\/: beta).
assume H5: forall x :e L1, x < SNoCut L1 R1.
assume H6: forall y :e R1, SNoCut L1 R1 < y.
assume H7: forall z, SNo z -> (forall x :e L1, x < z) -> (forall y :e R1, z < y) -> SNoLev (SNoCut L1 R1) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L1 R1)) (SNoCut L1 R1) z.
apply SNoCutP_SNoCut L2 R2 HLR2.
assume H8. apply H8. assume H8. apply H8. assume H8. apply H8.
assume H8: SNo (SNoCut L2 R2).
assume H9: SNoLev (SNoCut L2 R2) :e ordsucc (gamma :\/: delta).
assume H10: forall x :e L2, x < SNoCut L2 R2.
assume H11: forall y :e R2, SNoCut L2 R2 < y.
assume H12: forall z, SNo z -> (forall x :e L2, x < z) -> (forall y :e R2, z < y) -> SNoLev (SNoCut L2 R2) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L2 R2)) (SNoCut L2 R2) z.
apply SNoLtLe_or (SNoCut L2 R2) (SNoCut L1 R1) H8 H3.
- assume H13: SNoCut L2 R2 < SNoCut L1 R1.
  prove False.
  apply SNoLtE (SNoCut L2 R2) (SNoCut L1 R1) H8 H3 H13.
  + aby binintersectE2 In_irref SNoLt_tra H8 H7 H6 H3 HLR1b HLR1a H1.
  + aby In_irref SNoLt_tra H13 H8 H7 H6 H3 HLR1b H1.
  + aby In_irref SNoLt_tra H13 H12 H10 H8 H3 HLR2a H2.
- aby.
Qed.

Theorem SNoCut_ext : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R1, SNoCut L2 R2 < z)
  -> (forall w :e L2, w < SNoCut L1 R1)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 = SNoCut L2 R2.
aby SNoLe_antisym SNoCutP_SNo_SNoCut SNoCut_Le.
Qed.

Theorem SNoLt_SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> p.
aby binintersectE SNoLtE SNoL_I SNoR_I.
Qed.

Theorem SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y ->
 forall p:prop,
    (x = y -> p)
 -> (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> (forall z :e SNoR y, z :e SNoL x -> p)
 -> (x :e SNoR y -> p)
 -> (y :e SNoL x -> p)
 -> p.
aby SNoLt_trichotomy_or_impred SNoLt_SNoL_or_SNoR_impred.
Qed.

Theorem SNoL_SNoCutP_ex: forall L R, SNoCutP L R -> forall w :e SNoL (SNoCut L R), exists w' :e L, w <= w'.
let L R. assume HLR.
set y := SNoCut L R.
let w.
assume Hw: w :e SNoL y.
apply dneg.
assume HC: ~exists w' :e L, w <= w'.
apply HLR.
assume H. apply H.
assume HL HR HLR'.
apply SNoCutP_SNoCut_impred L R HLR.
aby In_irref SNoLt_tra SNoLtLe_or SNoL_E HR HL HC Hw.
Qed.

Theorem SNoR_SNoCutP_ex: forall L R, SNoCutP L R -> forall z :e SNoR (SNoCut L R), exists z' :e R, z' <= z.
let L R. assume HLR.
set y := SNoCut L R.
let z.
assume Hz: z :e SNoR y.
apply dneg.
assume HC: ~exists z' :e R, z' <= z.
apply HLR.
assume H. apply H.
assume HL HR HLR'.
apply SNoCutP_SNoCut_impred L R HLR.
aby In_irref SNoLt_tra SNoLtLe_or SNoR_E HR HL HC Hz.
Qed.

Theorem ordinal_SNo_ : forall alpha, ordinal alpha -> SNo_ alpha alpha.
aby exactly1of2_I2 binunionI1 ordinal_Hered tagged_not_ordinal.
Qed.

Theorem ordinal_SNo : forall alpha, ordinal alpha -> SNo alpha.
aby ordinal_SNo_.
Qed.

Theorem ordinal_SNoLev : forall alpha, ordinal alpha -> SNoLev alpha = alpha.
aby SNoLev_uniq SNoLev_prop ordinal_SNo_ ordinal_SNo.
Qed.

Theorem ordinal_SNoLev_max : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e alpha -> z < alpha.
aby binintersectE1 In_irref In_no2cycle SNoLtE SNoLt_trichotomy_or ordinal_SNo ordinal_SNoLev.
Qed.

Theorem ordinal_SNoL : forall alpha, ordinal alpha -> SNoL alpha = SNoS_ alpha.
let alpha.
assume Ha: ordinal alpha.
claim La1: SNo alpha.
{ aby ordinal_SNo Ha. }
aby set_ext SNoS_I2 SNoS_E2 SNoL_E SNoL_I ordinal_SNoLev ordinal_SNoLev_max La1 Ha.
Qed.

Theorem ordinal_SNoR : forall alpha, ordinal alpha -> SNoR alpha = Empty.
aby Empty_Subq_eq SNoLt_irref SNoLt_tra SNoR_E ordinal_SNo ordinal_SNoLev ordinal_SNoLev_max.
Qed.

Theorem nat_p_SNo: forall n, nat_p n -> SNo n.
aby nat_p_ordinal ordinal_SNo.
Qed.

Theorem omega_SNo: forall n :e omega, SNo n.
aby omega_nat_p nat_p_SNo.
Qed.

Theorem omega_SNoS_omega : omega c= SNoS_ omega.
aby nat_p_ordinal omega_nat_p omega_ordinal SNoLev_ SNoS_I ordinal_SNoLev omega_SNo.
Qed.

Theorem ordinal_In_SNoLt : forall alpha, ordinal alpha -> forall beta :e alpha, beta < alpha.
aby ordinal_Hered ordinal_SNo ordinal_SNoLev ordinal_SNoLev_max.
Qed.

Theorem ordinal_SNoLev_max_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> z <= alpha.
let alpha.
assume Ha: ordinal alpha.
apply Ha. assume Ha1 _.
let z.
assume Hz: SNo z.
assume Hz2: SNoLev z :e ordsucc alpha.
claim La1: SNo alpha.
{ aby ordinal_SNo Ha. }
claim La2: SNoLev alpha = alpha.
{ aby ordinal_SNoLev Ha. }
apply ordsuccE alpha (SNoLev z) Hz2.
- aby SNoLtLe ordinal_SNoLev_max Hz Ha.
- assume Hz3: SNoLev z = alpha.
  apply dneg.
  assume H1: ~(z <= alpha).
  claim L1: forall beta, ordinal beta -> beta :e alpha -> beta :e z.
  { apply ordinal_ind.
    let beta.
    assume Hb: ordinal beta.
    aby dneg SNoLtLe SNoLtI3 SNoLt_tra ordinal_SNo ordinal_SNoLev ordinal_In_SNoLt Hb H1 Hz3 La1 Hz Ha1 Ha.
  }
  aby ordinal_Hered SNo_eq SNoLe_ref L1 H1 Hz3 La2 La1 Hz Ha.
Qed.

Theorem ordinal_Subq_SNoLe : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> alpha <= beta.
aby set_ext ordsuccI1 ordsuccI2 ordinal_In_Or_Subq ordinal_SNo ordinal_SNoLev ordinal_SNoLev_max_2.
Qed.

Theorem ordinal_SNoLt_In : forall alpha beta, ordinal alpha -> ordinal beta -> alpha < beta -> alpha :e beta.
aby ordinal_In_Or_Subq SNoLt_irref SNoLtLe_tra ordinal_SNo ordinal_Subq_SNoLe.
Qed.

Theorem omega_nonneg : forall m :e omega, 0 <= m.
aby Subq_Empty ordinal_Empty nat_p_ordinal omega_nat_p ordinal_Subq_SNoLe.
Qed.

Theorem SNo_0 : SNo 0.
aby ordinal_Empty ordinal_SNo.
Qed.

Theorem SNo_1 : SNo 1.
aby nat_1 nat_p_ordinal ordinal_SNo.
Qed.

Theorem SNo_2 : SNo 2.
aby nat_2 nat_p_ordinal ordinal_SNo.
Qed.

Theorem SNoLev_0 : SNoLev 0 = 0.
aby ordinal_Empty ordinal_SNoLev.
Qed.

Theorem SNoCut_0_0: SNoCut 0 0 = 0.
aby EmptyE binunion_idl famunion_Empty cases_1 SNoEq_I SNo_eq SNoCutP_SNoCut_impred SNoCutP_0_0 SNo_0 SNoLev_0.
Qed.

Theorem SNoL_0 : SNoL 0 = 0.
aby EmptyE Empty_Subq_eq ordinal_Empty SNoS_E2 SNoL_SNoS_ SNoLev_0.
Qed.

Theorem SNoR_0 : SNoR 0 = 0.
aby EmptyE Empty_Subq_eq ordinal_Empty SNoS_E2 SNoR_SNoS_ SNoLev_0.
Qed.

Theorem SNoL_1 : SNoL 1 = 1.
apply set_ext.
- let x. aby EmptyE In_0_1 nat_1 cases_1 nat_p_ordinal SNoEq_I SNo_eq SNoL_E ordinal_SNoLev SNo_0 SNo_1 SNoLev_0.
- aby In_0_1 nat_1 cases_1 nat_p_ordinal SNoL_I ordinal_SNoLev ordinal_In_SNoLt SNo_0 SNo_1 SNoLev_0.
Qed.

Theorem SNoR_1 : SNoR 1 = 0.
aby nat_1 nat_p_ordinal ordinal_SNoR.
Qed.

Theorem SNo_max_SNoLev : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> SNoLev x = x.
aby In_irref ordsuccI2 SNoLev_ordinal SNoLev_ SNoLeE SNoLtE SNoLt_irref SNoLt_tra SNoS_I ordinal_SNo ordinal_SNoLev ordinal_SNoLev_max_2.
Qed.

Theorem SNo_max_ordinal : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> ordinal x.
aby SNoLev_ordinal SNo_max_SNoLev.
Qed.

Theorem pos_low_eq_one : forall x, SNo x -> 0 < x -> SNoLev x c= 1 -> x = 1.
let x. assume Hx Hxpos Hxlow.
apply SNoLtE 0 x SNo_0 Hx Hxpos.
- aby EmptyE binintersectE1 ordinal_Empty ordinal_SNoLev.
- aby set_ext In_0_1 nat_1 cases_1 ordinal_Empty nat_p_ordinal SNo_eq ordinal_SNoLev SNo_1 Hxlow Hx.
- aby EmptyE ordinal_Empty ordinal_SNoLev.
Qed.

Definition SNo_extend0 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x /\ delta <> SNoLev x).
Definition SNo_extend1 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x \/ delta = SNoLev x).

Theorem SNo_extend0_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend0 x).
aby ordinal_ordsucc SNo_PSNo SNoLev_ordinal.
Qed.

Theorem SNo_extend1_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend1 x).
aby ordinal_ordsucc SNo_PSNo SNoLev_ordinal.
Qed.

Theorem SNo_extend0_SNo : forall x, SNo x -> SNo (SNo_extend0 x).
aby ordinal_ordsucc SNo_SNo SNoLev_ordinal SNo_extend0_SNo_.
Qed.

Theorem SNo_extend1_SNo : forall x, SNo x -> SNo (SNo_extend1 x).
aby ordinal_ordsucc SNo_SNo SNoLev_ordinal SNo_extend1_SNo_.
Qed.

Theorem SNo_extend0_SNoLev : forall x, SNo x -> SNoLev (SNo_extend0 x) = ordsucc (SNoLev x).
aby ordinal_ordsucc SNoLev_ordinal SNoLev_uniq2 SNo_extend0_SNo_.
Qed.

Theorem SNo_extend1_SNoLev : forall x, SNo x -> SNoLev (SNo_extend1 x) = ordsucc (SNoLev x).
aby ordinal_ordsucc SNoLev_ordinal SNoLev_uniq2 SNo_extend1_SNo_.
Qed.

Theorem SNo_extend0_nIn : forall x, SNo x -> SNoLev x /:e SNo_extend0 x.
aby binunionE SepE2 ReplSepE_impred tagged_not_ordinal SNoLev_ordinal.
Qed.

Theorem SNo_extend1_In : forall x, SNo x -> SNoLev x :e SNo_extend1 x.
aby binunionI1 SepI ordsuccI2.
Qed.

Theorem SNo_extend0_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend0 x) x.
aby ordsuccI2 ordinal_ordsucc PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNo_extend0_eq PNoEq_PSNo SNoLev_ordinal.
Qed.

Theorem SNo_extend1_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend1 x) x.
aby ordsuccI2 ordinal_ordsucc PNoEq_sym_ PNoEq_tra_ PNoEq_antimon_ PNo_extend1_eq PNoEq_PSNo SNoLev_ordinal.
Qed.

Theorem SNoLev_0_eq_0 : forall x, SNo x -> SNoLev x = 0 -> x = 0.
aby EmptyE SNo_eq SNo_0 SNoLev_0.
Qed.

(** eps_ n is the Surreal Number 1/2^n, without needing to define division or exponents first **)
Definition eps_ : set -> set := fun n => {0} :\/: {(ordsucc m) ' | m :e n}.

Theorem eps_ordinal_In_eq_0 : forall n alpha, ordinal alpha -> alpha :e eps_ n -> alpha = 0.
aby ReplE_impred SingE binunionE tagged_not_ordinal.
Qed.

Theorem eps_0_1 : eps_ 0 = 1.
aby set_ext EmptyE ReplE_impred SingI SingE binunionI1 binunionE In_0_1 cases_1.
Qed.

Theorem SNo__eps_ : forall n :e omega, SNo_ (ordsucc n) (eps_ n).
let n. assume Hn.
claim Ln: nat_p n.
{ aby omega_nat_p Hn. }
prove eps_ n c= SNoElts_ (ordsucc n)
   /\ forall m :e ordsucc n, exactly1of2 (m ' :e eps_ n) (m :e eps_ n).
apply andI.
- let x. assume Hx: x :e {0} :\/: {(ordsucc m) ' | m :e n}.
  apply binunionE {0} {(ordsucc m) ' | m :e n} x Hx.
  + assume Hx: x :e {0}. rewrite SingE 0 x Hx.
    prove 0 :e SNoElts_ (ordsucc n).
    prove 0 :e ordsucc n :\/: {beta '|beta :e ordsucc n}.
    apply binunionI1.
    prove 0 :e ordsucc n.
    aby nat_0_in_ordsucc Hn Ln Hx Hx.
  + assume Hx: x :e {(ordsucc m) ' | m :e n}.
    apply ReplE_impred n (fun m => (ordsucc m) ') x Hx.
    let m. assume Hm: m :e n.
    assume Hxm: x = (ordsucc m) '.
    prove x :e SNoElts_ (ordsucc n).
    prove x :e ordsucc n :\/: {beta '|beta :e ordsucc n}.
    apply binunionI2.
    prove x :e {beta '|beta :e ordsucc n}.
    rewrite Hxm.
    prove (ordsucc m) ' :e {beta '|beta :e ordsucc n}.
    aby ReplI nat_ordsucc_in_ordsucc Hn Ln Hx Hx Hm Hxm.
- let m. assume Hm: m :e ordsucc n.
  claim Lm: nat_p m.
  { aby nat_ordsucc nat_p_trans Hm Ln. }
  apply nat_inv m Lm.
  + assume Hm: m = 0. aby EmptyE exactly1of2_I2 ReplE_impred SingI SingE binunionI1 binunionI2 binunionE neq_0_ordsucc nat_ordsucc nat_p_trans ordinal_Empty nat_p_ordinal tagged_eqE_eq Hm Ln.
  + assume H1. apply H1. let k. assume H1. apply H1.
    assume Hk: nat_p k.
    assume Hmk: m = ordsucc k.
    claim Lm: nat_p m.
    { aby nat_ordsucc Hmk Hk. }
    claim LSk: ordsucc k :e ordsucc n.
    { aby Hmk Hm. }
    claim Lk: k :e n.
    { aby ordsuccI2 ordsuccE nat_trans LSk Ln. }
    aby EmptyE exactly1of2_I1 ReplI ReplE_impred SingE binunionI2 binunionE nat_0_in_ordsucc nat_p_ordinal tagged_not_ordinal Lk Lm Hmk Hk.
Qed.

Theorem SNo_eps_ : forall n :e omega, SNo (eps_ n).
aby ordinal_ordsucc nat_p_ordinal omega_nat_p SNo_SNo SNo__eps_.
Qed.

Theorem SNo_eps_1 : SNo (eps_ 1).
aby nat_1 nat_p_omega SNo_eps_.
Qed.

Theorem SNoLev_eps_ : forall n :e omega, SNoLev (eps_ n) = ordsucc n.
aby ordinal_ordsucc nat_p_ordinal omega_nat_p SNoLev_uniq2 SNo__eps_.
Qed.

Theorem SNo_eps_SNoS_omega : forall n :e omega, eps_ n :e SNoS_ omega.
aby omega_ordsucc omega_ordinal SNoS_I SNo__eps_.
Qed.

Theorem SNo_eps_decr : forall n :e omega, forall m :e n, eps_ n < eps_ m.
aby SingI binunionI1 neq_ordsucc_0 nat_ordsucc nat_ordsucc_in_ordsucc nat_p_trans ordinal_ordsucc nat_p_ordinal omega_nat_p nat_p_omega SNoLtI3 eps_ordinal_In_eq_0 SNoLev_eps_.
Qed.

Theorem SNo_eps_pos : forall n :e omega, 0 < eps_ n.
aby EmptyE SingI binunionI1 nat_0_in_ordsucc omega_nat_p SNoLtI2 SNoLev_0 SNoLev_eps_.
Qed.

Theorem SNo_pos_eps_Lt : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> eps_ n < x.
aby In_irref In_no2cycle nat_ordsucc nat_p_ordinal nat_p_omega SNoLev_ordinal SNoLtE SNoLt_irref SNoLt_trichotomy_or_impred SNoLt_tra SNoS_E2 SNoLev_0_eq_0 eps_ordinal_In_eq_0 SNo_eps_ SNoLev_eps_.
Qed.

Theorem SNo_pos_eps_Le : forall n, nat_p n -> forall x :e SNoS_ (ordsucc (ordsucc n)), 0 < x -> eps_ n <= x.
aby In_irref In_no2cycle ordsuccE nat_ordsucc nat_p_ordinal nat_p_omega SNoLev_ordinal SNoLtE SNoLt_irref SNoLt_tra SNoLtLe_or SNoS_E2 SNoLev_0_eq_0 eps_ordinal_In_eq_0 SNo_eps_ SNoLev_eps_.
Qed.

Theorem eps_SNo_eq : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> SNoEq_ (SNoLev x) (eps_ n) x -> exists m :e n, x = eps_ m.
let n. assume Hn.
let x.
assume Hx1: x :e SNoS_ (ordsucc n).
assume Hx2: 0 < x.
assume Hx3: SNoEq_ (SNoLev x) (eps_ n) x.
apply SNoS_E2 (ordsucc n) (nat_p_ordinal (ordsucc n) (nat_ordsucc n Hn)) x Hx1.
assume Hx1a: SNoLev x :e ordsucc n.
assume Hx1b: ordinal (SNoLev x).
assume Hx1c: SNo x.
assume Hx1d: SNo_ (SNoLev x) x.
claim L1: nat_p (SNoLev x).
{ aby nat_ordsucc nat_p_trans Hx1a Hn. }
apply nat_inv (SNoLev x) L1.
- aby SNoLt_irref SNoLev_0_eq_0 Hx1c Hx2.
- assume H1. apply H1. let m. assume H1. apply H1.
  assume Hm1: nat_p m.
  assume Hm2: SNoLev x = ordsucc m.
  witness m. apply andI.
  + aby ordsuccI2 nat_ordsucc_trans Hm2 Hx1a Hn.
  + aby SingI binunionI1 nat_ordsucc nat_p_trans nat_p_ordinal nat_p_omega SNoEq_I SNo_eq SNoEq_sym_ SNoEq_tra_ eps_ordinal_In_eq_0 SNo_eps_ SNoLev_eps_ Hm2 Hm1 Hx1c Hx3.
Qed.

Theorem eps_SNoCutP : forall n :e omega, SNoCutP {0} {eps_ m|m :e n}.
aby and3I ReplE_impred SingE nat_p_trans omega_nat_p nat_p_omega SNo_0 SNo_eps_ SNo_eps_pos.
Qed.

Theorem eps_SNoCut : forall n :e omega, eps_ n = SNoCut {0} {eps_ m|m :e n}.
let n. assume Hn.
set L := {0}.
set R := {eps_ m|m :e n}.
claim Ln: nat_p n.
{ aby omega_nat_p Hn. }
claim L1: SNoCutP L R.
{ aby eps_SNoCutP Hn Ln. }
claim LRS: forall z :e R, SNo z.
{ aby L1. }
claim L2: (\/_ x :e L, ordsucc (SNoLev x)) = 1.
{ aby set_ext SingI SingE famunionI famunionE_impred In_0_1 cases_1 SNoLev_0. }
claim L3: n <> 0 -> (\/_ y :e R, ordsucc (SNoLev y)) = ordsucc n.
{ assume Hn0: n <> 0.
  apply set_ext.
  - let k. assume Hk. apply famunionE_impred R (fun y => ordsucc (SNoLev y)) k Hk.
    let z. assume Hz: z :e R. apply ReplE_impred n eps_ z Hz.
    let m. assume Hm1: m :e n. assume Hm2: z = eps_ m.
    rewrite Hm2. rewrite SNoLev_eps_ m (nat_p_omega m (nat_p_trans n Ln m Hm1)).
    assume H2: k :e ordsucc (ordsucc m).
    prove k :e ordsucc n.
    claim L3a: ordsucc m :e ordsucc n.
    { apply ordinal_ordsucc_In.
      - prove ordinal n. apply nat_p_ordinal n. aby Hn Ln L1 LRS L2 Hn0 Hk Hz Hm1 Hm2 H2.
      - aby Hn Ln L1 LRS L2 Hn0 Hk Hz Hm1 Hm2 H2.
    }
    claim L3b: ordsucc m c= ordsucc n.
    { aby nat_ordsucc nat_trans Hn Ln L1 LRS L2 Hn0 Hk Hz Hm1 Hm2 H2 L3a. }
    apply ordsuccE (ordsucc m) k H2.
    + assume H3: k :e ordsucc m. apply L3b. aby Hn Ln L1 LRS L2 Hn0 Hk Hz Hm1 Hm2 H2 L3a L3b H3.
    + assume H3: k = ordsucc m. rewrite H3. aby Hn Ln L1 LRS L2 Hn0 Hk Hz Hm1 Hm2 H2 L3a L3b H3.
  - aby ReplI famunionI ordsuccI2 nat_inv nat_p_omega SNoLev_eps_ Hn0 Ln.
}
claim L4: (\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)) = ordsucc n.
{ aby EmptyE xm Empty_eq ReplE_impred binunion_idr Subq_binunion_eq famunion_Empty nat_0_in_ordsucc cases_1 L3 L2 Ln. }
apply SNoCutP_SNoCut_impred L R L1.
assume H1: SNo (SNoCut L R).
rewrite L4.
assume H2: SNoLev (SNoCut L R) :e ordsucc (ordsucc n).
assume H3: forall w :e L, w < SNoCut L R.
assume H4: forall z :e R, SNoCut L R < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev (SNoCut L R) c= SNoLev u /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) u.
claim L5: SNo (eps_ n).
{ aby SNo_eps_ Hn. }
claim L6: forall w :e L, w < eps_ n.
{ aby SingE SNo_eps_pos Hn. }
claim L7: forall z :e R, eps_ n < z.
{ aby ReplE_impred SNo_eps_decr Hn. }
apply H5 (eps_ n) L5 L6 L7.
assume H6: SNoLev (SNoCut L R) c= SNoLev (eps_ n).
assume H7: SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) (eps_ n).
symmetry.
apply SNo_eq (SNoCut L R) (eps_ n) H1 L5.
- prove SNoLev (SNoCut L R) = SNoLev (eps_ n).
  rewrite SNoLev_eps_ n Hn.
  prove SNoLev (SNoCut L R) = ordsucc n.
  apply ordsuccE (ordsucc n) (SNoLev (SNoCut L R)) H2.
  + assume H8: SNoLev (SNoCut L R) :e ordsucc n.
    prove False.
    claim L8: eps_ n < SNoCut L R.
    { aby SingI nat_ordsucc nat_p_ordinal omega_nat_p SNoLev_ SNoS_I SNo_pos_eps_Lt H8 H3 H1 Hn. }
    apply SNoLtE (eps_ n) (SNoCut L R) (SNo_eps_ n Hn) H1 L8.
    * aby SingE binintersectE2 In_irref SNoLt_tra SNo_0 SNo_eps_ SNo_eps_pos H5 H4 H1 LRS Hn.
    * aby In_no2cycle SNoLev_eps_ H8 Hn.
    * aby ReplI SingI nat_ordsucc nat_p_ordinal omega_nat_p SNoLev_ SNoLt_irref SNoS_I SNoLev_eps_ eps_SNo_eq H4 H3 H1 Hn.
  + aby.
- aby Hn Ln L1 LRS L2 L3 L4 H1 H2 H3 H4 H5 L5 L6 L7 H6 H7.
Qed.

End TaggedSets2.

Theorem SNo_etaE : forall z, SNo z ->
  forall p:prop,
     (forall L R, SNoCutP L R
       -> (forall x :e L, SNoLev x :e SNoLev z)
       -> (forall y :e R, SNoLev y :e SNoLev z)
       -> z = SNoCut L R
       -> p)
   -> p.
let z. assume Hz: SNo z.
let p. assume H1.
claim LLz: ordinal (SNoLev z).
{ aby SNoLev_ordinal Hz. }
set L := {x :e SNoS_ (SNoLev z) | x < z}.
set R := {y :e SNoS_ (SNoLev z) | z < y}.
claim L1: z = SNoCut L R.
{ aby SNo_eta Hz H1 LLz. }
aby and3I SepE ordinal_Hered SNoLev_uniq SNoLev_prop SNoLt_tra SNoS_E L1 LLz H1 Hz.
Qed.

(*** surreal induction ***)
Theorem SNo_ind : forall P:set -> prop,
  (forall L R, SNoCutP L R
   -> (forall x :e L, P x)
   -> (forall y :e R, P y)
   -> P (SNoCut L R))
 -> forall z, SNo z -> P z.
let P.
assume H1.
claim L1: forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e alpha -> P z.
{ apply ordinal_ind.
  aby SNoLev_ordinal SNo_etaE H1.
}
aby ordsuccI2 ordinal_ordsucc SNoLev_ordinal L1.
Qed.

(*** surreal recursion ***)
Section SurrealRecI.
Variable F:set -> (set -> set) -> set.
Let default : set := Eps_i (fun _ => True).
Let G : set -> (set -> set -> set) -> set -> set
  := fun alpha g =>
       If_ii
          (ordinal alpha)
          (fun z:set => if z :e SNoS_ (ordsucc alpha) then
                           F z (fun w => g (SNoLev w) w)
                        else
                           default)
          (fun z:set => default).
(* Parameter SNo_rec_i "352082c509ab97c1757375f37a2ac62ed806c7b39944c98161720a584364bfaf" "be45dfaed6c479503a967f3834400c4fd18a8a567c8887787251ed89579f7be3" *)
Definition SNo_rec_i : set -> set
 := fun z => In_rec_ii G (SNoLev z) z.
Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> set, (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Theorem SNo_rec_i_eq : forall z, SNo z -> SNo_rec_i z = F z SNo_rec_i.
let z. assume Hz: SNo z.
prove SNo_rec_i z = F z SNo_rec_i.
prove In_rec_ii G (SNoLev z) z = F z (fun z => In_rec_ii G (SNoLev z) z).
claim L1: forall alpha, forall g h:set -> set -> set, (forall x :e alpha, g x = h x) -> G alpha g = G alpha h.
{ let alpha g h.
  assume Hgh: forall x :e alpha, g x = h x.
  prove G alpha g = G alpha h.
  prove (If_ii (ordinal alpha) (fun z:set => if z :e SNoS_ (ordsucc alpha) then F z (fun w => g (SNoLev w) w) else default) (fun z:set => default))
      = (If_ii (ordinal alpha) (fun z:set => if z :e SNoS_ (ordsucc alpha) then F z (fun w => h (SNoLev w) w) else default) (fun z:set => default)).
  apply xm (ordinal alpha).
  - assume H1: ordinal alpha.
    rewrite If_ii_1 (ordinal alpha) (fun z => if z :e SNoS_ (ordsucc alpha) then F z (fun w => h (SNoLev w) w) else default) (fun z:set => default) H1.
    rewrite If_ii_1 (ordinal alpha) (fun z => if z :e SNoS_ (ordsucc alpha) then F z (fun w => g (SNoLev w) w) else default) (fun z:set => default) H1.
    prove (fun z:set => if z :e SNoS_ (ordsucc alpha) then F z (fun w => g (SNoLev w) w) else default)
        = (fun z:set => if z :e SNoS_ (ordsucc alpha) then F z (fun w => h (SNoLev w) w) else default).
    apply func_ext set set.
    let z.
    prove (if z :e SNoS_ (ordsucc alpha) then F z (fun w => g (SNoLev w) w) else default)
        = (if z :e SNoS_ (ordsucc alpha) then F z (fun w => h (SNoLev w) w) else default).
    apply xm (z :e SNoS_ (ordsucc alpha)).
    + assume Hz: z :e SNoS_ (ordsucc alpha).
      rewrite If_i_1 (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default Hz.
      rewrite If_i_1 (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default Hz.
      prove F z (fun w => g (SNoLev w) w) = F z (fun w => h (SNoLev w) w).
      claim Lsa: ordinal (ordsucc alpha).
      { aby ordinal_ordsucc H1. }
      apply SNoS_E2 (ordsucc alpha) Lsa z Hz.
      aby ordsuccE SNoS_E2 H1 Hgh Fr.
    + aby If_i_0.
  - aby If_ii_0.
}
aby If_i_1 If_ii_1 In_rec_ii_eq SNoLev_ordinal SNoS_SNoLev L1 Hz.
Qed.

End SurrealRecI.
Section SurrealRecII.
Variable F:set -> (set -> (set -> set)) -> (set -> set).
Let default : (set -> set) := Descr_ii (fun _ => True).
Let G : set -> (set -> set -> (set -> set)) -> set -> (set -> set)
  := fun alpha g =>
       If_iii
          (ordinal alpha)
          (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha))
                              (F z (fun w => g (SNoLev w) w))
                              default)
          (fun z:set => default).
(* Parameter SNo_rec_ii "030b1b3db48f720b8db18b1192717cad8f204fff5fff81201b9a2414f5036417" "e148e62186e718374accb69cda703e3440725cca8832aed55c0b32731f7401ab" *)
Definition SNo_rec_ii : set -> (set -> set)
 := fun z => In_rec_iii G (SNoLev z) z.
Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> (set -> set), (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Theorem SNo_rec_ii_eq : forall z, SNo z -> SNo_rec_ii z = F z SNo_rec_ii.
let z. assume Hz: SNo z.
prove SNo_rec_ii z = F z SNo_rec_ii.
prove In_rec_iii G (SNoLev z) z = F z (fun z => In_rec_iii G (SNoLev z) z).
claim L1: forall alpha, forall g h:set -> set -> (set -> set), (forall x :e alpha, g x = h x) -> G alpha g = G alpha h.
{ let alpha g h.
  assume Hgh: forall x :e alpha, g x = h x.
  prove G alpha g = G alpha h.
  prove (If_iii (ordinal alpha) (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default) (fun z:set => default))
      = (If_iii (ordinal alpha) (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default) (fun z:set => default)).
  apply xm (ordinal alpha).
  - assume H1: ordinal alpha.
    rewrite If_iii_1 (ordinal alpha) (fun z => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default) (fun z:set => default) H1.
    rewrite If_iii_1 (ordinal alpha) (fun z => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default) (fun z:set => default) H1.
    prove (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default)
        = (fun z:set => If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default).
    apply func_ext set (set -> set).
    let z.
    prove (If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default)
        = (If_ii (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default).
    apply xm (z :e SNoS_ (ordsucc alpha)).
    + assume Hz: z :e SNoS_ (ordsucc alpha).
      rewrite If_ii_1 (z :e SNoS_ (ordsucc alpha)) (F z (fun w => g (SNoLev w) w)) default Hz.
      rewrite If_ii_1 (z :e SNoS_ (ordsucc alpha)) (F z (fun w => h (SNoLev w) w)) default Hz.
      prove F z (fun w => g (SNoLev w) w) = F z (fun w => h (SNoLev w) w).
      claim Lsa: ordinal (ordsucc alpha).
      { aby ordinal_ordsucc H1. }
      apply SNoS_E2 (ordsucc alpha) Lsa z Hz.
      aby ordsuccE SNoS_E2 H1 Hgh Fr.
    + aby If_ii_0.
  - aby If_iii_0.
}
aby If_ii_1 If_iii_1 In_rec_iii_eq SNoLev_ordinal SNoS_SNoLev L1 Hz.
Qed.

End SurrealRecII.
Section SurrealRec2.
Variable F:set -> set -> (set -> set -> set) -> set.
Let G:set -> (set -> set -> set) -> set -> (set -> set) -> set
  := fun w f z g => F w z (fun x y => if x = w then g y else f x y).
Let H:set -> (set -> set -> set) -> set -> set
  := fun w f z => if SNo z then SNo_rec_i (G w f) z else Empty.
(* Parameter SNo_rec2 "9c6267051fa817eed39b404ea37e7913b3571fe071763da2ebc1baa56b4b77f5" "7d10ab58310ebefb7f8bf63883310aa10fc2535f53bb48db513a868bc02ec028" *)
Definition SNo_rec2 : set -> set -> set
  := SNo_rec_ii H.
Hypothesis Fr: forall w, SNo w -> forall z, SNo z ->
   forall g h:set -> set -> set,
        (forall x :e SNoS_ (SNoLev w), forall y, SNo y -> g x y = h x y)
     -> (forall y :e SNoS_ (SNoLev z), g w y = h w y)
     -> F w z g = F w z h.

Theorem SNo_rec2_G_prop : forall w, SNo w -> forall f k:set -> set -> set,
    (forall x :e SNoS_ (SNoLev w), f x = k x)
 -> forall z, SNo z ->
    forall g h:set -> set, (forall u :e SNoS_ (SNoLev z), g u = h u)
 -> G w f z g = G w k z h.
aby If_i_0 If_i_1 SNoS_In_neq Fr.
Qed.

Theorem SNo_rec2_eq_1 : forall w, SNo w -> forall f:set -> set -> set,
  forall z, SNo z ->
   SNo_rec_i (G w f) z = G w f z (SNo_rec_i (G w f)).
let w. assume Hw: SNo w.
let f.
claim L1: forall z, SNo z -> forall g h:set -> set, (forall u :e SNoS_ (SNoLev z), g u = h u) -> G w f z g = G w f z h.
{ let z. assume Hz. let g h. assume Hgh.
  claim L1a: forall x :e SNoS_ (SNoLev w), f x = f x.
  { aby. }
  exact SNo_rec2_G_prop w Hw f f L1a z Hz g h Hgh.
}
exact SNo_rec_i_eq (G w f) L1.
Qed.

Theorem SNo_rec2_eq : forall w, SNo w -> forall z, SNo z ->
   SNo_rec2 w z = F w z SNo_rec2.
let w. assume Hw: SNo w.
let z. assume Hz: SNo z.
prove SNo_rec2 w z = F w z SNo_rec2.
prove SNo_rec_ii H w z = F w z SNo_rec2.
claim L1: forall w, SNo w ->
    forall g h:set -> set -> set, (forall x :e SNoS_ (SNoLev w), g x = h x)
     -> H w g = H w h.
{ let w. assume Hw: SNo w.
  let g h.
  assume Hgh: forall x :e SNoS_ (SNoLev w), g x = h x.
  prove H w g = H w h.
  prove (fun z:set => if SNo z then SNo_rec_i (G w g) z else Empty)
      = (fun z:set => if SNo z then SNo_rec_i (G w h) z else Empty).
  apply func_ext set set.
  let z.
  prove (if SNo z then SNo_rec_i (G w g) z else Empty)
      = (if SNo z then SNo_rec_i (G w h) z else Empty).
  apply xm (SNo z).
  - assume Hz: SNo z.
    rewrite If_i_1 (SNo z) (SNo_rec_i (G w g) z) Empty Hz.
    rewrite If_i_1 (SNo z) (SNo_rec_i (G w h) z) Empty Hz.
    prove SNo_rec_i (G w g) z = SNo_rec_i (G w h) z.
    claim L1a: forall alpha, ordinal alpha -> forall z :e SNoS_ alpha, SNo_rec_i (G w g) z = SNo_rec_i (G w h) z.
    { apply ordinal_ind.
      let alpha. assume Ha: ordinal alpha.
      assume IH: forall beta :e alpha, forall z :e SNoS_ beta, SNo_rec_i (G w g) z = SNo_rec_i (G w h) z.
      let z. assume Hz: z :e SNoS_ alpha.
      apply SNoS_E2 alpha Ha z Hz.
      assume Hz1: SNoLev z :e alpha.
      assume Hz2: ordinal (SNoLev z).
      assume Hz3: SNo z.
      assume Hz4: SNo_ (SNoLev z) z.
      prove SNo_rec_i (G w g) z = SNo_rec_i (G w h) z.
      rewrite SNo_rec2_eq_1 w Hw g z Hz3.
      rewrite SNo_rec2_eq_1 w Hw h z Hz3.
      prove G w g z (SNo_rec_i (G w g)) = G w h z (SNo_rec_i (G w h)).
      apply SNo_rec2_G_prop w Hw g h Hgh z Hz3 (SNo_rec_i (G w g)) (SNo_rec_i (G w h)).
      prove forall y :e SNoS_ (SNoLev z), SNo_rec_i (G w g) y = SNo_rec_i (G w h) y.
      let y.
      assume Hy : y :e SNoS_ (SNoLev z).
      aby Fr Hw Hz Hw Hgh Hz Ha IH Hz Hz1 Hz2 Hz3 Hz4 Hy.
    }
    aby ordinal_ordsucc SNoLev_ordinal SNoS_SNoLev Hw Hz Hw Hgh Hz L1a.
  - aby If_i_0.
}
claim L2: H w (SNo_rec_ii H) z = F w z SNo_rec2.
{ prove (if SNo z then SNo_rec_i (G w (SNo_rec_ii H)) z else Empty) = F w z SNo_rec2.
  rewrite If_i_1 (SNo z) (SNo_rec_i (G w (SNo_rec_ii H)) z) Empty Hz.
  prove SNo_rec_i (G w (SNo_rec_ii H)) z = F w z SNo_rec2.
  prove SNo_rec_i (G w (SNo_rec_ii H)) z = F w z (SNo_rec_ii H).
  rewrite SNo_rec2_eq_1 w Hw (SNo_rec_ii H) z Hz.
  prove G w (SNo_rec_ii H) z (SNo_rec_i (G w (SNo_rec_ii H))) = F w z (SNo_rec_ii H).
  prove F w z (fun x y => if x = w then SNo_rec_i (G w (SNo_rec_ii H)) y else SNo_rec_ii H x y) = F w z (SNo_rec_ii H).
  claim L2a: forall x :e SNoS_ (SNoLev w), forall y, SNo y -> (if x = w then SNo_rec_i (G w (SNo_rec_ii H)) y else SNo_rec_ii H x y) = SNo_rec_ii H x y.
  { aby If_i_0 SNoS_In_neq Hw. }
  claim L2b: forall y :e SNoS_ (SNoLev z), (if w = w then SNo_rec_i (G w (SNo_rec_ii H)) y else SNo_rec_ii H w y) = SNo_rec_ii H w y.
  { let y. assume Hy: y :e SNoS_ (SNoLev z).
    rewrite If_i_1 (w = w) (SNo_rec_i (G w (SNo_rec_ii H)) y) (SNo_rec_ii H w y) (fun q H => H).
    claim Ly: SNo y.
    { aby SNoLev_ordinal SNoS_E2 Hy Hz. }
    prove SNo_rec_i (G w (SNo_rec_ii H)) y = SNo_rec_ii H w y.
    apply eq_i_tra (SNo_rec_i (G w (SNo_rec_ii H)) y) (H w (SNo_rec_ii H) y) (SNo_rec_ii H w y).
    - aby If_i_1 Ly.
    - prove H w (SNo_rec_ii H) y = SNo_rec_ii H w y.
      rewrite SNo_rec_ii_eq H L1 w Hw.
      aby.
  }
  aby Fr Hw Hz L1 L2a L2b.
}
prove SNo_rec_ii H w z = F w z SNo_rec2.
rewrite SNo_rec_ii_eq H L1 w Hw.
aby L2.
Qed.

End SurrealRec2.

Theorem SNo_ordinal_ind : forall P:set -> prop,
  (forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, P x)
  ->
  (forall x, SNo x -> P x).
aby ordinal_ordsucc SNoLev_ordinal SNoS_SNoLev.
Qed.

Theorem SNo_ordinal_ind2 : forall P:set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, P x y)
  ->
  (forall x y, SNo x -> SNo y -> P x y).
aby ordinal_ordsucc SNoLev_ordinal SNoS_SNoLev.
Qed.

Theorem SNo_ordinal_ind3 : forall P:set -> set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall gamma, ordinal gamma ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, forall z :e SNoS_ gamma, P x y z)
  ->
  (forall x y z, SNo x -> SNo y -> SNo z -> P x y z).
aby ordinal_ordsucc SNoLev_ordinal SNoS_SNoLev.
Qed.

Theorem SNoLev_ind : forall P:set -> prop,
  (forall x, SNo x -> (forall w :e SNoS_ (SNoLev x), P w) -> P x)
  ->
  (forall x, SNo x -> P x).
let P.
assume H1: forall x, SNo x -> (forall w :e SNoS_ (SNoLev x), P w) -> P x.
claim L1: forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, P x.
{ apply ordinal_ind.
  aby SNoS_E2 H1.
}
aby SNo_ordinal_ind H1 L1.
Qed.

Theorem SNoLev_ind2 : forall P:set -> set -> prop,
  (forall x y, SNo x -> SNo y
    -> (forall w :e SNoS_ (SNoLev x), P w y)
    -> (forall z :e SNoS_ (SNoLev y), P x z)
    -> (forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z)
    -> P x y)
-> forall x y, SNo x -> SNo y -> P x y.
let P.
assume H1: forall x y, SNo x -> SNo y
    -> (forall w :e SNoS_ (SNoLev x), P w y)
    -> (forall z :e SNoS_ (SNoLev y), P x z)
    -> (forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z)
    -> P x y.
claim L1: forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall x :e SNoS_ alpha, forall y :e SNoS_ beta, P x y.
{ apply ordinal_ind.
  let alpha. assume Ha: ordinal alpha.
  assume IHa: forall gamma :e alpha, forall beta, ordinal beta -> forall x :e SNoS_ gamma, forall y :e SNoS_ beta, P x y.
  apply ordinal_ind.
  aby SNoS_E2 IHa Ha H1.
}
aby SNo_ordinal_ind2 H1 L1.
Qed.

Theorem SNoLev_ind3 : forall P:set -> set -> set -> prop,
  (forall x y z, SNo x -> SNo y -> SNo z
    -> (forall u :e SNoS_ (SNoLev x), P u y z)
    -> (forall v :e SNoS_ (SNoLev y), P x v z)
    -> (forall w :e SNoS_ (SNoLev z), P x y w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), P u v z)
    -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), P u y w)
    -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P x v w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P u v w)
    -> P x y z)
 -> forall x y z, SNo x -> SNo y -> SNo z -> P x y z.
let P.
assume H1: forall x y z, SNo x -> SNo y -> SNo z
    -> (forall u :e SNoS_ (SNoLev x), P u y z)
    -> (forall v :e SNoS_ (SNoLev y), P x v z)
    -> (forall w :e SNoS_ (SNoLev z), P x y w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), P u v z)
    -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), P u y w)
    -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P x v w)
    -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), P u v w)
    -> P x y z.
claim L1: forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma, ordinal gamma -> forall x :e SNoS_ alpha, forall y :e SNoS_ beta, forall z :e SNoS_ gamma, P x y z.
{ apply ordinal_ind.
  let alpha. assume Ha: ordinal alpha.
  assume IHa: forall delta :e alpha, forall beta, ordinal beta -> forall gamma, ordinal gamma -> forall x :e SNoS_ delta, forall y :e SNoS_ beta, forall z :e SNoS_ gamma, P x y z.
  apply ordinal_ind.
  let beta. assume Hb: ordinal beta.
  assume IHb: forall delta :e beta, forall gamma, ordinal gamma -> forall x :e SNoS_ alpha, forall y :e SNoS_ delta, forall z :e SNoS_ gamma, P x y z.
  apply ordinal_ind.
  aby SNoS_E2 IHb Hb IHa Ha H1.
}
aby SNo_ordinal_ind3 H1 L1.
Qed.

Theorem SNo_omega : SNo omega.
aby omega_ordinal ordinal_SNo.
Qed.

Theorem SNoLt_0_1 : 0 < 1.
aby In_0_1 ordinal_1 ordinal_In_SNoLt.
Qed.

Theorem SNoLt_0_2 : 0 < 2.
aby In_0_2 ordinal_2 ordinal_In_SNoLt.
Qed.

Theorem SNoLt_1_2 : 1 < 2.
aby In_1_2 ordinal_2 ordinal_In_SNoLt.
Qed.

Theorem restr_SNo_ : forall x, SNo x -> forall alpha :e SNoLev x, SNo_ alpha (x :/\: SNoElts_ alpha).
aby exactly1of2_I1 exactly1of2_I2 exactly1of2_E ReplI binunionI1 binunionI2 binintersectI binintersectE1 binintersect_Subq_2 ordinal_TransSet SNoLev_ordinal SNoLev_.
Qed.

Theorem restr_SNo : forall x, SNo x -> forall alpha :e SNoLev x, SNo (x :/\: SNoElts_ alpha).
aby ordinal_Hered SNo_SNo SNoLev_ordinal restr_SNo_.
Qed.

Theorem restr_SNoLev : forall x, SNo x -> forall alpha :e SNoLev x, SNoLev (x :/\: SNoElts_ alpha) = alpha.
aby ordinal_Hered SNoLev_ordinal SNoLev_uniq2 restr_SNo_.
Qed.

Theorem restr_SNoEq : forall x, SNo x -> forall alpha :e SNoLev x, SNoEq_ alpha (x :/\: SNoElts_ alpha) x.
aby binunionI1 binintersectI binintersectE1 SNoEq_I.
Qed.

Theorem SNo_extend0_restr_eq : forall x, SNo x -> x = SNo_extend0 x :/\: SNoElts_ (SNoLev x).
aby ordsuccI2 SNo_eq SNoEq_sym_ SNoEq_tra_ SNo_extend0_SNo SNo_extend0_SNoLev SNo_extend0_SNoEq restr_SNo restr_SNoLev restr_SNoEq.
Qed.

Theorem SNo_extend1_restr_eq : forall x, SNo x -> x = SNo_extend1 x :/\: SNoElts_ (SNoLev x).
aby ordsuccI2 SNo_eq SNoEq_sym_ SNoEq_tra_ SNo_extend1_SNo SNo_extend1_SNoLev SNo_extend1_SNoEq restr_SNo restr_SNoLev restr_SNoEq.
Qed.

Opaque eps_ SNo_rec2 SNo_rec_ii SNo_rec_i SNoLev SNo.

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
{ aby ReplEq_ext SNoL_SNoS SNoR_SNoS.
}
exact SNo_rec_i_eq (fun x m => SNoCut {m z|z :e SNoR x} {m w|w :e SNoL x}) L1.
Qed.

Theorem minus_SNo_prop1 : forall x, SNo x -> SNo (- x) /\ (forall u :e SNoL x, - x < - u) /\ (forall u :e SNoR x, - u < - x) /\ SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), SNo (- w) /\ (forall u :e SNoL w, - w < - u) /\ (forall u :e SNoR w, - u < - w) /\ SNoCutP {- z|z :e SNoR w} {- v|v :e SNoL w}.
claim IHLx : forall w :e SNoL x, SNo (- w) /\ (forall u :e SNoL w, - w < - u) /\ (forall u :e SNoR w, - u < - w).
{ aby SNoS_I2 SNoL_E IH Hx. }
claim IHRx : forall z :e SNoR x, SNo (- z) /\ (forall u :e SNoL z, - z < - u) /\ (forall u :e SNoR z, - u < - z).
{ aby SNoS_I2 SNoR_E IH Hx. }
set L := {- z|z :e SNoR x}.
set R := {- w|w :e SNoL x}.
claim LLR: SNoCutP L R.
{ prove (forall w :e L, SNo w)
     /\ (forall z :e R, SNo z)
     /\ (forall w :e L, forall z :e R, w < z).
  apply and3I.
  - aby ReplE_impred IHRx.
  - aby ReplE_impred IHLx.
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
    { aby SNoLt_tra Hv3 Hv1 Hu3 Hu1 Hx. }
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
      aby SepI binintersectE SNoLev_ordinal SNoLt_tra SNoS_I2 Hz5 Hz4 Hz1 Hz H6 H5 H4 H2 Hv1 Hu2 Hu1 IH Hx.
    + aby SepI SNoS_I2 Lvu H6 Hv1 Hu1.
    + aby SepI SNoS_I2 Lvu H4 Hv1 Hu1.
}
aby and3I ReplI SNoL_E SNoR_E SNoCutP_SNo_SNoCut SNoCutP_SNoCut_L SNoCutP_SNoCut_R minus_SNo_eq LLR Hx.
Qed.

Theorem SNo_minus_SNo : forall x, SNo x -> SNo (- x).
aby minus_SNo_prop1.
Qed.

Theorem minus_SNo_Lt_contra : forall x y, SNo x -> SNo y -> x < y -> - y < - x.
aby SepI binintersectE SNoLtE SNoLt_tra SNoS_I2 minus_SNo_prop1 SNo_minus_SNo.
Qed.

Theorem minus_SNo_Le_contra : forall x y, SNo x -> SNo y -> x <= y -> - y <= - x.
aby SNoLtLe SNoLeE SNoLe_ref minus_SNo_Lt_contra.
Qed.

Theorem minus_SNo_SNoCutP : forall x, SNo x -> SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
aby minus_SNo_prop1.
Qed.

Theorem minus_SNo_SNoCutP_gen : forall L R, SNoCutP L R -> SNoCutP {- z|z :e R} {- w|w :e L}.
aby and3I ReplE_impred SNo_minus_SNo minus_SNo_Lt_contra.
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
{ aby minus_SNo_SNoCutP Ha Ha1 Ha2 IH Hx Hx1 Hx2 Hx3 Hx4. }
prove SNoLev (- x) c= SNoLev x.
rewrite minus_SNo_eq x Hx3.
prove SNoLev (SNoCut L R) c= SNoLev x.
apply SNoCutP_SNoCut_impred L R LLR.
assume H2: SNo (SNoCut L R).
assume H3: SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume _ _ _.
claim L3: ordinal ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ aby ReplE_impred ordinal_ordsucc ordinal_famunion ordinal_binunion SNoLev_ordinal SNoL_E SNoR_E SNo_minus_SNo Hx3. }
claim L3a: TransSet ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ aby L3. }
let beta. assume Hb: beta :e SNoLev (SNoCut L R).
claim Lb: beta :e ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ aby ordsuccE Hb L3a H3. }
prove beta :e SNoLev x.
apply binunionE (\/_ x :e L, ordsucc (SNoLev x)) (\/_ y :e R, ordsucc (SNoLev y)) beta Lb.
- assume H4: beta :e \/_ x :e L, ordsucc (SNoLev x).
  apply famunionE L (fun x => ordsucc (SNoLev x)) beta H4.
  let w. assume Hw. apply Hw.
  assume Hw1: w :e L.
  assume Hw2: beta :e ordsucc (SNoLev w).
  prove beta :e SNoLev x.
  apply ReplE_impred (SNoR x) (fun z => - z) w Hw1.
  aby In_irref In_no2cycle ordsuccE ordinal_Hered ordinal_ordsucc ordinal_In_Or_Subq ordinal_ordsucc_In_eq SNoLev_ordinal SNoS_SNoLev SNoR_E SNo_minus_SNo Hw2 Hx3 Hx2 Hx1 IH Ha1.
- assume H4: beta :e \/_ y :e R, ordsucc (SNoLev y).
  apply famunionE R (fun x => ordsucc (SNoLev x)) beta H4.
  let w. assume Hw. apply Hw.
  assume Hw1: w :e R.
  assume Hw2: beta :e ordsucc (SNoLev w).
  prove beta :e SNoLev x.
  apply ReplE_impred (SNoL x) (fun z => - z) w Hw1.
  aby In_irref In_no2cycle ordsuccE ordinal_Hered ordinal_ordsucc ordinal_In_Or_Subq ordinal_ordsucc_In_eq SNoLev_ordinal SNoS_SNoLev SNoL_E SNo_minus_SNo Hw2 Hx3 Hx2 Hx1 IH Ha1.
Qed.

Theorem minus_SNo_Lev_lem2 : forall x, SNo x -> SNoLev (- x) c= SNoLev x.
aby ordinal_ordsucc SNoLev_ordinal SNoS_SNoLev minus_SNo_Lev_lem1.
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
{ aby SNoCutP_SNo_SNoCut HLR. }
claim LmCLR: SNo (- SNoCut L R).
{ aby SNo_minus_SNo LCLR. }
claim LmmCLR: SNo (- - SNoCut L R).
{ aby SNo_minus_SNo LmCLR. }
claim L1: SNoLev (SNoCut L R) c= SNoLev (- - SNoCut L R)
       /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) (- - SNoCut L R).
{ aby SNoCutP_SNoCut_L SNoCutP_SNoCut_R SNoCutP_SNoCut_fst SNo_minus_SNo minus_SNo_Lt_contra LmmCLR LmCLR LCLR HLR2 HLR1 IHR IHL HLR. }
aby set_ext Subq_tra SNo_eq minus_SNo_Lev_lem2 L1 LmmCLR LmCLR LCLR.
Qed.

Theorem minus_SNo_Lev : forall x, SNo x -> SNoLev (- x) = SNoLev x.
aby set_ext SNo_minus_SNo minus_SNo_Lev_lem2 minus_SNo_invol.
Qed.

Theorem minus_SNo_SNo_ : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNo_ alpha (- x).
aby SNo_SNo SNoLev_ SNoLev_uniq2 SNo_minus_SNo minus_SNo_Lev.
Qed.

Theorem minus_SNo_SNoS_ : forall alpha, ordinal alpha -> forall x, x :e SNoS_ alpha -> - x :e SNoS_ alpha.
aby SNoS_I SNoS_E2 minus_SNo_SNo_.
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
{ aby SNoCutP_SNo_SNoCut HLR. }
claim L2: SNoCutP mR mL.
{ aby minus_SNo_SNoCutP_gen Hv IHv HLR HLR1 HLR1 HLR2 HLR3 HvLR L1. }
apply SNoCutP_SNoCut_impred mR mL L2.
assume H1: SNo (SNoCut mR mL).
assume H2: SNoLev (SNoCut mR mL) :e ordsucc ((\/_ x :e mR, ordsucc (SNoLev x)) :\/: (\/_ y :e mL, ordsucc (SNoLev y))).
assume H3: forall x :e mR, x < SNoCut mR mL.
assume H4: forall y :e mL, SNoCut mR mL < y.
assume H5: forall z, SNo z -> (forall x :e mR, x < z) -> (forall y :e mL, z < y) -> SNoLev (SNoCut mR mL) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut mR mL)) (SNoCut mR mL) z.
claim L3: forall x :e mR, x < - v.
{ aby ReplE_impred SNoCutP_SNoCut_R minus_SNo_Lt_contra HvLR HLR2 HLR Hv.
}
claim L4: forall y :e mL, - v < y.
{ aby ReplE_impred SNoCutP_SNoCut_L minus_SNo_Lt_contra HvLR HLR1 HLR Hv.
}
apply H5 (- v) (SNo_minus_SNo v Hv) L3 L4.
aby set_ext Repl_invol_eq In_irref ordinal_In_Or_Subq SNoLev_ordinal SNo_eq SNoS_I2 SNo_minus_SNo minus_SNo_invol minus_SNo_Lev H1 L2 HvLR HLR2 HLR1 IHv Hv.
Qed.

Theorem minus_SNoCut_eq : forall L R, SNoCutP L R -> - SNoCut L R = SNoCut {- z|z :e R} {- w|w :e L}.
aby SNoCutP_SNo_SNoCut minus_SNoCut_eq_lem.
Qed.

Theorem minus_SNo_Lt_contra1 : forall x y, SNo x -> SNo y -> -x < y -> - y < x.
aby SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_invol.
Qed.

Theorem minus_SNo_Lt_contra2 : forall x y, SNo x -> SNo y -> x < -y -> y < - x.
aby SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_invol.
Qed.

Theorem mordinal_SNoLev_min_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> - alpha <= z.
aby ordinal_SNo ordinal_SNoLev_max_2 SNo_minus_SNo minus_SNo_Le_contra minus_SNo_invol minus_SNo_Lev.
Qed.

Theorem minus_SNo_SNoS_omega : forall x :e SNoS_ omega, - x :e SNoS_ omega.
aby omega_ordinal SNoLev_ SNoS_I SNoS_E2 SNo_minus_SNo minus_SNo_Lev.
Qed.

Theorem SNoL_minus_SNoR: forall x, SNo x -> SNoL (- x) = {- w|w :e SNoR x}.
let x. assume Hx.
claim Lmx: SNo (- x).
{ aby SNo_minus_SNo Hx. }
apply set_ext.
- aby ReplI SNoL_E SNoR_I SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra2 Lmx Hx.
- aby ReplE_impred SNoR_E SNoL_I SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_Lev Lmx Hx.
Qed.

End SurrealMinus.
Opaque minus_SNo.
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
{ aby ReplEq_ext SNoL_SNoS SNoR_SNoS. }
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
{ aby. }
prove forall x y, SNo x -> SNo y -> P x y.
apply SNoLev_ind2.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
assume IHx: forall w :e SNoS_ (SNoLev x), P w y.
assume IHy: forall z :e SNoS_ (SNoLev y), P x z.
assume IHxy: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z.
claim LLx: ordinal (SNoLev x).
{ aby SNoLev_ordinal Hx. }
claim LLxa: TransSet (SNoLev x).
{ aby ordinal_TransSet LLx. }
claim LLy: ordinal (SNoLev y).
{ aby SNoLev_ordinal Hy. }
claim LLya: TransSet (SNoLev y).
{ aby ordinal_TransSet LLy. }
set L1 := {w + y|w :e SNoL x}.
set L2 := {x + w|w :e SNoL y}.
set L := L1 :\/: L2.
set R1 := {z + y|z :e SNoR x}.
set R2 := {x + z|z :e SNoR y}.
set R := R1 :\/: R2.
claim IHLx : forall w :e SNoL x, P w y.
{ aby SNoS_I2 SNoL_E IHx Hx.
}
claim IHRx : forall w :e SNoR x, P w y.
{ aby SNoS_I2 SNoR_E IHx Hx. }
claim IHLy : forall w :e SNoL y, P x w.
{ aby SNoS_I2 SNoL_E IHy Hy. }
claim IHRy : forall w :e SNoR y, P x w.
{ aby SNoS_I2 SNoR_E IHy Hy. }
claim LLR: SNoCutP L R.
{ prove (forall w :e L, SNo w)
     /\ (forall z :e R, SNo z)
     /\ (forall w :e L, forall z :e R, w < z).
  apply and3I.
  - aby ReplE_impred binunionE IHLy IHLx LPE.
  - aby ReplE_impred binunionE IHRy IHRx LPE.
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
      { aby SNoS_I2 Hu2 Hu1 Hx. }
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
          { aby SNoLt_tra Hv3 Hv1 Hu3 Hu1 Hx. }
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
            { aby LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Lux IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v. }
            claim Lqx2: q :e SNoS_ (SNoLev x).
            { aby SNoS_I2 LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Lux IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqx. }
            claim Lqy: SNo (q + y).
            { apply LPE q y (IHx q Lqx2).
              assume IHq1 _ _ _ _. aby LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Lux IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqx Lqx2 IHq1.
            }
            apply SNoLt_tra (u + y) (q + y) (v + y) IHu1 Lqy IHv1.
            + prove u + y < q + y.
              apply IHu3.
              prove q :e SNoR u.
              aby SNoR_I LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Lux IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqx Lqx2 Lqy.
            + prove q + y < v + y.
              apply IHv2.
              prove q :e SNoL v.
              aby SNoL_I LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Lux IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqx Lqx2 Lqy.
          - aby SNoL_I Luv IHv2 Hv1 Hu1.
          - aby SNoR_I Luv Hv1 IHu3 Hu1.
        }
      * aby ReplE_impred SNoLt_tra SNoS_I2 SNoR_E SNoL_I SNoR_I IHu5 IHu1 Lux Hu3 Hu2 Hu1 IHRy IHxy Hy Hx LPE.
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
      { aby SNoS_I2 Hu2 Hu1 Hy. }
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
      * aby ReplE_impred SNoLt_tra SNoS_I2 SNoR_E SNoL_I SNoR_I IHu3 IHu1 Luy Hu3 Hu2 Hu1 IHRx IHxy Hy Hx LPE.
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
          { aby SNoLt_tra Hv3 Hv1 Hu3 Hu1 Hy. }
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
            { aby LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Luy IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v. }
            claim Lqy2: q :e SNoS_ (SNoLev y).
            { aby SNoS_I2 LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Luy IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqy. }
            claim Lxq: SNo (x + q).
            { apply LPE x q (IHy q Lqy2).
              assume IHq1 _ _ _ _. aby LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Luy IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqy Lqy2 IHq1.
            }
            prove x + u < x + v.
            apply SNoLt_tra (x + u) (x + q) (x + v) IHu1 Lxq IHv1.
            + prove x + u < x + q.
              apply IHu5.
              prove q :e SNoR u.
              aby SNoR_I LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Luy IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqy Lqy2 Lxq.
            + prove x + q < x + v.
              apply IHv4.
              prove q :e SNoL v.
              aby SNoL_I LPE Hx Hy IHx IHy IHxy LLx LLxa LLy LLya IHLx IHRx IHLy IHRy Hw Hz Hw Hu Hwu Hu1 Hu2 Hu3 Luy IHu1 IHu2 IHu3 IHu4 IHu5 Hz Hv Hzv Hv1 Hv2 Hv3 IHv1 IHv2 IHv3 IHv4 IHv5 Luv Hq1 Hq2 Hq5 Hq6 Hq2u Hq2v Lqy Lqy2 Lxq.
          - aby SNoL_I Luv IHv4 Hv1 Hu1.
          - aby SNoR_I Luv Hv1 IHu5 Hu1.
        }
}
aby and5I ReplI binunionI1 binunionI2 SNoL_E SNoR_E SNoCutP_SNo_SNoCut SNoCutP_SNoCut_L SNoCutP_SNoCut_R add_SNo_eq LLR Hy Hx.
Qed.

Theorem SNo_add_SNo : forall x y, SNo x -> SNo y -> SNo (x + y).
aby add_SNo_prop1.
Qed.

Theorem SNo_add_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + z).
aby SNo_add_SNo.
Qed.

Theorem SNo_add_SNo_3c : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + - z).
aby SNo_minus_SNo SNo_add_SNo_3.
Qed.

Theorem SNo_add_SNo_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> SNo (x + y + z + w).
aby SNo_add_SNo SNo_add_SNo_3.
Qed.

Theorem add_SNo_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x < z -> x + y < z + y.
aby binintersectE SNoLtE SNoLt_tra SNoL_I SNoR_I add_SNo_prop1 SNo_add_SNo.
Qed.

Theorem add_SNo_Le1 : forall x y z, SNo x -> SNo y -> SNo z -> x <= z -> x + y <= z + y.
aby SNoLtLe SNoLeE SNoLe_ref add_SNo_Lt1.
Qed.

Theorem add_SNo_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> y < z -> x + y < x + z.
aby binintersectE SNoLtE SNoLt_tra SNoL_I SNoR_I add_SNo_prop1 SNo_add_SNo.
Qed.

Theorem add_SNo_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> y <= z -> x + y <= x + z.
aby SNoLtLe SNoLeE SNoLe_ref add_SNo_Lt2.
Qed.

Theorem add_SNo_Lt3a : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y <= w -> x + y < z + w.
aby SNoLtLe_tra SNo_add_SNo add_SNo_Lt1 add_SNo_Le2.
Qed.

Theorem add_SNo_Lt3b : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y < w -> x + y < z + w.
aby SNoLeLt_tra SNo_add_SNo add_SNo_Le1 add_SNo_Lt2.
Qed.

Theorem add_SNo_Lt3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y < w -> x + y < z + w.
aby SNoLtLe add_SNo_Lt3a.
Qed.

Theorem add_SNo_Le3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y <= w -> x + y <= z + w.
aby SNoLe_tra SNo_add_SNo add_SNo_Le1 add_SNo_Le2.
Qed.

Theorem add_SNo_SNoCutP : forall x y, SNo x -> SNo y -> SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).
aby add_SNo_prop1.
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
{ aby SNoS_I2 SNoL_E IHx Hx. }
claim IHRx : forall w :e SNoR x, w + y = y + w.
{ aby SNoS_I2 SNoR_E IHx Hx. }
claim IHLy : forall w :e SNoL y, x + w = w + x.
{ aby SNoS_I2 SNoL_E IHy Hy. }
claim IHRy : forall w :e SNoR y, x + w = w + x.
{ aby SNoS_I2 SNoR_E IHy Hy. }
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
aby ReplEq_ext binunion_com IHRy IHLy IHRx IHLx.
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
{ aby set_ext ReplI ReplE_impred Repl_Empty binunion_idl SNoL_SNoS_ SNoL_0 IH. }
claim L2: {w + x|w :e SNoR 0} :\/: {0 + w|w :e SNoR x} = SNoR x.
{ aby set_ext ReplI ReplE_impred Repl_Empty binunion_idl SNoR_SNoS_ SNoR_0 IH. }
aby SNo_eta L2 L1 Hx.
Qed.

Theorem add_SNo_0R : forall x, SNo x -> x + 0 = x.
aby SNo_0 add_SNo_com add_SNo_0L.
Qed.

Theorem add_SNo_minus_SNo_linv : forall x, SNo x -> -x+x = 0.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), -w+w = 0.
prove -x+x = 0.
claim Lmx: SNo (-x).
{ aby SNo_minus_SNo Hx. }
set L1 := {w + x|w :e SNoL (- x)}.
set L2 := {- x + w|w :e SNoL x}.
set R1 := {z + x|z :e SNoR (- x)}.
set R2 := {- x + z|z :e SNoR x}.
set L := L1 :\/: L2.
set R := R1 :\/: R2.
rewrite add_SNo_eq (- x) Lmx x Hx.
prove SNoCut L R = 0.
claim LLR: SNoCutP L R.
{ aby add_SNo_SNoCutP Hx IH Lmx. }
claim LNLR: SNo (SNoCut L R).
{ aby SNoCutP_SNo_SNoCut Hx IH Lmx LLR. }
claim Lfst: SNoLev (SNoCut L R) c= SNoLev 0
         /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) 0.
{ apply SNoCutP_SNoCut_fst L R LLR 0 SNo_0.
  - aby ReplE_impred binunionE SNoS_I2 SNoL_E SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_invol minus_SNo_Lev add_SNo_Lt1 add_SNo_com Lmx IH Hx.
  - aby ReplE_impred binunionE SNoS_I2 SNoR_E SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_invol minus_SNo_Lev add_SNo_Lt1 add_SNo_com Lmx IH Hx.
}
aby set_ext Subq_Empty ordinal_Empty SNo_eq ordinal_SNoLev SNo_0 Lfst LNLR.
Qed.

Theorem add_SNo_minus_SNo_rinv : forall x, SNo x -> x + -x = 0.
aby SNo_minus_SNo add_SNo_com add_SNo_minus_SNo_linv.
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
- aby ReplE_impred binunionE SNoS_E2 ordinal_SNo SNo_add_SNo Hb Ha.
- aby EmptyE.
- aby EmptyE.
Qed.

Theorem add_SNo_ordinal_eq : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + beta = SNoCut ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.
aby Repl_Empty binunion_idl ordinal_SNo ordinal_SNoL ordinal_SNoR add_SNo_eq.
Qed.

Theorem add_SNo_ordinal_ordinal : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordinal (alpha + beta).
let alpha. assume Ha: ordinal alpha.
let beta. assume Hb: ordinal beta.
claim La: SNo alpha.
{ aby ordinal_SNo Ha. }
claim Lb: SNo beta.
{ aby ordinal_SNo Hb. }
claim Lab1: SNo (alpha + beta).
{ aby SNo_add_SNo Lb La. }
claim Lab2: ordinal (SNoLev (alpha + beta)).
{ aby SNoLev_ordinal Lab1. }
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
apply SNoLt_trichotomy_or y (alpha + beta) Hy3 Lab1.
- assume H1. aby In_irref H1 Hy1.
- assume H1: alpha + beta < y.
  prove False.
  apply add_SNo_ordinal_SNoCutP alpha Ha beta Hb.
  assume H2. apply H2.
  assume H2: forall x :e Lo1 :\/: Lo2, SNo x.
  assume _ _.
  apply SNoCutP_SNoCut (Lo1 :\/: Lo2) Empty
               (add_SNo_ordinal_SNoCutP alpha Ha beta Hb).
  assume H3. aby EmptyE In_irref SNoLt_tra add_SNo_ordinal_eq H3 H2 H1 Hy3 Hy1 Lab1 Hb Ha.
Qed.

Theorem add_SNo_ordinal_SL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordsucc alpha + beta = ordsucc (alpha + beta).
let alpha. assume Ha: ordinal alpha.
apply ordinal_ind.
let beta. assume Hb: ordinal beta.
assume IH: forall delta :e beta, ordsucc alpha + delta = ordsucc (alpha + delta).
claim La: SNo alpha.
{ aby ordinal_SNo Ha. }
claim Lb: SNo beta.
{ aby ordinal_SNo Hb. }
claim Lab: ordinal (alpha + beta).
{ aby add_SNo_ordinal_ordinal Hb Ha. }
claim LSa: ordinal (ordsucc alpha).
{ aby ordinal_ordsucc Ha. }
claim LSa2: SNo (ordsucc alpha).
{ aby ordinal_SNo LSa. }
claim LSab: ordinal (ordsucc alpha + beta).
{ aby add_SNo_ordinal_ordinal LSa Hb. }
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
{ aby ReplI binunionI1 ordsuccI2 SNoS_I ordinal_SNo_ ordinal_SNoLt_In H1 LSab LSa Lab Ha. }
apply ordinal_ordsucc_In_eq (ordsucc alpha + beta) (alpha + beta) LSab L1.
- assume H3: ordsucc (alpha + beta) :e ordsucc alpha + beta.
  prove False.
  set z := ordsucc (alpha + beta).
  claim Lz: ordinal z.
  { aby ordinal_ordsucc Lab. }
  claim Lz1: TransSet z.
  { aby ordinal_TransSet Lz. }
  claim Lz2: SNo z.
  { aby ordinal_SNo Lz. }
  claim L2: SNoLev (ordsucc alpha + beta) c= SNoLev z
         /\ SNoEq_ (SNoLev (ordsucc alpha + beta)) (ordsucc alpha + beta) z.
  { apply H2 z (ordinal_SNo z Lz).
    - let w. assume Hw: w :e Lo1 :\/: Lo2.
      prove w < z.
      apply binunionE Lo1 Lo2 w Hw.
      + assume H4: w :e Lo1.
        apply ReplE_impred (SNoS_ (ordsucc alpha)) (fun x => x + beta) w H4.
        aby Subq_ref ordsuccI2 ordsuccE SNoLeLt_tra SNoS_E2 ordinal_SNo ordinal_In_SNoLt ordinal_SNoLev_max_2 ordinal_Subq_SNoLe SNo_add_SNo add_SNo_Le1 add_SNo_ordinal_ordinal Lz2 Lz LSa Lab Lb La Hb Ha.
      + assume H4: w :e Lo2.
        apply ReplE_impred (SNoS_ beta) (fun x => ordsucc alpha + x) w H4.
        aby ordsuccI2 ordinal_ordsucc_In SNoLeLt_tra SNoS_E2 ordinal_SNo ordinal_In_SNoLt ordinal_SNoLev_max_2 ordinal_SNoLt_In SNo_add_SNo add_SNo_Lt2 add_SNo_Le2 add_SNo_ordinal_ordinal Lz2 Lz LSa2 LSa Lab Lb La IH Hb Ha.
    - aby EmptyE.
  }
  aby In_irref ordinal_SNoLev L2 Lz H3 LSab.
- aby.
Qed.

Theorem add_SNo_ordinal_SR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + ordsucc beta = ordsucc (alpha + beta).
aby ordinal_ordsucc ordinal_SNo add_SNo_com add_SNo_ordinal_SL.
Qed.

Theorem add_SNo_ordinal_InL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e alpha, gamma + beta :e alpha + beta.
aby ordinal_Hered ordinal_SNo ordinal_In_SNoLt ordinal_SNoLt_In add_SNo_Lt1 add_SNo_ordinal_ordinal.
Qed.

Theorem add_SNo_ordinal_InR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e beta, alpha + gamma :e alpha + beta.
aby ordinal_Hered ordinal_SNo add_SNo_com add_SNo_ordinal_InL.
Qed.

Theorem add_nat_add_SNo : forall n m :e omega, add_nat n m = n + m.
let n. assume Hn: n :e omega.
claim Ln1: nat_p n.
{ aby omega_nat_p Hn. }
claim Ln2: ordinal n.
{ aby nat_p_ordinal Ln1. }
claim Ln3: SNo n.
{ aby ordinal_SNo Ln2. }
claim L1: forall m, nat_p m -> add_nat n m = n + m.
{ apply nat_ind.
  - aby add_nat_0R add_SNo_0R Ln3.
  - aby nat_p_ordinal add_nat_SR add_SNo_ordinal_SR Ln2.
}
aby omega_nat_p L1.
Qed.

Theorem add_SNo_In_omega : forall n m :e omega, n + m :e omega.
aby add_nat_p omega_nat_p nat_p_omega add_nat_add_SNo.
Qed.

Theorem add_SNo_1_1_2 : 1 + 1 = 2.
aby nat_1 add_nat_1_1_2 nat_p_omega add_nat_add_SNo.
Qed.

Theorem add_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x + y), (exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Hy Hx. }
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
  - aby add_SNo_SNoCutP Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC.
  - aby SNoCutP_SNoL_SNoR Hu1.
  - aby ReplE_impred binunionE SNoLtLe_or SNoL_E SNo_eta SNo_add_SNo HNC Hu1 Hy Hx.
  - rewrite <- add_SNo_eq x Hx y Hy.
    prove forall z :e SNoR u, x + y < z.
    let z. assume Hz: z :e SNoR u.
    apply SNoR_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: u < z.
    apply SNoLt_trichotomy_or (x + y) z Lxy Hz1.
    + assume H1. aby In_no2cycle H1 Hz2 Hu2.
    + assume H1: z < x + y.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { aby SNoR_SNoS_ Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { apply SNoLev_ordinal (x+y) Lxy. assume Hxy1 _.
        aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Hxy1.
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
          - aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
          - prove u <= v + y.
            apply SNoLe_tra u z (v + y) Hu1 Hz1 (SNo_add_SNo v y Hv1 Hy).
            + prove u <= z. apply SNoLtLe. aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
            + prove z <= v + y. aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
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
          - aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
          - prove u <= x + v.
            apply SNoLe_tra u z (x + v) Hu1 Hz1 (SNo_add_SNo x v Hx Hv1).
            + prove u <= z. apply SNoLtLe. aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
            + prove z <= x + v. aby Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1 Lz1 Lz2 H2 H3 Hv H3 Hv1 Hv2 Hv3.
        }
}
aby SNoL_E LI Lxy.
Qed.

Theorem add_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x + y), (exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u).
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Hy Hx. }
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
  - aby SNoCutP_SNoL_SNoR Hu1.
  - aby add_SNo_SNoCutP Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC.
  - rewrite <- add_SNo_eq x Hx y Hy.
    prove forall z :e SNoL u, z < x + y.
    let z. assume Hz: z :e SNoL u.
    apply SNoL_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: z < u.
    apply SNoLt_trichotomy_or z (x + y) Hz1 Lxy.
    + assume H1. aby In_no2cycle H1 Hz2 Hu2.
    + assume H1: x + y < z.
      prove False.
      claim Lz1: z :e SNoS_ (SNoLev u).
      { aby SNoL_SNoS_ Hx Hy Lxy Hu1 IH Hu2 Hu3 HNC Hz Hz1 Hz2 Hz3 H1. }
      claim Lz2: SNoLev z :e SNoLev (x + y).
      { aby SNoLev_ordinal Hz2 Hu2 Lxy. }
      aby SNoLtLe SNoLe_tra SNoR_E SNo_add_SNo Lz2 Lz1 H1 Hz3 Hz1 HNC IH Hu1 Hy Hx.
  - aby ReplE_impred binunionE SNoLtLe_or SNoR_E SNo_eta SNo_add_SNo HNC Hu1 Hy Hx.
}
aby SNoR_E LI Lxy.
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
{ aby SNo_add_SNo Hy Hx. }
claim Lyz: SNo (y + z).
{ aby SNo_add_SNo Hz Hy. }
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
{ aby add_SNo_SNoCutP Hx Hy Hz IH1 IH2 IH3 IH4 IH5 IH6 IH7 Lxy Lyz. }
claim Lxyz34: SNoCutP (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4).
{ aby add_SNo_SNoCutP Hx Hy Hz IH1 IH2 IH3 IH4 IH5 IH6 IH7 Lxy Lyz Lxyz12. }
apply SNoCut_ext.
- aby Hx Hy Hz IH1 IH2 IH3 IH4 IH5 IH6 IH7 Lxy Lyz Lxyz12 Lxyz34.
- aby Hx Hy Hz IH1 IH2 IH3 IH4 IH5 IH6 IH7 Lxy Lyz Lxyz12 Lxyz34.
- prove forall w :e Lxyz1 :\/: Lxyz2, w < SNoCut (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4).
  rewrite <- add_SNo_eq (x+y) Lxy z Hz.
  prove forall w :e Lxyz1 :\/: Lxyz2, w < (x + y) + z.
  let w. assume Hw: w :e Lxyz1 :\/: Lxyz2.
  apply binunionE Lxyz1 Lxyz2 w Hw.
  + assume Hw: w :e Lxyz1.
    apply ReplE_impred (SNoL x) (fun w => w+(y+z)) w Hw.
    aby SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt1 Lxy IH1 Hz Hy Hx.
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
    * aby SNoLeLt_tra SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Lt2 add_SNo_Le2 Hu1 Lxy IH2 Hz Hy Hx.
    * aby SNoLeLt_tra SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt2 add_SNo_Le2 Hu1 Lxy IH3 Hz Hy Hx.
- prove forall v :e Rxyz1 :\/: Rxyz2, SNoCut (Lxyz3 :\/: Lxyz4) (Rxyz3 :\/: Rxyz4) < v.
  rewrite <- add_SNo_eq (x+y) Lxy z Hz.
  prove forall v :e Rxyz1 :\/: Rxyz2, (x + y) + z < v.
  let v. assume Hv: v :e Rxyz1 :\/: Rxyz2.
  apply binunionE Rxyz1 Rxyz2 v Hv.
  + assume Hv: v :e Rxyz1.
    apply ReplE_impred (SNoR x) (fun w => w+(y+z)) v Hv.
    aby SNoR_E SNoR_SNoS_ SNo_add_SNo add_SNo_Lt1 Lxy IH1 Hz Hy Hx.
  + assume Hv: v :e Rxyz2.
    apply ReplE_impred (SNoR (y+z)) (fun w => x+w) v Hv.
    let u.
    assume Hu: u :e SNoR (y+z).
    aby SNoLtLe_tra SNoR_E SNoR_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Lt2 add_SNo_Le2 add_SNo_SNoR_interpolate Hu Lyz Lxy IH3 IH2 Hz Hy Hx.
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
    * aby SNoLeLt_tra SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Le1 Hu1 Lyz IH1 Hz Hy Hx.
    * aby SNoLeLt_tra SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Le1 add_SNo_Lt2 Hu1 Lyz IH2 Hz Hy Hx.
  + assume Hw: w :e Lxyz4.
    apply ReplE_impred (SNoL z) (fun w => (x+y)+w) w Hw.
    aby SNoL_E SNoL_SNoS_ SNo_add_SNo add_SNo_Lt2 Lyz IH3 Hz Hy Hx.
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
    * aby SNoLtLe_tra SNoR_E SNoR_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Le1 Hu1 Lyz IH1 Hz Hy Hx.
    * aby SNoLtLe_tra SNoR_E SNoR_SNoS_ SNo_add_SNo add_SNo_Lt1 add_SNo_Le1 add_SNo_Lt2 Hu1 Lyz IH2 Hz Hy Hx.
  + assume Hv: v :e Rxyz4.
    apply ReplE_impred (SNoR z) (fun w => (x+y)+w) v Hv.
    aby SNoR_E SNoR_SNoS_ SNo_add_SNo add_SNo_Lt2 Lyz IH3 Hz Hy Hx.
Qed.

Theorem add_SNo_minus_R2 : forall x y, SNo x -> SNo y -> (x + y) + - y = x.
aby SNo_minus_SNo add_SNo_0R add_SNo_minus_SNo_rinv add_SNo_assoc.
Qed.

Theorem add_SNo_minus_R2' : forall x y, SNo x -> SNo y -> (x + - y) + y = x.
aby SNo_minus_SNo minus_SNo_invol add_SNo_minus_R2.
Qed.

Theorem add_SNo_minus_L2 : forall x y, SNo x -> SNo y -> - x + (x + y) = y.
aby SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_minus_R2.
Qed.

Theorem add_SNo_minus_L2' : forall x y, SNo x -> SNo y -> x + (- x + y) = y.
aby SNo_minus_SNo minus_SNo_invol add_SNo_minus_L2.
Qed.

Theorem add_SNo_cancel_L : forall x y z, SNo x -> SNo y -> SNo z -> x + y = x + z -> y = z.
aby SNo_minus_SNo add_SNo_minus_L2.
Qed.

Theorem add_SNo_cancel_R : forall x y z, SNo x -> SNo y -> SNo z -> x + y = z + y -> x = z.
aby add_SNo_com add_SNo_cancel_L.
Qed.

Theorem minus_SNo_0 : - 0 = 0.
aby SNo_0 SNo_minus_SNo add_SNo_0L add_SNo_minus_SNo_rinv add_SNo_cancel_L.
Qed.

Theorem minus_add_SNo_distr : forall x y, SNo x -> SNo y -> -(x+y) = (-x) + (-y).
aby SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0R add_SNo_minus_SNo_rinv add_SNo_assoc add_SNo_cancel_L.
Qed.

Theorem minus_add_SNo_distr_3 : forall x y z, SNo x -> SNo y -> SNo z -> -(x + y + z) = -x + - y + -z.
aby SNo_add_SNo minus_add_SNo_distr.
Qed.

Theorem add_SNo_Lev_bd : forall x y, SNo x -> SNo y -> SNoLev (x + y) c= SNoLev x + SNoLev y.
set P : set -> set -> prop := fun x y => SNoLev (x + y) c= SNoLev x + SNoLev y.
apply SNoLev_ind2.
let x y.
assume Hx: SNo x.
assume Hy: SNo y.
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Hy Hx. }
claim LLxLy: ordinal (SNoLev x + SNoLev y).
{ aby SNoLev_ordinal add_SNo_ordinal_ordinal Hy Hx. }
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
{ aby add_SNo_SNoCutP Hx Hy Lxy LLxLy IH1 IH2 IH3. }
apply SNoCutP_SNoCut_impred (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2) L1.
assume H1: SNo (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)).
assume H2: SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) :e ordsucc ((\/_ x :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev x)) :\/: (\/_ y :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev y))).
assume _ _ _.
claim Lxy1E: forall u :e Lxy1, forall p:set -> prop, (forall w :e SNoS_ (SNoLev x), u = w + y -> SNo w -> SNoLev w :e SNoLev x -> w < x -> p (w + y)) -> p u.
{ aby ReplE_impred SNoL_E SNoL_SNoS_ Hx. }
claim Lxy2E: forall u :e Lxy2, forall p:set -> prop, (forall w :e SNoS_ (SNoLev y), u = x + w -> SNo w -> SNoLev w :e SNoLev y -> w < y -> p (x + w)) -> p u.
{ aby ReplE_impred SNoL_E SNoL_SNoS_ Hy. }
claim Rxy1E: forall u :e Rxy1, forall p:set -> prop, (forall w :e SNoS_ (SNoLev x), u = w + y -> SNo w -> SNoLev w :e SNoLev x -> x < w -> p (w + y)) -> p u.
{ aby ReplE_impred SNoR_E SNoR_SNoS_ Hx. }
claim Rxy2E: forall u :e Rxy2, forall p:set -> prop, (forall w :e SNoS_ (SNoLev y), u = x + w -> SNo w -> SNoLev w :e SNoLev y -> y < w -> p (x + w)) -> p u.
{ aby ReplE_impred SNoR_E SNoR_SNoS_ Hy. }
claim Lxy1E2: forall u :e Lxy1, SNo u.
{ aby SNo_add_SNo Lxy1E Hy. }
claim Lxy2E2: forall u :e Lxy2, SNo u.
{ aby SNo_add_SNo Lxy2E Hx. }
claim Rxy1E2: forall u :e Rxy1, SNo u.
{ aby SNo_add_SNo Rxy1E Hy. }
claim Rxy2E2: forall u :e Rxy2, SNo u.
{ aby SNo_add_SNo Rxy2E Hx. }
claim L2: ordinal ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))).
{ aby binunionE ordinal_ordsucc ordinal_famunion ordinal_binunion SNoLev_ordinal Rxy2E2 Rxy1E2 Lxy2E2 Lxy1E2. }
claim L3: SNoLev (SNoCut (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2)) c= (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u)).
{ aby TransSet_In_ordsucc_Subq L2 H2. }
claim L4: ((\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) :\/: (\/_ u :e (Rxy1 :\/: Rxy2), ordsucc (SNoLev u))) c= SNoLev x + SNoLev y.
{ apply binunion_Subq_min.
  - prove (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)) c= SNoLev x + SNoLev y.
    let v. assume Hv: v :e (\/_ u :e (Lxy1 :\/: Lxy2), ordsucc (SNoLev u)).
    apply famunionE_impred (Lxy1 :\/: Lxy2) (fun u => ordsucc (SNoLev u)) v Hv.
    let u. assume Hu: u :e Lxy1 :\/: Lxy2.
    apply binunionE Lxy1 Lxy2 u Hu.
    + assume Hu: u :e Lxy1. apply Lxy1E u Hu.
      aby In_irref In_no2cycle ordsuccE ordinal_Hered ordinal_ordsucc ordinal_In_Or_Subq SNoLev_ordinal SNo_add_SNo add_SNo_ordinal_InL IH1 LLxLy Hy Hx.
    + assume Hu: u :e Lxy2. apply Lxy2E u Hu.
      aby In_irref In_no2cycle ordsuccE ordinal_Hered ordinal_ordsucc ordinal_In_Or_Subq SNoLev_ordinal SNo_add_SNo add_SNo_ordinal_InR IH2 LLxLy Hy Hx.
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
          + aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
          + aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
        - aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (w + y) c= SNoLev w + SNoLev y.
          { apply IH1. prove w :e SNoS_ (SNoLev x). aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1. }
          claim L4a: SNoLev w + SNoLev y :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InL.
            - apply SNoLev_ordinal. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
            - apply SNoLev_ordinal. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
            - aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
          }
          claim L4b: SNoLev w + SNoLev y c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a H. }
          claim L4c: v c= SNoLev (w + y).
          { apply ordinal_In_Or_Subq (SNoLev (w + y)) v (SNoLev_ordinal (w + y) (SNo_add_SNo w y Hw3 Hy)) Lv.
            - assume H2: SNoLev (w + y) :e v.
              prove False.
              apply ordsuccE (SNoLev (w + y)) v Hw6.
              + assume H3: v :e SNoLev (w + y).
                exact In_no2cycle (SNoLev (w + y)) v H2 H3.
              + assume H3: v = SNoLev (w + y).
                apply In_irref v. rewrite H3 at 1. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b H2 H3.
            - assume H2: v c= SNoLev (w + y). aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b H2.
          }
          apply In_irref (SNoLev w + SNoLev y).
          prove (SNoLev w + SNoLev y) :e (SNoLev w + SNoLev y).
          apply LIHw.
          prove (SNoLev w + SNoLev y) :e SNoLev (w + y).
          apply L4c.
          prove (SNoLev w + SNoLev y) :e v.
          apply H1.
          prove (SNoLev w + SNoLev y) :e SNoLev x + SNoLev y.
          aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b L4c.
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
          + aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
          + aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
        - aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6.
      }
      apply ordinal_In_Or_Subq v (SNoLev x + SNoLev y) Lv LLxLy.
      * assume H1: v :e SNoLev x + SNoLev y. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1.
      * { assume H1: SNoLev x + SNoLev y c= v.
          prove False.
          claim LIHw: SNoLev (x + w) c= SNoLev x + SNoLev w.
          { apply IH2. prove w :e SNoS_ (SNoLev y). aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1. }
          claim L4a: SNoLev x + SNoLev w :e SNoLev x + SNoLev y.
          { apply add_SNo_ordinal_InR.
            - apply SNoLev_ordinal. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
            - apply SNoLev_ordinal. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
            - aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw.
          }
          claim L4b: SNoLev x + SNoLev w c= SNoLev x + SNoLev y.
          { apply LLxLy. assume H _. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a H. }
          claim L4c: v c= SNoLev (x + w).
          { apply ordinal_In_Or_Subq (SNoLev (x + w)) v (SNoLev_ordinal (x + w) (SNo_add_SNo x w Hx Hw3)) Lv.
            - assume H2: SNoLev (x + w) :e v.
              prove False.
              apply ordsuccE (SNoLev (x + w)) v Hw6.
              + assume H3: v :e SNoLev (x + w).
                exact In_no2cycle (SNoLev (x + w)) v H2 H3.
              + assume H3: v = SNoLev (x + w).
                apply In_irref v. rewrite H3 at 1. aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b H2 H3.
            - assume H2: v c= SNoLev (x + w). aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b H2.
          }
          apply In_irref (SNoLev x + SNoLev w).
          prove (SNoLev x + SNoLev w) :e (SNoLev x + SNoLev w).
          apply LIHw.
          prove (SNoLev x + SNoLev w) :e SNoLev (x + w).
          apply L4c.
          prove (SNoLev x + SNoLev w) :e v.
          apply H1.
          prove (SNoLev x + SNoLev w) :e SNoLev x + SNoLev y.
          aby Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 Hv Hu Hu Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Lv H1 LIHw L4a L4b L4c.
        }
}
aby Subq_tra Hx Hy Lxy LLxLy IH1 IH2 IH3 L1 H1 H2 Lxy1E Lxy2E Rxy1E Rxy2E Lxy1E2 Lxy2E2 Rxy1E2 Rxy2E2 L2 L3 L4.
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
- aby In_irref ordinal_In_Or_Subq omega_ordinal SNoLev_ordinal SNo_add_SNo add_SNo_In_omega add_SNo_Lev_bd Hy3 Hy1 Hx3 Hx1.
- aby SNoLev_ SNo_add_SNo Hy3 Hx3.
Qed.

Theorem add_SNo_Lt1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < z + y -> x < z.
aby SNo_minus_SNo SNo_add_SNo add_SNo_Lt1 add_SNo_minus_R2.
Qed.

Theorem add_SNo_Lt2_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < x + z -> y < z.
aby add_SNo_com add_SNo_Lt1_cancel.
Qed.

Theorem add_SNo_Le1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y <= z + y -> x <= z.
aby SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_minus_R2.
Qed.

Theorem add_SNo_assoc_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> x + y + z + w = (x + y + z) + w.
aby SNo_add_SNo add_SNo_assoc.
Qed.

Theorem add_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x + y + z = y + x + z.
aby add_SNo_com add_SNo_assoc.
Qed.

Theorem add_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) + z = (x + z) + y.
aby add_SNo_com add_SNo_assoc.
Qed.

Theorem add_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
aby SNo_add_SNo add_SNo_assoc add_SNo_com_3b_1_2.
Qed.

Theorem add_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x + y + z = z + x + y.
aby add_SNo_com add_SNo_assoc.
Qed.

Theorem add_SNo_rotate_4_1 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w ->
  x + y + z + w = w + x + y + z.
aby SNo_add_SNo add_SNo_com_3_0_1 add_SNo_rotate_3_1.
Qed.

Theorem add_SNo_rotate_5_1 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = v + x + y + z + w.
aby SNo_add_SNo_3 add_SNo_com_3_0_1 add_SNo_rotate_4_1.
Qed.

Theorem add_SNo_rotate_5_2 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = w + v + x + y + z.
aby add_SNo_rotate_5_1.
Qed.

Theorem add_SNo_minus_SNo_prop2 : forall x y, SNo x -> SNo y -> x + - x + y = y.
aby SNo_minus_SNo add_SNo_0L add_SNo_minus_SNo_rinv add_SNo_assoc.
Qed.

Theorem add_SNo_minus_SNo_prop3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (- z + w) = x + y + w.
aby SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_L2' add_SNo_minus_SNo_prop2.
Qed.

Theorem add_SNo_minus_SNo_prop5 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + - z) + (z + w) = x + y + w.
aby SNo_minus_SNo minus_SNo_invol add_SNo_minus_SNo_prop3.
Qed.

Theorem add_SNo_minus_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x + - y < z -> x < z + y.
aby SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_rinv add_SNo_assoc add_SNo_Lt1_cancel.
Qed.

Theorem add_SNo_minus_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> z < x + - y -> z + y < x.
aby SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_rinv add_SNo_assoc add_SNo_Lt1_cancel.
Qed.

Theorem add_SNo_minus_Lt1b : forall x y z, SNo x -> SNo y -> SNo z -> x < z + y -> x + - y < z.
aby SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_linv add_SNo_assoc add_SNo_Lt1_cancel.
Qed.

Theorem add_SNo_minus_Lt2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y < x -> z < x + - y.
aby SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_linv add_SNo_assoc add_SNo_Lt1_cancel.
Qed.

Theorem add_SNo_minus_Lt1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y < w + z -> x + y + - z < w.
aby SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt1b.
Qed.

Theorem add_SNo_minus_Lt2b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> w + z < x + y -> w < x + y + - z.
aby SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt2b.
Qed.

Theorem add_SNo_minus_Lt_lem : forall x y z u v w, SNo x -> SNo y -> SNo z -> SNo u -> SNo v -> SNo w ->
  x + y + w < u + v + z ->
  x + y + - z < u + v + - w.
aby SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_assoc add_SNo_minus_Lt1b add_SNo_minus_Lt2b.
Qed.

Theorem add_SNo_minus_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> z <= x + - y -> z + y <= x.
aby SNoLtLe SNoLeE SNoLe_ref SNo_minus_SNo SNo_add_SNo add_SNo_minus_R2' add_SNo_minus_Lt2.
Qed.

Theorem add_SNo_minus_Le2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y <= x -> z <= x + - y.
aby SNoLtLe SNoLeE SNoLe_ref SNo_add_SNo add_SNo_minus_R2 add_SNo_minus_Lt2b.
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
aby SNo_add_SNo add_SNo_Lt3 add_SNo_assoc add_SNo_com_4_inner_mid add_SNo_rotate_3_1 H2 H1 Hv Hu Hw Hz Hy Hx.
Qed.

Theorem add_SNo_Lt_subprop3a : forall x y z w u a, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a
  -> x + z < w + a
  -> y + a < u
  -> x + y + z < w + u.
aby SNoLt_tra SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 add_SNo_rotate_3_1.
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
aby SNo_0 SNo_add_SNo add_SNo_com add_SNo_0R add_SNo_Lt_subprop3a H2 H1 Ha Hv Hu Hw Hy Hx.
Qed.

Theorem add_SNo_Lt_subprop3c : forall x y z w u a b c, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a -> SNo b -> SNo c
 -> x + a < b + c
 -> y + c < u
 -> b + z < w + a
 -> x + y + z < w + u.
let x y z w u a b c.
assume Hx Hy Hz Hw Hu Ha Hb Hc H1 H2 H3.
claim L1: x + z < c + w.
{ aby add_SNo_com add_SNo_Lt_subprop2 H3 H1 Hc Hb Ha Hw Hz Hx. }
claim Lxz: SNo (x + z).
{ aby SNo_add_SNo Hz Hx. }
claim Lcw: SNo (c + w).
{ aby SNo_add_SNo Hc Hw. }
aby SNoLt_tra SNo_add_SNo add_SNo_Lt1 add_SNo_Lt2 add_SNo_com add_SNo_assoc add_SNo_rotate_3_1 Lcw Lxz L1 H2 Hc Hu Hw Hz Hy Hx.
Qed.

Theorem add_SNo_Lt_subprop3d : forall x y w u v a b c, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a -> SNo b -> SNo c
 -> x + a < b + v
 -> y < c + u
 -> b + c < w + a
 -> x + y < w + u + v.
let x y w u v a b c.
assume Hx Hy Hw Hu Hv Ha Hb Hc H1 H2 H3.
claim L1: b + y < w + u + a.
{ aby add_SNo_Lt_subprop3b H3 H2 Hc Hb Ha Hu Hw Hy. }
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Hy Hx. }
claim Lwuv: SNo (w + u + v).
{ aby SNo_add_SNo Hv Hu Hw. }
claim Lwua: SNo (w + u + a).
{ aby SNo_add_SNo Ha Hu Hw. }
claim Lby: SNo (b + y).
{ aby SNo_add_SNo Hb Hy. }
apply add_SNo_Lt1_cancel (x + y) b (w + u + v) Lxy Hb Lwuv.
prove (x + y) + b < (w + u + v) + b.
apply SNoLt_tra ((x + y) + b)
                (x + w + u + a)
                ((w + u + v) + b)
                (SNo_add_SNo (x + y) b Lxy Hb)
                (SNo_add_SNo x (w + u + a) Hx Lwua)
                (SNo_add_SNo (w + u + v) b Lwuv Hb).
- aby add_SNo_Lt2 add_SNo_com add_SNo_assoc Lby Lwua L1 Hb Hy Hx.
- aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_assoc add_SNo_assoc_4 add_SNo_rotate_3_1 H1 Hb Ha Hv Hu Hw Hx.
Qed.

Theorem ordinal_ordsucc_SNo_eq : forall alpha, ordinal alpha -> ordsucc alpha = 1 + alpha.
aby ordinal_Empty ordinal_SNo add_SNo_0L add_SNo_ordinal_SL.
Qed.

Theorem add_SNo_3a_2b: forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u
 -> (x + y + z) + (w + u) = (u + y + z) + (w + x).
aby SNo_add_SNo SNo_add_SNo_3 add_SNo_com add_SNo_com_4_inner_mid.
Qed.

Theorem add_SNo_1_ordsucc : forall n :e omega, n + 1 = ordsucc n.
aby nat_0 nat_1 add_nat_0R add_nat_SR nat_p_omega add_nat_add_SNo.
Qed.

Theorem add_SNo_eps_Lt : forall x, SNo x -> forall n :e omega, x < x + eps_ n.
aby SNo_0 SNo_eps_ SNo_eps_pos add_SNo_Lt2 add_SNo_0R.
Qed.

Theorem add_SNo_eps_Lt' : forall x y, SNo x -> SNo y -> forall n :e omega, x < y -> x < y + eps_ n.
aby SNoLt_tra SNo_eps_ SNo_add_SNo add_SNo_eps_Lt.
Qed.

Theorem SNoLt_minus_pos : forall x y, SNo x -> SNo y -> x < y -> 0 < y + - x.
aby SNo_0 add_SNo_0L add_SNo_minus_Lt2b.
Qed.

Theorem add_SNo_omega_In_cases: forall m, forall n :e omega, forall k, nat_p k -> m :e n + k -> m :e n \/ m + - n :e k.
let m n. assume Hn.
claim Ln: SNo n.
{ aby omega_SNo Hn. }
apply nat_ind.
- aby add_SNo_0R Ln.
- aby ordsuccI1 ordsuccI2 ordsuccE nat_p_omega nat_p_SNo SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_In_omega add_SNo_assoc add_SNo_minus_L2 add_SNo_1_ordsucc Ln Hn.
Qed.

Theorem add_SNo_Lt4 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v -> x < w -> y < u -> z < v -> x + y + z < w + u + v.
aby SNo_add_SNo add_SNo_Lt3.
Qed.

Theorem add_SNo_3_3_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  x + y < z + w -> x + y + u < z + w + u.
aby SNo_add_SNo add_SNo_Lt1 add_SNo_assoc.
Qed.

Theorem add_SNo_3_2_3_Lt1 : forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u ->
  y + x < z + w -> x + u + y < z + w + u.
aby add_SNo_rotate_3_1 add_SNo_3_3_3_Lt1. 
Qed.

Theorem add_SNo_minus_Lt12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v < w + u + z
 -> x + y + - z < w + u + - v.
aby SNo_minus_SNo SNo_add_SNo SNo_add_SNo_3 add_SNo_assoc add_SNo_com_3b_1_2 add_SNo_minus_Lt2b add_SNo_minus_Lt1b3.
Qed.

Theorem add_SNo_minus_Le1b : forall x y z, SNo x -> SNo y -> SNo z -> x <= z + y -> x + - y <= z.
aby SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_linv add_SNo_assoc add_SNo_Le1_cancel.
Qed.

Theorem add_SNo_minus_Le1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y <= w + z -> x + y + - z <= w.
aby SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Le1b.
Qed.

Theorem add_SNo_minus_Le12b3: forall x y z w u v,
    SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
 -> x + y + v <= w + u + z
 -> x + y + - z <= w + u + - v.
aby SNo_minus_SNo SNo_add_SNo SNo_add_SNo_3 add_SNo_assoc add_SNo_com_3b_1_2 add_SNo_minus_Le2b add_SNo_minus_Le1b3.
Qed.

End SurrealAdd.

Opaque add_SNo.

Section SurrealAbs.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
(* Parameter abs_SNo "9f9389c36823b2e0124a7fe367eb786d080772b5171a5d059b10c47361cef0ef" "34f6dccfd6f62ca020248cdfbd473fcb15d8d9c5c55d1ec7c5ab6284006ff40f" *)
Definition abs_SNo : set -> set := fun x => if 0 <= x then x else - x.

Theorem nonneg_abs_SNo : forall x, 0 <= x -> abs_SNo x = x.
aby If_i_1.
Qed.

Theorem not_nonneg_abs_SNo : forall x, ~(0 <= x) -> abs_SNo x = - x.
aby If_i_0.
Qed.

Theorem pos_abs_SNo : forall x, 0 < x -> abs_SNo x = x.
aby SNoLtLe nonneg_abs_SNo.
Qed.

Theorem neg_abs_SNo : forall x, SNo x -> x < 0 -> abs_SNo x = - x.
aby SNoLt_irref SNoLtLe_tra SNo_0 not_nonneg_abs_SNo.
Qed.

Theorem SNo_abs_SNo : forall x, SNo x -> SNo (abs_SNo x).
aby SNo_minus_SNo nonneg_abs_SNo not_nonneg_abs_SNo.
Qed.

Theorem abs_SNo_minus: forall x, SNo x -> abs_SNo (- x) = abs_SNo x.
aby SNoLtLe SNoLe_antisym SNoLtLe_or SNo_0 SNo_minus_SNo minus_SNo_Le_contra minus_SNo_invol minus_SNo_Lt_contra2 minus_SNo_0 nonneg_abs_SNo neg_abs_SNo.
Qed.

Theorem abs_SNo_dist_swap: forall x y, SNo x -> SNo y -> abs_SNo (x + - y) = abs_SNo (y + - x).
aby SNo_minus_SNo minus_SNo_invol SNo_add_SNo add_SNo_com minus_add_SNo_distr abs_SNo_minus.
Qed.

End SurrealAbs.

Opaque abs_SNo.

Section SurrealMul.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
(* Parameter mul_SNo "f56bf39b8eea93d7f63da529dedb477ae1ab1255c645c47d8915623f364f2d6b" "48d05483e628cb37379dd5d279684d471d85c642fe63533c3ad520b84b18df9d" *)
Definition mul_SNo : set -> set -> set
  := SNo_rec2
      (fun x y m =>
        SNoCut ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoR y})
               ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoL y})).

Infix * 355 right := mul_SNo.

Theorem mul_SNo_eq : forall x, SNo x -> forall y, SNo y ->
   x * y
      = SNoCut ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoR y})
               ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoL y}).
set F : set -> set -> (set -> set -> set) -> set
  := fun x y m => 
        SNoCut ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoR y})
               ({m (w 0) y + m x (w 1) + - m (w 0) (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {m (z 0) y + m x (z 1) + - m (z 0) (z 1)|z :e SNoR x :*: SNoL y}).
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
  claim L1a: {g (w 0) y + g x (w 1) + - g (w 0) (w 1)|w :e SNoL x :*: SNoL y}
           = {h (w 0) y + h x (w 1) + - h (w 0) (w 1)|w :e SNoL x :*: SNoL y}.
  { apply ReplEq_setprod_ext (SNoL x) (SNoL y) (fun w0 w1 => g w0 y + g x w1 + - g w0 w1) (fun w0 w1 => h w0 y + h x w1 + - h w0 w1).
    aby SNoL_E SNoL_SNoS Hgh2 Hgh1 Hy Hx.
  }
  claim L1b: {g (z 0) y + g x (z 1) + - g (z 0) (z 1)|z :e SNoR x :*: SNoR y}
           = {h (z 0) y + h x (z 1) + - h (z 0) (z 1)|z :e SNoR x :*: SNoR y}.
  { apply ReplEq_setprod_ext (SNoR x) (SNoR y) (fun z0 z1 => g z0 y + g x z1 + - g z0 z1) (fun z0 z1 => h z0 y + h x z1 + - h z0 z1).
    aby SNoR_E SNoR_SNoS Hgh2 Hgh1 Hy Hx.
  }
  claim L1c: {g (w 0) y + g x (w 1) + - g (w 0) (w 1)|w :e SNoL x :*: SNoR y}
           = {h (w 0) y + h x (w 1) + - h (w 0) (w 1)|w :e SNoL x :*: SNoR y}.
  { apply ReplEq_setprod_ext (SNoL x) (SNoR y) (fun w0 w1 => g w0 y + g x w1 + - g w0 w1) (fun w0 w1 => h w0 y + h x w1 + - h w0 w1).
    aby SNoR_E SNoL_SNoS SNoR_SNoS Hgh2 Hgh1 Hy Hx.
  }
  claim L1d: {g (z 0) y + g x (z 1) + - g (z 0) (z 1)|z :e SNoR x :*: SNoL y}
           = {h (z 0) y + h x (z 1) + - h (z 0) (z 1)|z :e SNoR x :*: SNoL y}.
  { aby ReplEq_setprod_ext SNoL_E SNoL_SNoS SNoR_SNoS Hgh2 Hgh1 Hy Hx. }
  aby L1d L1c L1b L1a.
}
exact SNo_rec2_eq F L1.
Qed.

Theorem mul_SNo_eq_2 : forall x y, SNo x -> SNo y ->
  forall p:prop,
    (forall L R,
         (forall u, u :e L ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L)
      -> (forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L)
      -> (forall u, u :e R ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
             -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R)
      -> (forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R)
      -> x * y = SNoCut L R
      -> p)
   -> p.
let x y. assume Hx Hy. let p. assume Hp.
prove p.
set Lxy1 := {(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoL y}.
set Lxy2 := {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoR y}.
set Rxy1 := {(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoR y}.
set Rxy2 := {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoL y}.
apply Hp (Lxy1 :\/: Lxy2) (Rxy1 :\/: Rxy2).
- aby ReplE_impred binunionE ap0_Sigma ap1_Sigma.
- aby ReplI binunionI1 tuple_2_0_eq tuple_2_1_eq tuple_2_setprod.
- aby ReplI binunionI2 tuple_2_0_eq tuple_2_1_eq tuple_2_setprod.
- aby ReplE_impred binunionE ap0_Sigma ap1_Sigma.
- aby ReplI binunionI1 tuple_2_0_eq tuple_2_1_eq tuple_2_setprod.
- aby ReplI binunionI2 tuple_2_0_eq tuple_2_1_eq tuple_2_setprod.
- aby mul_SNo_eq Hx Hy Hp.         
Qed.

Theorem mul_SNo_prop_1 : forall x, SNo x -> forall y, SNo y ->
 forall p:prop,
    (SNo (x * y)
  -> (forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v)
  -> (forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v)
  -> p)
 -> p.
set P : set -> prop
 := fun x =>
 forall y, SNo y ->
 forall p:prop,
    (SNo (x * y)
  -> (forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v)
  -> (forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v)
  -> p)
 -> p.
prove forall x, SNo x -> P x.
apply SNoLev_ind.
let x.
assume Hx: SNo x.
assume IHx: forall w :e SNoS_ (SNoLev x), P w.
set Q : set -> prop
 := fun y =>
 forall p:prop,
    (SNo (x * y)
  -> (forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v)
  -> (forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v)
  -> p)
 -> p.
prove forall y, SNo y -> Q y.
apply SNoLev_ind.
let y.
assume Hy: SNo y.
assume IHy: forall z :e SNoS_ (SNoLev y), Q z.
apply mul_SNo_eq_2 x y Hx Hy.
let L R.
assume HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy.
claim LLx: forall u :e SNoL x, forall v, SNo v -> SNo (u * v).
{ aby SNoL_SNoS IHx Hx. }
claim LRx: forall u :e SNoR x, forall v, SNo v -> SNo (u * v).
{ aby SNoR_SNoS IHx Hx. }
claim LLxy: forall u :e SNoL x, SNo (u * y).
{ aby LLx Hy. }
claim LRxy: forall u :e SNoR x, SNo (u * y).
{ aby LRx Hy. }
claim LxLy: forall v :e SNoL y, SNo (x * v).
{ aby SNoL_SNoS IHy Hy. }
claim LxRy: forall v :e SNoR y, SNo (x * v).
{ aby SNoR_SNoS IHy Hy. }
claim LLR1: SNoCutP L R.
{ prove (forall x :e L, SNo x)
     /\ (forall y :e R, SNo y)
     /\ (forall x :e L, forall y :e R, x < y).
  apply and3I.
  - aby SNoL_E SNoR_E SNo_minus_SNo SNo_add_SNo LxRy LxLy LRxy LLxy LRx LLx HLE Hy.
  - aby SNoL_E SNoR_E SNo_minus_SNo SNo_add_SNo LxRy LxLy LRxy LLxy LRx LLx HRE Hy.
  - let u. assume Hu. let v. assume Hv.
    claim Luvimp: forall u0 v0 :e SNoS_ (SNoLev x), forall u1 v1 :e SNoS_ (SNoLev y),
           forall p:prop,
            (SNo (u0 * y) -> SNo (x * u1) -> SNo (u0 * u1) ->
             SNo (v0 * y) -> SNo (x * v1) -> SNo (v0 * v1) ->
             SNo (u0 * v1) -> SNo (v0 * u1) ->
                 (u = u0 * y + x * u1 + - u0 * u1
               -> v = v0 * y + x * v1 + - v0 * v1
               -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1
               -> u < v)
              -> p)
            -> p.
    { let u0. assume Hu0. let v0. assume Hv0.
      let u1. assume Hu1. let v1. assume Hv1.
      apply SNoS_E2 (SNoLev y) (SNoLev_ordinal y Hy) u1 Hu1.
      assume Hu1a: SNoLev u1 :e SNoLev y.
      assume Hu1b: ordinal (SNoLev u1).
      assume Hu1c: SNo u1.
      assume _.
      apply SNoS_E2 (SNoLev y) (SNoLev_ordinal y Hy) v1 Hv1.
      assume Hv1a: SNoLev v1 :e SNoLev y.
      assume Hv1b: ordinal (SNoLev v1).
      assume Hv1c: SNo v1.
      assume _.
      claim Lu0u1: SNo (u0 * u1).
      { apply IHx u0 Hu0 u1 Hu1c.
        assume IHx0 _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c IHx0.
      }
      claim Lv0v1: SNo (v0 * v1).
      { apply IHx v0 Hv0 v1 Hv1c.
        assume IHx0 _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 IHx0.
      }
      claim Lu0y: SNo (u0 * y).
      { apply IHx u0 Hu0 y Hy. assume H _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 H. }
      claim Lxu1: SNo (x * u1).
      { apply IHy u1 Hu1. assume H _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y H. }
      claim Lv0y: SNo (v0 * y).
      { apply IHx v0 Hv0 y Hy. assume H _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 H. }
      claim Lxv1: SNo (x * v1).
      { apply IHy v1 Hv1. assume H _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y H. }
      claim Lu0v1: SNo (u0 * v1).
      { apply IHx u0 Hu0 v1 Hv1c.
        assume IHx0 _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y Lxv1 IHx0.
      }
      claim Lv0u1: SNo (v0 * u1).
      { apply IHx v0 Hv0 u1 Hu1c.
        assume IHx0 _ _ _ _. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y Lxv1 Lu0v1 IHx0.
      }
      let p. assume Hp.
      apply Hp Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1.
      assume Hue Hve H1.
      prove u < v.
      rewrite Hue. rewrite Hve.
      apply add_SNo_Lt1_cancel
                   (u0 * y + x * u1 + - u0 * u1)
                   (u0 * u1 + v0 * v1)
                   (v0 * y + x * v1 + - v0 * v1)
                   (SNo_add_SNo (u0 * y) (x * u1 + - u0 * u1) Lu0y (SNo_add_SNo (x * u1) (- u0 * u1) Lxu1 (SNo_minus_SNo (u0 * u1) Lu0u1)))
                   (SNo_add_SNo (u0 * u1) (v0 * v1) Lu0u1 Lv0v1)
                   (SNo_add_SNo (v0 * y) (x * v1 + - v0 * v1) Lv0y (SNo_add_SNo (x * v1) (- v0 * v1) Lxv1 (SNo_minus_SNo (v0 * v1) Lv0v1))).
      claim L1: (u0 * y + x * u1 + - u0 * u1) + (u0 * u1 + v0 * v1)
               = u0 * y + x * u1 + v0 * v1.
      { aby add_SNo_minus_SNo_prop5 Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y Lxv1 Lu0v1 Lv0u1 Hp Hue Hve H1. }
      claim L2: (v0 * y + x * v1 + - v0 * v1) + (u0 * u1 + v0 * v1)
               = v0 * y + x * v1 + u0 * u1.
      { rewrite add_SNo_com (u0 * u1) (v0 * v1) Lu0u1 Lv0v1.
        aby add_SNo_minus_SNo_prop5 Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y Lxv1 Lu0v1 Lv0u1 Hp Hue Hve H1 L1.
      }
      rewrite L1. rewrite L2. aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Hu0 Hv0 Hu1 Hv1 Hu1a Hu1b Hu1c Hv1a Hv1b Hv1c Lu0u1 Lv0v1 Lu0y Lxu1 Lv0y Lxv1 Lu0v1 Lv0u1 Hp Hue Hve H1 L1 L2.
    }
    apply HLE u Hu.
    + let u0. assume Hu0. let u1. assume Hu1 Hue.
      apply SNoL_E x Hx u0 Hu0.
      assume Hu0a: SNo u0.
      assume Hu0b: SNoLev u0 :e SNoLev x.
      assume Hu0c: u0 < x.
      apply SNoL_E y Hy u1 Hu1.
      assume Hu1a: SNo u1.
      assume Hu1b: SNoLev u1 :e SNoLev y.
      assume Hu1c: u1 < y.
      apply HRE v Hv.
      * { let v0. assume Hv0. let v1. assume Hv1 Hve.
          apply SNoL_E x Hx v0 Hv0.
          assume Hv0a: SNo v0.
          assume Hv0b: SNoLev v0 :e SNoLev x.
          assume Hv0c: v0 < x.
          apply SNoR_E y Hy v1 Hv1.
          assume Hv1a: SNo v1.
          assume Hv1b: SNoLev v1 :e SNoLev y.
          assume Hv1c: y < v1.
          apply Luvimp u0 (SNoL_SNoS x Hx u0 Hu0) v0 (SNoL_SNoS x Hx v0 Hv0)
                       u1 (SNoL_SNoS y Hy u1 Hu1) v1 (SNoR_SNoS y Hy v1 Hv1).
          assume Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv.
          apply Luv Hue Hve.
          prove u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          claim Lu1v1lt: u1 < v1.
          { aby SNoLt_tra Hv1c Hv1a Hu1c Hu1a Hy. }
          claim L3: forall z :e SNoL x, x * u1 + z * v1 < z * u1 + x * v1.
          { let z. assume Hz.
            claim Lzu1: SNo (z * u1).
            { aby Hz Hu1a LLx. }
            claim Lzv1: SNo (z * v1).
            { aby Hz Hv1a LLx. }
            apply SNoLt_SNoL_or_SNoR_impred u1 v1 Hu1a Hv1a Lu1v1lt.
            - let w.
              assume Hwv1: w :e SNoL v1.
              assume Hwu1: w :e SNoR u1.
              apply SNoR_E u1 Hu1a w Hwu1.
              assume Hwu1a: SNo w.
              assume Hwu1b: SNoLev w :e SNoLev u1.
              assume Hwu1c: u1 < w.
              claim LwSy: w :e SNoS_ (SNoLev y).
              { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 Hwu1b Hwu1a Hu1b Hy. }
              aby SNoL_SNoS SNoR_SNoS add_SNo_Lt_subprop2 LwSy Hwu1a Hwu1 Hwv1 Lzv1 Lzu1 Hz Lxv1 Lxu1 Hv1 Hu1 LLx IHy Hy.
            - aby SNoR_SNoS add_SNo_com Lzv1 Lzu1 Hz Lxv1 Lxu1 Hv1 IHy Hy.
            - aby SNoL_SNoS Hz Hu1 IHy Hy.
          }
          claim L3u0: x * u1 + u0 * v1 < u0 * u1 + x * v1.
          { aby L3 Hu0. }
          claim L3v0: x * u1 + v0 * v1 < v0 * u1 + x * v1.
          { aby L3 Hv0. }
          claim L3u0imp: u0 * y + v0 * v1 < v0 * y + u0 * v1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { assume H1.
            aby SNo_add_SNo add_SNo_com add_SNo_Lt_subprop3a H1 L3u0 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y.
          }
          claim L3v0imp: u0 * y + v0 * u1 < v0 * y + u0 * u1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { assume H1.
            aby SNo_add_SNo add_SNo_Lt_subprop3b H1 L3v0 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y.
          }
          apply SNoL_or_SNoR_impred v0 u0 Hv0a Hu0a.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com L3u0 Lu0v1 Lxv1 Lu0u1 Lxu1 Lu0y.
          - let z.
            assume Hzu0: z :e SNoL u0.
            assume Hzv0: z :e SNoR v0.
            claim L4: u0 * y + z * v1 < z * y + u0 * v1.
            { aby SNoL_SNoS Hzu0 Hv1 Hu0 Hy IHx Hx. }
            claim L5: z * y + v0 * v1 < v0 * y + z * v1.
            { aby SNoL_SNoS Hzv0 Hv1 Hv0 Hy IHx Hx. }
            claim Lz: z :e SNoL x.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoL_E SNoL_I Hzu0 Hu0c Hu0b Hu0a Hx. }
            aby SNo_add_SNo add_SNo_com add_SNo_Lt_subprop3c Lz L5 L4 L3u0 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hv1a LLxy LLx.
          - aby SNoL_SNoS L3u0imp Hv1 Hu0 Hy IHx Hx.
          - aby SNoL_SNoS L3u0imp Hv1 Hv0 Hy IHx Hx.
          - let z.
            assume Hzu0: z :e SNoR u0.
            assume Hzv0: z :e SNoL v0.
            claim L6: z * y + v0 * u1 < v0 * y + z * u1.
            { aby SNoL_SNoS Hzv0 Hv0 Hu1 Hy IHx Hx. }
            claim L7: u0 * y + z * u1 < z * y + u0 * u1.
            { aby SNoL_SNoS Hzu0 Hu1 Hu0 Hy IHx Hx. }
            claim Lz: z :e SNoL x.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoL_E SNoL_I Hzv0 Hv0c Hv0b Hv0a Hx. }
            aby SNo_add_SNo add_SNo_Lt_subprop3d Lz L7 L6 L3v0 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hu1a LLxy LLx.
          - aby SNoL_SNoS L3v0imp Hu1 Hu0 Hy IHx Hx.
          - aby SNoL_SNoS L3v0imp Hv0 Hu1 Hy IHx Hx.
        }
      * { let v0. assume Hv0. let v1. assume Hv1 Hve.
          apply SNoR_E x Hx v0 Hv0.
          assume Hv0a: SNo v0.
          assume Hv0b: SNoLev v0 :e SNoLev x.
          assume Hv0c: x < v0.
          apply SNoL_E y Hy v1 Hv1.
          assume Hv1a: SNo v1.
          assume Hv1b: SNoLev v1 :e SNoLev y.
          assume Hv1c: v1 < y.
          apply Luvimp u0 (SNoL_SNoS x Hx u0 Hu0) v0 (SNoR_SNoS x Hx v0 Hv0)
                       u1 (SNoL_SNoS y Hy u1 Hu1) v1 (SNoL_SNoS y Hy v1 Hv1).
          assume Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv.
          apply Luv Hue Hve.
          prove u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          claim Lu0v0lt: u0 < v0.
          { aby SNoLt_tra Hv0c Hv0a Hu0c Hu0a Hx. }
          claim L3: forall z :e SNoL y, u0 * y + v0 * z < v0 * y + u0 * z.
          { let z. assume Hz.
            apply SNoL_E y Hy z Hz.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev y.
            assume Hzc: z < y.
            claim Lu0z: SNo (u0 * z).
            { aby Hza Hu0 LLx. }
            claim Lv0z: SNo (v0 * z).
            { aby Hza Hv0 LRx. }
            apply SNoLt_SNoL_or_SNoR_impred u0 v0 Hu0a Hv0a Lu0v0lt.
            - let w.
              assume Hwv0: w :e SNoL v0.
              assume Hwu0: w :e SNoR u0.
              apply SNoR_E u0 Hu0a w Hwu0.
              assume Hwu0a: SNo w.
              assume Hwu0b: SNoLev w :e SNoLev u0.
              assume Hwu0c: u0 < w.
              claim LLevwLevx: SNoLev w :e SNoLev x.
              { aby ordinal_TransSet SNoLev_ordinal Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lu0v0lt Hz Hza Hzb Hzc Lu0z Lv0z Hwv0 Hwu0 Hwu0a Hwu0b Hwu0c. }
              claim LwSx: w :e SNoS_ (SNoLev x).
              { aby SNoS_I2 LLevwLevx Hwu0a Hx. }
              claim Lwz: SNo (w * z).
              { aby LwSx Hza IHx. }
              claim Lwy: SNo (w * y).
              { aby LwSx Hy IHx. }
              aby SNoL_SNoS SNoR_SNoS add_SNo_com add_SNo_Lt_subprop2 Lwy Lwz Hwu0 Hwv0 Lv0z Lu0z Hz Lv0y Lu0y Hv0 Hu0 Hy IHx Hx.
            - aby SNoR_SNoS Hz Hv0 Hy IHx Hx.
            - aby SNoL_SNoS Hz Hu0 Hy IHx Hx.
          }
          claim L3u1: u0 * y + v0 * u1 < v0 * y + u0 * u1.
          { aby L3 Hu1. }
          claim L3v1: u0 * y + v0 * v1 < v0 * y + u0 * v1.
          { aby L3 Hv1. }
          claim L3u1imp: x * u1 + v0 * v1 < v0 * u1 + x * v1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { aby SNo_add_SNo add_SNo_Lt_subprop3b L3u1 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y. }
          claim L3v1imp: x * u1 + u0 * v1 < x * v1 + u0 * u1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { aby SNo_add_SNo add_SNo_Lt_subprop3a L3v1 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y. }
          apply SNoL_or_SNoR_impred v1 u1 Hv1a Hu1a.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com_3_0_1 L3u1 Lv0u1 Lv0y Lu0u1 Lxu1 Lu0y.
          - let z.
            assume Hzu1: z :e SNoL u1.
            assume Hzv1: z :e SNoR v1.
            apply SNoL_E u1 Hu1a z Hzu1.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev u1.
            assume Hzc: z < u1.
            claim Lz: z :e SNoL y.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoL_I Hzc Hzb Hza Hu1c Hu1b Hu1a Hy. }
            claim L4: x * u1 + v0 * z < x * z + v0 * u1.
            { aby SNoL_SNoS add_SNo_com Lz Hzu1 Lv0u1 Hv0 Hu1 LxLy IHy Hy. }
            claim L5: x * z + v0 * v1 < x * v1 + v0 * z.
            { aby SNoL_SNoS add_SNo_com Lz Hzv1 Lv0v1 Hv1 Hv0 LxLy IHy Hy. }
            aby SNo_add_SNo add_SNo_com_3_0_1 add_SNo_Lt_subprop3c L5 L4 Lz Hza L3u1 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hv0 LxLy LRx.
          - aby SNoL_SNoS L3u1imp Hv0 Hu1 IHy Hy.
          - aby SNoL_SNoS add_SNo_com L3u1imp Lv0u1 Lv0v1 Lxv1 Lxu1 Hv1 Hv0 IHy Hy.
          - let z.
            assume Hzu1: z :e SNoR u1.
            assume Hzv1: z :e SNoL v1.
            apply SNoL_E v1 Hv1a z Hzv1.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev v1.
            assume Hzc: z < v1.
            claim Lz: z :e SNoL y.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoL_I Hzc Hzb Hza Hv1c Hv1b Hv1a Hy. }
            claim L6: x * u1 + u0 * z < x * z + u0 * u1.
            { aby SNoL_SNoS add_SNo_com Lz Hzu1 Lu0u1 Hu1 Hu0 LxLy IHy Hy. }
            claim L7: x * z + u0 * v1 < x * v1 + u0 * z.
            { aby SNoL_SNoS add_SNo_com Lz Hzv1 Lu0v1 Hv1 Hu0 LxLy IHy Hy. }
            aby SNo_add_SNo add_SNo_com add_SNo_com_3_0_1 add_SNo_Lt_subprop3d L7 L6 Lz Hza L3v1 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hu0 LxLy LLx.
          - aby SNoL_SNoS add_SNo_com L3v1imp Lxv1 Lu0u1 Hu1 Hu0 IHy Hy.
          - aby SNoL_SNoS add_SNo_com L3v1imp Lu0v1 Lxu1 Hv1 Hu0 IHy Hy.
        }
    + let u0. assume Hu0. let u1. assume Hu1 Hue.
      apply SNoR_E x Hx u0 Hu0.
      assume Hu0a: SNo u0.
      assume Hu0b: SNoLev u0 :e SNoLev x.
      assume Hu0c: x < u0.
      apply SNoR_E y Hy u1 Hu1.
      assume Hu1a: SNo u1.
      assume Hu1b: SNoLev u1 :e SNoLev y.
      assume Hu1c: y < u1.
      apply HRE v Hv.
      * { let v0. assume Hv0. let v1. assume Hv1 Hve.
          apply SNoL_E x Hx v0 Hv0.
          assume Hv0a: SNo v0.
          assume Hv0b: SNoLev v0 :e SNoLev x.
          assume Hv0c: v0 < x.
          apply SNoR_E y Hy v1 Hv1.
          assume Hv1a: SNo v1.
          assume Hv1b: SNoLev v1 :e SNoLev y.
          assume Hv1c: y < v1.
          apply Luvimp u0 (SNoR_SNoS x Hx u0 Hu0) v0 (SNoL_SNoS x Hx v0 Hv0)
                       u1 (SNoR_SNoS y Hy u1 Hu1) v1 (SNoR_SNoS y Hy v1 Hv1).
          assume Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv.
          apply Luv Hue Hve.
          prove u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          claim Lv0u0lt: v0 < u0.
          { aby SNoLt_tra Hv0c Hv0a Hu0c Hu0a Hx. }
          claim L3: forall z :e SNoR y, u0 * y + v0 * z < v0 * y + u0 * z.
          { let z. assume Hz.
            apply SNoR_E y Hy z Hz.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev y.
            assume Hzc: y < z.
            claim Lu0z: SNo (u0 * z).
            { aby Hza Hu0 LRx. }
            claim Lv0z: SNo (v0 * z).
            { aby Hza Hv0 LLx. }
            apply SNoLt_SNoL_or_SNoR_impred v0 u0 Hv0a Hu0a Lv0u0lt.
            - let w.
              assume Hwu0: w :e SNoL u0.
              assume Hwv0: w :e SNoR v0.
              apply SNoL_E u0 Hu0a w Hwu0.
              assume Hwu0a: SNo w.
              assume Hwu0b: SNoLev w :e SNoLev u0.
              assume Hwu0c: w < u0.
              claim LLevwLevx: SNoLev w :e SNoLev x.
              { aby ordinal_TransSet SNoLev_ordinal Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lv0u0lt Hz Hza Hzb Hzc Lu0z Lv0z Hwu0 Hwv0 Hwu0a Hwu0b Hwu0c. }
              aby SNoS_I2 SNoL_SNoS SNoR_SNoS add_SNo_com add_SNo_Lt_subprop2 LLevwLevx Hwu0a Hwv0 Hwu0 Lv0z Lu0z Hza Hz Lv0y Lu0y Hv0 Hu0 Hy IHx Hx.
            - aby SNoR_SNoS Hz Hu0 Hy IHx Hx.
            - aby SNoL_SNoS Hz Hv0 Hy IHx Hx.
          }
          claim L3u1: u0 * y + v0 * u1 < v0 * y + u0 * u1.
          { aby L3 Hu1. }
          claim L3v1: u0 * y + v0 * v1 < v0 * y + u0 * v1.
          { aby L3 Hv1. }
          claim L3u1imp: x * u1 + v0 * v1 < v0 * u1 + x * v1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { aby SNo_add_SNo add_SNo_Lt_subprop3b L3u1 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y. }
          claim L3v1imp: x * u1 + u0 * v1 < x * v1 + u0 * u1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { aby SNo_add_SNo add_SNo_Lt_subprop3a L3v1 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y. }
          apply SNoL_or_SNoR_impred v1 u1 Hv1a Hu1a.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com_3_0_1 L3u1 Lv0u1 Lv0y Lu0u1 Lxu1 Lu0y.
          - let z.
            assume Hzu1: z :e SNoL u1.
            assume Hzv1: z :e SNoR v1.
            apply SNoR_E v1 Hv1a z Hzv1.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev v1.
            assume Hzc: v1 < z.
            claim Lz: z :e SNoR y.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoR_I Hzc Hzb Hza Hv1c Hv1b Hv1a Hy. }
            claim L4: x * u1 + u0 * z < x * z + u0 * u1.
            { aby SNoR_SNoS add_SNo_com Lz Hzu1 Lu0u1 Hu1 Hu0 LxRy IHy Hy. }
            claim L5: x * z + u0 * v1 < x * v1 + u0 * z.
            { aby SNoR_SNoS add_SNo_com Lz Hzv1 Lu0v1 Hv1 Hu0 LxRy IHy Hy. }
            aby SNo_add_SNo add_SNo_com add_SNo_com_3_0_1 add_SNo_Lt_subprop3d L5 L4 Lz Hza L3v1 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hu0 LxRy LRx.
          - aby SNoR_SNoS add_SNo_com L3v1imp Lxv1 Lu0u1 Hu1 Hu0 IHy Hy.
          - aby SNoR_SNoS add_SNo_com L3v1imp Lu0v1 Lxu1 Hv1 Hu0 IHy Hy.
          - let z.
            assume Hzu1: z :e SNoR u1.
            assume Hzv1: z :e SNoL v1.
            apply SNoR_E u1 Hu1a z Hzu1.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev u1.
            assume Hzc: u1 < z.
            claim Lz: z :e SNoR y.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoR_I Hzc Hzb Hza Hu1c Hu1b Hu1a Hy. }
            claim L6: x * u1 + v0 * z < x * z + v0 * u1.
            { aby SNoR_SNoS add_SNo_com Lz Hzu1 Lv0u1 Hv0 Hu1 LxRy IHy Hy. }
            claim L7: x * z + v0 * v1 < x * v1 + v0 * z.
            { aby SNoR_SNoS add_SNo_com Lz Hzv1 Lv0v1 Hv1 Hv0 LxRy IHy Hy. }
            aby SNo_add_SNo add_SNo_com_3_0_1 add_SNo_Lt_subprop3c L7 L6 Lz Hza L3u1 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hv0 LxRy LLx.
          - aby SNoR_SNoS L3u1imp Hv0 Hu1 IHy Hy.
          - aby SNoR_SNoS add_SNo_com L3u1imp Lv0u1 Lv0v1 Lxv1 Lxu1 Hv1 Hv0 IHy Hy.
        }
      * { let v0. assume Hv0. let v1. assume Hv1 Hve.
          apply SNoR_E x Hx v0 Hv0.
          assume Hv0a: SNo v0.
          assume Hv0b: SNoLev v0 :e SNoLev x.
          assume Hv0c: x < v0.
          apply SNoL_E y Hy v1 Hv1.
          assume Hv1a: SNo v1.
          assume Hv1b: SNoLev v1 :e SNoLev y.
          assume Hv1c: v1 < y.
          apply Luvimp u0 (SNoR_SNoS x Hx u0 Hu0) v0 (SNoR_SNoS x Hx v0 Hv0)
                       u1 (SNoR_SNoS y Hy u1 Hu1) v1 (SNoL_SNoS y Hy v1 Hv1).
          assume Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv.
          apply Luv Hue Hve.
          prove u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          claim Lv1u1lt: v1 < u1.
          { aby SNoLt_tra Hv1c Hv1a Hu1c Hu1a Hy. }
          claim L3: forall z :e SNoR x, x * u1 + z * v1 < z * u1 + x * v1.
          { let z. assume Hz.
            claim Lzu1: SNo (z * u1).
            { aby Hz Hu1a LRx. }
            claim Lzv1: SNo (z * v1).
            { aby Hz Hv1a LRx. }
            apply SNoLt_SNoL_or_SNoR_impred v1 u1 Hv1a Hu1a Lv1u1lt.
            - let w.
              assume Hwu1: w :e SNoL u1.
              assume Hwv1: w :e SNoR v1.
              apply SNoL_E u1 Hu1a w Hwu1.
              assume Hwu1a: SNo w.
              assume Hwu1b: SNoLev w :e SNoLev u1.
              assume Hwu1c: w < u1.
              claim LwSy: w :e SNoS_ (SNoLev y).
              { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 Hwu1b Hwu1a Hu1b Hy. }
              aby SNoL_SNoS SNoR_SNoS add_SNo_Lt_subprop2 LwSy Hwu1a Hwv1 Hwu1 Lzv1 Lzu1 Hz Lxv1 Lxu1 Hv1 Hu1 LRx IHy Hy.
            - aby SNoR_SNoS Hz Hu1 IHy Hy.
            - aby SNoL_SNoS add_SNo_com Lzv1 Lzu1 Hz Lxv1 Lxu1 Hv1 IHy Hy.
          }
          claim L3u0: x * u1 + u0 * v1 < u0 * u1 + x * v1.
          { aby L3 Hu0. }
          claim L3v0: x * u1 + v0 * v1 < v0 * u1 + x * v1.
          { aby L3 Hv0. }
          claim L3u0imp: u0 * y + v0 * v1 < v0 * y + u0 * v1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { assume H1.
            aby SNo_add_SNo add_SNo_com add_SNo_Lt_subprop3a H1 L3u0 Lu0v1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y.
          }
          claim L3v0imp: u0 * y + v0 * u1 < v0 * y + u0 * u1 -> u0 * y + x * u1 + v0 * v1 < v0 * y + x * v1 + u0 * u1.
          { assume H1.
            aby SNo_add_SNo add_SNo_Lt_subprop3b H1 L3v0 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y.
          }
          apply SNoL_or_SNoR_impred v0 u0 Hv0a Hu0a.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com L3u0 Lu0v1 Lxv1 Lu0u1 Lxu1 Lu0y.
          - let z.
            assume Hzu0: z :e SNoL u0.
            assume Hzv0: z :e SNoR v0.
            apply SNoR_E v0 Hv0a z Hzv0.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev v0.
            assume Hzc: v0 < z.
            claim Lz: z :e SNoR x.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoR_I Hzc Hzb Hza Hv0c Hv0b Hv0a Hx. }
            aby SNoR_SNoS SNo_add_SNo add_SNo_Lt_subprop3d Lz Hzv0 Hzu0 L3v0 Lv0u1 Lv0v1 Lxv1 Lv0y Lu0u1 Lxu1 Lu0y Hv0 Hu1a Hu1 Hu0 LRxy LRx Hy IHx Hx.
          - aby SNoR_SNoS L3v0imp Hu1 Hu0 Hy IHx Hx.
          - aby SNoR_SNoS L3v0imp Hv0 Hu1 Hy IHx Hx.
          - let z.
            assume Hzu0: z :e SNoR u0.
            assume Hzv0: z :e SNoL v0.
            apply SNoR_E u0 Hu0a z Hzu0.
            assume Hza: SNo z.
            assume Hzb: SNoLev z :e SNoLev u0.
            assume Hzc: u0 < z.
            claim Lz: z :e SNoR x.
            { aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoR_I Hzc Hzb Hza Hu0c Hu0b Hu0a Hx. }
            claim L6: u0 * y + z * v1 < z * y + u0 * v1.
            { apply IHx u0 (SNoR_SNoS x Hx u0 Hu0) y Hy.
              assume _ _ _ _ IHx4.
              aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lv1u1lt L3 L3u0 L3v0 L3u0imp L3v0imp Hzu0 Hzv0 Hza Hzb Hzc Lz IHx4.
            }
            claim L7: z * y + v0 * v1 < v0 * y + z * v1.
            { apply IHx v0 (SNoR_SNoS x Hx v0 Hv0) y Hy.
              assume _ IHx1 _ _ _.
              aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lv1u1lt L3 L3u0 L3v0 L3u0imp L3v0imp Hzu0 Hzv0 Hza Hzb Hzc Lz L6 IHx1.
            }
            apply add_SNo_Lt_subprop3c (u0 * y) (x * u1) (v0 * v1) (v0 * y) (x * v1 + u0 * u1) (z * v1) (z * y) (u0 * v1)
                       Lu0y Lxu1 Lv0v1 Lv0y
                       (SNo_add_SNo (x * v1) (u0 * u1) Lxv1 Lu0u1)
                       (LRx z Lz v1 Hv1a) (LRxy z Lz)
                       Lu0v1 L6.
            + prove x * u1 + u0 * v1 < x * v1 + u0 * u1.
              rewrite add_SNo_com (x * v1) (u0 * u1) Lxv1 Lu0u1.
              aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lv1u1lt L3 L3u0 L3v0 L3u0imp L3v0imp Hzu0 Hzv0 Hza Hzb Hzc Lz L6 L7.
            + prove z * y + v0 * v1 < v0 * y + z * v1.
              aby Hx IHx Hy IHy HLE HLI1 HLI2 HRE HRI1 HRI2 Hxy LLx LRx LLxy LRxy LxLy LxRy Hu Hv Luvimp Hu0 Hu1 Hue Hu0a Hu0b Hu0c Hu1a Hu1b Hu1c Hv0 Hv1 Hve Hv0a Hv0b Hv0c Hv1a Hv1b Hv1c Lu0y Lxu1 Lu0u1 Lv0y Lxv1 Lv0v1 Lu0v1 Lv0u1 Luv Lv1u1lt L3 L3u0 L3v0 L3u0imp L3v0imp Hzu0 Hzv0 Hza Hzb Hzc Lz L6 L7.
          - aby SNoR_SNoS L3u0imp Hv1 Hu0 Hy IHx Hx.
          - aby SNoR_SNoS L3u0imp Hv1 Hv0 Hy IHx Hx.
        }
}
claim Lxy: SNo (x * y).
{ aby SNoCutP_SNo_SNoCut LLR1 Hxy. }
let p. assume Hp. prove p. apply Hp.
- aby Lxy.
- aby SNoL_E SNoCutP_SNoCut_L SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt1 Lxy LLR1 LxLy LLx Hxy HLI1 Hy.
- aby SNoR_E SNoCutP_SNoCut_L SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt1 Lxy LLR1 LxRy LRx Hxy HLI2 Hy.
- aby SNoR_E SNoCutP_SNoCut_R SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt2 Lxy LLR1 LxRy LLx Hxy HRI1 Hy.
- aby SNoL_E SNoCutP_SNoCut_R SNo_minus_SNo SNo_add_SNo add_SNo_assoc add_SNo_minus_Lt2 Lxy LLR1 LxLy LRx Hxy HRI2 Hy.
Qed.

Theorem SNo_mul_SNo : forall x y, SNo x -> SNo y -> SNo (x * y).
aby mul_SNo_prop_1.
Qed.

Theorem SNo_mul_SNo_lem : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v -> SNo (u * y + x * v + - (u * v)).
aby SNo_add_SNo_3c SNo_mul_SNo.
Qed.

Theorem SNo_mul_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x * y * z).
aby SNo_mul_SNo.
Qed.

Theorem mul_SNo_eq_3 : forall x y, SNo x -> SNo y ->
  forall p:prop,
    (forall L R, SNoCutP L R
       -> (forall u, u :e L ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L)
      -> (forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L)
      -> (forall u, u :e R ->
           (forall q:prop,
                (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
             -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
             -> q))
      -> (forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R)
      -> (forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R)
      -> x * y = SNoCut L R
      -> p)
   -> p.
let x y. assume Hx Hy. let p. assume Hp.
apply mul_SNo_eq_2 x y Hx Hy.
let L R.
assume HLE HLI1 HLI2 HRE HRI1 HRI2 He.
apply mul_SNo_prop_1 x Hx y Hy.
assume Hxy: SNo (x * y).
assume Hxy1: forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v.
assume Hxy2: forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v.
assume Hxy3: forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v.
assume Hxy4: forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v.
claim LLR: SNoCutP L R.
{ prove (forall w :e L, SNo w)
     /\ (forall z :e R, SNo z)
     /\ (forall w :e L, forall z :e R, w < z).
  apply and3I.
  - aby SNoL_E SNoR_E SNo_mul_SNo_lem HLE Hy Hx.
  - aby SNoL_E SNoR_E SNo_mul_SNo_lem HRE Hy Hx.
  - let w. assume Hw. let z. assume Hz. prove w < z.
    apply HLE w Hw.
    + let u. assume Hu. let v. assume Hv Hwe.
      apply SNoL_E x Hx u Hu.
      assume Hua: SNo u. assume _ _.
      apply SNoL_E y Hy v Hv.
      assume Hva: SNo v. assume _ _.
      claim Luy: SNo (u * y).
      { aby SNo_mul_SNo Hua Hy. }
      claim Lxv: SNo (x * v).
      { aby SNo_mul_SNo Hva Hx. }
      claim Luv: SNo (u * v).
      { aby SNo_mul_SNo Hva Hua. }
      apply HRE z Hz.
      * aby SNoLt_tra SNoL_E SNoR_E SNo_add_SNo_3 add_SNo_com add_SNo_minus_Lt_lem add_SNo_3_3_3_Lt1 add_SNo_3_2_3_Lt1 add_SNo_minus_Lt12b3 SNo_mul_SNo Luv Lxv Luy Hwe Hv Hu Hxy3 Hxy1 Hxy Hy Hx.
      * aby SNoLt_tra SNoL_E SNoR_E SNo_add_SNo_3 add_SNo_com add_SNo_minus_Lt_lem add_SNo_3_3_3_Lt1 add_SNo_3_2_3_Lt1 add_SNo_minus_Lt12b3 SNo_mul_SNo Luv Lxv Luy Hwe Hv Hu Hxy4 Hxy1 Hxy Hy Hx.
    + let u. assume Hu. let v. assume Hv Hwe.
      apply SNoR_E x Hx u Hu.
      assume Hua: SNo u. assume _ _.
      apply SNoR_E y Hy v Hv.
      assume Hva: SNo v. assume _ _.
      claim Luy: SNo (u * y).
      { aby SNo_mul_SNo Hua Hy. }
      claim Lxv: SNo (x * v).
      { aby SNo_mul_SNo Hva Hx. }
      claim Luv: SNo (u * v).
      { aby SNo_mul_SNo Hva Hua. }
      apply HRE z Hz.
      * aby SNoLt_tra SNoL_E SNoR_E SNo_add_SNo_3 add_SNo_com add_SNo_minus_Lt_lem add_SNo_3_3_3_Lt1 add_SNo_3_2_3_Lt1 add_SNo_minus_Lt12b3 SNo_mul_SNo Luv Lxv Luy Hwe Hv Hu Hxy3 Hxy2 Hxy Hy Hx.
      * aby SNoLt_tra SNoL_E SNoR_E SNo_add_SNo_3 add_SNo_com add_SNo_minus_Lt_lem add_SNo_3_3_3_Lt1 add_SNo_3_2_3_Lt1 add_SNo_minus_Lt12b3 SNo_mul_SNo Luv Lxv Luy Hwe Hv Hu Hxy4 Hxy2 Hxy Hy Hx.
}
aby Hx Hy Hp HLE HLI1 HLI2 HRE HRI1 HRI2 He Hxy Hxy1 Hxy2 Hxy3 Hxy4 LLR.
Qed.

Theorem mul_SNo_Lt : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u < x -> v < y -> u * y + x * v < x * y + u * v.
let x y u v. assume Hx Hy Hu Hv Hux Hvy.
apply mul_SNo_prop_1 x Hx y Hy.
assume Hxy: SNo (x * y).
assume Hxy1: forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v.
assume Hxy2: forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v.
assume Hxy3: forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v.
assume Hxy4: forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v.
apply mul_SNo_prop_1 u Hu y Hy.
assume Huy: SNo (u * y).
assume Huy1: forall x :e SNoL u, forall v :e SNoL y, x * y + u * v < u * y + x * v.
assume Huy2: forall x :e SNoR u, forall v :e SNoR y, x * y + u * v < u * y + x * v.
assume Huy3: forall x :e SNoL u, forall v :e SNoR y, u * y + x * v < x * y + u * v.
assume Huy4: forall x :e SNoR u, forall v :e SNoL y, u * y + x * v < x * y + u * v.
apply mul_SNo_prop_1 x Hx v Hv.
assume Hxv: SNo (x * v).
assume Hxv1: forall u :e SNoL x, forall y :e SNoL v, u * v + x * y < x * v + u * y.
assume Hxv2: forall u :e SNoR x, forall y :e SNoR v, u * v + x * y < x * v + u * y.
assume Hxv3: forall u :e SNoL x, forall y :e SNoR v, x * v + u * y < u * v + x * y.
assume Hxv4: forall u :e SNoR x, forall y :e SNoL v, x * v + u * y < u * v + x * y.
apply mul_SNo_prop_1 u Hu v Hv.
assume Huv: SNo (u * v).
assume Huv1: forall x :e SNoL u, forall y :e SNoL v, x * v + u * y < u * v + x * y.
assume Huv2: forall x :e SNoR u, forall y :e SNoR v, x * v + u * y < u * v + x * y.
assume Huv3: forall x :e SNoL u, forall y :e SNoR v, u * v + x * y < x * v + u * y.
assume Huv4: forall x :e SNoR u, forall y :e SNoL v, u * v + x * y < x * v + u * y.
claim Luyxv: SNo (u * y + x * v).
{ aby SNo_add_SNo Hxv Huy. }
claim Lxyuv: SNo (x * y + u * v).
{ aby SNo_add_SNo Huv Hxy. }
apply SNoLtE u x Hu Hx Hux.
- let w.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev u :/\: SNoLev x.
  assume Hw3: SNoEq_ (SNoLev w) w u.
  assume Hw4: SNoEq_ (SNoLev w) w x.
  assume Hw5: u < w.
  assume Hw6: w < x.
  assume Hw7: SNoLev w /:e u.
  assume Hw8: SNoLev w :e x.
  apply binintersectE (SNoLev u) (SNoLev x) (SNoLev w) Hw2.
  assume Hw2a Hw2b.
  claim Lwx: w :e SNoL x.
  { aby SNoL_I Hw2b Hw6 Hw1 Hx. }
  claim Lwu: w :e SNoR u.
  { aby SNoR_I Hw2a Hw5 Hw1 Hu. }
  claim Lwy: SNo (w * y).
  { aby SNo_mul_SNo Hw1 Hy. }
  claim Lwv: SNo (w * v).
  { aby SNo_mul_SNo Hw1 Hv. }
  claim Lwyxv: SNo (w * y + x * v).
  { aby SNo_add_SNo Lwy Hxv. }
  claim Lwyuv: SNo (w * y + u * v).
  { aby SNo_add_SNo Lwy Huv. }
  claim Lxywv: SNo (x * y + w * v).
  { aby SNo_add_SNo Lwv Hxy. }
  claim Luywv: SNo (u * y + w * v).
  { aby SNo_add_SNo Lwv Huy. }
  claim Luvwy: SNo (u * v + w * y).
  { aby SNo_add_SNo Lwy Huv. }
  claim Lwvxy: SNo (w * v + x * y).
  { aby SNo_add_SNo Lwv Hxy. }
  claim Lxvwy: SNo (x * v + w * y).
  { aby SNo_add_SNo Lwy Hxv. }
  claim Lwvuy: SNo (w * v + u * y).
  { aby SNo_add_SNo Lwv Huy. }
  apply SNoLtE v y Hv Hy Hvy.
  + let z.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev v :/\: SNoLev y.
    assume Hz3: SNoEq_ (SNoLev z) z v.
    assume Hz4: SNoEq_ (SNoLev z) z y.
    assume Hz5: v < z.
    assume Hz6: z < y.
    assume Hz7: SNoLev z /:e v.
    assume Hz8: SNoLev z :e y.
    apply binintersectE (SNoLev v) (SNoLev y) (SNoLev z) Hz2.
    assume Hz2a Hz2b.
    claim Lzy: z :e SNoL y.
    { aby SNoL_I Hz2b Hz6 Hz1 Hy. }
    claim Lzv: z :e SNoR v.
    { aby SNoR_I Hz2a Hz5 Hz1 Hv. }
    claim Lxz: SNo (x * z).
    { aby SNo_mul_SNo Hz1 Hx. }
    claim Luz: SNo (u * z).
    { aby SNo_mul_SNo Hz1 Hu. }
    claim Lwz: SNo (w * z).
    { aby SNo_mul_SNo Hz1 Hw1. }
    claim L1: w * y + x * z < x * y + w * z.
    { aby Lzy Lwx Hxy1. }
    claim L2: w * v + u * z < u * v + w * z.
    { aby Lzv Lwu Huv2. }
    claim L3: x * v + w * z < w * v + x * z.
    { aby Lzv Lwx Hxv3. }
    claim L4: u * y + w * z < w * y + u * z.
    { aby Lzy Lwu Huy4. }
    claim Lwzwz: SNo (w * z + w * z).
    { aby SNo_add_SNo Lwz. }
    apply add_SNo_Lt1_cancel (u * y + x * v) (w * z + w * z) (x * y + u * v) Luyxv Lwzwz Lxyuv.
    prove (u * y + x * v) + (w * z + w * z) < (x * y + u * v) + (w * z + w * z).
    claim Lwyuz: SNo (w * y + u * z).
    { aby SNo_add_SNo Luz Lwy. }
    claim Lwvxz: SNo (w * v + x * z).
    { aby SNo_add_SNo Lxz Lwv. }
    claim Luywz: SNo (u * y + w * z).
    { aby SNo_add_SNo Lwz Huy. }
    claim Lxvwz: SNo (x * v + w * z).
    { aby SNo_add_SNo Lwz Hxv. }
    claim Lwvuz: SNo (w * v + u * z).
    { aby SNo_add_SNo Luz Lwv. }
    claim Lxyxz: SNo (x * y + x * z).
    { aby SNo_add_SNo Lxz Hxy. }
    claim Lwyxz: SNo (w * y + x * z).
    { aby SNo_add_SNo Lxz Lwy. }
    claim Lxywz: SNo (x * y + w * z).
    { aby SNo_add_SNo Lwz Hxy. }
    claim Luvwz: SNo (u * v + w * z).
    { aby SNo_add_SNo Lwz Huv. }
    apply SNoLt_tra ((u * y + x * v) + (w * z + w * z))
                    ((w * y + u * z) + (w * v + x * z))
                    ((x * y + u * v) + (w * z + w * z))
                    (SNo_add_SNo (u * y + x * v) (w * z + w * z) Luyxv Lwzwz)
                    (SNo_add_SNo (w * y + u * z) (w * v + x * z) Lwyuz Lwvxz)
                    (SNo_add_SNo (x * y + u * v) (w * z + w * z) Lxyuv Lwzwz).
    * aby add_SNo_Lt3 add_SNo_com_4_inner_mid Lxvwz Luywz Lwvxz Lwyuz L4 L3 Lwz Hxv Huy.
    * aby add_SNo_Lt3 add_SNo_com add_SNo_com_4_inner_mid Luvwz Lxywz Lwyxz Lwvuz L2 L1 Lwz Luz Lxz Lwv Lwy Huv Hxy.
  + assume H4: SNoLev v :e SNoLev y.
    assume H5: SNoEq_ (SNoLev v) v y.
    assume H6: SNoLev v :e y.
    claim Lvy: v :e SNoL y.
    { aby SNoL_I H4 Hvy Hv Hy. }
    claim L1: w * y + x * v < x * y + w * v.
    { aby Lvy Lwx Hxy1. }
    claim L2: u * y + w * v < w * y + u * v.
    { aby Lvy Lwu Huy4. }
    prove u * y + x * v < x * y + u * v.
    apply add_SNo_Lt2_cancel (w * y) (u * y + x * v) (x * y + u * v) Lwy Luyxv Lxyuv.
    prove w * y + u * y + x * v < w * y + x * y + u * v.
    apply SNoLt_tra (w * y + u * y + x * v) (u * y + w * v + x * y) (w * y + x * y + u * v)
                    (SNo_add_SNo (w * y) (u * y + x * v) Lwy Luyxv)
                    (SNo_add_SNo (u * y) (w * v + x * y) Huy (SNo_add_SNo (w * v) (x * y) Lwv Hxy))
                    (SNo_add_SNo (w * y) (x * y + u * v) Lwy Lxyuv).
    * aby add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 L1 Lxywv Lwyxv Lwv Lwy Hxv Huy Hxy.
    * aby add_SNo_Lt1 add_SNo_com add_SNo_assoc L2 Luywv Lwyuv Lwv Lwy Huv Huy Hxy.
  + assume H4: SNoLev y :e SNoLev v.
    assume H5: SNoEq_ (SNoLev y) v y.
    assume H6: SNoLev y /:e v.
    claim Lyv: y :e SNoR v.
    { aby SNoR_I H4 Hvy Hv Hy. }
    claim L1: x * v + w * y < w * v + x * y.
    { aby Lyv Lwx Hxv3. }
    claim L2: w * v + u * y < u * v + w * y.
    { aby Lyv Lwu Huv2. }
    prove u * y + x * v < x * y + u * v.
    apply add_SNo_Lt2_cancel (w * y) (u * y + x * v) (x * y + u * v) Lwy Luyxv Lxyuv.
    prove w * y + u * y + x * v < w * y + x * y + u * v.
    apply SNoLt_tra (w * y + u * y + x * v) (u * y + w * v + x * y) (w * y + x * y + u * v)
                    (SNo_add_SNo (w * y) (u * y + x * v) Lwy Luyxv)
                    (SNo_add_SNo (u * y) (w * v + x * y) Huy (SNo_add_SNo (w * v) (x * y) Lwv Hxy))
                    (SNo_add_SNo (w * y) (x * y + u * v) Lwy Lxyuv).
    * aby add_SNo_Lt2 add_SNo_rotate_3_1 L1 Lxvwy Lwvxy Lwy Hxv Huy.
    * aby add_SNo_Lt1 add_SNo_com add_SNo_assoc add_SNo_rotate_3_1 L2 Lwvuy Luvwy Lwv Lwy Huv Huy Hxy.
- assume H1: SNoLev u :e SNoLev x.
  assume H2: SNoEq_ (SNoLev u) u x.
  assume H3: SNoLev u :e x.
  claim Lux: u :e SNoL x.
  { aby SNoL_I H1 Hux Hu Hx. }
  apply SNoLtE v y Hv Hy Hvy.
  + let z.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev v :/\: SNoLev y.
    assume Hz3: SNoEq_ (SNoLev z) z v.
    assume Hz4: SNoEq_ (SNoLev z) z y.
    assume Hz5: v < z.
    assume Hz6: z < y.
    assume Hz7: SNoLev z /:e v.
    assume Hz8: SNoLev z :e y.
    apply binintersectE (SNoLev v) (SNoLev y) (SNoLev z) Hz2.
    assume Hz2a Hz2b.
    claim Lzy: z :e SNoL y.
    { aby SNoL_I Hz2b Hz6 Hz1 Hy. }
    claim Lzv: z :e SNoR v.
    { aby SNoR_I Hz2a Hz5 Hz1 Hv. }
    claim Lxz: SNo (x * z).
    { aby SNo_mul_SNo Hz1 Hx. }
    claim Luz: SNo (u * z).
    { aby SNo_mul_SNo Hz1 Hu. }
    claim Luyxz: SNo (u * y + x * z).
    { aby SNo_add_SNo Lxz Huy. }
    claim Luvxz: SNo (u * v + x * z).
    { aby SNo_add_SNo Lxz Huv. }
    claim Lxyuz: SNo (x * y + u * z).
    { aby SNo_add_SNo Luz Hxy. }
    claim Lxvuz: SNo (x * v + u * z).
    { aby SNo_add_SNo Luz Hxv. }
    claim L1: u * y + x * z < x * y + u * z.
    { aby Lzy Lux Hxy1. }
    claim L2: x * v + u * z < u * v + x * z.
    { aby Lzv Lux Hxv3. }
    prove u * y + x * v < x * y + u * v.
    apply add_SNo_Lt2_cancel (x * z) (u * y + x * v) (x * y + u * v) Lxz Luyxv Lxyuv.
    prove x * z + u * y + x * v < x * z + x * y + u * v.
    apply SNoLt_tra (x * z + u * y + x * v) (x * y + u * z + x * v) (x * z + x * y + u * v)
                    (SNo_add_SNo (x * z) (u * y + x * v) Lxz Luyxv)
                    (SNo_add_SNo (x * y) (u * z + x * v) Hxy (SNo_add_SNo (u * z) (x * v) Luz Hxv))
                    (SNo_add_SNo (x * z) (x * y + u * v) Lxz Lxyuv).
    * aby add_SNo_Lt1 add_SNo_com add_SNo_assoc L1 Lxyuz Luyxz Luz Lxz Hxv Huy Hxy.
    * aby add_SNo_Lt2 add_SNo_com add_SNo_rotate_3_1 L2 Lxvuz Luvxz Luz Lxz Huv Hxv Hxy.
  + aby SNoL_I Lux Hxy1 Hvy Hv Hy.
  + aby SNoR_I add_SNo_com Lux Huv Hxv3 Hxv Huy Hxy Hvy Hv Hy.
- assume H1: SNoLev x :e SNoLev u.
  assume H2: SNoEq_ (SNoLev x) u x.
  assume H3: SNoLev x /:e u.
  claim Lxu: x :e SNoR u.
  { aby SNoR_I H1 Hux Hu Hx. }
  apply SNoLtE v y Hv Hy Hvy.
  + let z.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev v :/\: SNoLev y.
    assume Hz3: SNoEq_ (SNoLev z) z v.
    assume Hz4: SNoEq_ (SNoLev z) z y.
    assume Hz5: v < z.
    assume Hz6: z < y.
    assume Hz7: SNoLev z /:e v.
    assume Hz8: SNoLev z :e y.
    apply binintersectE (SNoLev v) (SNoLev y) (SNoLev z) Hz2.
    assume Hz2a Hz2b.
    claim Lzy: z :e SNoL y.
    { aby SNoL_I Hz2b Hz6 Hz1 Hy. }
    claim Lzv: z :e SNoR v.
    { aby SNoR_I Hz2a Hz5 Hz1 Hv. }
    claim Lxz: SNo (x * z).
    { aby SNo_mul_SNo Hz1 Hx. }
    claim Luz: SNo (u * z).
    { aby SNo_mul_SNo Hz1 Hu. }
    claim L1: u * y + x * z < x * y + u * z.
    { aby Lzy Lxu Huy4. }
    claim L2: x * v + u * z < u * v + x * z.
    { aby Lzv Lxu Huv2. }
    prove u * y + x * v < x * y + u * v.
    apply add_SNo_Lt1_cancel (u * y + x * v) (x * z) (x * y + u * v) Luyxv Lxz Lxyuv.
    prove (u * y + x * v) + x * z < (x * y + u * v) + x * z.
    rewrite add_SNo_com (u * y) (x * v) Huy Hxv.
    prove (x * v + u * y) + x * z < (x * y + u * v) + x * z.
    rewrite <- add_SNo_assoc (x * v) (u * y) (x * z) Hxv Huy Lxz.
    rewrite <- add_SNo_assoc (x * y) (u * v) (x * z) Hxy Huv Lxz.
    prove x * v + u * y + x * z < x * y + u * v + x * z.
    claim Luyxz: SNo (u * y + x * z).
    { aby SNo_add_SNo Hx Hy Hu Hv Hux Hvy Hxy Hxy1 Hxy2 Hxy3 Hxy4 Huy Huy1 Huy2 Huy3 Huy4 Hxv Hxv1 Hxv2 Hxv3 Hxv4 Huv Huv1 Huv2 Huv3 Huv4 Luyxv Lxyuv H1 H2 H3 Lxu Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 Hz7 Hz8 Hz2a Hz2b Lzy Lzv Lxz Luz L1 L2. }
    claim Luzxy: SNo (u * z + x * y).
    { aby SNo_add_SNo Hx Hy Hu Hv Hux Hvy Hxy Hxy1 Hxy2 Hxy3 Hxy4 Huy Huy1 Huy2 Huy3 Huy4 Hxv Hxv1 Hxv2 Hxv3 Hxv4 Huv Huv1 Huv2 Huv3 Huv4 Luyxv Lxyuv H1 H2 H3 Lxu Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 Hz7 Hz8 Hz2a Hz2b Lzy Lzv Lxz Luz L1 L2 Luyxz. }
    claim Luvxz: SNo (u * v + x * z).
    { aby SNo_add_SNo Hx Hy Hu Hv Hux Hvy Hxy Hxy1 Hxy2 Hxy3 Hxy4 Huy Huy1 Huy2 Huy3 Huy4 Hxv Hxv1 Hxv2 Hxv3 Hxv4 Huv Huv1 Huv2 Huv3 Huv4 Luyxv Lxyuv H1 H2 H3 Lxu Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 Hz7 Hz8 Hz2a Hz2b Lzy Lzv Lxz Luz L1 L2 Luyxz Luzxy. }
    apply SNoLt_tra (x * v + u * y + x * z)
                    (x * v + u * z + x * y)
                    (x * y + u * v + x * z)
                    (SNo_add_SNo (x * v) (u * y + x * z) Hxv Luyxz)
                    (SNo_add_SNo (x * v) (u * z + x * y) Hxv Luzxy)
                    (SNo_add_SNo (x * y) (u * v + x * z) Hxy Luvxz).
    * prove x * v + u * y + x * z < x * v + u * z + x * y.
      rewrite add_SNo_com (u * z) (x * y) Luz Hxy.
      aby SNo_add_SNo add_SNo_Lt2 Hx Hy Hu Hv Hux Hvy Hxy Hxy1 Hxy2 Hxy3 Hxy4 Huy Huy1 Huy2 Huy3 Huy4 Hxv Hxv1 Hxv2 Hxv3 Hxv4 Huv Huv1 Huv2 Huv3 Huv4 Luyxv Lxyuv H1 H2 H3 Lxu Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 Hz7 Hz8 Hz2a Hz2b Lzy Lzv Lxz Luz L1 L2 Luyxz Luzxy Luvxz.
    * prove x * v + u * z + x * y < x * y + u * v + x * z.
      rewrite add_SNo_rotate_3_1 (x * v) (u * z) (x * y) Hxv Luz Hxy.
      prove x * y + x * v + u * z < x * y + u * v + x * z.
      aby SNo_add_SNo add_SNo_Lt2 Hx Hy Hu Hv Hux Hvy Hxy Hxy1 Hxy2 Hxy3 Hxy4 Huy Huy1 Huy2 Huy3 Huy4 Hxv Hxv1 Hxv2 Hxv3 Hxv4 Huv Huv1 Huv2 Huv3 Huv4 Luyxv Lxyuv H1 H2 H3 Lxu Hz1 Hz2 Hz3 Hz4 Hz5 Hz6 Hz7 Hz8 Hz2a Hz2b Lzy Lzv Lxz Luz L1 L2 Luyxz Luzxy Luvxz.
  + aby SNoL_I Lxu Huy4 Hvy Hv Hy.
  + aby SNoR_I add_SNo_com Lxu Huv2 Huv Hxv Huy Hxy Hvy Hv Hy.
Qed.

Theorem mul_SNo_Le : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u <= x -> v <= y -> u * y + x * v <= x * y + u * v.
aby SNoLtLe SNoLeE SNoLe_ref add_SNo_com SNo_mul_SNo mul_SNo_Lt.
Qed.

Theorem mul_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 (exists v :e SNoL x, exists w :e SNoL y, u + v * w <= v * y + x * w)
 \/
 (exists v :e SNoR x, exists w :e SNoR y, u + v * w <= v * y + x * w).
let x y. assume Hx Hy.
set P1 : set -> prop :=
  fun u => exists v :e SNoL x, exists w :e SNoL y, u + v * w <= v * y + x * w.
set P2 : set -> prop :=
  fun u => exists v :e SNoR x, exists w :e SNoR y, u + v * w <= v * y + x * w.
set P : set -> prop := fun u => P1 u \/ P2 u.
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy Hx. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x * y) -> u < x * y -> P u.
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x * y) -> z < x * y -> P z.
  assume Hu2: SNoLev u :e SNoLev (x * y).
  assume Hu3: u < x * y.
  apply dneg.
  assume HNC: ~P u.
  claim L1: forall v :e SNoL x, forall w :e SNoL y, v * y + x * w < u + v * w.
  { aby SNoLtLe_or SNoL_E SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy Hx. }
  claim L2: forall v :e SNoR x, forall w :e SNoR y, v * y + x * w < u + v * w.
  { aby SNoLtLe_or SNoR_E SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy Hx. }
  apply SNoLt_irref u.
  apply SNoLtLe_tra u (x * y) u Hu1 Lxy Hu1 Hu3.
  prove x * y <= u.
  apply mul_SNo_eq_3 x y Hx Hy.
  let L R. assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2.
  assume HE: x * y = SNoCut L R.
  rewrite HE.
  prove SNoCut L R <= u.
  rewrite SNo_eta u Hu1.
  prove SNoCut L R <= SNoCut (SNoL u) (SNoR u).
  apply SNoCut_Le L R (SNoL u) (SNoR u) HLR (SNoCutP_SNoL_SNoR u Hu1).
  - aby SNoL_E SNoR_E SNo_eta add_SNo_minus_Lt1b3 SNo_mul_SNo HLE L2 L1 Hu1 Hy Hx.
  - prove forall z :e SNoR u, SNoCut L R < z.
    let z. assume Hz: z :e SNoR u.
    rewrite <- HE.
    prove x * y < z.
    apply SNoR_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: u < z.
    apply SNoLt_trichotomy_or_impred z (x * y) Hz1 Lxy.
    + assume H1: z < x * y.
      claim LPz: P z.
      { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 H1 Hz2 Hz1 Hu2 IH Hu1 Lxy. }
      aby SNoLt_irref SNoLt_tra SNoLeLt_tra SNoL_E SNoR_E SNo_add_SNo add_SNo_Lt1_cancel SNo_mul_SNo LPz Hz3 Hz1 L2 L1 Hu1 Hy Hx.
    + aby In_no2cycle Hz2 Hu2.
    + aby.
}
aby SNoL_E LI Lxy.
Qed.

Theorem mul_SNo_SNoL_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + v * w <= v * y + x * w -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + v * w <= v * y + x * w -> p)
   -> p.
aby mul_SNo_SNoL_interpolate.
Qed.  

Theorem mul_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 (exists v :e SNoL x, exists w :e SNoR y, v * y + x * w <= u + v * w)
 \/
 (exists v :e SNoR x, exists w :e SNoL y, v * y + x * w <= u + v * w).
let x y. assume Hx Hy.
set P1 : set -> prop :=
  fun u => exists v :e SNoL x, exists w :e SNoR y, v * y + x * w <= u + v * w.
set P2 : set -> prop :=
  fun u => exists v :e SNoR x, exists w :e SNoL y, v * y + x * w <= u + v * w.
set P : set -> prop := fun u => P1 u \/ P2 u.
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy Hx. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x * y) -> x * y < u -> P u.
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x * y) -> x * y < z -> P z.
  assume Hu2: SNoLev u :e SNoLev (x * y).
  assume Hu3: x * y < u.
  apply dneg.
  assume HNC: ~P u.
  claim L1: forall v :e SNoL x, forall w :e SNoR y, u + v * w < v * y + x * w.
  { aby SNoLtLe_or SNoL_E SNoR_E SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy Hx. }
  claim L2: forall v :e SNoR x, forall w :e SNoL y, u + v * w < v * y + x * w.
  { aby SNoLtLe_or SNoL_E SNoR_E SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy Hx. }
  apply SNoLt_irref (x * y).
  apply SNoLtLe_tra (x * y) u (x * y) Lxy Hu1 Lxy Hu3.
  prove u <= x * y.
  apply mul_SNo_eq_3 x y Hx Hy.
  let L R. assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2.
  assume HE: x * y = SNoCut L R.
  rewrite HE.
  prove u <= SNoCut L R.
  rewrite SNo_eta u Hu1.
  prove SNoCut (SNoL u) (SNoR u) <= SNoCut L R.
  apply SNoCut_Le (SNoL u) (SNoR u) L R (SNoCutP_SNoL_SNoR u Hu1) HLR.
  - prove forall z :e SNoL u, z < SNoCut L R.
    let z. assume Hz: z :e SNoL u.
    rewrite <- HE.
    prove z < x * y.
    apply SNoL_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: z < u.
    apply SNoLt_trichotomy_or_impred z (x * y) Hz1 Lxy.
    + aby.
    + aby In_no2cycle Hz2 Hu2.
    + assume H1: x * y < z.
      claim LPz: P z.
      { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 H1 Hz2 Hz1 Hu2 IH Hu1 Lxy. }
      aby SNoLt_irref SNoLt_tra SNoLtLe_tra SNoL_E SNoR_E SNo_add_SNo add_SNo_Lt1_cancel SNo_mul_SNo LPz Hz3 Hz1 L2 L1 Hu1 Hy Hx.
  - aby SNoL_E SNoR_E SNo_eta add_SNo_minus_Lt2b3 SNo_mul_SNo HRE L2 L1 Hu1 Hy Hx.
}
aby SNoR_E LI Lxy.
Qed.

Theorem mul_SNo_SNoR_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 forall p:prop,
     (forall v :e SNoL x, forall w :e SNoR y, v * y + x * w <= u + v * w -> p)
  -> (forall v :e SNoR x, forall w :e SNoL y, v * y + x * w <= u + v * w -> p)
  -> p.
aby mul_SNo_SNoR_interpolate.
Qed.

(** This could be useful for proving L c= L', L = L', R c= R' or R = R'
    when corresponding conditions hold. **)
Theorem mul_SNo_Subq_lem : forall x y X Y Z W,
  forall U U',
      (forall u, u :e U ->
         (forall q:prop,
                (forall w0 :e X, forall w1 :e Y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e Z, forall z1 :e W, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q))
   -> (forall w0 :e X, forall w1 :e Y, w0 * y + x * w1 + - w0 * w1 :e U')
   -> (forall w0 :e Z, forall w1 :e W, w0 * y + x * w1 + - w0 * w1 :e U')
   -> U c= U'.
aby.
Qed.

(** Part of Conway Chapter 2 Theorem 7 **)
Theorem mul_SNo_zeroR : forall x, SNo x -> x * 0 = 0.
aby EmptyE Empty_Subq_eq SNo_0 SNoCut_0_0 SNoL_0 SNoR_0 mul_SNo_eq_2.
Qed.

Theorem mul_SNo_oneR : forall x, SNo x -> x * 1 = x.
apply SNoLev_ind.
let x. assume Hx.
assume IHx: forall w :e SNoS_ (SNoLev x), w * 1 = w.
apply mul_SNo_eq_3 x 1 Hx SNo_1.
let L R.
assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2 Hx1e.
prove x * 1 = x.
apply mul_SNo_prop_1 x Hx 1 SNo_1.
assume Hx1: SNo (x * 1).
assume Hx11: forall u :e SNoL x, forall v :e SNoL 1, u * 1 + x * v < x * 1 + u * v.
assume Hx12: forall u :e SNoR x, forall v :e SNoR 1, u * 1 + x * v < x * 1 + u * v.
assume Hx13: forall u :e SNoL x, forall v :e SNoR 1, x * 1 + u * v < u * 1 + x * v.
assume Hx14: forall u :e SNoR x, forall v :e SNoL 1, x * 1 + u * v < u * 1 + x * v.
claim L0L1: 0 :e SNoL 1.
{ aby In_0_1 SNoL_1. }
rewrite Hx1e.
prove SNoCut L R = x.
rewrite SNo_eta x Hx.
prove SNoCut L R = SNoCut (SNoL x) (SNoR x).
apply SNoCut_ext L R (SNoL x) (SNoR x) HLR (SNoCutP_SNoL_SNoR x Hx).
- aby EmptyE cases_1 SNoCutP_SNoL_SNoR SNoL_E SNoL_SNoS SNoCutP_SNoCut_L SNo_0 SNo_1 SNoL_1 SNoR_1 add_SNo_0R minus_SNo_0 SNo_mul_SNo mul_SNo_zeroR HLE IHx Hx.
- aby EmptyE cases_1 SNoCutP_SNoL_SNoR SNoR_E SNoR_SNoS SNoCutP_SNoCut_R SNo_0 SNo_1 SNoL_1 SNoR_1 add_SNo_0R minus_SNo_0 SNo_mul_SNo mul_SNo_zeroR HRE IHx Hx.
- aby SNoL_E SNoL_SNoS SNo_1 add_SNo_0R SNo_mul_SNo mul_SNo_zeroR L0L1 Hx11 Hx1e IHx Hx.
- aby SNoR_E SNoR_SNoS SNo_1 add_SNo_0R SNo_mul_SNo mul_SNo_zeroR L0L1 Hx14 Hx1e IHx Hx.
Qed.

Theorem mul_SNo_com : forall x y, SNo x -> SNo y -> x * y = y * x.
apply SNoLev_ind2.
let x y.
assume Hx Hy.
assume IHx: forall w :e SNoS_ (SNoLev x), w * y = y * w.
assume IHy: forall z :e SNoS_ (SNoLev y), x * z = z * x.
assume IHxy: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), w * z = z * w.
apply mul_SNo_eq_3 x y Hx Hy.
let L R.
assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2 Hxye.
apply mul_SNo_eq_3 y x Hy Hx.
let L' R'.
assume HL'R' HL'E HL'I1 HL'I2 HR'E HR'I1 HR'I2 Hyxe.
rewrite Hxye. rewrite Hyxe.
prove SNoCut L R = SNoCut L' R'.
claim LLL': L = L'.
{ apply set_ext.
  - prove L c= L'.
    apply mul_SNo_Subq_lem x y (SNoL x) (SNoL y) (SNoR x) (SNoR y) L L' HLE.
    + aby SNoL_E SNoL_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HL'I1 IHxy IHy IHx Hy Hx.
    + aby SNoR_E SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HL'I2 IHxy IHy IHx Hy Hx.
  - prove L' c= L.
    apply mul_SNo_Subq_lem y x (SNoL y) (SNoL x) (SNoR y) (SNoR x) L' L HL'E.
    + aby SNoL_E SNoL_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HLI1 IHxy IHy IHx Hy Hx.
    + aby SNoR_E SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HLI2 IHxy IHy IHx Hy Hx.
}
claim LRR': R = R'.
{ apply set_ext.
  - apply mul_SNo_Subq_lem x y (SNoL x) (SNoR y) (SNoR x) (SNoL y) R R' HRE.
    + aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HR'I2 IHxy IHy IHx Hy Hx.
    + aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HR'I1 IHxy IHy IHx Hy Hx.
  - apply mul_SNo_Subq_lem y x (SNoL y) (SNoR x) (SNoR y) (SNoL x) R' R HR'E.
    + aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HRI2 IHxy IHy IHx Hy Hx.
    + aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HRI1 IHxy IHy IHx Hy Hx.
}
aby LRR' LLL'.
Qed.

Theorem mul_SNo_minus_distrL : forall x y, SNo x -> SNo y -> (- x) * y = - x * y.
apply SNoLev_ind2.
let x y.
assume Hx Hy.
assume IHx: forall w :e SNoS_ (SNoLev x), (- w) * y = - w * y.
assume IHy: forall z :e SNoS_ (SNoLev y), (- x) * z = - x * z.
assume IHxy: forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), (- w) * z = - w * z.
claim Lmx: SNo (- x).
{ aby SNo_minus_SNo Hx. }
apply mul_SNo_eq_3 x y Hx Hy.
let L R.
assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2.
assume Hxye: x * y = SNoCut L R.
apply mul_SNo_eq_3 (- x) y (SNo_minus_SNo x Hx) Hy.
let L' R'.
assume HL'R' HL'E HL'I1 HL'I2 HR'E HR'I1 HR'I2.
assume Hmxye: (- x) * y = SNoCut L' R'.
claim L1: - (x * y) = SNoCut {- z | z :e R} {- w | w :e L}.
{ aby minus_SNoCut_eq Hxye HLR. }
rewrite L1. rewrite Hmxye.
prove SNoCut L' R' = SNoCut {- z | z :e R} {- w | w :e L}.
f_equal.
- prove L' = {- z | z :e R}.
  apply set_ext.
  + apply mul_SNo_Subq_lem (- x) y (SNoL (- x)) (SNoL y) (SNoR (- x)) (SNoR y) L' {- z | z :e R} HL'E.
    * aby ReplI SNoL_E SNoL_SNoS SNoR_SNoS SNoR_I SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra2 minus_add_SNo_distr_3 SNo_mul_SNo HRI2 Lmx IHxy IHy IHx Hy Hx.
    * aby ReplI SNoR_E SNoL_SNoS SNoR_SNoS SNoL_I SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra1 minus_add_SNo_distr_3 SNo_mul_SNo HRI1 Lmx IHxy IHy IHx Hy Hx.
  + prove {- z | z :e R} c= L'.
    let a. assume Ha.
    apply ReplE_impred R (fun z => - z) a Ha.
    let z. assume Hz: z :e R. assume Hze: a = - z.
    rewrite Hze.
    prove - z :e L'.
    apply HRE z Hz.
    * aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNoR_I SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_Lev minus_add_SNo_distr_3 SNo_mul_SNo HL'I2 IHxy IHy IHx Hy Hx.
    * aby SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNoL_I SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_Lev minus_add_SNo_distr_3 SNo_mul_SNo HL'I1 IHxy IHy IHx Hy Hx.
- prove R' = {- w | w :e L}.
  apply set_ext.
  + apply mul_SNo_Subq_lem (- x) y (SNoL (- x)) (SNoR y) (SNoR (- x)) (SNoL y) R' {- w | w :e L} HR'E.
    * aby ReplI SNoL_E SNoR_E SNoR_SNoS SNoR_I SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra2 minus_add_SNo_distr_3 SNo_mul_SNo HLI2 Lmx IHxy IHy IHx Hy Hx.
    * aby ReplI SNoL_E SNoR_E SNoL_SNoS SNoL_I SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra1 minus_add_SNo_distr_3 SNo_mul_SNo HLI1 Lmx IHxy IHy IHx Hy Hx.
  + prove {- w | w :e L} c= R'.
    let a. assume Ha.
    apply ReplE_impred L (fun w => - w) a Ha.
    let w. assume Hw: w :e L. assume Hwe: a = - w.
    rewrite Hwe.
    prove - w :e R'.
    apply HLE w Hw.
    * aby SNoL_E SNoL_SNoS SNoR_I SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_Lev minus_add_SNo_distr_3 SNo_mul_SNo HR'I2 IHxy IHy IHx Hy Hx.
    * aby SNoR_E SNoR_SNoS SNoL_I SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_Lev minus_add_SNo_distr_3 SNo_mul_SNo HR'I1 IHxy IHy IHx Hy Hx.
Qed.

Theorem mul_SNo_minus_distrR: forall x y, SNo x -> SNo y -> x * (- y) = - (x * y).
aby SNo_minus_SNo mul_SNo_com mul_SNo_minus_distrL.
Qed.

Theorem mul_SNo_distrR : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) * z = x * z + y * z.
set P : set -> set -> set -> prop := fun x y z => (x + y) * z = x * z + y * z.
prove forall x y z, SNo x -> SNo y -> SNo z -> P x y z.
apply SNoLev_ind3 P.
let x y z. assume Hx Hy Hz.
assume IHx: forall u :e SNoS_ (SNoLev x), (u + y) * z = u * z + y * z.
assume IHy: forall v :e SNoS_ (SNoLev y), (x + v) * z = x * z + v * z.
assume IHz: forall w :e SNoS_ (SNoLev z), (x + y) * w = x * w + y * w.
assume IHxy: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), (u + v) * z = u * z + v * z.
assume IHxz: forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), (u + y) * w = u * w + y * w.
assume IHyz: forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), (x + v) * w = x * w + v * w.
assume IHxyz: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), (u + v) * w = u * w + v * w.
prove (x + y) * z = x * z + y * z.
apply mul_SNo_eq_3 (x + y) z (SNo_add_SNo x y Hx Hy) Hz.
let L R. assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2.
assume HE: (x + y) * z = SNoCut L R.
set L1 := {w + y * z | w :e SNoL (x * z)}.
set L2 := {x * z + w | w :e SNoL (y * z)}.
set R1 := {w + y * z | w :e SNoR (x * z)}.
set R2 := {x * z + w | w :e SNoR (y * z)}.
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Hy Hx. }
claim Lxyz: SNo ((x + y) * z).
{ aby SNo_mul_SNo Lxy Hz. }
claim Lxz: SNo (x * z).
{ aby SNo_mul_SNo Hz Hx. }
claim Lyz: SNo (y * z).
{ aby SNo_mul_SNo Hz Hy. }
claim Lxzyz: SNo (x * z + y * z).
{ aby SNo_add_SNo Lyz Lxz. }
claim LE: x * z + y * z = SNoCut (L1 :\/: L2) (R1 :\/: R2).
{ aby add_SNo_eq SNo_mul_SNo Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz. }
rewrite HE. rewrite LE.
apply SNoCut_ext.
- aby HLR.
- aby add_SNo_SNoCutP SNo_mul_SNo Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE.
- let u. assume Hu: u :e L. rewrite <- LE.
  prove u < x * z + y * z.
  apply HLE u Hu.
  + let v. assume Hv: v :e SNoL (x + y).
    let w. assume Hw: w :e SNoL z.
    assume Hue: u = v * z + (x + y) * w + - v * w.
    rewrite Hue.
    prove v * z + (x + y) * w + - v * w < x * z + y * z.
    apply SNoL_E (x + y) Lxy v Hv.
    assume Hv1 Hv2 Hv3.
    apply SNoL_E z Hz w Hw.
    assume Hw1 Hw2 Hw3.
    claim Lxw: SNo (x * w).
    { aby SNo_mul_SNo Hw1 Hx. }
    claim Lyw: SNo (y * w).
    { aby SNo_mul_SNo Hw1 Hy. }
    claim Lvz: SNo (v * z).
    { aby SNo_mul_SNo Hv1 Hz. }
    claim Lxyw: SNo ((x + y) * w).
    { aby SNo_mul_SNo Hw1 Lxy. }
    claim Lxwyw: SNo (x * w + y * w).
    { aby SNo_add_SNo Lyw Lxw. }
    claim Lvw: SNo (v * w).
    { aby SNo_mul_SNo Hw1 Hv1. }
    claim Lvzxwyw: SNo (v * z + x * w + y * w).
    { aby SNo_add_SNo_3 Lvz Lyw Lxw. }
    claim Lxzyzvw: SNo (x * z + y * z + v * w).
    { aby SNo_add_SNo_3 Lvw Lyz Lxz. }
    apply add_SNo_minus_Lt1b3 (v * z) ((x + y) * w) (v * w) (x * z + y * z)
                              Lvz Lxyw Lvw Lxzyz.
    prove v * z + (x + y) * w < (x * z + y * z) + v * w.
    rewrite IHz w (SNoL_SNoS z Hz w Hw).
    prove v * z + x * w + y * w < (x * z + y * z) + v * w.
    rewrite <- add_SNo_assoc (x * z) (y * z) (v * w) Lxz Lyz Lvw.
    prove v * z + x * w + y * w < x * z + y * z + v * w.
    apply add_SNo_SNoL_interpolate x y Hx Hy v Hv.
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoL x.
        assume Hvu: v <= u + y.
        apply SNoL_E x Hx u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Luy: SNo (u + y).
        { aby SNo_add_SNo Hu1 Hy. }
        apply add_SNo_Lt1_cancel (v * z + x * w + y * w)
                                 (u * w)
                                 (x * z + y * z + v * w)
                                   Lvzxwyw Luw Lxzyzvw.
        prove (v * z + x * w + y * w) + u * w < (x * z + y * z + v * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove v * z + x * w + y * w + u * w < x * z + y * z + v * w + u * w.
        apply SNoLeLt_tra (v * z + x * w + y * w + u * w)
                          (u * z + y * z + v * w + x * w)
                          (x * z + y * z + v * w + u * w)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw)
                          (SNo_add_SNo_4 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw).
        - prove v * z + x * w + y * w + u * w <= u * z + y * z + v * w + x * w.
          rewrite add_SNo_com_3_0_1 (v * z) (x * w) (y * w + u * w) Lvz Lxw (SNo_add_SNo (y * w) (u * w) Lyw Luw).
          prove x * w + v * z + y * w + u * w <= u * z + y * z + v * w + x * w.
          rewrite add_SNo_rotate_4_1 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw.
          prove x * w + v * z + y * w + u * w <= x * w + u * z + y * z + v * w.
          apply add_SNo_Le2 (x * w) (v * z + y * w + u * w) (u * z + y * z + v * w)
                            Lxw
                            (SNo_add_SNo_3 (v * z) (y * w) (u * w) Lvz Lyw Luw)
                            (SNo_add_SNo_3 (u * z) (y * z) (v * w) Luz Lyz Lvw).
          prove v * z + y * w + u * w <= u * z + y * z + v * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove v * z + u * w + y * w <= u * z + y * z + v * w.
          rewrite <- IHxz u (SNoL_SNoS x Hx u Hu) w (SNoL_SNoS z Hz w Hw).
          prove v * z + (u + y) * w <= u * z + y * z + v * w.
          rewrite add_SNo_assoc (u * z) (y * z) (v * w) Luz Lyz Lvw.
          prove v * z + (u + y) * w <= (u * z + y * z) + v * w.
          rewrite <- IHx u (SNoL_SNoS x Hx u Hu).
          prove v * z + (u + y) * w <= (u + y) * z + v * w.
          apply mul_SNo_Le (u + y) z v w Luy Hz Hv1 Hw1.
          + prove v <= u + y. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
          + prove w <= z. apply SNoLtLe. prove w < z. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lxw Hw3 Hw1 Lyz Lxz Hz Hx.
      }
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoL y.
        assume Hvu: v <= x + u.
        apply SNoL_E y Hy u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Lxu: SNo (x + u).
        { aby SNo_add_SNo Hu1 Hx. }
        apply add_SNo_Lt1_cancel (v * z + x * w + y * w)
                                 (u * w)
                                 (x * z + y * z + v * w)
                                   Lvzxwyw Luw Lxzyzvw.
        prove (v * z + x * w + y * w) + u * w < (x * z + y * z + v * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove v * z + x * w + y * w + u * w < x * z + y * z + v * w + u * w.
        apply SNoLeLt_tra (v * z + x * w + y * w + u * w)
                          (x * z + u * z + v * w + y * w)
                          (x * z + y * z + v * w + u * w)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw)
                          (SNo_add_SNo_4 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw).
        - prove v * z + x * w + y * w + u * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove v * z + x * w + u * w + y * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_rotate_4_1 (v * z) (x * w) (u * w) (y * w) Lvz Lxw Luw Lyw.
          prove y * w + v * z + x * w + u * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_rotate_4_1 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw.
          prove y * w + v * z + x * w + u * w <= y * w + x * z + u * z + v * w.
          apply add_SNo_Le2 (y * w) (v * z + x * w + u * w) (x * z + u * z + v * w)
                            Lyw
                            (SNo_add_SNo_3 (v * z) (x * w) (u * w) Lvz Lxw Luw)
                            (SNo_add_SNo_3 (x * z) (u * z) (v * w) Lxz Luz Lvw).
          prove v * z + x * w + u * w <= x * z + u * z + v * w.
          rewrite <- IHyz u (SNoL_SNoS y Hy u Hu) w (SNoL_SNoS z Hz w Hw).
          prove v * z + (x + u) * w <= x * z + u * z + v * w.
          rewrite add_SNo_assoc (x * z) (u * z) (v * w) Lxz Luz Lvw.
          prove v * z + (x + u) * w <= (x * z + u * z) + v * w.
          rewrite <- IHy u (SNoL_SNoS y Hy u Hu).
          prove v * z + (x + u) * w <= (x + u) * z + v * w.
          apply mul_SNo_Le (x + u) z v w Lxu Hz Hv1 Hw1.
          + prove v <= x + u. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
          + prove w <= z. apply SNoLtLe. prove w < z. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lyw Hw3 Hw1 Lyz Lxz Hz Hy.
      }
  + let v. assume Hv: v :e SNoR (x + y).
    let w. assume Hw: w :e SNoR z.
    assume Hue: u = v * z + (x + y) * w + - v * w.
    rewrite Hue.
    prove v * z + (x + y) * w + - v * w < x * z + y * z.
    apply SNoR_E (x + y) Lxy v Hv.
    assume Hv1 Hv2 Hv3.
    apply SNoR_E z Hz w Hw.
    assume Hw1 Hw2 Hw3.
    claim Lxw: SNo (x * w).
    { aby SNo_mul_SNo Hw1 Hx. }
    claim Lyw: SNo (y * w).
    { aby SNo_mul_SNo Hw1 Hy. }
    claim Lvz: SNo (v * z).
    { aby SNo_mul_SNo Hv1 Hz. }
    claim Lxyw: SNo ((x + y) * w).
    { aby SNo_mul_SNo Hw1 Lxy. }
    claim Lxwyw: SNo (x * w + y * w).
    { aby SNo_add_SNo Lyw Lxw. }
    claim Lvw: SNo (v * w).
    { aby SNo_mul_SNo Hw1 Hv1. }
    claim Lvzxwyw: SNo (v * z + x * w + y * w).
    { aby SNo_add_SNo_3 Lvz Lyw Lxw. }
    claim Lxzyzvw: SNo (x * z + y * z + v * w).
    { aby SNo_add_SNo_3 Lvw Lyz Lxz. }
    apply add_SNo_minus_Lt1b3 (v * z) ((x + y) * w) (v * w) (x * z + y * z)
                              Lvz Lxyw Lvw Lxzyz.
    prove v * z + (x + y) * w < (x * z + y * z) + v * w.
    rewrite IHz w (SNoR_SNoS z Hz w Hw).
    prove v * z + x * w + y * w < (x * z + y * z) + v * w.
    rewrite <- add_SNo_assoc (x * z) (y * z) (v * w) Lxz Lyz Lvw.
    prove v * z + x * w + y * w < x * z + y * z + v * w.
    apply add_SNo_SNoR_interpolate x y Hx Hy v Hv.
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoR x.
        assume Hvu: u + y <= v.
        apply SNoR_E x Hx u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Luy: SNo (u + y).
        { aby SNo_add_SNo Hu1 Hy. }
        apply add_SNo_Lt1_cancel (v * z + x * w + y * w)
                                 (u * w)
                                 (x * z + y * z + v * w)
                                   Lvzxwyw Luw Lxzyzvw.
        prove (v * z + x * w + y * w) + u * w < (x * z + y * z + v * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove v * z + x * w + y * w + u * w < x * z + y * z + v * w + u * w.
        apply SNoLeLt_tra (v * z + x * w + y * w + u * w)
                          (u * z + y * z + v * w + x * w)
                          (x * z + y * z + v * w + u * w)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw)
                          (SNo_add_SNo_4 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw).
        - prove v * z + x * w + y * w + u * w <= u * z + y * z + v * w + x * w.
          rewrite add_SNo_com_3_0_1 (v * z) (x * w) (y * w + u * w) Lvz Lxw (SNo_add_SNo (y * w) (u * w) Lyw Luw).
          prove x * w + v * z + y * w + u * w <= u * z + y * z + v * w + x * w.
          rewrite add_SNo_rotate_4_1 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw.
          prove x * w + v * z + y * w + u * w <= x * w + u * z + y * z + v * w.
          apply add_SNo_Le2 (x * w) (v * z + y * w + u * w) (u * z + y * z + v * w)
                            Lxw
                            (SNo_add_SNo_3 (v * z) (y * w) (u * w) Lvz Lyw Luw)
                            (SNo_add_SNo_3 (u * z) (y * z) (v * w) Luz Lyz Lvw).
          prove v * z + y * w + u * w <= u * z + y * z + v * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove v * z + u * w + y * w <= u * z + y * z + v * w.
          rewrite <- IHxz u (SNoR_SNoS x Hx u Hu) w (SNoR_SNoS z Hz w Hw).
          prove v * z + (u + y) * w <= u * z + y * z + v * w.
          rewrite add_SNo_assoc (u * z) (y * z) (v * w) Luz Lyz Lvw.
          prove v * z + (u + y) * w <= (u * z + y * z) + v * w.
          rewrite <- IHx u (SNoR_SNoS x Hx u Hu).
          prove v * z + (u + y) * w <= (u + y) * z + v * w.
          rewrite add_SNo_com ((u + y) * z) (v * w) (SNo_mul_SNo (u + y) z Luy Hz) Lvw.
          rewrite add_SNo_com (v * z) ((u + y) * w) Lvz (SNo_mul_SNo (u + y) w Luy Hw1).
          apply mul_SNo_Le v w (u + y) z Hv1 Hw1 Luy Hz.
          + prove u + y <= v. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
          + prove z <= w. apply SNoLtLe. prove z < w. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lxw Hw3 Hw1 Lyz Lxz Hz Hx.
      }
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoR y.
        assume Hvu: x + u <= v.
        apply SNoR_E y Hy u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Lxu: SNo (x + u).
        { aby SNo_add_SNo Hu1 Hx. }
        apply add_SNo_Lt1_cancel (v * z + x * w + y * w)
                                 (u * w)
                                 (x * z + y * z + v * w)
                                   Lvzxwyw Luw Lxzyzvw.
        prove (v * z + x * w + y * w) + u * w < (x * z + y * z + v * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove v * z + x * w + y * w + u * w < x * z + y * z + v * w + u * w.
        apply SNoLeLt_tra (v * z + x * w + y * w + u * w)
                          (x * z + u * z + v * w + y * w)
                          (x * z + y * z + v * w + u * w)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw)
                          (SNo_add_SNo_4 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw).
        - prove v * z + x * w + y * w + u * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove v * z + x * w + u * w + y * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_rotate_4_1 (v * z) (x * w) (u * w) (y * w) Lvz Lxw Luw Lyw.
          prove y * w + v * z + x * w + u * w <= x * z + u * z + v * w + y * w.
          rewrite add_SNo_rotate_4_1 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw.
          prove y * w + v * z + x * w + u * w <= y * w + x * z + u * z + v * w.
          apply add_SNo_Le2 (y * w) (v * z + x * w + u * w) (x * z + u * z + v * w)
                            Lyw
                            (SNo_add_SNo_3 (v * z) (x * w) (u * w) Lvz Lxw Luw)
                            (SNo_add_SNo_3 (x * z) (u * z) (v * w) Lxz Luz Lvw).
          prove v * z + x * w + u * w <= x * z + u * z + v * w.
          rewrite <- IHyz u (SNoR_SNoS y Hy u Hu) w (SNoR_SNoS z Hz w Hw).
          prove v * z + (x + u) * w <= x * z + u * z + v * w.
          rewrite add_SNo_assoc (x * z) (u * z) (v * w) Lxz Luz Lvw.
          prove v * z + (x + u) * w <= (x * z + u * z) + v * w.
          rewrite <- IHy u (SNoR_SNoS y Hy u Hu).
          prove v * z + (x + u) * w <= (x + u) * z + v * w.
          rewrite add_SNo_com ((x + u) * z) (v * w) (SNo_mul_SNo (x + u) z Lxu Hz) Lvw.
          rewrite add_SNo_com (v * z) ((x + u) * w) Lvz (SNo_mul_SNo (x + u) w Lxu Hw1).
          apply mul_SNo_Le v w (x + u) z Hv1 Hw1 Lxu Hz.
          + prove x + u <= v. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
          + prove z <= w. apply SNoLtLe. prove z < w. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lyw Hw3 Hw1 Lyz Lxz Hz Hy.
      }
- let u. assume Hu: u :e R. rewrite <- LE.
  prove x * z + y * z < u.
  apply HRE u Hu.
  + let v. assume Hv: v :e SNoL (x + y).
    let w. assume Hw: w :e SNoR z.
    assume Hue: u = v * z + (x + y) * w + - v * w.
    rewrite Hue.
    prove x * z + y * z < v * z + (x + y) * w + - v * w.
    apply SNoL_E (x + y) Lxy v Hv.
    assume Hv1 Hv2 Hv3.
    apply SNoR_E z Hz w Hw.
    assume Hw1 Hw2 Hw3.
    claim Lxw: SNo (x * w).
    { aby SNo_mul_SNo Hw1 Hx. }
    claim Lyw: SNo (y * w).
    { aby SNo_mul_SNo Hw1 Hy. }
    claim Lvz: SNo (v * z).
    { aby SNo_mul_SNo Hv1 Hz. }
    claim Lxyw: SNo ((x + y) * w).
    { aby SNo_mul_SNo Hw1 Lxy. }
    claim Lxwyw: SNo (x * w + y * w).
    { aby SNo_add_SNo Lyw Lxw. }
    claim Lvw: SNo (v * w).
    { aby SNo_mul_SNo Hw1 Hv1. }
    claim Lvzxwyw: SNo (v * z + x * w + y * w).
    { aby SNo_add_SNo_3 Lvz Lyw Lxw. }
    claim Lxzyzvw: SNo (x * z + y * z + v * w).
    { aby SNo_add_SNo_3 Lvw Lyz Lxz. }
    prove x * z + y * z < v * z + (x + y) * w + - v * w.
    apply add_SNo_minus_Lt2b3 (v * z) ((x + y) * w) (v * w) (x * z + y * z)
                              Lvz Lxyw Lvw Lxzyz.
    prove (x * z + y * z) + v * w < v * z + (x + y) * w.
    rewrite IHz w (SNoR_SNoS z Hz w Hw).
    prove (x * z + y * z) + v * w < v * z + x * w + y * w.
    rewrite <- add_SNo_assoc (x * z) (y * z) (v * w) Lxz Lyz Lvw.
    prove x * z + y * z + v * w < v * z + x * w + y * w.
    apply add_SNo_SNoL_interpolate x y Hx Hy v Hv.
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoL x.
        assume Hvu: v <= u + y.
        apply SNoL_E x Hx u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Luy: SNo (u + y).
        { aby SNo_add_SNo Hu1 Hy. }
        apply add_SNo_Lt1_cancel (x * z + y * z + v * w)
                                 (u * w)
                                 (v * z + x * w + y * w)
                                   Lxzyzvw Luw Lvzxwyw.
        prove (x * z + y * z + v * w) + u * w < (v * z + x * w + y * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove x * z + y * z + v * w + u * w < v * z + x * w + y * w + u * w.
        apply SNoLtLe_tra (x * z + y * z + v * w + u * w)
                          (u * z + y * z + v * w + x * w)
                          (v * z + x * w + y * w + u * w)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw)
                          (SNo_add_SNo_4 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw).
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lxw Hw3 Hw1 Lyz Lxz Hz Hx.
        - prove u * z + y * z + v * w + x * w <= v * z + x * w + y * w + u * w.
          rewrite add_SNo_com_3_0_1 (v * z) (x * w) (y * w + u * w) Lvz Lxw (SNo_add_SNo (y * w) (u * w) Lyw Luw).
          prove u * z + y * z + v * w + x * w <= x * w + v * z + y * w + u * w.
          rewrite add_SNo_rotate_4_1 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw.
          prove x * w + u * z + y * z + v * w <= x * w + v * z + y * w + u * w.
          apply add_SNo_Le2 (x * w) (u * z + y * z + v * w) (v * z + y * w + u * w)
                            Lxw
                            (SNo_add_SNo_3 (u * z) (y * z) (v * w) Luz Lyz Lvw)
                            (SNo_add_SNo_3 (v * z) (y * w) (u * w) Lvz Lyw Luw).
          prove u * z + y * z + v * w <= v * z + y * w + u * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove u * z + y * z + v * w <= v * z + u * w + y * w.
          rewrite <- IHxz u (SNoL_SNoS x Hx u Hu) w (SNoR_SNoS z Hz w Hw).
          prove u * z + y * z + v * w <= v * z + (u + y) * w.
          rewrite add_SNo_assoc (u * z) (y * z) (v * w) Luz Lyz Lvw.
          prove (u * z + y * z) + v * w <= v * z + (u + y) * w.
          rewrite <- IHx u (SNoL_SNoS x Hx u Hu).
          prove (u + y) * z + v * w <= v * z + (u + y) * w.
          rewrite add_SNo_com ((u + y) * z) (v * w) (SNo_mul_SNo (u + y) z Luy Hz) Lvw.
          rewrite add_SNo_com (v * z) ((u + y) * w) Lvz (SNo_mul_SNo (u + y) w Luy Hw1).
          prove v * w + (u + y) * z  <= (u + y) * w + v * z.
          apply mul_SNo_Le (u + y) w v z Luy Hw1 Hv1 Hz.
          + prove v <= u + y. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
          + prove z <= w. apply SNoLtLe. prove z < w. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
      }
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoL y.
        assume Hvu: v <= x + u.
        apply SNoL_E y Hy u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Lxu: SNo (x + u).
        { aby SNo_add_SNo Hu1 Hx. }
        apply add_SNo_Lt1_cancel (x * z + y * z + v * w)
                                 (u * w)
                                 (v * z + x * w + y * w)
                                   Lxzyzvw Luw Lvzxwyw.
        prove (x * z + y * z + v * w) + u * w < (v * z + x * w + y * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove x * z + y * z + v * w + u * w < v * z + x * w + y * w + u * w.
        apply SNoLtLe_tra (x * z + y * z + v * w + u * w)
                          (x * z + u * z + v * w + y * w)
                          (v * z + x * w + y * w + u * w)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw)
                          (SNo_add_SNo_4 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw).
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lyw Hw3 Hw1 Lyz Lxz Hz Hy.
        - prove x * z + u * z + v * w + y * w <= v * z + x * w + y * w + u * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove x * z + u * z + v * w + y * w <= v * z + x * w + u * w + y * w.
          rewrite add_SNo_rotate_4_1 (v * z) (x * w) (u * w) (y * w) Lvz Lxw Luw Lyw.
          prove x * z + u * z + v * w + y * w <= y * w + v * z + x * w + u * w.
          rewrite add_SNo_rotate_4_1 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw.
          aby SNoLtLe SNoL_SNoS SNoR_SNoS SNo_add_SNo_3 add_SNo_Le2 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Le Lxu Luz Luw Hvu Hu Lvw Lvz Lyw Lxw Hw3 Hw1 Hv1 Hw Lxz IHyz IHy Hz Hy.
      }
  + let v. assume Hv: v :e SNoR (x + y).
    let w. assume Hw: w :e SNoL z.
    assume Hue: u = v * z + (x + y) * w + - v * w.
    rewrite Hue.
    prove x * z + y * z < v * z + (x + y) * w + - v * w.
    apply SNoR_E (x + y) Lxy v Hv.
    assume Hv1 Hv2 Hv3.
    apply SNoL_E z Hz w Hw.
    assume Hw1 Hw2 Hw3.
    claim Lxw: SNo (x * w).
    { aby SNo_mul_SNo Hw1 Hx. }
    claim Lyw: SNo (y * w).
    { aby SNo_mul_SNo Hw1 Hy. }
    claim Lvz: SNo (v * z).
    { aby SNo_mul_SNo Hv1 Hz. }
    claim Lxyw: SNo ((x + y) * w).
    { aby SNo_mul_SNo Hw1 Lxy. }
    claim Lxwyw: SNo (x * w + y * w).
    { aby SNo_add_SNo Lyw Lxw. }
    claim Lvw: SNo (v * w).
    { aby SNo_mul_SNo Hw1 Hv1. }
    claim Lvzxwyw: SNo (v * z + x * w + y * w).
    { aby SNo_add_SNo_3 Lvz Lyw Lxw. }
    claim Lxzyzvw: SNo (x * z + y * z + v * w).
    { aby SNo_add_SNo_3 Lvw Lyz Lxz. }
    prove x * z + y * z < v * z + (x + y) * w + - v * w.
    apply add_SNo_minus_Lt2b3 (v * z) ((x + y) * w) (v * w) (x * z + y * z)
                              Lvz Lxyw Lvw Lxzyz.
    prove (x * z + y * z) + v * w < v * z + (x + y) * w.
    rewrite IHz w (SNoL_SNoS z Hz w Hw).
    prove (x * z + y * z) + v * w < v * z + x * w + y * w.
    rewrite <- add_SNo_assoc (x * z) (y * z) (v * w) Lxz Lyz Lvw.
    prove x * z + y * z + v * w < v * z + x * w + y * w.
    apply add_SNo_SNoR_interpolate x y Hx Hy v Hv.
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoR x.
        assume Hvu: u + y <= v.
        apply SNoR_E x Hx u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Luy: SNo (u + y).
        { aby SNo_add_SNo Hu1 Hy. }
        apply add_SNo_Lt1_cancel (x * z + y * z + v * w)
                                 (u * w)
                                 (v * z + x * w + y * w)
                                   Lxzyzvw Luw Lvzxwyw.
        prove (x * z + y * z + v * w) + u * w < (v * z + x * w + y * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove x * z + y * z + v * w + u * w < v * z + x * w + y * w + u * w.
        apply SNoLtLe_tra (x * z + y * z + v * w + u * w)
                          (u * z + y * z + v * w + x * w)
                          (v * z + x * w + y * w + u * w)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw)
                          (SNo_add_SNo_4 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw).
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lxw Hw3 Hw1 Lyz Lxz Hz Hx.
        - prove u * z + y * z + v * w + x * w <= v * z + x * w + y * w + u * w.
          rewrite add_SNo_com_3_0_1 (v * z) (x * w) (y * w + u * w) Lvz Lxw (SNo_add_SNo (y * w) (u * w) Lyw Luw).
          prove u * z + y * z + v * w + x * w <= x * w + v * z + y * w + u * w.
          rewrite add_SNo_rotate_4_1 (u * z) (y * z) (v * w) (x * w) Luz Lyz Lvw Lxw.
          prove x * w + u * z + y * z + v * w <= x * w + v * z + y * w + u * w.
          apply add_SNo_Le2 (x * w) (u * z + y * z + v * w) (v * z + y * w + u * w)
                            Lxw
                            (SNo_add_SNo_3 (u * z) (y * z) (v * w) Luz Lyz Lvw)
                            (SNo_add_SNo_3 (v * z) (y * w) (u * w) Lvz Lyw Luw).
          prove u * z + y * z + v * w <= v * z + y * w + u * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove u * z + y * z + v * w <= v * z + u * w + y * w.
          rewrite <- IHxz u (SNoR_SNoS x Hx u Hu) w (SNoL_SNoS z Hz w Hw).
          prove u * z + y * z + v * w <= v * z + (u + y) * w.
          rewrite add_SNo_assoc (u * z) (y * z) (v * w) Luz Lyz Lvw.
          prove (u * z + y * z) + v * w <= v * z + (u + y) * w.
          rewrite <- IHx u (SNoR_SNoS x Hx u Hu).
          prove (u + y) * z + v * w <= v * z + (u + y) * w.
          apply mul_SNo_Le v z (u + y) w Hv1 Hz Luy Hw1.
          + prove u + y <= v. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
          + prove w <= z. apply SNoLtLe. prove w < z. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Luy.
      }
    * { assume H1. apply H1.
        let u. assume H1. apply H1.
        assume Hu: u :e SNoR y.
        assume Hvu: x + u <= v.
        apply SNoR_E y Hy u Hu.
        assume Hu1 Hu2 Hu3.
        claim Luw: SNo (u * w).
        { aby SNo_mul_SNo Hu1 Hw1. }
        claim Luz: SNo (u * z).
        { aby SNo_mul_SNo Hu1 Hz. }
        claim Lxu: SNo (x + u).
        { aby SNo_add_SNo Hu1 Hx. }
        apply add_SNo_Lt1_cancel (x * z + y * z + v * w)
                                 (u * w)
                                 (v * z + x * w + y * w)
                                   Lxzyzvw Luw Lvzxwyw.
        prove (x * z + y * z + v * w) + u * w < (v * z + x * w + y * w) + u * w.
        rewrite <- add_SNo_assoc_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw.
        rewrite <- add_SNo_assoc_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw.
        prove x * z + y * z + v * w + u * w < v * z + x * w + y * w + u * w.
        apply SNoLtLe_tra (x * z + y * z + v * w + u * w)
                          (x * z + u * z + v * w + y * w)
                          (v * z + x * w + y * w + u * w)
                          (SNo_add_SNo_4 (x * z) (y * z) (v * w) (u * w) Lxz Lyz Lvw Luw)
                          (SNo_add_SNo_4 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw)
                          (SNo_add_SNo_4 (v * z) (x * w) (y * w) (u * w) Lvz Lxw Lyw Luw).
        - aby SNo_add_SNo SNo_add_SNo_3 add_SNo_Lt2 add_SNo_com_3_0_1 mul_SNo_Lt Luz Luw Hu3 Hu1 Lvw Lyw Hw3 Hw1 Lyz Lxz Hz Hy.
        - prove x * z + u * z + v * w + y * w <= v * z + x * w + y * w + u * w.
          rewrite add_SNo_com (y * w) (u * w) Lyw Luw.
          prove x * z + u * z + v * w + y * w <= v * z + x * w + u * w + y * w.
          rewrite add_SNo_rotate_4_1 (v * z) (x * w) (u * w) (y * w) Lvz Lxw Luw Lyw.
          prove x * z + u * z + v * w + y * w <= y * w + v * z + x * w + u * w.
          rewrite add_SNo_rotate_4_1 (x * z) (u * z) (v * w) (y * w) Lxz Luz Lvw Lyw.
          prove y * w + x * z + u * z + v * w <= y * w + v * z + x * w + u * w.
          apply add_SNo_Le2 (y * w) (x * z + u * z + v * w) (v * z + x * w + u * w)
                            Lyw
                            (SNo_add_SNo_3 (x * z) (u * z) (v * w) Lxz Luz Lvw)
                            (SNo_add_SNo_3 (v * z) (x * w) (u * w) Lvz Lxw Luw).
          prove x * z + u * z + v * w <= v * z + x * w + u * w.
          rewrite <- IHyz u (SNoR_SNoS y Hy u Hu) w (SNoL_SNoS z Hz w Hw).
          prove x * z + u * z + v * w <= v * z + (x + u) * w.
          rewrite add_SNo_assoc (x * z) (u * z) (v * w) Lxz Luz Lvw.
          prove (x * z + u * z) + v * w <= v * z + (x + u) * w.
          rewrite <- IHy u (SNoR_SNoS y Hy u Hu).
          prove (x + u) * z + v * w <= v * z + (x + u) * w.
          apply mul_SNo_Le v z (x + u) w Hv1 Hz Lxu Hw1.
          + prove x + u <= v. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
          + prove w <= z. apply SNoLtLe. prove w < z. aby Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HE Lxy Lxyz Lxz Lyz Lxzyz LE Hu Hv Hw Hue Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 Lxw Lyw Lvz Lxyw Lxwyw Lvw Lvzxwyw Lxzyzvw H1 H1 Hu Hvu Hu1 Hu2 Hu3 Luw Luz Lxu.
      }
- let u'. assume Hu': u' :e L1 :\/: L2. rewrite <- HE.
  prove u' < (x + y) * z.
  apply binunionE L1 L2 u' Hu'.
  + assume Hu': u' :e L1.
    apply ReplE_impred (SNoL (x * z)) (fun w => w + y * z) u' Hu'.
    let u. assume Hu: u :e SNoL (x * z).
    assume Hu'u: u' = u + y * z.
    rewrite Hu'u.
    prove u + y * z < (x + y) * z.
    apply SNoL_E (x * z) Lxz u Hu.
    assume Hu1 Hu2 Hu3.
    apply mul_SNo_SNoL_interpolate_impred x z Hx Hz u Hu.
    * { let v. assume Hv: v :e SNoL x.
        let w. assume Hw: w :e SNoL z.
        assume Hvw: u + v * w <= v * z + x * w.
        apply SNoL_E x Hx v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoL_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lvy: SNo (v + y).
        { aby SNo_add_SNo Hv1 Hy. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luyz: SNo (u + y * z).
        { aby SNo_add_SNo Hu1 Lyz. }
        claim Lvwyw: SNo (v * w + y * w).
        { aby SNo_add_SNo Lyw Lvw. }
        claim Lvzxw: SNo (v * z + x * w).
        { aby SNo_add_SNo Lxw Lvz. }
        prove u + y * z < (x + y) * z.
        apply add_SNo_Lt1_cancel (u + y * z) (v * w + y * w) ((x + y) * z)
                                 Luyz Lvwyw Lxyz.
        prove (u + y * z) + v * w + y * w < (x + y) * z + v * w + y * w.
        rewrite add_SNo_com_4_inner_mid u (y * z) (v * w) (y * w) Hu1 Lyz Lvw Lyw.
        aby SNoLeLt_tra SNoL_SNoS SNo_add_SNo SNo_add_SNo_3 SNo_add_SNo_4 add_SNo_Lt1 add_SNo_Le1 add_SNo_assoc add_SNo_com_4_inner_mid mul_SNo_Lt Lyw Lxw Lvz Lxyw Luvw Lvy Lvw Hw3 Hw1 Hv3 Hv1 Hvw Hw Hv Lyz Lxyz Lxy IHxz IHz IHx Hz Hy Hx.
      }
    * { let v. assume Hv: v :e SNoR x.
        let w. assume Hw: w :e SNoR z.
        assume Hvw: u + v * w <= v * z + x * w.
        apply SNoR_E x Hx v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoR_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lvy: SNo (v + y).
        { aby SNo_add_SNo Hv1 Hy. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luyz: SNo (u + y * z).
        { aby SNo_add_SNo Hu1 Lyz. }
        claim Lvwyw: SNo (v * w + y * w).
        { aby SNo_add_SNo Lyw Lvw. }
        prove u + y * z < (x + y) * z.
        apply add_SNo_Lt1_cancel (u + y * z) (v * w + y * w) ((x + y) * z)
                                 Luyz Lvwyw Lxyz.
        prove (u + y * z) + v * w + y * w < (x + y) * z + v * w + y * w.
        rewrite add_SNo_com_4_inner_mid u (y * z) (v * w) (y * w) Hu1 Lyz Lvw Lyw.
        prove (u + v * w) + y * z + y * w < (x + y) * z + v * w + y * w.
        apply SNoLeLt_tra ((u + v * w) + y * z + y * w)
                          (v * z + y * z + x * w + y * w)
                          ((x + y) * z + v * w + y * w)
                          (SNo_add_SNo_3 (u + v * w) (y * z) (y * w) Luvw Lyz Lyw)
                          (SNo_add_SNo_4 (v * z) (y * z) (x * w) (y * w) Lvz Lyz Lxw Lyw)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (y * w) Lxyz Lvw Lyw).
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lyz.
        - aby SNoR_SNoS add_SNo_Lt1 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Lt Lvz Lxyw Lvy Hw3 Hw1 Hv3 Hv1 Hw Hv Lyz Lxyz Lxy IHxz IHz IHx Hz Hy Hx.
      }
  + assume Hu': u' :e L2.
    apply ReplE_impred (SNoL (y * z)) (fun w => x * z + w) u' Hu'.
    let u. assume Hu: u :e SNoL (y * z).
    assume Hu'u: u' = x * z + u.
    rewrite Hu'u.
    prove x * z + u < (x + y) * z.
    apply SNoL_E (y * z) Lyz u Hu.
    assume Hu1 Hu2 Hu3.
    rewrite add_SNo_com (x * z) u Lxz Hu1.
    prove u + x * z < (x + y) * z.
    apply mul_SNo_SNoL_interpolate_impred y z Hy Hz u Hu.
    * { let v. assume Hv: v :e SNoL y.
        let w. assume Hw: w :e SNoL z.
        assume Hvw: u + v * w <= v * z + y * w.
        apply SNoL_E y Hy v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoL_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lxv: SNo (x + v).
        { aby SNo_add_SNo Hv1 Hx. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luxz: SNo (u + x * z).
        { aby SNo_add_SNo Hu1 Lxz. }
        claim Lvwxw: SNo (v * w + x * w).
        { aby SNo_add_SNo Lxw Lvw. }
        prove u + x * z < (x + y) * z.
        apply add_SNo_Lt1_cancel (u + x * z) (v * w + x * w) ((x + y) * z)
                                 Luxz Lvwxw Lxyz.
        prove (u + x * z) + v * w + x * w < (x + y) * z + v * w + x * w.
        rewrite add_SNo_com_4_inner_mid u (x * z) (v * w) (x * w) Hu1 Lxz Lvw Lxw.
        prove (u + v * w) + x * z + x * w < (x + y) * z + v * w + x * w.
        apply SNoLeLt_tra ((u + v * w) + x * z + x * w)
                          (v * z + x * z + x * w + y * w)
                          ((x + y) * z + v * w + x * w)
                          (SNo_add_SNo_3 (u + v * w) (x * z) (x * w) Luvw Lxz Lxw)
                          (SNo_add_SNo_4 (v * z) (x * z) (x * w) (y * w) Lvz Lxz Lxw Lyw)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (x * w) Lxyz Lvw Lxw).
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lxz.
        - aby SNoL_SNoS add_SNo_Lt2 add_SNo_com add_SNo_assoc mul_SNo_Lt Lxw Lvz Lxyw Lxv Lvw Hw3 Hw1 Hv3 Hv1 Hw Hv Lxz Lxy IHyz IHz IHy Hz Hy Hx.
      }
    * { let v. assume Hv: v :e SNoR y.
        let w. assume Hw: w :e SNoR z.
        assume Hvw: u + v * w <= v * z + y * w.
        apply SNoR_E y Hy v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoR_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lxv: SNo (x + v).
        { aby SNo_add_SNo Hv1 Hx. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luxz: SNo (u + x * z).
        { aby SNo_add_SNo Hu1 Lxz. }
        claim Lvwxw: SNo (v * w + x * w).
        { aby SNo_add_SNo Lxw Lvw. }
        claim Lvzxw: SNo (v * z + x * w).
        { aby SNo_add_SNo Lxw Lvz. }
        prove u + x * z < (x + y) * z.
        apply add_SNo_Lt1_cancel (u + x * z) (v * w + x * w) ((x + y) * z)
                                 Luxz Lvwxw Lxyz.
        prove (u + x * z) + v * w + x * w < (x + y) * z + v * w + x * w.
        rewrite add_SNo_com_4_inner_mid u (x * z) (v * w) (x * w) Hu1 Lxz Lvw Lxw.
        prove (u + v * w) + x * z + x * w < (x + y) * z + v * w + x * w.
        apply SNoLeLt_tra ((u + v * w) + x * z + x * w)
                          (v * z + x * z + x * w + y * w)
                          ((x + y) * z + v * w + x * w)
                          (SNo_add_SNo_3 (u + v * w) (x * z) (x * w) Luvw Lxz Lxw)
                          (SNo_add_SNo_4 (v * z) (x * z) (x * w) (y * w) Lvz Lxz Lxw Lyw)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (x * w) Lxyz Lvw Lxw).
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lxz.
        - aby SNoR_SNoS add_SNo_Lt2 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Lt Lxw Lvz Lxyw Lxv Lvw Hw3 Hw1 Hv3 Hv1 Hw Hv Lxz Lxyz Lxy IHyz IHz IHy Hz Hy Hx.
      }
- let u'. assume Hu': u' :e R1 :\/: R2. rewrite <- HE.
  prove (x + y) * z < u'.
  apply binunionE R1 R2 u' Hu'.
  + assume Hu': u' :e R1.
    apply ReplE_impred (SNoR (x * z)) (fun w => w + y * z) u' Hu'.
    let u. assume Hu: u :e SNoR (x * z).
    assume Hu'u: u' = u + y * z.
    rewrite Hu'u.
    prove (x + y) * z < u + y * z.
    apply SNoR_E (x * z) Lxz u Hu.
    assume Hu1 Hu2 Hu3.
    apply mul_SNo_SNoR_interpolate_impred x z Hx Hz u Hu.
    * { let v. assume Hv: v :e SNoL x.
        let w. assume Hw: w :e SNoR z.
        assume Hvw: v * z + x * w <= u + v * w.
        apply SNoL_E x Hx v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoR_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lvy: SNo (v + y).
        { aby SNo_add_SNo Hv1 Hy. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luyz: SNo (u + y * z).
        { aby SNo_add_SNo Hu1 Lyz. }
        claim Lvwyw: SNo (v * w + y * w).
        { aby SNo_add_SNo Lyw Lvw. }
        claim Lvzxw: SNo (v * z + x * w).
        { aby SNo_add_SNo Lxw Lvz. }
        prove (x + y) * z < u + y * z.
        apply add_SNo_Lt1_cancel ((x + y) * z) (v * w + y * w) (u + y * z)
                                 Lxyz Lvwyw Luyz.
        prove (x + y) * z + v * w + y * w < (u + y * z) + v * w + y * w.
        rewrite add_SNo_com_4_inner_mid u (y * z) (v * w) (y * w) Hu1 Lyz Lvw Lyw.
        prove (x + y) * z + v * w + y * w < (u + v * w) + y * z + y * w.
        apply SNoLtLe_tra ((x + y) * z + v * w + y * w)
                          (v * z + y * z + x * w + y * w)
                          ((u + v * w) + y * z + y * w)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (y * w) Lxyz Lvw Lyw)
                          (SNo_add_SNo_4 (v * z) (y * z) (x * w) (y * w) Lvz Lyz Lxw Lyw)
                          (SNo_add_SNo_3 (u + v * w) (y * z) (y * w) Luvw Lyz Lyw).
        - aby SNoL_SNoS SNoR_SNoS add_SNo_Lt1 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Lt Lvz Lxyw Lvy Hw3 Hw1 Hv3 Hv1 Hw Hv Lyz Lxyz Lxy IHxz IHz IHx Hz Hy Hx.
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lyz.
      }
    * { let v. assume Hv: v :e SNoR x.
        let w. assume Hw: w :e SNoL z.
        assume Hvw: v * z + x * w <= u + v * w.
        apply SNoR_E x Hx v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoL_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lvy: SNo (v + y).
        { aby SNo_add_SNo Hv1 Hy. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luyz: SNo (u + y * z).
        { aby SNo_add_SNo Hu1 Lyz. }
        claim Lvwyw: SNo (v * w + y * w).
        { aby SNo_add_SNo Lyw Lvw. }
        prove (x + y) * z < u + y * z.
        apply add_SNo_Lt1_cancel ((x + y) * z) (v * w + y * w) (u + y * z)
                                 Lxyz Lvwyw Luyz.
        prove (x + y) * z + v * w + y * w < (u + y * z) + v * w + y * w.
        rewrite add_SNo_com_4_inner_mid u (y * z) (v * w) (y * w) Hu1 Lyz Lvw Lyw.
        aby SNoLtLe_tra SNoL_SNoS SNoR_SNoS SNo_add_SNo SNo_add_SNo_3 SNo_add_SNo_4 add_SNo_Lt1 add_SNo_Le1 add_SNo_assoc add_SNo_com_4_inner_mid mul_SNo_Lt Lyw Lxw Lvz Lxyw Luvw Lvy Lvw Hw3 Hw1 Hv3 Hv1 Hvw Hw Hv Lyz Lxyz Lxy IHxz IHz IHx Hz Hy Hx.
      }
  + assume Hu': u' :e R2.
    apply ReplE_impred (SNoR (y * z)) (fun w => x * z + w) u' Hu'.
    let u. assume Hu: u :e SNoR (y * z).
    assume Hu'u: u' = x * z + u.
    rewrite Hu'u.
    prove (x + y) * z < x * z + u.
    apply SNoR_E (y * z) Lyz u Hu.
    assume Hu1 Hu2 Hu3.
    rewrite add_SNo_com (x * z) u Lxz Hu1.
    prove (x + y) * z < u + x * z.
    apply mul_SNo_SNoR_interpolate_impred y z Hy Hz u Hu.
    * { let v. assume Hv: v :e SNoL y.
        let w. assume Hw: w :e SNoR z.
        assume Hvw: v * z + y * w <= u + v * w.
        apply SNoL_E y Hy v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoR_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lxv: SNo (x + v).
        { aby SNo_add_SNo Hv1 Hx. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luxz: SNo (u + x * z).
        { aby SNo_add_SNo Hu1 Lxz. }
        claim Lvwxw: SNo (v * w + x * w).
        { aby SNo_add_SNo Lxw Lvw. }
        prove (x + y) * z < u + x * z.
        apply add_SNo_Lt1_cancel ((x + y) * z) (v * w + x * w) (u + x * z)
                                 Lxyz Lvwxw Luxz.
        prove (x + y) * z + v * w + x * w < (u + x * z) + v * w + x * w.
        rewrite add_SNo_com_4_inner_mid u (x * z) (v * w) (x * w) Hu1 Lxz Lvw Lxw.
        prove (x + y) * z + v * w + x * w < (u + v * w) + x * z + x * w.
        apply SNoLtLe_tra ((x + y) * z + v * w + x * w)
                          (v * z + x * z + x * w + y * w)
                          ((u + v * w) + x * z + x * w)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (x * w) Lxyz Lvw Lxw)
                          (SNo_add_SNo_4 (v * z) (x * z) (x * w) (y * w) Lvz Lxz Lxw Lyw)
                          (SNo_add_SNo_3 (u + v * w) (x * z) (x * w) Luvw Lxz Lxw).
        - aby SNoL_SNoS SNoR_SNoS add_SNo_Lt2 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Lt Lxw Lvz Lxyw Lxv Lvw Hw3 Hw1 Hv3 Hv1 Hw Hv Lxz Lxyz Lxy IHyz IHz IHy Hz Hy Hx.
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lxz.
      }
    * { let v. assume Hv: v :e SNoR y.
        let w. assume Hw: w :e SNoL z.
        assume Hvw: v * z + y * w <= u + v * w.
        apply SNoR_E y Hy v Hv.
        assume Hv1 Hv2 Hv3.
        apply SNoL_E z Hz w Hw.
        assume Hw1 Hw2 Hw3.
        claim Lvw: SNo (v * w).
        { aby SNo_mul_SNo Hw1 Hv1. }
        claim Lxv: SNo (x + v).
        { aby SNo_add_SNo Hv1 Hx. }
        claim Luvw: SNo (u + v * w).
        { aby SNo_add_SNo Lvw Hu1. }
        claim Lxyw: SNo ((x + y) * w).
        { aby SNo_mul_SNo Hw1 Lxy. }
        claim Lvz: SNo (v * z).
        { aby SNo_mul_SNo Hv1 Hz. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        claim Lyw: SNo (y * w).
        { aby SNo_mul_SNo Hw1 Hy. }
        claim Luxz: SNo (u + x * z).
        { aby SNo_add_SNo Hu1 Lxz. }
        claim Lvwxw: SNo (v * w + x * w).
        { aby SNo_add_SNo Lxw Lvw. }
        claim Lvzxw: SNo (v * z + x * w).
        { aby SNo_add_SNo Lxw Lvz. }
        prove (x + y) * z < u + x * z.
        apply add_SNo_Lt1_cancel ((x + y) * z) (v * w + x * w) (u + x * z)
                                 Lxyz Lvwxw Luxz.
        prove (x + y) * z + v * w + x * w < (u + x * z) + v * w + x * w.
        rewrite add_SNo_com_4_inner_mid u (x * z) (v * w) (x * w) Hu1 Lxz Lvw Lxw.
        prove (x + y) * z + v * w + x * w < (u + v * w) + x * z + x * w.
        apply SNoLtLe_tra ((x + y) * z + v * w + x * w)
                          (v * z + x * z + x * w + y * w)
                          ((u + v * w) + x * z + x * w)
                          (SNo_add_SNo_3 ((x + y) * z) (v * w) (x * w) Lxyz Lvw Lxw)
                          (SNo_add_SNo_4 (v * z) (x * z) (x * w) (y * w) Lvz Lxz Lxw Lyw)
                          (SNo_add_SNo_3 (u + v * w) (x * z) (x * w) Luvw Lxz Lxw).
        - aby SNoL_SNoS SNoR_SNoS add_SNo_Lt2 add_SNo_com add_SNo_assoc SNo_mul_SNo mul_SNo_Lt Lxw Lvz Lxyw Lxv Lvw Hw3 Hw1 Hv3 Hv1 Hw Hv Lxz Lxyz Lxy IHyz IHz IHy Hz Hy Hx.
        - aby SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_assoc add_SNo_com_4_inner_mid Lyw Lxw Lvz Luvw Hvw Lxz.
      }
Qed.

Theorem mul_SNo_distrL : forall x y z, SNo x -> SNo y -> SNo z
  -> x * (y + z) = x * y + x * z.
aby SNo_add_SNo mul_SNo_com mul_SNo_distrR.
Qed.

Section mul_SNo_assoc_lems.
Variable M:set -> set -> set.
Infix * 355 right := M.
Hypothesis SNo_M : forall x y, SNo x -> SNo y -> SNo (x * y).
Hypothesis DL: forall x y z, SNo x -> SNo y -> SNo z -> x * (y + z) = x * y + x * z.
Hypothesis DR: forall x y z, SNo x -> SNo y -> SNo z -> (x + y) * z = x * z + y * z.
Hypothesis IL: forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + v * w <= v * y + x * w -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + v * w <= v * y + x * w -> p)
   -> p.
Hypothesis IR: forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 forall p:prop,
     (forall v :e SNoL x, forall w :e SNoR y, v * y + x * w <= u + v * w -> p)
  -> (forall v :e SNoR x, forall w :e SNoL y, v * y + x * w <= u + v * w -> p)
  -> p.
Hypothesis M_Lt: forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u < x -> v < y -> u * y + x * v < x * y + u * v.
Hypothesis M_Le: forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u <= x -> v <= y -> u * y + x * v <= x * y + u * v.

Theorem mul_SNo_assoc_lem1 : forall x y z, SNo x -> SNo y -> SNo z
 -> (forall u :e SNoS_ (SNoLev x), u * (y * z) = (u * y) * z)
 -> (forall v :e SNoS_ (SNoLev y), x * (v * z) = (x * v) * z)
 -> (forall w :e SNoS_ (SNoLev z), x * (y * w) = (x * y) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), u * (v * z) = (u * v) * z)
 -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), u * (y * w) = (u * y) * w)
 -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), x * (v * w) = (x * v) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), u * (v * w) = (u * v) * w)
 -> forall L,
    (forall u :e L,
     forall q:prop,
         (forall v :e SNoL x, forall w :e SNoL (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> (forall v :e SNoR x, forall w :e SNoR (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> q)
 -> forall u :e L, u < (x * y) * z.
let x y z. assume Hx Hy Hz.
assume IHx IHy IHz IHxy IHxz IHyz IHxyz.
let L. assume HLE.
let u. assume Hu: u :e L.
prove u < (x * y) * z.
claim Lxy: SNo (x * y).
{ aby Hy Hx SNo_M. }
claim Lyz: SNo (y * z).
{ aby Hz Hy SNo_M. }
claim Lxyz2: SNo ((x * y) * z).
{ aby Lxy Hz SNo_M. }
claim L1: forall v :e SNoS_ (SNoLev x),
          forall w, SNo w ->
          forall w1 :e SNoS_ (SNoLev y),
          forall w2 :e SNoS_ (SNoLev z),
        u = v * (y * z) + x * w + - v * w
     -> v * (w1 * z + y * w2) + x * (w + w1 * w2) <= x * (w1 * z + y * w2) + v * (w + w1 * w2)
     -> (v * y + x * w1) * z + (x * y + v * w1) * w2 < (x * y + v * w1) * z + (v * y + x * w1) * w2
     -> u < (x * y) * z.
{ let v. assume Hv. let w. assume Hw. let w1. assume Hw1. let w2. assume Hw2.
  assume Hue H1 H2.
  apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) v Hv.
  assume Hv1 Hv2 Hv3 Hv4.
  apply SNoS_E2 (SNoLev y) (SNoLev_ordinal y Hy) w1 Hw1.
  assume Hw11 Hw12 Hw13 Hw14.
  apply SNoS_E2 (SNoLev z) (SNoLev_ordinal z Hz) w2 Hw2.
  assume Hw21 Hw22 Hw23 Hw24.
  claim Lvyz: SNo (v * (y * z)).
  { aby Hv3 Lyz SNo_M. }
  claim Lxw: SNo (x * w).
  { aby Hw Hx SNo_M. }
  claim Lxw1: SNo (x * w1).
  { aby Hw13 Hx SNo_M. }
  claim Lvw: SNo (v * w).
  { aby Hv3 Hw SNo_M. }
  claim Lvw1: SNo (v * w1).
  { aby Hw13 Hv3 SNo_M. }
  claim Lvy: SNo (v * y).
  { aby Hv3 Hy SNo_M. }
  claim Lw1z: SNo (w1 * z).
  { aby Hw13 Hz SNo_M. }
  claim Lyw2: SNo (y * w2).
  { aby Hw23 Hy SNo_M. }
  claim Lvw1z: SNo (v * (w1 * z)).
  { aby Lw1z Hv3 SNo_M. }
  claim Lvyw2: SNo (v * (y * w2)).
  { aby Lyw2 Hv3 SNo_M. }
  claim Lw1w2: SNo (w1 * w2).
  { aby Hw23 Hw13 SNo_M. }
  claim Lxw1w2: SNo (x * (w1 * w2)).
  { aby Lw1w2 Hx SNo_M. }
  claim Lxw1z: SNo (x * (w1 * z)).
  { aby Lw1z Hx SNo_M. }
  claim Lxyw2: SNo (x * (y * w2)).
  { aby Lyw2 Hx SNo_M. }
  claim Lvyzxw: SNo (v * (y * z) + x * w).
  { aby SNo_add_SNo Lxw Lvyz. }
  claim Lxyzvw: SNo ((x * y) * z + v * w).
  { aby SNo_add_SNo Lvw Lxyz2. }
  claim Lvw1w2: SNo (v * (w1 * w2)).
  { aby Lw1w2 Hv3 SNo_M. }
  claim Lww1w2: SNo (w + w1 * w2).
  { aby SNo_add_SNo Lw1w2 Hw. }
  claim Lvww1w2: SNo (v * (w + w1 * w2)).
  { aby Lww1w2 Hv3 SNo_M. }
  claim Lvw1zyw2: SNo (v * (w1 * z + y * w2)).
  { aby SNo_add_SNo Lyw2 Lw1z Hv3 SNo_M. }
  claim Lvwvw1w2: SNo (v * w + v * (w1 * w2)).
  { aby SNo_add_SNo Lvw1w2 Lvw. }
  claim Lvyzxw1zxyw2vwvw1w2: SNo (v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2)).
  { aby SNo_add_SNo_4 Lvwvw1w2 Lxyw2 Lxw1z Lvyz. }
  claim Lvw1zvyw2xw1w2: SNo (v * (w1 * z) + v * (y * w2) + x * (w1 * w2)).
  { aby SNo_add_SNo_3 Lxw1w2 Lvyw2 Lvw1z. }
  prove u < (x * y) * z.
  rewrite Hue.
  prove (v * (y * z)) + (x * w) + - (v * w) < (x * y) * z.
  apply add_SNo_minus_Lt1b3 (v * (y * z)) (x * w) (v * w) ((x * y) * z) Lvyz Lxw Lvw Lxyz2.
  prove v * (y * z) + x * w < (x * y) * z + v * w.
  apply add_SNo_Lt1_cancel (v * (y * z) + x * w)
                           (v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                           ((x * y) * z + v * w)
                           Lvyzxw
                           Lvw1zvyw2xw1w2
                           Lxyzvw.
  prove (v * (y * z) + x * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
      < ((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
  apply SNoLeLt_tra ((v * (y * z) + x * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                    (v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2))
                    (((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)).
  - aby SNo_add_SNo Lvw1zvyw2xw1w2 Lvyzxw.
  - aby Lvyzxw1zxyw2vwvw1w2.
  - aby SNo_add_SNo Lvw1zvyw2xw1w2 Lxyzvw.
  - aby SNo_add_SNo SNo_add_SNo_4 add_SNo_Le2 add_SNo_assoc add_SNo_com_3_0_1 Lvw1zvyw2xw1w2 Lvw1zyw2 Lvww1w2 Lvw1w2 Lxyw2 Lxw1z Lxw1w2 Lw1w2 Lvyw2 Lvw1z Lyw2 Lw1z Lvw Lxw Lvyz Hv3 H1 Hw Hx DL.
  - prove v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2)
        < ((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
    rewrite add_SNo_com ((x * y) * z) (v * w) Lxyz2 Lvw.
    rewrite <- add_SNo_assoc (v * w) ((x * y) * z) (v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                             Lvw Lxyz2 Lvw1zvyw2xw1w2.
    prove v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2)
        < v * w + (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
    rewrite add_SNo_rotate_5_2 (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) (v * w) (v * (w1 * w2))
                               Lvyz Lxw1z Lxyw2 Lvw Lvw1w2.
    prove v * w + v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < v * w + (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
    apply add_SNo_Lt2 (v * w)
                      (v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2))
                      ((x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                      Lvw
                      (SNo_add_SNo_4 (v * (w1 * w2)) (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) Lvw1w2 Lvyz Lxw1z Lxyw2)
                      (SNo_add_SNo_4 ((x * y) * z) (v * (w1 * z)) (v * (y * w2)) (x * (w1 * w2)) Lxyz2 Lvw1z Lvyw2 Lxw1w2).
    prove v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
    rewrite add_SNo_assoc ((x * y) * z) (v * (w1 * z)) (v * (y * w2) + x * (w1 * w2)) Lxyz2 Lvw1z (SNo_add_SNo (v * (y * w2)) (x * (w1 * w2)) Lvyw2 Lxw1w2).
    prove v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < ((x * y) * z + v * (w1 * z)) + v * (y * w2) + x * (w1 * w2).
    rewrite IHxz v Hv w2 Hw2. rewrite IHyz w1 Hw1 w2 Hw2.
    prove v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < ((x * y) * z + v * (w1 * z)) + (v * y) * w2 + (x * w1) * w2.
    rewrite <- DR (v * y) (x * w1) w2 Lvy Lxw1 Hw23.
    prove v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < ((x * y) * z + v * (w1 * z)) + (v * y + x * w1) * w2.
    rewrite IHxy v Hv w1 Hw1.
    rewrite <- DR (x * y) (v * w1) z Lxy Lvw1 Hz.
    prove v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2)
        < (x * y + v * w1) * z + (v * y + x * w1) * w2.
    rewrite <- add_SNo_rotate_4_1 (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) (v * (w1 * w2)) Lvyz Lxw1z Lxyw2 Lvw1w2.
    prove v * (y * z) + x * (w1 * z) + x * (y * w2) + v * (w1 * w2)
        < (x * y + v * w1) * z + (v * y + x * w1) * w2.
    rewrite add_SNo_assoc (v * (y * z)) (x * (w1 * z)) (x * (y * w2) + v * (w1 * w2))
                          Lvyz Lxw1z (SNo_add_SNo (x * (y * w2)) (v * (w1 * w2)) Lxyw2 Lvw1w2).
    prove (v * (y * z) + x * (w1 * z)) + x * (y * w2) + v * (w1 * w2)
        < (x * y + v * w1) * z + (v * y + x * w1) * w2.
    rewrite IHx v Hv. rewrite IHy w1 Hw1. rewrite IHz w2 Hw2.
    rewrite IHxyz v Hv w1 Hw1 w2 Hw2.
    prove ((v * y) * z + (x * w1) * z) + (x * y) * w2 + (v * w1) * w2
        < (x * y + v * w1) * z + (v * y + x * w1) * w2.
    rewrite <- DR (v * y) (x * w1) z Lvy Lxw1 Hz.
    rewrite <- DR (x * y) (v * w1) w2 Lxy Lvw1 Hw23.
    prove (v * y + x * w1) * z + (x * y + v * w1) * w2
        < (x * y + v * w1) * z + (v * y + x * w1) * w2.
    aby SNo_M DL DR IL IR M_Lt M_Le Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HLE Hu Lxy Lyz Lxyz2 Hv Hw Hw1 Hw2 Hue H1 H2 Hv1 Hv2 Hv3 Hv4 Hw11 Hw12 Hw13 Hw14 Hw21 Hw22 Hw23 Hw24 Lvyz Lxw Lxw1 Lvw Lvw1 Lvy Lw1z Lyw2 Lvw1z Lvyw2 Lw1w2 Lxw1w2 Lxw1z Lxyw2 Lvyzxw Lxyzvw Lvw1w2 Lww1w2 Lvww1w2 Lvw1zyw2 Lvwvw1w2 Lvyzxw1zxyw2vwvw1w2 Lvw1zvyw2xw1w2.
}
apply HLE u Hu.
+ let v. assume Hv: v :e SNoL x.
  let w. assume Hw: w :e SNoL (y * z).
  assume Hue: u = v * (y * z) + x * w + - v * w.
  apply SNoL_E x Hx v Hv.
  assume Hv1 Hv2 Hv3.
  claim Lw: SNo w.
  { aby SNoL_E Hw Lyz. }
  apply IL y z Hy Hz w Hw.
  * aby SNoLtLe SNoL_E SNoL_SNoS SNo_add_SNo Lw Hv3 Hv1 Hue Hv L1 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
  * aby SNoLtLe SNoR_E SNoL_SNoS SNoR_SNoS SNo_add_SNo add_SNo_com Lw Hv3 Hv1 Hue Hv L1 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
+ let v. assume Hv: v :e SNoR x.
  let w. assume Hw: w :e SNoR (y * z).
  assume Hue: u = v * (y * z) + x * w + - v * w.
  apply SNoR_E x Hx v Hv.
  assume Hv1 Hv2 Hv3.
  claim Lw: SNo w.
  { aby SNoR_E Hw Lyz. }
  claim Lvw: SNo (v * w).
  { aby Lw Hv1 SNo_M. }
  apply IR y z Hy Hz w Hw.
  * aby SNoLtLe SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_add_SNo add_SNo_com Lvw Lw Hv3 Hv1 Hue Hv L1 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
  * aby SNoLtLe SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_add_SNo add_SNo_com Lvw Lw Hv3 Hv1 Hue Hv L1 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
Qed.

Theorem mul_SNo_assoc_lem2 : forall x y z, SNo x -> SNo y -> SNo z
 -> (forall u :e SNoS_ (SNoLev x), u * (y * z) = (u * y) * z)
 -> (forall v :e SNoS_ (SNoLev y), x * (v * z) = (x * v) * z)
 -> (forall w :e SNoS_ (SNoLev z), x * (y * w) = (x * y) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), u * (v * z) = (u * v) * z)
 -> (forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), u * (y * w) = (u * y) * w)
 -> (forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), x * (v * w) = (x * v) * w)
 -> (forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), u * (v * w) = (u * v) * w)
 -> forall R,
    (forall u :e R,
     forall q:prop,
         (forall v :e SNoL x, forall w :e SNoR (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> (forall v :e SNoR x, forall w :e SNoL (y * z), u = v * (y * z) + x * w + - v * w -> q)
      -> q)
 -> forall u :e R, (x * y) * z < u.
let x y z. assume Hx Hy Hz.
assume IHx IHy IHz IHxy IHxz IHyz IHxyz.
let R. assume HRE.
let u. assume Hu: u :e R.
prove (x * y) * z < u.
claim Lxy: SNo (x * y).
{ aby Hy Hx SNo_M. }
claim Lyz: SNo (y * z).
{ aby Hz Hy SNo_M. }
claim Lxyz2: SNo ((x * y) * z).
{ aby Lxy Hz SNo_M. }
claim L2: forall v :e SNoS_ (SNoLev x),
          forall w, SNo w ->
          forall w1 :e SNoS_ (SNoLev y),
          forall w2 :e SNoS_ (SNoLev z),
        u = v * (y * z) + x * w + - v * w
     -> x * (w1 * z + y * w2) + v * (w + w1 * w2) <= v * (w1 * z + y * w2) + x * (w + w1 * w2)
     -> (x * y + v * w1) * z + (v * y + x * w1) * w2 < (v * y + x * w1) * z + (x * y + v * w1) * w2
     -> (x * y) * z < u.
{ let v. assume Hv. let w. assume Hw. let w1. assume Hw1. let w2. assume Hw2.
  assume Hue H1 H2.
  apply SNoS_E2 (SNoLev x) (SNoLev_ordinal x Hx) v Hv.
  assume Hv1 Hv2 Hv3 Hv4.
  apply SNoS_E2 (SNoLev y) (SNoLev_ordinal y Hy) w1 Hw1.
  assume Hw11 Hw12 Hw13 Hw14.
  apply SNoS_E2 (SNoLev z) (SNoLev_ordinal z Hz) w2 Hw2.
  assume Hw21 Hw22 Hw23 Hw24.
  claim Lvyz: SNo (v * (y * z)).
  { aby Hv3 Lyz SNo_M. }
  claim Lxw: SNo (x * w).
  { aby Hw Hx SNo_M. }
  claim Lxw1: SNo (x * w1).
  { aby Hw13 Hx SNo_M. }
  claim Lvw: SNo (v * w).
  { aby Hv3 Hw SNo_M. }
  claim Lvw1: SNo (v * w1).
  { aby Hw13 Hv3 SNo_M. }
  claim Lvy: SNo (v * y).
  { aby Hv3 Hy SNo_M. }
  claim Lw1z: SNo (w1 * z).
  { aby Hw13 Hz SNo_M. }
  claim Lyw2: SNo (y * w2).
  { aby Hw23 Hy SNo_M. }
  claim Lvw1z: SNo (v * (w1 * z)).
  { aby Lw1z Hv3 SNo_M. }
  claim Lvyw2: SNo (v * (y * w2)).
  { aby Lyw2 Hv3 SNo_M. }
  claim Lw1w2: SNo (w1 * w2).
  { aby Hw23 Hw13 SNo_M. }
  claim Lxw1w2: SNo (x * (w1 * w2)).
  { aby Lw1w2 Hx SNo_M. }
  claim Lxw1z: SNo (x * (w1 * z)).
  { aby Lw1z Hx SNo_M. }
  claim Lxyw2: SNo (x * (y * w2)).
  { aby Lyw2 Hx SNo_M. }
  claim Lvyzxw: SNo (v * (y * z) + x * w).
  { aby SNo_add_SNo Lxw Lvyz. }
  claim Lxyzvw: SNo ((x * y) * z + v * w).
  { aby SNo_add_SNo Lvw Lxyz2. }
  claim Lvw1w2: SNo (v * (w1 * w2)).
  { aby Lw1w2 Hv3 SNo_M. }
  claim Lww1w2: SNo (w + w1 * w2).
  { aby SNo_add_SNo Lw1w2 Hw. }
  claim Lvww1w2: SNo (v * (w + w1 * w2)).
  { aby Lww1w2 Hv3 SNo_M. }
  claim Lvw1zyw2: SNo (v * (w1 * z + y * w2)).
  { aby SNo_add_SNo Lyw2 Lw1z Hv3 SNo_M. }
  claim Lvwvw1w2: SNo (v * w + v * (w1 * w2)).
  { aby SNo_add_SNo Lvw1w2 Lvw. }
  claim Lvyzxw1zxyw2vwvw1w2: SNo (v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2)).
  { aby SNo_add_SNo_4 Lvwvw1w2 Lxyw2 Lxw1z Lvyz. }
  claim Lvw1zvyw2xw1w2: SNo (v * (w1 * z) + v * (y * w2) + x * (w1 * w2)).
  { aby SNo_add_SNo_3 Lxw1w2 Lvyw2 Lvw1z. }
  rewrite Hue.
  apply add_SNo_minus_Lt2b3 (v * (y * z)) (x * w) (v * w) ((x * y) * z) Lvyz Lxw Lvw Lxyz2.
  prove (x * y) * z + v * w < v * (y * z) + x * w.
  apply add_SNo_Lt1_cancel ((x * y) * z + v * w)
                           (v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                           (v * (y * z) + x * w)
                           Lxyzvw
                           Lvw1zvyw2xw1w2
                           Lvyzxw.
  prove ((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
      < (v * (y * z) + x * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2).
  apply SNoLtLe_tra (((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                    (v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2))
                    ((v * (y * z) + x * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)).
  - aby SNo_add_SNo Lvw1zvyw2xw1w2 Lxyzvw.
  - aby Lvyzxw1zxyw2vwvw1w2.
  - aby SNo_add_SNo Lvw1zvyw2xw1w2 Lvyzxw.
  - prove ((x * y) * z + v * w) + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
        < v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2).
    rewrite add_SNo_com ((x * y) * z) (v * w) Lxyz2 Lvw.
    rewrite <- add_SNo_assoc (v * w) ((x * y) * z) (v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                             Lvw Lxyz2 Lvw1zvyw2xw1w2.
    prove v * w + (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
        < v * (y * z) + x * (w1 * z) + x * (y * w2) + v * w + v * (w1 * w2).
    rewrite add_SNo_rotate_5_2 (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) (v * w) (v * (w1 * w2))
                               Lvyz Lxw1z Lxyw2 Lvw Lvw1w2.
    prove v * w + (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
        < v * w + v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    apply add_SNo_Lt2 (v * w)
                      ((x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2))
                      (v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2))
                      Lvw
                      (SNo_add_SNo_4 ((x * y) * z) (v * (w1 * z)) (v * (y * w2)) (x * (w1 * w2)) Lxyz2 Lvw1z Lvyw2 Lxw1w2)
                      (SNo_add_SNo_4 (v * (w1 * w2)) (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) Lvw1w2 Lvyz Lxw1z Lxyw2).
    prove (x * y) * z + v * (w1 * z) + v * (y * w2) + x * (w1 * w2)
        < v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    rewrite add_SNo_assoc ((x * y) * z) (v * (w1 * z)) (v * (y * w2) + x * (w1 * w2)) Lxyz2 Lvw1z (SNo_add_SNo (v * (y * w2)) (x * (w1 * w2)) Lvyw2 Lxw1w2).
    prove ((x * y) * z + v * (w1 * z)) + v * (y * w2) + x * (w1 * w2)
        < v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    rewrite IHxz v Hv w2 Hw2. rewrite IHyz w1 Hw1 w2 Hw2.
    prove ((x * y) * z + v * (w1 * z)) + (v * y) * w2 + (x * w1) * w2
        < v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    rewrite <- DR (v * y) (x * w1) w2 Lvy Lxw1 Hw23.
    prove ((x * y) * z + v * (w1 * z)) + (v * y + x * w1) * w2
        < v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    rewrite IHxy v Hv w1 Hw1.
    rewrite <- DR (x * y) (v * w1) z Lxy Lvw1 Hz.
    prove (x * y + v * w1) * z + (v * y + x * w1) * w2
        < v * (w1 * w2) + v * (y * z) + x * (w1 * z) + x * (y * w2).
    rewrite <- add_SNo_rotate_4_1 (v * (y * z)) (x * (w1 * z)) (x * (y * w2)) (v * (w1 * w2)) Lvyz Lxw1z Lxyw2 Lvw1w2.
    prove (x * y + v * w1) * z + (v * y + x * w1) * w2
        < v * (y * z) + x * (w1 * z) + x * (y * w2) + v * (w1 * w2).
    rewrite add_SNo_assoc (v * (y * z)) (x * (w1 * z)) (x * (y * w2) + v * (w1 * w2))
                          Lvyz Lxw1z (SNo_add_SNo (x * (y * w2)) (v * (w1 * w2)) Lxyw2 Lvw1w2).
    prove (x * y + v * w1) * z + (v * y + x * w1) * w2
        < (v * (y * z) + x * (w1 * z)) + x * (y * w2) + v * (w1 * w2).
    rewrite IHx v Hv. rewrite IHy w1 Hw1. rewrite IHz w2 Hw2.
    rewrite IHxyz v Hv w1 Hw1 w2 Hw2.
    prove (x * y + v * w1) * z + (v * y + x * w1) * w2
        < ((v * y) * z + (x * w1) * z) + (x * y) * w2 + (v * w1) * w2.
    rewrite <- DR (v * y) (x * w1) z Lvy Lxw1 Hz.
    rewrite <- DR (x * y) (v * w1) w2 Lxy Lvw1 Hw23.
    prove (x * y + v * w1) * z + (v * y + x * w1) * w2
        < (v * y + x * w1) * z + (x * y + v * w1) * w2.
    aby SNo_M DL DR IL IR M_Lt M_Le Hx Hy Hz IHx IHy IHz IHxy IHxz IHyz IHxyz HRE Hu Lxy Lyz Lxyz2 Hv Hw Hw1 Hw2 Hue H1 H2 Hv1 Hv2 Hv3 Hv4 Hw11 Hw12 Hw13 Hw14 Hw21 Hw22 Hw23 Hw24 Lvyz Lxw Lxw1 Lvw Lvw1 Lvy Lw1z Lyw2 Lvw1z Lvyw2 Lw1w2 Lxw1w2 Lxw1z Lxyw2 Lvyzxw Lxyzvw Lvw1w2 Lww1w2 Lvww1w2 Lvw1zyw2 Lvwvw1w2 Lvyzxw1zxyw2vwvw1w2 Lvw1zvyw2xw1w2.
  - aby SNo_add_SNo SNo_add_SNo_4 add_SNo_Le2 add_SNo_assoc add_SNo_com_3_0_1 Lvw1zvyw2xw1w2 Lvw1zyw2 Lvww1w2 Lvw1w2 Lxyw2 Lxw1z Lxw1w2 Lw1w2 Lvyw2 Lvw1z Lyw2 Lw1z Lvw Lxw Lvyz Hv3 H1 Hw Hx DL.
}
apply HRE u Hu.
+ let v. assume Hv: v :e SNoL x.
  let w. assume Hw: w :e SNoR (y * z).
  assume Hue: u = v * (y * z) + x * w + - v * w.
  apply SNoL_E x Hx v Hv.
  assume Hv1 Hv2 Hv3.
  claim Lw: SNo w.
  { aby SNoR_E Hw Lyz. }
  claim Lvw: SNo (v * w).
  { aby Lw Hv1 SNo_M. }
  claim Lvy: SNo (v * y).
  { aby Hv1 Hy SNo_M. }
  apply IR y z Hy Hz w Hw.
  * aby SNoLtLe SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_add_SNo add_SNo_com Lvy Lvw Lw Hv3 Hv1 Hue Hv L2 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
  * aby SNoLtLe SNoL_E SNoR_E SNoL_SNoS SNoR_SNoS SNo_add_SNo add_SNo_com Lw Hv3 Hv1 Hue Hv L2 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
+ let v. assume Hv: v :e SNoR x.
  let w. assume Hw: w :e SNoL (y * z).
  assume Hue: u = v * (y * z) + x * w + - v * w.
  apply SNoR_E x Hx v Hv.
  assume Hv1 Hv2 Hv3.
  claim Lw: SNo w.
  { aby SNoL_E Hw Lyz. }
  claim Lvw: SNo (v * w).
  { aby Lw Hv1 SNo_M SNo_M. }
  apply IL y z Hy Hz w Hw.
  * aby SNoLtLe SNoL_E SNoL_SNoS SNoR_SNoS SNo_add_SNo Lvw Lw Hv3 Hv1 Hue Hv L2 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
  * aby SNoLtLe SNoR_E SNoR_SNoS SNo_add_SNo add_SNo_com Lvw Lw Hv3 Hv1 Hue Hv L2 Lxy Hz Hy Hx M_Le M_Lt SNo_M.
Qed.

End mul_SNo_assoc_lems.

Theorem mul_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z
  -> x * (y * z) = (x * y) * z.
set P : set -> set -> set -> prop := fun x y z => x * (y * z) = (x * y) * z.
prove forall x y z, SNo x -> SNo y -> SNo z -> P x y z.
apply SNoLev_ind3 P.
let x y z. assume Hx Hy Hz.
assume IHx: forall u :e SNoS_ (SNoLev x), u * (y * z) = (u * y) * z.
assume IHy: forall v :e SNoS_ (SNoLev y), x * (v * z) = (x * v) * z.
assume IHz: forall w :e SNoS_ (SNoLev z), x * (y * w) = (x * y) * w.
assume IHxy: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), u * (v * z) = (u * v) * z.
assume IHxz: forall u :e SNoS_ (SNoLev x), forall w :e SNoS_ (SNoLev z), u * (y * w) = (u * y) * w.
assume IHyz: forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), x * (v * w) = (x * v) * w.
assume IHxyz: forall u :e SNoS_ (SNoLev x), forall v :e SNoS_ (SNoLev y), forall w :e SNoS_ (SNoLev z), u * (v * w) = (u * v) * w.
prove x * (y * z) = (x * y) * z.
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy Hx. }
claim Lyz: SNo (y * z).
{ aby SNo_mul_SNo Hz Hy. }
claim Lxyz1: SNo (x * (y * z)).
{ aby SNo_mul_SNo Lyz Hx. }
claim Lxyz2: SNo ((x * y) * z).
{ aby SNo_mul_SNo Lxy Hz. }
apply mul_SNo_eq_3 x (y * z) Hx Lyz.
let L R. assume HLR HLE HLI1 HLI2 HRE HRI1 HRI2.
assume HE: x * (y * z) = SNoCut L R.
apply mul_SNo_eq_3 (x * y) z Lxy Hz.
let L' R'. assume HLR' HLE' HLI1' HLI2' HRE' HRI1' HRI2'.
assume HE': (x * y) * z = SNoCut L' R'.
rewrite HE. rewrite HE'.
prove SNoCut L R = SNoCut L' R'.
claim LIL': forall x y, SNo x -> SNo y -> forall u :e SNoL (y * x),
  forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + w * v <= y * v + w * x -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + w * v <= y * v + w * x -> p)
   -> p.
{ aby SNoL_E SNoR_E add_SNo_com SNo_mul_SNo mul_SNo_SNoL_interpolate_impred. }
claim LIR': forall x y, SNo x -> SNo y -> forall u :e SNoR (y * x),
  forall p:prop,
      (forall v :e SNoL x, forall w :e SNoR y, y * v + w * x <= u + w * v -> p)
   -> (forall v :e SNoR x, forall w :e SNoL y, y * v + w * x <= u + w * v -> p)
   -> p.
{ aby SNoL_E SNoR_E add_SNo_com SNo_mul_SNo mul_SNo_SNoR_interpolate_impred. }
claim LMLt': forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
      -> u < x -> v < y -> y * u + v * x < y * x + v * u.
{ aby add_SNo_com SNo_mul_SNo mul_SNo_Lt. }
claim LMLe': forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
      -> u <= x -> v <= y -> y * u + v * x <= y * x + v * u.
{ aby add_SNo_com SNo_mul_SNo mul_SNo_Le. }
claim LIHx': forall u :e SNoS_ (SNoLev x), (u * y) * z = u * (y * z).
{ aby IHx. }
claim LIHy': forall v :e SNoS_ (SNoLev y), (x * v) * z = x * (v * z).
{ aby IHy. }
claim LIHz': forall w :e SNoS_ (SNoLev z), (x * y) * w = x * (y * w).
{ aby IHz. }
claim LIHyx': forall v :e SNoS_ (SNoLev y), forall u :e SNoS_ (SNoLev x), (u * v) * z = u * (v * z).
{ aby IHxy. }
claim LIHzx': forall w :e SNoS_ (SNoLev z), forall u :e SNoS_ (SNoLev x), (u * y) * w = u * (y * w).
{ aby IHxz. }
claim LIHzy': forall w :e SNoS_ (SNoLev z), forall v :e SNoS_ (SNoLev y), (x * v) * w = x * (v * w).
{ aby IHyz. }
claim LIHzyx': forall w :e SNoS_ (SNoLev z), forall v :e SNoS_ (SNoLev y), forall u :e SNoS_ (SNoLev x), (u * v) * w = u * (v * w).
{ aby IHxyz. }
apply SNoCut_ext.
- aby HLR.
- aby HLR'.
- rewrite <- HE'.
  prove forall u :e L, u < (x * y) * z.
  exact mul_SNo_assoc_lem1 mul_SNo SNo_mul_SNo mul_SNo_distrL mul_SNo_distrR
            mul_SNo_SNoL_interpolate_impred
            mul_SNo_SNoR_interpolate_impred
            mul_SNo_Lt mul_SNo_Le
            x y z Hx Hy Hz
            IHx IHy IHz IHxy IHxz IHyz IHxyz L HLE.
- rewrite <- HE'.
  prove forall u :e R, (x * y) * z < u.
  exact mul_SNo_assoc_lem2 mul_SNo SNo_mul_SNo mul_SNo_distrL mul_SNo_distrR
            mul_SNo_SNoL_interpolate_impred
            mul_SNo_SNoR_interpolate_impred
            mul_SNo_Lt mul_SNo_Le
            x y z Hx Hy Hz
            IHx IHy IHz IHxy IHxz IHyz IHxyz R HRE.
- rewrite <- HE.
  prove forall u :e L', u < x * (y * z).
  apply mul_SNo_assoc_lem1 (fun x y => y * x)
     (fun x y Hx Hy => SNo_mul_SNo y x Hy Hx)
     (fun x y z Hx Hy Hz => mul_SNo_distrR y z x Hy Hz Hx)
     (fun x y z Hx Hy Hz => mul_SNo_distrL z x y Hz Hx Hy)
     LIL' LIR' LMLt' LMLe'
     z y x Hz Hy Hx LIHz' LIHy' LIHx' LIHzy' LIHzx' LIHyx' LIHzyx'.
  aby SNoL_E SNoR_E SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HLE' Lxy Hz.
- rewrite <- HE.
  prove forall u :e R', x * (y * z) < u.
  apply mul_SNo_assoc_lem2 (fun x y => y * x)
     (fun x y Hx Hy => SNo_mul_SNo y x Hy Hx)
     (fun x y z Hx Hy Hz => mul_SNo_distrR y z x Hy Hz Hx)
     (fun x y z Hx Hy Hz => mul_SNo_distrL z x y Hz Hx Hy)
     LIL' LIR' LMLt' LMLe'
     z y x Hz Hy Hx LIHz' LIHy' LIHx' LIHzy' LIHzx' LIHyx' LIHzyx'.
  aby SNoL_E SNoR_E SNo_minus_SNo add_SNo_com_3_0_1 SNo_mul_SNo HRE' Lxy Hz.
Qed.

Theorem mul_nat_mul_SNo : forall n m :e omega, mul_nat n m = n * m.
let n. assume Hn: n :e omega.
claim Ln1: nat_p n.
{ aby omega_nat_p Hn. }
claim Ln2: ordinal n.
{ aby nat_p_ordinal Ln1. }
claim Ln3: SNo n.
{ aby ordinal_SNo Ln2. }
claim L1: forall m, nat_p m -> mul_nat n m = n * m.
{ apply nat_ind.
  - aby mul_nat_0R mul_SNo_zeroR Ln3.
  - aby ordinal_Empty nat_p_ordinal mul_nat_SR mul_nat_p nat_p_omega ordinal_SNo SNo_1 add_SNo_0L add_SNo_ordinal_SL add_nat_add_SNo mul_SNo_oneR mul_SNo_distrL Ln3 Ln1 Hn.
}
aby omega_nat_p L1.
Qed.

Theorem mul_SNo_In_omega : forall n m :e omega, n * m :e omega.
aby mul_nat_p omega_nat_p nat_p_omega mul_nat_mul_SNo.
Qed.

Theorem mul_SNo_zeroL : forall x, SNo x -> 0 * x = 0.
aby SNo_0 mul_SNo_zeroR mul_SNo_com.
Qed.

Theorem mul_SNo_oneL : forall x, SNo x -> 1 * x = x.
aby SNo_1 mul_SNo_oneR mul_SNo_com.
Qed.

Theorem mul_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x * y * z = z * x * y.
aby mul_SNo_com mul_SNo_assoc.
Qed.

Theorem pos_mul_SNo_Lt : forall x y z, SNo x -> 0 < x -> SNo y -> SNo z -> y < z -> x * y < x * z.
aby SNo_0 add_SNo_0L add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroL.
Qed.

Theorem nonneg_mul_SNo_Le : forall x y z, SNo x -> 0 <= x -> SNo y -> SNo z -> y <= z -> x * y <= x * z.
aby SNo_0 add_SNo_0L add_SNo_0R SNo_mul_SNo mul_SNo_Le mul_SNo_zeroL.
Qed.

Theorem neg_mul_SNo_Lt : forall x y z, SNo x -> x < 0 -> SNo y -> SNo z -> z < y -> x * y < x * z.
aby SNo_0 add_SNo_0L add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroL.
Qed.

Theorem pos_mul_SNo_Lt' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < z -> x < y -> x * z < y * z.
aby mul_SNo_com pos_mul_SNo_Lt.
Qed.

Theorem mul_SNo_Lt1_pos_Lt : forall x y, SNo x -> SNo y -> x < 1 -> 0 < y -> x * y < y.
aby SNo_1 mul_SNo_oneL pos_mul_SNo_Lt'.
Qed.

Theorem nonneg_mul_SNo_Le' : forall x y z, SNo x -> SNo y -> SNo z -> 0 <= z -> x <= y -> x * z <= y * z.
aby mul_SNo_com nonneg_mul_SNo_Le.
Qed.

Theorem mul_SNo_Le1_nonneg_Le : forall x y, SNo x -> SNo y -> x <= 1 -> 0 <= y -> x * y <= y.
aby SNo_1 mul_SNo_oneL nonneg_mul_SNo_Le'.
Qed.

Theorem pos_mul_SNo_Lt2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 < x -> 0 < y -> x < z -> y < w -> x * y < z * w.
aby SNoLt_tra SNo_0 SNo_mul_SNo pos_mul_SNo_Lt pos_mul_SNo_Lt'.
Qed.

Theorem nonneg_mul_SNo_Le2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 <= x -> 0 <= y -> x <= z -> y <= w -> x * y <= z * w.
aby SNoLe_tra SNo_0 SNo_mul_SNo nonneg_mul_SNo_Le nonneg_mul_SNo_Le'.
Qed.

Theorem mul_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x * y.
aby SNo_0 add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroR mul_SNo_com.
Qed.

Theorem mul_SNo_pos_neg: forall x y, SNo x -> SNo y -> 0 < x -> y < 0 -> x * y < 0.
aby SNo_0 add_SNo_0L add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroR mul_SNo_com.
Qed.

Theorem mul_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x * y < 0.
aby SNo_0 add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroR mul_SNo_com.
Qed.

Theorem mul_SNo_neg_neg: forall x y, SNo x -> SNo y -> x < 0 -> y < 0 -> 0 < x * y.
aby SNo_0 add_SNo_0L add_SNo_0R SNo_mul_SNo mul_SNo_Lt mul_SNo_zeroR mul_SNo_com.
Qed.

Theorem mul_SNo_nonneg_nonneg: forall x y, SNo x -> SNo y -> 0 <= x -> 0 <= y -> 0 <= x * y.
aby SNoLtLe SNoLeE SNoLe_ref SNo_0 mul_SNo_zeroR mul_SNo_zeroL mul_SNo_pos_pos.
Qed.

Theorem mul_SNo_nonpos_pos: forall x y, SNo x -> SNo y -> x <= 0 -> 0 < y -> x * y <= 0.
aby SNoLtLe SNoLe_ref SNoLe_antisym SNoLtLe_or SNo_0 mul_SNo_zeroL mul_SNo_neg_pos.
Qed.

Theorem mul_SNo_nonpos_neg: forall x y, SNo x -> SNo y -> x <= 0 -> y < 0 -> 0 <= x * y.
aby SNoLtLe SNoLe_ref SNoLe_antisym SNoLtLe_or SNo_0 mul_SNo_zeroL mul_SNo_neg_neg.
Qed.

Theorem nonpos_mul_SNo_Le : forall x y z, SNo x -> x <= 0 -> SNo y -> SNo z -> z <= y -> x * y <= x * z.
aby SNoLtLe SNoLe_ref SNoLe_antisym SNoLtLe_or SNo_0 mul_SNo_zeroL neg_mul_SNo_Lt.
Qed.

Theorem SNo_zero_or_sqr_pos : forall x, SNo x -> x = 0 \/ 0 < x * x.
aby SNoLt_trichotomy_or_impred SNo_0 mul_SNo_pos_pos mul_SNo_neg_neg.
Qed.

Theorem SNo_pos_sqr_uniq: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> x * x = y * y -> x = y.
aby SNoLt_irref SNoLt_trichotomy_or_impred pos_mul_SNo_Lt2.
Qed.

Theorem SNo_nonneg_sqr_uniq: forall x y, SNo x -> SNo y -> 0 <= x -> 0 <= y -> x * x = y * y -> x = y.
aby SNoLeE SNoLt_irref SNo_0 mul_SNo_zeroR SNo_zero_or_sqr_pos SNo_pos_sqr_uniq.
Qed.

Theorem SNo_foil: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y) * (z + w) = x * z + x * w + y * z + y * w.
aby SNo_add_SNo add_SNo_assoc add_SNo_com_4_inner_mid SNo_mul_SNo mul_SNo_distrR mul_SNo_distrL.
Qed.

Theorem mul_SNo_minus_minus: forall x y, SNo x -> SNo y -> (- x) * (- y) = x * y.
aby SNo_minus_SNo minus_SNo_invol SNo_mul_SNo mul_SNo_minus_distrL mul_SNo_minus_distrR.
Qed.

Theorem mul_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x * y * z = y * x * z.
aby mul_SNo_com mul_SNo_assoc.
Qed.

Theorem mul_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x * y) * z = (x * z) * y.
aby mul_SNo_com mul_SNo_assoc.
Qed.

Theorem mul_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x * y) * (z * w) = (x * z) * (y * w).
aby SNo_mul_SNo mul_SNo_assoc mul_SNo_com_3b_1_2.
Qed.

Theorem SNo_foil_mm: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + - y) * (z + - w) = x * z + - x * w + - y * z + y * w.
aby SNo_minus_SNo mul_SNo_minus_distrL mul_SNo_minus_distrR SNo_foil mul_SNo_minus_minus.
Qed.

Theorem mul_SNo_nonzero_cancel: forall x y z, SNo x -> x <> 0 -> SNo y -> SNo z -> x * y = x * z -> y = z.
aby SNoLt_irref SNoLt_trichotomy_or_impred SNo_0 pos_mul_SNo_Lt neg_mul_SNo_Lt.
Qed.

Theorem mul_SNoCutP_lem : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> SNoCutP ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ly}
              :\/:
             {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ry})
            ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ry}
              :\/:
             {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ly})
 /\ x * y
  = SNoCut ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ly}
             :\/:
            {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ry})
           ({w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ry}
             :\/:
            {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ly})
 /\ forall q:prop,
     (forall LxLy' RxRy' LxRy' RxLy',
         (forall u :e LxLy', forall p:prop, (forall w :e Lx, forall w' :e Ly, SNo w -> SNo w' -> w < x -> w' < y -> u = w * y + x * w' + - w * w' -> p) -> p)
      -> (forall w :e Lx, forall w' :e Ly, w * y + x * w' + - w * w' :e LxLy')
      -> (forall u :e RxRy', forall p:prop, (forall z :e Rx, forall z' :e Ry, SNo z -> SNo z' -> x < z -> y < z' -> u = z * y + x * z' + - z * z' -> p) -> p)
      -> (forall z :e Rx, forall z' :e Ry, z * y + x * z' + - z * z' :e RxRy')
      -> (forall u :e LxRy', forall p:prop, (forall w :e Lx, forall z :e Ry, SNo w -> SNo z -> w < x -> y < z -> u = w * y + x * z + - w * z -> p) -> p)
      -> (forall w :e Lx, forall z :e Ry, w * y + x * z + - w * z :e LxRy')
      -> (forall u :e RxLy', forall p:prop, (forall z :e Rx, forall w :e Ly, SNo z -> SNo w -> x < z -> w < y -> u = z * y + x * w + - z * w -> p) -> p)
      -> (forall z :e Rx, forall w :e Ly, z * y + x * w + - z * w :e RxLy')
      -> SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> q)
    -> q.
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
set LxLy' := {w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ly}.
set RxRy' := {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ry}.
set LxRy' := {w 0 * y + x * w 1 + - w 0 * w 1|w :e Lx :*: Ry}.
set RxLy' := {z 0 * y + x * z 1 + - z 0 * z 1|z :e Rx :*: Ly}.
claim LxLy'E: forall u :e LxLy', forall p:prop, (forall w :e Lx, forall w' :e Ly, SNo w -> SNo w' -> w < x -> w' < y -> u = w * y + x * w' + - w * w' -> p) -> p.
{ aby ReplE_impred ap0_Sigma ap1_Sigma Hy3 Hx3 HLRy1 HLRx1. }
claim LxLy'I: forall w :e Lx, forall w' :e Ly, w * y + x * w' + - w * w' :e LxLy'.
{ aby ReplI tuple_2_0_eq tuple_2_1_eq tuple_2_setprod. }
claim RxRy'E: forall u :e RxRy', forall p:prop, (forall z :e Rx, forall z' :e Ry, SNo z -> SNo z' -> x < z -> y < z' -> u = z * y + x * z' + - z * z' -> p) -> p.
{ aby ReplE_impred ap0_Sigma ap1_Sigma Hy4 Hx4 HLRy2 HLRx2. }
claim RxRy'I: forall z :e Rx, forall z' :e Ry, z * y + x * z' + - z * z' :e RxRy'.
{ aby ReplI tuple_2_0_eq tuple_2_1_eq tuple_2_setprod. }
claim LxRy'E: forall u :e LxRy', forall p:prop, (forall w :e Lx, forall z :e Ry, SNo w -> SNo z -> w < x -> y < z -> u = w * y + x * z + - w * z -> p) -> p.
{ aby ReplE_impred ap0_Sigma ap1_Sigma Hy4 Hx3 HLRy2 HLRx1. }
claim LxRy'I: forall w :e Lx, forall z :e Ry, w * y + x * z + - w * z :e LxRy'.
{ aby ReplI tuple_2_0_eq tuple_2_1_eq tuple_2_setprod. }
claim RxLy'E: forall u :e RxLy', forall p:prop, (forall z :e Rx, forall w :e Ly, SNo z -> SNo w -> x < z -> w < y -> u = z * y + x * w + - z * w -> p) -> p.
{ aby ReplE_impred ap0_Sigma ap1_Sigma Hy3 Hx4 HLRy1 HLRx2. }
claim RxLy'I: forall z :e Rx, forall w :e Ly, z * y + x * w + - z * w :e RxLy'.
{ aby ReplI tuple_2_0_eq tuple_2_1_eq tuple_2_setprod. }
claim L1: SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
{ prove (forall w :e LxLy' :\/: RxRy', SNo w)
     /\ (forall z :e LxRy' :\/: RxLy', SNo z)
     /\ (forall w :e LxLy' :\/: RxRy', forall z :e LxRy' :\/: RxLy', w < z).
  apply and3I.
  - aby binunionE' SNo_minus_SNo SNo_add_SNo_3 SNo_mul_SNo RxRy'E LxLy'E Hy1 Hx1.
  - aby binunionE' SNo_minus_SNo SNo_add_SNo_3 SNo_mul_SNo RxLy'E LxRy'E Hy1 Hx1.
  - let w. apply binunionE'.
    + assume Hw: w :e LxLy'.
      apply LxLy'E w Hw.
      let w'. assume Hw': w' :e Lx.
      let w''. assume Hw'': w'' :e Ly.
      assume Hw'1: SNo w'.
      assume Hw''1: SNo w''.
      assume Hw'2: w' < x.
      assume Hw''2: w'' < y.
      assume Hwe. rewrite Hwe.
      let z. apply binunionE'.
      * { assume Hz: z :e LxRy'.
          apply LxRy'E z Hz.
          let w'''. assume Hw''': w''' :e Lx.
          let z'. assume Hz': z' :e Ry.
          assume Hw'''1: SNo w'''.
          assume Hz'1: SNo z'.
          assume Hw'''2: w''' < x.
          assume Hz'2: y < z'.
          assume Hze. rewrite Hze.
          prove w' * y + x * w'' + - w' * w'' < w''' * y + x * z' + - w''' * z'.
          apply add_SNo_minus_Lt12b3 (w' * y) (x * w'') (w' * w'') (w''' * y) (x * z') (w''' * z')
                       (SNo_mul_SNo w' y Hw'1 Hy1)
                       (SNo_mul_SNo x w'' Hx1 Hw''1)
                       (SNo_mul_SNo w' w'' Hw'1 Hw''1)
                       (SNo_mul_SNo w''' y Hw'''1 Hy1)
                       (SNo_mul_SNo x z' Hx1 Hz'1)
                       (SNo_mul_SNo w''' z' Hw'''1 Hz'1).
          prove w' * y + x * w'' + w''' * z' < w''' * y + x * z' + w' * w''.
          apply SNoLt_tra (w' * y + x * w'' + w''' * z')
                          (x * y + w' * w'' + w''' * z')
                          (w''' * y + x * z' + w' * w'')
                          (SNo_add_SNo_3 (w' * y) (x * w'') (w''' * z')
                              (SNo_mul_SNo w' y Hw'1 Hy1)
                              (SNo_mul_SNo x w'' Hx1 Hw''1)
                              (SNo_mul_SNo w''' z' Hw'''1 Hz'1))
                          (SNo_add_SNo_3 (x * y) (w' * w'') (w''' * z')
                              (SNo_mul_SNo x y Hx1 Hy1)
                              (SNo_mul_SNo w' w'' Hw'1 Hw''1)
                              (SNo_mul_SNo w''' z' Hw'''1 Hz'1))
                          (SNo_add_SNo_3 (w''' * y) (x * z') (w' * w'')
                              (SNo_mul_SNo w''' y Hw'''1 Hy1)
                              (SNo_mul_SNo x z' Hx1 Hz'1)
                              (SNo_mul_SNo w' w'' Hw'1 Hw''1)).
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hz'1 Hw'''1 Hw''2 Hw'2 Hw''1 Hw'1 Hy1 Hx1.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hz'2 Hw'''2 Hz'1 Hw'''1 Hw''1 Hw'1 Hy1 Hx1.
        }
      * { assume Hz: z :e RxLy'.
          apply RxLy'E z Hz.
          let z'. assume Hz': z' :e Rx.
          let w'''. assume Hw''': w''' :e Ly.
          assume Hz'1: SNo z'.
          assume Hw'''1: SNo w'''.
          assume Hz'2: x < z'.
          assume Hw'''2: w''' < y.
          assume Hze. rewrite Hze.
          prove w' * y + x * w'' + - w' * w'' < z' * y + x * w''' + - z' * w'''.
          apply add_SNo_minus_Lt12b3 (w' * y) (x * w'') (w' * w'') (z' * y) (x * w''') (z' * w''')
                       (SNo_mul_SNo w' y Hw'1 Hy1)
                       (SNo_mul_SNo x w'' Hx1 Hw''1)
                       (SNo_mul_SNo w' w'' Hw'1 Hw''1)
                       (SNo_mul_SNo z' y Hz'1 Hy1)
                       (SNo_mul_SNo x w''' Hx1 Hw'''1)
                       (SNo_mul_SNo z' w''' Hz'1 Hw'''1).
          prove w' * y + x * w'' + z' * w''' < z' * y + x * w''' + w' * w''.
          apply SNoLt_tra (w' * y + x * w'' + z' * w''')
                          (z' * w''' + x * y + w' * w'')
                          (z' * y + x * w''' + w' * w'')
                          (SNo_add_SNo_3 (w' * y) (x * w'') (z' * w''')
                              (SNo_mul_SNo w' y Hw'1 Hy1)
                              (SNo_mul_SNo x w'' Hx1 Hw''1)
                              (SNo_mul_SNo z' w''' Hz'1 Hw'''1))
                          (SNo_add_SNo_3 (z' * w''') (x * y) (w' * w'')
                              (SNo_mul_SNo z' w''' Hz'1 Hw'''1)
                              (SNo_mul_SNo x y Hx1 Hy1)
                              (SNo_mul_SNo w' w'' Hw'1 Hw''1))
                          (SNo_add_SNo_3 (z' * y) (x * w''') (w' * w'')
                              (SNo_mul_SNo z' y Hz'1 Hy1)
                              (SNo_mul_SNo x w''' Hx1 Hw'''1)
                              (SNo_mul_SNo w' w'' Hw'1 Hw''1)).
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hw'''1 Hz'1 Hw''2 Hw'2 Hw''1 Hw'1 Hy1 Hx1.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hw'''2 Hz'2 Hw'''1 Hz'1 Hw''1 Hw'1 Hy1 Hx1.
        }
    + assume Hw: w :e RxRy'.
      apply RxRy'E w Hw.
      let z'. assume Hz': z' :e Rx.
      let z''. assume Hz'': z'' :e Ry.
      assume Hz'1: SNo z'.
      assume Hz''1: SNo z''.
      assume Hz'2: x < z'.
      assume Hz''2: y < z''.
      assume Hwe. rewrite Hwe.
      let z. apply binunionE'.
      * { assume Hz: z :e LxRy'.
          apply LxRy'E z Hz.
          let w'. assume Hw': w' :e Lx.
          let z'''. assume Hz''': z''' :e Ry.
          assume Hw'1: SNo w'.
          assume Hz'''1: SNo z'''.
          assume Hw'2: w' < x.
          assume Hz'''2: y < z'''.
          assume Hze. rewrite Hze.
          prove z' * y + x * z'' + - z' * z'' < w' * y + x * z''' + - w' * z'''.
          apply add_SNo_minus_Lt12b3 (z' * y) (x * z'') (z' * z'') (w' * y) (x * z''') (w' * z''')
                       (SNo_mul_SNo z' y Hz'1 Hy1)
                       (SNo_mul_SNo x z'' Hx1 Hz''1)
                       (SNo_mul_SNo z' z'' Hz'1 Hz''1)
                       (SNo_mul_SNo w' y Hw'1 Hy1)
                       (SNo_mul_SNo x z''' Hx1 Hz'''1)
                       (SNo_mul_SNo w' z''' Hw'1 Hz'''1).
          prove z' * y + x * z'' + w' * z''' < w' * y + x * z''' + z' * z''.
          apply SNoLt_tra (z' * y + x * z'' + w' * z''')
                          (w' * z''' + z' * z'' + x * y)
                          (w' * y + x * z''' + z' * z'')
                          (SNo_add_SNo_3 (z' * y) (x * z'') (w' * z''')
                              (SNo_mul_SNo z' y Hz'1 Hy1)
                              (SNo_mul_SNo x z'' Hx1 Hz''1)
                              (SNo_mul_SNo w' z''' Hw'1 Hz'''1))
                          (SNo_add_SNo_3 (w' * z''') (z' * z'') (x * y)
                              (SNo_mul_SNo w' z''' Hw'1 Hz'''1)
                              (SNo_mul_SNo z' z'' Hz'1 Hz''1)
                              (SNo_mul_SNo x y Hx1 Hy1))
                          (SNo_add_SNo_3 (w' * y) (x * z''') (z' * z'')
                              (SNo_mul_SNo w' y Hw'1 Hy1)
                              (SNo_mul_SNo x z''' Hx1 Hz'''1)
                              (SNo_mul_SNo z' z'' Hz'1 Hz''1)).
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hz'''1 Hw'1 Hz''2 Hz'2 Hz''1 Hz'1 Hy1 Hx1.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hz'''2 Hw'2 Hz'''1 Hw'1 Hz''1 Hz'1 Hy1 Hx1.
        }
      * { assume Hz: z :e RxLy'.
          apply RxLy'E z Hz.
          let z'''. assume Hz''': z''' :e Rx.
          let w'. assume Hw': w' :e Ly.
          assume Hz'''1: SNo z'''.
          assume Hw'1: SNo w'.
          assume Hz'''2: x < z'''.
          assume Hw'2: w' < y.
          assume Hze. rewrite Hze.
          prove z' * y + x * z'' + - z' * z'' < z''' * y + x * w' + - z''' * w'.
          apply add_SNo_minus_Lt12b3 (z' * y) (x * z'') (z' * z'') (z''' * y) (x * w') (z''' * w')
                       (SNo_mul_SNo z' y Hz'1 Hy1)
                       (SNo_mul_SNo x z'' Hx1 Hz''1)
                       (SNo_mul_SNo z' z'' Hz'1 Hz''1)
                       (SNo_mul_SNo z''' y Hz'''1 Hy1)
                       (SNo_mul_SNo x w' Hx1 Hw'1)
                       (SNo_mul_SNo z''' w' Hz'''1 Hw'1).
          prove z' * y + x * z'' + z''' * w' < z''' * y + x * w' + z' * z''.
          apply SNoLt_tra (z' * y + x * z'' + z''' * w')
                          (z''' * w' + z' * z'' + x * y)
                          (z''' * y + x * w' + z' * z'')        
                          (SNo_add_SNo_3 (z' * y) (x * z'') (z''' * w')
                              (SNo_mul_SNo z' y Hz'1 Hy1)
                              (SNo_mul_SNo x z'' Hx1 Hz''1)
                              (SNo_mul_SNo z''' w' Hz'''1 Hw'1))
                          (SNo_add_SNo_3 (z''' * w') (z' * z'') (x * y)
                              (SNo_mul_SNo z''' w' Hz'''1 Hw'1)
                              (SNo_mul_SNo z' z'' Hz'1 Hz''1)
                              (SNo_mul_SNo x y Hx1 Hy1))
                          (SNo_add_SNo_3 (z''' * y) (x * w') (z' * z'')
                              (SNo_mul_SNo z''' y Hz'''1 Hy1)
                              (SNo_mul_SNo x w' Hx1 Hw'1)
                              (SNo_mul_SNo z' z'' Hz'1 Hz''1)).
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hw'1 Hz'''1 Hz''2 Hz'2 Hz''1 Hz'1 Hy1 Hx1.
          - aby SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_com_3_0_1 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Lt Hw'2 Hz'''2 Hw'1 Hz'''1 Hz''1 Hz'1 Hy1 Hx1.
        }
}
claim Lxyeq: x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
{ set v := SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  apply SNoCutP_SNoCut_impred (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') L1.
  assume Hv1: SNo v.
  assume Hv2: SNoLev v :e ordsucc ((\/_ w :e LxLy' :\/: RxRy', ordsucc (SNoLev w)) :\/: (\/_ z :e LxRy' :\/: RxLy', ordsucc (SNoLev z))).
  assume Hv3: forall w :e LxLy' :\/: RxRy', w < v.
  assume Hv4: forall z :e LxRy' :\/: RxLy', v < z.
  assume Hv5: forall u, SNo u -> (forall w :e LxLy' :\/: RxRy', w < u) -> (forall z :e LxRy' :\/: RxLy', u < z) -> SNoLev v c= SNoLev u /\ SNoEq_ (SNoLev v) v u.
  apply mul_SNo_eq_3 x y Hx1 Hy1.
  let L' R'.
  assume HLR': SNoCutP L' R'.
  assume HL'E: forall u, u :e L' ->
               forall q:prop,
                  (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
               -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
               -> q.
  assume HL'I1: forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L'.
  assume HL'I2: forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L'.
  assume HR'E: forall u, u :e R' ->
               forall q:prop,
                    (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
                 -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
                 -> q.
  assume HR'I1: forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R'.
  assume HR'I2: forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R'.
  assume HLR'eq: x * y = SNoCut L' R'.
  rewrite HLR'eq.
  apply SNoCut_ext L' R' (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  - aby HLR'.
  - aby HLRx HLRy Hxe Hye H HLRx1 HLRx2 HLRx3 H HLRy1 HLRy2 HLRy3 Hx1 Hx2 Hx3 Hx4 Hx5 Hy1 Hy2 Hy3 Hy4 Hy5 LxLy'E LxLy'I RxRy'E RxRy'I LxRy'E LxRy'I RxLy'E RxLy'I L1 Hv1 Hv2 Hv3 Hv4 Hv5 HLR' HL'E HL'I1 HL'I2 HR'E HR'I1 HR'I2 HLR'eq.
  - prove forall w :e L', w < v.
    let w. assume Hw.
    apply HL'E w Hw.
    + let w0. assume Hw0: w0 :e SNoL x.
      let w1. assume Hw1: w1 :e SNoL y.
      assume Hwe. rewrite Hwe.
      prove w0 * y + x * w1 + - w0 * w1 < v.
      apply SNoL_E x Hx1 w0 Hw0.
      assume Hw0a Hw0b Hw0c.
      apply SNoL_E y Hy1 w1 Hw1.
      assume Hw1a Hw1b Hw1c.
      claim L2: exists w0' :e Lx, w0 <= w0'.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hw0c Hw0b Hw0a Hx5 Hx4 Hx1 HLRx2 HLRx1. }
      claim L3: exists w1' :e Ly, w1 <= w1'.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hw1c Hw1b Hw1a Hy5 Hy4 Hy1 HLRy2 HLRy1. }
      apply L2.
      let w0'. assume H. apply H.
      assume Hw0'1: w0' :e Lx.
      assume Hw0'2: w0 <= w0'.
      apply L3.
      let w1'. assume H. apply H.
      assume Hw1'1: w1' :e Ly.
      assume Hw1'2: w1 <= w1'.
      prove w0 * y + x * w1 + - w0 * w1 < v.
      apply SNoLeLt_tra (w0 * y + x * w1 + - w0 * w1)
                        (w0' * y + x * w1' + - w0' * w1')
                        v
                        (SNo_add_SNo_3 (w0 * y) (x * w1) (- w0 * w1)
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_minus_SNo (w0 * w1) (SNo_mul_SNo w0 w1 Hw0a Hw1a)))
                        (SNo_add_SNo_3 (w0' * y) (x * w1') (- w0' * w1')
                           (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_minus_SNo (w0' * w1') (SNo_mul_SNo w0' w1' (HLRx1 w0' Hw0'1) (HLRy1 w1' Hw1'1))))
                        Hv1.
      * { prove w0 * y + x * w1 + - w0 * w1 <= w0' * y + x * w1' + - w0' * w1'.
          apply add_SNo_minus_Le12b3 (w0 * y) (x * w1) (w0 * w1) (w0' * y) (x * w1') (w0' * w1')
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_mul_SNo w0 w1 Hw0a Hw1a)
                           (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo w0' w1' (HLRx1 w0' Hw0'1) (HLRy1 w1' Hw1'1)).
          prove w0 * y + x * w1 + w0' * w1' <= w0' * y + x * w1' + w0 * w1.
          apply SNoLe_tra (w0 * y + x * w1 + w0' * w1')
                          (w0 * y + x * w1' + w0' * w1)
                          (w0' * y + x * w1' + w0 * w1)
                          (SNo_add_SNo_3 (w0 * y) (x * w1) (w0' * w1')
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_mul_SNo w0' w1' (HLRx1 w0' Hw0'1) (HLRy1 w1' Hw1'1)))
                          (SNo_add_SNo_3 (w0 * y) (x * w1') (w0' * w1)
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo w0' w1 (HLRx1 w0' Hw0'1) Hw1a))
                          (SNo_add_SNo_3 (w0' * y) (x * w1') (w0 * w1)
                           (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo w0 w1 Hw0a Hw1a)).
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com SNo_mul_SNo mul_SNo_Le Hw1'2 Hw1'1 Hw0'1 Hw1a Hw0a Hy1 Hx3 Hx1 HLRy1 HLRx1.
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com_3_0_1 SNo_mul_SNo mul_SNo_Le Hw1'1 Hw0'2 Hw0'1 Hw1c Hw1a Hw0a Hy1 Hx1 HLRy1 HLRx1.
        }
      * aby binunionI1 Hw1'1 Hw0'1 Hv3 LxLy'I.
    + let z0. assume Hz0: z0 :e SNoR x.
      let z1. assume Hz1: z1 :e SNoR y.
      assume Hwe. rewrite Hwe.
      prove z0 * y + x * z1 + - z0 * z1 < v.
      apply SNoR_E x Hx1 z0 Hz0.
      assume Hz0a Hz0b Hz0c.
      apply SNoR_E y Hy1 z1 Hz1.
      assume Hz1a Hz1b Hz1c.
      claim L4: exists z0' :e Rx, z0' <= z0.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hz0c Hz0b Hz0a Hx5 Hx3 Hx1 HLRx2 HLRx1. }
      claim L5: exists z1' :e Ry, z1' <= z1.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hz1c Hz1b Hz1a Hy5 Hy3 Hy1 HLRy2 HLRy1. }
      apply L4.
      let z0'. assume H. apply H.
      assume Hz0'1: z0' :e Rx.
      assume Hz0'2: z0' <= z0.
      apply L5.
      let z1'. assume H. apply H.
      assume Hz1'1: z1' :e Ry.
      assume Hz1'2: z1' <= z1.
      prove z0 * y + x * z1 + - z0 * z1 < v.
      apply SNoLeLt_tra (z0 * y + x * z1 + - z0 * z1)
                        (z0' * y + x * z1' + - z0' * z1')
                        v
                        (SNo_add_SNo_3 (z0 * y) (x * z1) (- z0 * z1)
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo x z1 Hx1 Hz1a)
                           (SNo_minus_SNo (z0 * z1) (SNo_mul_SNo z0 z1 Hz0a Hz1a)))
                        (SNo_add_SNo_3 (z0' * y) (x * z1') (- z0' * z1')
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_minus_SNo (z0' * z1') (SNo_mul_SNo z0' z1' (HLRx2 z0' Hz0'1) (HLRy2 z1' Hz1'1))))
                        Hv1.
      * { prove z0 * y + x * z1 + - z0 * z1 <= z0' * y + x * z1' + - z0' * z1'.
          apply add_SNo_minus_Le12b3 (z0 * y) (x * z1) (z0 * z1) (z0' * y) (x * z1') (z0' * z1')
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo x z1 Hx1 Hz1a)
                           (SNo_mul_SNo z0 z1 Hz0a Hz1a)
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo z0' z1' (HLRx2 z0' Hz0'1) (HLRy2 z1' Hz1'1)).
          prove z0 * y + x * z1 + z0' * z1' <= z0' * y + x * z1' + z0 * z1.
          apply SNoLe_tra (z0 * y + x * z1 + z0' * z1')
                          (z0 * y + z0' * z1 + x * z1')
                          (z0' * y + x * z1' + z0 * z1)
                          (SNo_add_SNo_3 (z0 * y) (x * z1) (z0' * z1')
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo x z1 Hx1 Hz1a)
                           (SNo_mul_SNo z0' z1' (HLRx2 z0' Hz0'1) (HLRy2 z1' Hz1'1)))
                          (SNo_add_SNo_3 (z0 * y) (z0' * z1) (x * z1')
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo z0' z1 (HLRx2 z0' Hz0'1) Hz1a)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1)))
                          (SNo_add_SNo_3 (z0' * y) (x * z1') (z0 * z1)
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo z0 z1 Hz0a Hz1a)).
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 SNo_mul_SNo mul_SNo_Le Hz1'2 Hz1'1 Hz0'1 Hz1a Hz0a Hy1 Hx4 Hx1 HLRy2 HLRx2.
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com add_SNo_com_3_0_1 add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Le Hz1'1 Hz0'2 Hz0'1 Hz1c Hz1a Hz0a Hy1 Hx1 HLRy2 HLRx2.
        }
      * aby binunionI2 Hz1'1 Hz0'1 Hv3 RxRy'I.
  - prove forall z :e R', v < z.
    let z. assume Hz.
    apply HR'E z Hz.
    + let w0. assume Hw0: w0 :e SNoL x.
      let z1. assume Hz1: z1 :e SNoR y.
      assume Hze. rewrite Hze.
      prove v < w0 * y + x * z1 + - w0 * z1.
      apply SNoL_E x Hx1 w0 Hw0.
      assume Hw0a Hw0b Hw0c.
      apply SNoR_E y Hy1 z1 Hz1.
      assume Hz1a Hz1b Hz1c.
      claim L6: exists w0' :e Lx, w0 <= w0'.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hw0c Hw0b Hw0a Hx5 Hx4 Hx1 HLRx2 HLRx1. }
      claim L7: exists z1' :e Ry, z1' <= z1.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hz1c Hz1b Hz1a Hy5 Hy3 Hy1 HLRy2 HLRy1. }
      apply L6.
      let w0'. assume H. apply H.
      assume Hw0'1: w0' :e Lx.
      assume Hw0'2: w0 <= w0'.
      apply L7.
      let z1'. assume H. apply H.
      assume Hz1'1: z1' :e Ry.
      assume Hz1'2: z1' <= z1.
      prove v < w0 * y + x * z1 + - w0 * z1.
      apply SNoLtLe_tra v (w0' * y + x * z1' + - w0' * z1') (w0 * y + x * z1 + - w0 * z1)
                        Hv1
                        (SNo_add_SNo_3 (w0' * y) (x * z1') (- w0' * z1')
                                (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                                (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                                (SNo_minus_SNo (w0' * z1') (SNo_mul_SNo w0' z1' (HLRx1 w0' Hw0'1) (HLRy2 z1' Hz1'1))))
                        (SNo_add_SNo_3 (w0 * y) (x * z1) (- w0 * z1)
                                (SNo_mul_SNo w0 y Hw0a Hy1)
                                (SNo_mul_SNo x z1 Hx1 Hz1a)
                                (SNo_minus_SNo (w0 * z1) (SNo_mul_SNo w0 z1 Hw0a Hz1a))).
      * aby binunionI1 Hz1'1 Hw0'1 Hv4 LxRy'I.
      * { prove w0' * y + x * z1' + - w0' * z1' <= w0 * y + x * z1 + - w0 * z1.
          apply add_SNo_minus_Le12b3 (w0' * y) (x * z1') (w0' * z1') (w0 * y) (x * z1) (w0 * z1)
                           (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo w0' z1' (HLRx1 w0' Hw0'1) (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x z1 Hx1 Hz1a)
                           (SNo_mul_SNo w0 z1 Hw0a Hz1a).
          prove w0' * y + x * z1' + w0 * z1 <= w0 * y + x * z1 + w0' * z1'.
          apply SNoLe_tra (w0' * y + x * z1' + w0 * z1)
                          (x * z1' + w0' * z1 + w0 * y)
                          (w0 * y + x * z1 + w0' * z1')
                          (SNo_add_SNo_3 (w0' * y) (x * z1') (w0 * z1)
                           (SNo_mul_SNo w0' y (HLRx1 w0' Hw0'1) Hy1)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo w0 z1 Hw0a Hz1a))
                          (SNo_add_SNo_3 (x * z1') (w0' * z1) (w0 * y)
                           (SNo_mul_SNo x z1' Hx1 (HLRy2 z1' Hz1'1))
                           (SNo_mul_SNo w0' z1 (HLRx1 w0' Hw0'1) Hz1a)
                           (SNo_mul_SNo w0 y Hw0a Hy1))
                          (SNo_add_SNo_3 (w0 * y) (x * z1) (w0' * z1')
                           (SNo_mul_SNo w0 y Hw0a Hy1)
                           (SNo_mul_SNo x z1 Hx1 Hz1a)
                           (SNo_mul_SNo w0' z1' (HLRx1 w0' Hw0'1) (HLRy2 z1' Hz1'1))).
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com add_SNo_com_3_0_1 SNo_mul_SNo mul_SNo_Le Hz1'1 Hw0'2 Hw0'1 Hz1c Hz1a Hw0a Hy1 Hx1 HLRy2 HLRx1.
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_Le Hz1'2 Hz1'1 Hw0'1 Hz1a Hw0a Hy1 Hx3 Hx1 HLRy2 HLRx1.
        }
    + let z0. assume Hz0: z0 :e SNoR x.
      let w1. assume Hw1: w1 :e SNoL y.
      assume Hze. rewrite Hze.
      prove v < z0 * y + x * w1 + - z0 * w1.
      apply SNoR_E x Hx1 z0 Hz0.
      assume Hz0a Hz0b Hz0c.
      apply SNoL_E y Hy1 w1 Hw1.
      assume Hw1a Hw1b Hw1c.
      claim L8: exists z0' :e Rx, z0' <= z0.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hz0c Hz0b Hz0a Hx5 Hx3 Hx1 HLRx2 HLRx1. }
      claim L9: exists w1' :e Ly, w1 <= w1'.
      { aby dneg In_irref SNoLt_tra SNoLtLe_or Hw1c Hw1b Hw1a Hy5 Hy4 Hy1 HLRy2 HLRy1. }
      apply L8.
      let z0'. assume H. apply H.
      assume Hz0'1: z0' :e Rx.
      assume Hz0'2: z0' <= z0.
      apply L9.
      let w1'. assume H. apply H.
      assume Hw1'1: w1' :e Ly.
      assume Hw1'2: w1 <= w1'.
      prove v < z0 * y + x * w1 + - z0 * w1.
      apply SNoLtLe_tra v (z0' * y + x * w1' + - z0' * w1') (z0 * y + x * w1 + - z0 * w1)
                        Hv1
                        (SNo_add_SNo_3 (z0' * y) (x * w1') (- z0' * w1')
                                (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                                (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                                (SNo_minus_SNo (z0' * w1') (SNo_mul_SNo z0' w1' (HLRx2 z0' Hz0'1) (HLRy1 w1' Hw1'1))))
                        (SNo_add_SNo_3 (z0 * y) (x * w1) (- z0 * w1)
                                (SNo_mul_SNo z0 y Hz0a Hy1)
                                (SNo_mul_SNo x w1 Hx1 Hw1a)
                                (SNo_minus_SNo (z0 * w1) (SNo_mul_SNo z0 w1 Hz0a Hw1a))).
      * aby binunionI2 Hw1'1 Hz0'1 Hv4 RxLy'I.
      * { prove z0' * y + x * w1' + - z0' * w1' <= z0 * y + x * w1 + - z0 * w1.
          apply add_SNo_minus_Le12b3 (z0' * y) (x * w1') (z0' * w1') (z0 * y) (x * w1) (z0 * w1)
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo z0' w1' (HLRx2 z0' Hz0'1) (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_mul_SNo z0 w1 Hz0a Hw1a).
          prove z0' * y + x * w1' + z0 * w1 <= z0 * y + x * w1 + z0' * w1'.
          apply SNoLe_tra (z0' * y + x * w1' + z0 * w1)
                          (z0' * y + x * w1 + z0 * w1')
                          (z0 * y + x * w1 + z0' * w1')
                          (SNo_add_SNo_3 (z0' * y) (x * w1') (z0 * w1)
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x w1' Hx1 (HLRy1 w1' Hw1'1))
                           (SNo_mul_SNo z0 w1 Hz0a Hw1a))
                          (SNo_add_SNo_3 (z0' * y) (x * w1) (z0 * w1')
                           (SNo_mul_SNo z0' y (HLRx2 z0' Hz0'1) Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_mul_SNo z0 w1' Hz0a (HLRy1 w1' Hw1'1)))
                          (SNo_add_SNo_3 (z0 * y) (x * w1) (z0' * w1')
                           (SNo_mul_SNo z0 y Hz0a Hy1)
                           (SNo_mul_SNo x w1 Hx1 Hw1a)
                           (SNo_mul_SNo z0' w1' (HLRx2 z0' Hz0'1) (HLRy1 w1' Hw1'1))).
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com SNo_mul_SNo mul_SNo_Le Hw1'2 Hw1'1 Hz0'1 Hw1a Hz0c Hz0a Hy1 Hx1 HLRy1 HLRx2.
          - aby SNoLtLe SNo_add_SNo add_SNo_Le2 add_SNo_com_3_0_1 SNo_mul_SNo mul_SNo_Le Hw1'1 Hz0'2 Hz0'1 Hw1a Hz0a Hy3 Hy1 Hx1 HLRy1 HLRx2.
        }
  - aby binunionE' add_SNo_com add_SNo_minus_Lt1b3 SNo_mul_SNo mul_SNo_Lt HLR'eq RxRy'E LxLy'E Hy1 Hx1.
  - aby binunionE' add_SNo_com add_SNo_minus_Lt2b3 SNo_mul_SNo mul_SNo_Lt HLR'eq RxLy'E LxRy'E Hy1 Hx1.
}
aby and3I Lxyeq L1 RxLy'I RxLy'E LxRy'I LxRy'E RxRy'I RxRy'E LxLy'I LxLy'E.
Qed.

Theorem mul_SNoCut_abs : forall Lx Rx Ly Ry x y,
    SNoCutP Lx Rx
 -> SNoCutP Ly Ry
 -> x = SNoCut Lx Rx
 -> y = SNoCut Ly Ry
 -> forall q:prop,
     (forall LxLy' RxRy' LxRy' RxLy',
         (forall u :e LxLy', forall p:prop, (forall w :e Lx, forall w' :e Ly, SNo w -> SNo w' -> w < x -> w' < y -> u = w * y + x * w' + - w * w' -> p) -> p)
      -> (forall w :e Lx, forall w' :e Ly, w * y + x * w' + - w * w' :e LxLy')
      -> (forall u :e RxRy', forall p:prop, (forall z :e Rx, forall z' :e Ry, SNo z -> SNo z' -> x < z -> y < z' -> u = z * y + x * z' + - z * z' -> p) -> p)
      -> (forall z :e Rx, forall z' :e Ry, z * y + x * z' + - z * z' :e RxRy')
      -> (forall u :e LxRy', forall p:prop, (forall w :e Lx, forall z :e Ry, SNo w -> SNo z -> w < x -> y < z -> u = w * y + x * z + - w * z -> p) -> p)
      -> (forall w :e Lx, forall z :e Ry, w * y + x * z + - w * z :e LxRy')
      -> (forall u :e RxLy', forall p:prop, (forall z :e Rx, forall w :e Ly, SNo z -> SNo w -> x < z -> w < y -> u = z * y + x * w + - z * w -> p) -> p)
      -> (forall z :e Rx, forall w :e Ly, z * y + x * w + - z * w :e RxLy')
      -> SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy')
      -> q)
    -> q.
let Lx Rx Ly Ry x y.
assume HLRx HLRy Hxe Hye.
apply mul_SNoCutP_lem Lx Rx Ly Ry x y HLRx HLRy Hxe Hye.
assume _ H. aby HLRx HLRy Hxe Hye H.
Qed.

Theorem mul_SNo_SNoCut_SNoL_interpolate : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoL (x * y),
 (exists v :e Lx, exists w :e Ly, u + v * w <= v * y + x * w)
 \/
 (exists v :e Rx, exists w :e Ry, u + v * w <= v * y + x * w).
let Lx Rx Ly Ry. assume HLRx HLRy.
let x y. assume Hx Hy.
set P1 : set -> prop :=
  fun u => exists v :e Lx, exists w :e Ly, u + v * w <= v * y + x * w.
set P2 : set -> prop :=
  fun u => exists v :e Rx, exists w :e Ry, u + v * w <= v * y + x * w.
set P : set -> prop := fun u => P1 u \/ P2 u.
apply HLRx. assume H. apply H.
assume HLx HRx HLRx'.
apply HLRy. assume H. apply H.
assume HLy HRy HLRy'.
apply SNoCutP_SNoCut_impred Lx Rx HLRx.
rewrite <- Hx.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc ((\/_ x :e Lx, ordsucc (SNoLev x)) :\/: (\/_ y :e Rx, ordsucc (SNoLev y))).
assume Hx3: forall w :e Lx, w < x.
assume Hx4: forall z :e Rx, x < z.
assume Hx5: forall u, SNo u -> (forall w :e Lx, w < u) -> (forall z :e Rx, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u.
apply SNoCutP_SNoCut_impred Ly Ry HLRy.
rewrite <- Hy.
assume Hy1: SNo y.
assume Hy2: SNoLev y :e ordsucc ((\/_ y :e Ly, ordsucc (SNoLev y)) :\/: (\/_ y :e Ry, ordsucc (SNoLev y))).
assume Hy3: forall w :e Ly, w < y.
assume Hy4: forall z :e Ry, y < z.
assume Hy5: forall u, SNo u -> (forall w :e Ly, w < u) -> (forall z :e Ry, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy1 Hx1. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x * y) -> u < x * y -> P u.
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x * y) -> z < x * y -> P z.
  assume Hu2: SNoLev u :e SNoLev (x * y).
  assume Hu3: u < x * y.
  apply dneg.
  assume HNC: ~P u.
  claim L1: forall v :e Lx, forall w :e Ly, v * y + x * w < u + v * w.
  { aby SNoLtLe_or SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy1 Hx1 HLy HLx. }
  claim L2: forall v :e Rx, forall w :e Ry, v * y + x * w < u + v * w.
  { aby SNoLtLe_or SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy1 Hx1 HRy HRx. }
  apply SNoLt_irref u.
  apply SNoLtLe_tra u (x * y) u Hu1 Lxy Hu1 Hu3.
  prove x * y <= u.
  apply mul_SNoCut_abs Lx Rx Ly Ry x y HLRx HLRy Hx Hy.
  let LxLy' RxRy' LxRy' RxLy'.
  assume LxLy'E LxLy'I RxRy'E RxRy'I LxRy'E LxRy'I RxLy'E RxLy'I.
  assume HSC: SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  assume HE: x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  rewrite HE.
  prove SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') <= u.
  rewrite SNo_eta u Hu1.
  prove SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') <= SNoCut (SNoL u) (SNoR u).
  apply SNoCut_Le (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') (SNoL u) (SNoR u) HSC (SNoCutP_SNoL_SNoR u Hu1).
  - aby binunionE' SNoLtLe_or SNo_eta SNo_add_SNo add_SNo_minus_Lt1b3 SNo_mul_SNo RxRy'E LxLy'E HNC Hu1 Hy1 Hx1.
  - prove forall z :e SNoR u, SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') < z.
    let z. assume Hz: z :e SNoR u.
    rewrite <- HE.
    prove x * y < z.
    apply SNoR_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: u < z.
    apply SNoLt_trichotomy_or_impred z (x * y) Hz1 Lxy.
    + assume H1: z < x * y.
      claim LPz: P z.
      { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 H1 Hz2 Hz1 Hu2 IH Hu1 Lxy. }
      aby SNoLt_irref SNoLt_tra SNoLeLt_tra SNo_add_SNo add_SNo_Lt1_cancel SNo_mul_SNo LPz Hz3 Hz1 L2 L1 Hu1 Hy1 Hx1 HRy HLy HRx HLx.
    + aby In_no2cycle Hz2 Hu2.
    + aby.
}
aby SNoL_E LI Lxy.
Qed.

Theorem mul_SNo_SNoCut_SNoL_interpolate_impred : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoL (x * y),
    forall p:prop,
        (forall v :e Lx, forall w :e Ly, u + v * w <= v * y + x * w -> p)
     -> (forall v :e Rx, forall w :e Ry, u + v * w <= v * y + x * w -> p)
     -> p.
aby mul_SNo_SNoCut_SNoL_interpolate.
Qed.

Theorem mul_SNo_SNoCut_SNoR_interpolate : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoR (x * y),
 (exists v :e Lx, exists w :e Ry, v * y + x * w <= u + v * w)
 \/
 (exists v :e Rx, exists w :e Ly, v * y + x * w <= u + v * w).
let Lx Rx Ly Ry. assume HLRx HLRy.
let x y. assume Hx Hy.
set P1 : set -> prop :=
  fun u => exists v :e Lx, exists w :e Ry, v * y + x * w <= u + v * w.
set P2 : set -> prop :=
  fun u => exists v :e Rx, exists w :e Ly, v * y + x * w <= u + v * w.
set P : set -> prop := fun u => P1 u \/ P2 u.
apply HLRx. assume H. apply H.
assume HLx HRx HLRx'.
apply HLRy. assume H. apply H.
assume HLy HRy HLRy'.
apply SNoCutP_SNoCut_impred Lx Rx HLRx.
rewrite <- Hx.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc ((\/_ x :e Lx, ordsucc (SNoLev x)) :\/: (\/_ y :e Rx, ordsucc (SNoLev y))).
assume Hx3: forall w :e Lx, w < x.
assume Hx4: forall z :e Rx, x < z.
assume Hx5: forall u, SNo u -> (forall w :e Lx, w < u) -> (forall z :e Rx, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u.
apply SNoCutP_SNoCut_impred Ly Ry HLRy.
rewrite <- Hy.
assume Hy1: SNo y.
assume Hy2: SNoLev y :e ordsucc ((\/_ y :e Ly, ordsucc (SNoLev y)) :\/: (\/_ y :e Ry, ordsucc (SNoLev y))).
assume Hy3: forall w :e Ly, w < y.
assume Hy4: forall z :e Ry, y < z.
assume Hy5: forall u, SNo u -> (forall w :e Ly, w < u) -> (forall z :e Ry, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy1 Hx1. }
claim LI: forall u, SNo u -> SNoLev u :e SNoLev (x * y) -> x * y < u -> P u.
{ apply SNoLev_ind.
  let u.
  assume Hu1: SNo u.
  assume IH: forall z :e SNoS_ (SNoLev u), SNoLev z :e SNoLev (x * y) -> x * y < z -> P z.
  assume Hu2: SNoLev u :e SNoLev (x * y).
  assume Hu3: x * y < u.
  apply dneg.
  assume HNC: ~P u.
  claim L1: forall v :e Lx, forall w :e Ry, u + v * w < v * y + x * w.
  { aby SNoLtLe_or SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy1 Hx1 HRy HLx. }
  claim L2: forall v :e Rx, forall w :e Ly, u + v * w < v * y + x * w.
  { aby SNoLtLe_or SNo_add_SNo SNo_mul_SNo HNC Hu1 Hy1 Hx1 HLy HRx. }
  apply SNoLt_irref (x * y).
  apply SNoLtLe_tra (x * y) u (x * y) Lxy Hu1 Lxy Hu3.
  prove u <= x * y.
  apply mul_SNoCut_abs Lx Rx Ly Ry x y HLRx HLRy Hx Hy.
  let LxLy' RxRy' LxRy' RxLy'.
  assume LxLy'E LxLy'I RxRy'E RxRy'I LxRy'E LxRy'I RxLy'E RxLy'I.
  assume HSC: SNoCutP (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  assume HE: x * y = SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  rewrite HE.
  prove u <= SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  rewrite SNo_eta u Hu1.
  prove SNoCut (SNoL u) (SNoR u) <= SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
  apply SNoCut_Le (SNoL u) (SNoR u) (LxLy' :\/: RxRy') (LxRy' :\/: RxLy') (SNoCutP_SNoL_SNoR u Hu1) HSC.
  - prove forall z :e SNoL u, z < SNoCut (LxLy' :\/: RxRy') (LxRy' :\/: RxLy').
    let z. assume Hz: z :e SNoL u.
    rewrite <- HE.
    prove z < x * y.
    apply SNoL_E u Hu1 z Hz.
    assume Hz1: SNo z.
    assume Hz2: SNoLev z :e SNoLev u.
    assume Hz3: z < u.
    apply SNoLt_trichotomy_or_impred (x * y) z Lxy Hz1.
    + assume H1: x * y < z.
      claim LPz: P z.
      { aby ordinal_TransSet SNoLev_ordinal SNoS_I2 H1 Hz2 Hz1 Hu2 IH Hu1 Lxy. }
      aby SNoLt_irref SNoLt_tra SNoLtLe_tra SNo_add_SNo add_SNo_Lt1_cancel SNo_mul_SNo LPz Hz3 Hz1 L2 L1 Hu1 Hy1 Hx1 HRy HLy HRx HLx.
    + aby In_no2cycle Hz2 Hu2.
    + aby.
  - aby binunionE' SNoLtLe_or SNo_eta SNo_add_SNo add_SNo_minus_Lt2b3 SNo_mul_SNo RxLy'E LxRy'E HNC Hu1 Hy1 Hx1.
}
aby SNoR_E LI Lxy.
Qed.

Theorem mul_SNo_SNoCut_SNoR_interpolate_impred : forall Lx Rx Ly Ry,
    SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> forall x y, x = SNoCut Lx Rx -> y = SNoCut Ly Ry
 -> forall u :e SNoR (x * y),
    forall p:prop,
        (forall v :e Lx, forall w :e Ry, v * y + x * w <= u + v * w -> p)
     -> (forall v :e Rx, forall w :e Ly, v * y + x * w <= u + v * w -> p)
     -> p.
aby mul_SNo_SNoCut_SNoR_interpolate.
Qed.

Theorem nonpos_nonneg_0 : forall m n :e omega, m = - n -> m = 0 /\ n = 0.
aby Subq_Empty nat_0_in_ordsucc nat_inv ordinal_Empty nat_p_ordinal omega_nat_p SNoLt_irref SNoLeLt_tra omega_SNo ordinal_In_SNoLt ordinal_Subq_SNoLe SNo_0 minus_SNo_Lt_contra1 minus_SNo_0.
Qed.

Theorem mul_minus_SNo_distrR: forall x y, SNo x -> SNo y -> x * (- y) = - (x * y).
aby SNo_minus_SNo mul_SNo_com mul_SNo_minus_distrL.
Qed.

End SurrealMul.

Opaque mul_SNo.

Section Int.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Definition int : set := omega :\/: {- n|n :e omega}.

Theorem int_SNo_cases : forall p:set -> prop,
    (forall n :e omega, p n)
 -> (forall n :e omega, p (- n))
 -> forall x :e int, p x.
aby ReplE_impred binunionE.
Qed.

Theorem int_3_cases: forall n :e int, forall p:prop,
    (forall m :e omega, n = - ordsucc m -> p)
 -> (n = 0 -> p)
 -> (forall m :e omega, n = ordsucc m -> p)
 -> p.
aby nat_inv_impred omega_nat_p nat_p_omega minus_SNo_0 int_SNo_cases.
Qed.

Theorem int_SNo : forall x :e int, SNo x.
aby omega_SNo SNo_minus_SNo int_SNo_cases.
Qed.

Theorem Subq_omega_int : omega c= int.
aby binunionI1.
Qed.

Theorem int_minus_SNo_omega : forall n :e omega, - n :e int.
aby ReplI binunionI2.
Qed.

Theorem int_add_SNo_lem: forall n :e omega, forall m, nat_p m -> - n + m :e int.
let n. assume Hn.
claim Lnn: nat_p n.
{ aby omega_nat_p Hn. }
claim Lno: ordinal n.
{ aby nat_p_ordinal Lnn. }
claim LnS: SNo n.
{ aby ordinal_SNo Lno. }
apply nat_ind.
- aby SNo_minus_SNo add_SNo_0R int_minus_SNo_omega LnS Hn.
- let m. assume Hm: nat_p m.
  assume IHm: - n + m :e int.
  claim Lmo: ordinal m.
  { aby nat_p_ordinal Hm. }
  claim LmS: SNo m.
  { aby ordinal_SNo Lmo. }
  prove - n + ordsucc m :e int.
  rewrite ordinal_ordsucc_SNo_eq m Lmo.
  prove - n + (1 + m) :e int.
  rewrite add_SNo_com_3_0_1 (- n) 1 m (SNo_minus_SNo n LnS) SNo_1 LmS.
  prove 1 + (- n + m) :e int.
  claim L1: forall k :e omega, - n + m = k -> 1 + (- n + m) :e int.
  { aby nat_p_ordinal omega_nat_p omega_ordsucc ordinal_ordsucc_SNo_eq Subq_omega_int. }
  claim L2: forall k :e omega, - n + m = - k -> 1 + (- n + m) :e int.
  { aby nat_1 nat_inv nat_p_ordinal omega_nat_p nat_p_omega ordinal_SNo SNo_1 SNo_minus_SNo add_SNo_0R add_SNo_minus_L2' minus_SNo_0 minus_add_SNo_distr add_SNo_minus_SNo_prop2 ordinal_ordsucc_SNo_eq Subq_omega_int int_minus_SNo_omega. }
  aby int_SNo_cases L2 L1 IHm.
Qed.

Theorem int_add_SNo: forall x y :e int, x + y :e int.
apply int_SNo_cases.
- aby nat_p_ordinal omega_nat_p ordinal_SNo SNo_minus_SNo add_SNo_com add_SNo_In_omega int_SNo_cases Subq_omega_int int_add_SNo_lem.
- aby nat_p_ordinal omega_nat_p ordinal_SNo add_SNo_In_omega minus_add_SNo_distr int_SNo_cases int_minus_SNo_omega int_add_SNo_lem.
Qed.

Theorem int_minus_SNo: forall x :e int, - x :e int.
aby nat_p_ordinal omega_nat_p ordinal_SNo minus_SNo_invol int_SNo_cases Subq_omega_int int_minus_SNo_omega.
Qed.

Theorem int_mul_SNo: forall x y :e int, x * y :e int.
apply int_SNo_cases.
- let n. assume Hn: n :e omega.
  claim Lnn: nat_p n.
  { aby omega_nat_p Hn. }
  claim Lno: ordinal n.
  { aby nat_p_ordinal Lnn. }
  claim LnS: SNo n.
  { aby ordinal_SNo Lno. }
  apply int_SNo_cases.
  + aby mul_SNo_In_omega Subq_omega_int Hn.
  + aby nat_p_ordinal omega_nat_p ordinal_SNo SNo_minus_SNo mul_SNo_com mul_SNo_minus_distrL mul_SNo_In_omega Subq_omega_int int_minus_SNo LnS Hn.
- let n. assume Hn: n :e omega.
  claim Lnn: nat_p n.
  { aby omega_nat_p Hn. }
  claim Lno: ordinal n.
  { aby nat_p_ordinal Lnn. }
  claim LnS: SNo n.
  { aby ordinal_SNo Lno. }
  apply int_SNo_cases.
  + aby nat_p_ordinal omega_nat_p ordinal_SNo mul_SNo_minus_distrL mul_SNo_In_omega Subq_omega_int int_minus_SNo LnS Hn.
  + aby nat_p_ordinal omega_nat_p ordinal_SNo SNo_minus_SNo minus_SNo_invol SNo_mul_SNo mul_SNo_com mul_SNo_minus_distrL mul_SNo_In_omega Subq_omega_int LnS Hn.
Qed.

Theorem nonneg_int_nat_p: forall n :e int, 0 <= n -> nat_p n.
aby Subq_Empty nat_0 ordinal_Empty nat_p_ordinal omega_nat_p SNoLe_antisym omega_SNo ordinal_Subq_SNoLe SNo_0 SNo_minus_SNo minus_SNo_Le_contra minus_SNo_invol minus_SNo_0 int_SNo_cases.
Qed.

End Int.

Section BezoutAndGCD.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Theorem quotient_remainder_nat: forall n :e omega :\: {0}, forall m, nat_p m -> exists q :e omega, exists r :e n, m = q * n + r.
let n. assume Hn.
apply setminusE omega {0} n Hn.
assume Hn1: n :e omega.
assume Hn2: n /:e {0}.
claim LnN: nat_p n.
{ aby omega_nat_p Hn1. }
claim Lno: ordinal n.
{ aby nat_p_ordinal LnN. }
claim L0n: 0 :e n.
{ aby Empty_Subq_eq SingI ordinal_Empty ordinal_In_Or_Subq Lno Hn2. }
apply nat_ind.
- aby nat_0 add_nat_0R mul_nat_0L nat_p_omega L0n LnN.
- aby In_irref nat_p_trans ordinal_ordsucc nat_p_ordinal ordinal_ordsucc_In_Subq ordinal_trichotomy_or_impred add_nat_0R add_nat_SR mul_nat_SL omega_nat_p omega_ordsucc L0n Lno LnN.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.

Theorem mul_SNo_nonpos_nonneg: forall x y, SNo x -> SNo y -> x <= 0 -> 0 <= y -> x * y <= 0.
aby SNoLeE SNoLe_ref SNo_0 mul_SNo_zeroR mul_SNo_nonpos_pos.
Qed.

Theorem ordinal_0_In_ordsucc: forall alpha, ordinal alpha -> 0 :e ordsucc alpha.
aby EmptyE ordsuccI2 ordinal_Empty ordinal_ordsucc ordinal_In_Or_Subq.
Qed.

Theorem ordinal_ordsucc_pos: forall alpha, ordinal alpha -> 0 < ordsucc alpha.
aby ordinal_ordsucc ordinal_In_SNoLt ordinal_0_In_ordsucc.
Qed.

Theorem quotient_remainder_int: forall n :e omega :\: {0}, forall m :e int, exists q :e int, exists r :e n, m = q * n + r.
let n. assume Hn.
apply setminusE omega {0} n Hn.
assume Hn1: n :e omega.
assume Hn2: n /:e {0}.
claim LnN: nat_p n.
{ aby omega_nat_p Hn1. }
claim Lno: ordinal n.
{ aby nat_p_ordinal LnN. }
claim L0n: 0 :e n.
{ aby Empty_Subq_eq SingI ordinal_Empty ordinal_In_Or_Subq Lno Hn2. }
apply int_SNo_cases.
- aby nat_p_trans mul_nat_p omega_nat_p nat_p_omega add_nat_add_SNo mul_nat_mul_SNo Subq_omega_int quotient_remainder_nat LnN Hn1 Hn.
- let m. assume Hm: m :e omega.
  prove exists q :e int, exists r :e n, - m = q * n + r.
  apply quotient_remainder_nat n Hn m (omega_nat_p m Hm).
  let q. assume H. apply H.
  assume Hq: q :e omega. assume H. apply H.
  let r. assume H. apply H.
  assume Hr: r :e n.
  assume H1: m = add_nat (mul_nat q n) r.
  claim LqN: nat_p q.
  { aby omega_nat_p Hq. }
  claim LqS: SNo q.
  { aby nat_p_SNo LqN. }
  claim LrN: nat_p r.
  { aby nat_p_trans Hr LnN. }
  claim LrS: SNo r.
  { aby nat_p_SNo LrN. }
  claim LnS: SNo n.
  { aby nat_p_SNo LnN. }
  claim LqnS: SNo (q * n).
  { aby SNo_mul_SNo LnS LqS. }
  claim L2: m = q * n + r.
  { transitivity mul_nat q n + r.
    - aby mul_nat_p nat_p_omega add_nat_add_SNo LrN LqN H1 LnN.
    - aby mul_nat_mul_SNo Hq Hn1.
  }
  claim L3: 0 <= r.
  { aby nat_p_omega omega_nonneg LrN. }
  apply SNoLeE 0 r SNo_0 LrS L3.
  + assume H2: 0 < r.
    claim L4: n + - r :e n.
    { aby nat_p_ordinal nat_p_omega SNoLtLe ordinal_In_SNoLt ordinal_SNoLt_In SNo_0 add_SNo_Lt2 add_SNo_0L add_SNo_0R add_SNo_minus_Lt1b add_SNo_minus_Le2b Subq_omega_int int_add_SNo int_minus_SNo nonneg_int_nat_p H2 LnS LrS LrN Hr Lno Hn1. }
    witness (- q + - 1). apply andI.
    * { apply int_add_SNo.
        - apply int_minus_SNo_omega. aby Hn Hn1 Hn2 LnN Lno L0n Hm H Hq H H Hr H1 LqN LqS LrN LrS LnS LqnS L2 L3 H2 L4.
        - apply int_minus_SNo_omega. apply nat_p_omega. aby nat_1 Hn Hn1 Hn2 LnN Lno L0n Hm H Hq H H Hr H1 LqN LqS LrN LrS LnS LqnS L2 L3 H2 L4.
      }
    * { witness (n + - r). apply andI.
        - aby Hn Hn1 Hn2 LnN Lno L0n Hm H Hq H H Hr H1 LqN LqS LrN LrS LnS LqnS L2 L3 H2 L4.
        - prove - m = (- q + - 1) * n + (n + - r).
          rewrite mul_SNo_distrR (- q) (- 1) n (SNo_minus_SNo q LqS) (SNo_minus_SNo 1 SNo_1) LnS.
          prove - m = ((- q) * n + (- 1) * n) + (n + - r).
          rewrite mul_SNo_minus_distrL 1 n SNo_1 LnS.
          rewrite mul_SNo_minus_distrL q n LqS LnS.
          prove - m = (- q * n + - 1 * n) + (n + - r).
          rewrite mul_SNo_oneL n LnS.
          prove - m = (- q * n + - n) + (n + - r).
          rewrite <- add_SNo_assoc (- q * n) (- n) (n + - r) (SNo_minus_SNo (q * n) LqnS) (SNo_minus_SNo n LnS) (SNo_add_SNo n (- r) LnS (SNo_minus_SNo r LrS)).
          prove - m = - q * n + - n + n + - r.
          rewrite add_SNo_minus_L2 n (- r) LnS (SNo_minus_SNo r LrS).
          prove - m = - q * n + - r.
          rewrite <- minus_add_SNo_distr (q * n) r LqnS LrS.
          aby Hn Hn1 Hn2 LnN Lno L0n Hm H Hq H H Hr H1 LqN LqS LrN LrS LnS LqnS L2 L3 H2 L4.
      }
  + aby SNo_minus_SNo add_SNo_0R mul_SNo_minus_distrL int_minus_SNo_omega L2 LqnS LnS LqS Hq L0n.
Qed.

Definition divides_int : set -> set -> prop := fun m n => m :e int /\ n :e int /\ exists k :e int, m * k = n.

Theorem divides_int_ref: forall n :e int, divides_int n n.
aby and3I nat_1 nat_p_omega mul_SNo_oneR int_SNo Subq_omega_int.
Qed.

Theorem divides_int_0: forall n :e int, divides_int n 0.
aby and3I nat_0 nat_p_omega mul_SNo_zeroR int_SNo Subq_omega_int.
Qed.

Theorem divides_int_add_SNo: forall m n k, divides_int m n -> divides_int m k -> divides_int m (n + k).
aby and3I mul_SNo_distrL int_SNo int_add_SNo.
Qed.

Theorem divides_int_mul_SNo: forall m n m' n', divides_int m m' -> divides_int n n' -> divides_int (m * n) (m' * n').
aby and3I mul_SNo_com_4_inner_mid int_SNo int_mul_SNo.
Qed.

Theorem divides_nat_divides_int: forall m n, divides_nat m n -> divides_int m n.
aby and3I mul_nat_mul_SNo Subq_omega_int.
Qed.

Theorem divides_int_divides_nat: forall m n :e omega, divides_int m n -> divides_nat m n.
aby xm and3I ReplE_impred binunionE nat_0 mul_nat_0R nat_p_omega omega_SNo mul_SNo_minus_distrR mul_nat_mul_SNo mul_SNo_In_omega nonpos_nonneg_0 mul_minus_SNo_distrR.
Qed.

Theorem divides_int_minus_SNo: forall m n, divides_int m n -> divides_int m (- n).
aby and3I mul_SNo_minus_distrR mul_minus_SNo_distrR int_SNo int_minus_SNo.
Qed.

Theorem divides_int_mul_SNo_L: forall m n, forall k :e int, divides_int m n -> divides_int m (n * k).
aby and3I mul_SNo_assoc int_SNo int_mul_SNo.
Qed.

Theorem divides_int_mul_SNo_R: forall m n, forall k :e int, divides_int m n -> divides_int m (k * n).
aby mul_SNo_com int_SNo divides_int_mul_SNo_L.
Qed.

Theorem divides_int_1: forall n :e int, divides_int 1 n.
aby and3I nat_1 nat_p_omega mul_SNo_oneL int_SNo Subq_omega_int.
Qed.

Theorem divides_int_pos_Le: forall m n, divides_int m n -> 0 < n -> m <= n.
aby ordinal_Empty ordinal_ordsucc nat_p_ordinal ordinal_ordsucc_In_Subq SNoLtLe SNoLt_irref SNoLtLe_tra SNoLeLt_tra SNoLe_tra SNoLtLe_or omega_SNo ordinal_Subq_SNoLe ordinal_SNoLt_In omega_nonneg SNo_0 SNo_1 SNo_minus_SNo minus_SNo_Le_contra minus_SNo_0 SNo_mul_SNo mul_SNo_oneR mul_SNo_com nonneg_mul_SNo_Le int_SNo_cases int_SNo nonneg_int_nat_p mul_SNo_nonpos_nonneg.
Qed.

Definition gcd_reln : set -> set -> set -> prop := fun m n d => divides_int d m /\ divides_int d n /\ forall d', divides_int d' m -> divides_int d' n -> d' <= d.

Theorem gcd_reln_uniq: forall a b c d, gcd_reln a b c -> gcd_reln a b d -> c = d.
aby SNoLe_antisym int_SNo.
Qed.

Definition int_lin_comb : set -> set -> set -> prop := fun a b c => a :e int /\ b :e int /\ c :e int /\ exists m n :e int, m * a + n * b = c.

Theorem int_lin_comb_I: forall a b c :e int, (exists m n :e int, m * a + n * b = c) -> int_lin_comb a b c.
aby and4I.
Qed.

Theorem int_lin_comb_E: forall a b c, int_lin_comb a b c ->
  forall p:prop,
       (a :e int -> b :e int -> c :e int -> forall m n :e int, m * a + n * b = c -> p)
    -> p.
aby.
Qed.

Theorem int_lin_comb_E1: forall a b c, int_lin_comb a b c -> a :e int.
aby int_lin_comb_E.
Qed.

Theorem int_lin_comb_E2: forall a b c, int_lin_comb a b c -> b :e int.
aby int_lin_comb_E.
Qed.

Theorem int_lin_comb_E3: forall a b c, int_lin_comb a b c -> c :e int.
aby int_lin_comb_E.
Qed.

Theorem int_lin_comb_E4: forall a b c, int_lin_comb a b c ->
  forall p:prop,
       (forall m n :e int, m * a + n * b = c -> p)
    -> p.
aby int_lin_comb_E.
Qed.

Theorem least_pos_int_lin_comb_ex: forall a b :e int, ~(a = 0 /\ b = 0) -> exists c, int_lin_comb a b c /\ 0 < c /\ forall c', int_lin_comb a b c' -> 0 < c' -> c <= c'.
let a. assume Ha. let b. assume Hb.
assume H1: ~(a = 0 /\ b = 0).
claim LaS: SNo a.
{ aby int_SNo Ha. }
claim LbS: SNo b.
{ aby int_SNo Hb. }
set p : set -> prop := fun c => int_lin_comb a b c /\ 0 < c.
claim L1: exists c, ordinal c /\ p c.
{ apply int_3_cases a Ha.
  - aby nat_0 nat_ordsucc nat_1 ordinal_ordsucc nat_p_ordinal omega_nat_p nat_p_omega omega_ordsucc nat_p_SNo SNo_1 minus_SNo_invol add_SNo_0R mul_SNo_minus_distrL mul_SNo_zeroL mul_SNo_oneL Subq_omega_int int_minus_SNo_omega ordinal_ordsucc_pos int_lin_comb_I LbS LaS Hb Ha.
  - assume H2: a = 0.
    apply int_3_cases b Hb.
    + aby nat_0 nat_ordsucc nat_1 ordinal_ordsucc nat_p_ordinal omega_nat_p nat_p_omega omega_ordsucc nat_p_SNo SNo_1 minus_SNo_invol add_SNo_0L mul_SNo_minus_distrL mul_SNo_zeroL mul_SNo_oneL Subq_omega_int int_minus_SNo_omega ordinal_ordsucc_pos int_lin_comb_I LbS LaS Hb Ha.
    + aby H2 H1.
    + aby nat_0 nat_1 ordinal_ordsucc nat_p_ordinal omega_nat_p nat_p_omega omega_ordsucc add_SNo_0L mul_SNo_zeroL mul_SNo_oneL Subq_omega_int ordinal_ordsucc_pos int_lin_comb_I LbS LaS Hb Ha.
  - aby nat_0 nat_1 ordinal_ordsucc nat_p_ordinal omega_nat_p nat_p_omega omega_ordsucc add_SNo_0R mul_SNo_zeroL mul_SNo_oneL Subq_omega_int ordinal_ordsucc_pos int_lin_comb_I LbS LaS Hb Ha.
}
claim L2: exists c, ordinal c /\ p c /\ forall beta :e c, ~p beta.
{ exact least_ordinal_ex p L1. }
aby nat_p_ordinal SNoLtLe SNoLtLe_or ordinal_SNo ordinal_SNoLt_In int_SNo nonneg_int_nat_p int_lin_comb_E3 L2.
Qed.

Theorem int_lin_comb_sym: forall a b d,
     int_lin_comb a b d
  -> int_lin_comb b a d.
aby add_SNo_com SNo_mul_SNo int_SNo int_lin_comb_I int_lin_comb_E.
Qed.
  
Theorem least_pos_int_lin_comb_divides_int: forall a b d,
     int_lin_comb a b d
  -> 0 < d
  -> (forall c, int_lin_comb a b c -> 0 < c -> d <= c)
  -> divides_int d a.
let a b d.
assume Hd1: int_lin_comb a b d.
assume Hd2: 0 < d.
assume Hd3: forall c, int_lin_comb a b c -> 0 < c -> d <= c.
apply int_lin_comb_E a b d Hd1.
assume Ha: a :e int.
assume Hb: b :e int.
assume HdZ: d :e int.
let m. assume Hm: m :e int.
let n. assume Hn: n :e int.
assume H2: m * a + n * b = d.
claim LaS: SNo a.
{ aby int_SNo Ha. }
claim LbS: SNo b.
{ aby int_SNo Hb. }
claim LmS: SNo m.
{ aby int_SNo Hm. }
claim LnS: SNo n.
{ aby int_SNo Hn. }
claim LdN: nat_p d.
{ aby SNoLtLe nonneg_int_nat_p HdZ Hd2. }
claim Ld1: d :e omega :\: {0}.
{ aby SingE setminusI nat_p_omega SNoLt_irref LdN Hd2. }
claim LdS: SNo d.
{ aby nat_p_SNo LdN. }
apply quotient_remainder_int d Ld1 a Ha.
let q. assume H. apply H.
assume Hq: q :e int. assume H. apply H.
let r. assume H. apply H.
assume Hr: r :e d.
assume H1: a = q * d + r.
claim LqS: SNo q.
{ aby int_SNo Hq. }
claim LmqS: SNo (- q).
{ aby SNo_minus_SNo LqS. }
claim LrN: nat_p r.
{ aby nat_p_trans Hr LdN. }
claim Lrnn: 0 <= r.
{ aby nat_p_omega omega_nonneg LrN. }
claim Lrd: r < d.
{ aby nat_p_ordinal ordinal_In_SNoLt Hr LdN. }
claim LqdS: SNo (q * d).
{ aby SNo_mul_SNo LqS LdS. }
claim LrS: SNo r.
{ aby nat_p_SNo LrN. }
claim L1: r = (1 + - q * m) * a + (- q * n) * b.
{ transitivity a + - q * d,
               a + (- q) * (m * a + n * b).
  - aby SNo_minus_SNo add_SNo_com add_SNo_minus_L2 LrS LqdS H1 LaS.
  - aby mul_SNo_minus_distrL LqS LdS H2.
  - aby SNo_1 add_SNo_assoc SNo_mul_SNo mul_SNo_minus_distrL mul_SNo_distrR mul_SNo_distrL mul_SNo_assoc mul_SNo_oneL LmqS LqS LnS LmS LbS LaS.
}
aby and3I and4I nat_1 nat_p_omega SNoLeE SNoLt_irref SNoLtLe_tra SNo_0 add_SNo_0R mul_SNo_com Subq_omega_int int_add_SNo int_minus_SNo int_mul_SNo L1 LrS LqdS Lrd Lrnn LrN LqS H1 Hq LdS Hn Hm HdZ Hb Ha Hd3.
Qed.

Theorem least_pos_int_lin_comb_gcd: forall a b d,
     int_lin_comb a b d
  -> 0 < d
  -> (forall c, int_lin_comb a b c -> 0 < c -> d <= c)
  -> gcd_reln a b d.
aby and3I SingE setminusI nat_p_omega SNoLtLe SNoLt_irref nat_p_SNo nonneg_int_nat_p divides_int_add_SNo divides_int_mul_SNo_R divides_int_pos_Le int_lin_comb_E int_lin_comb_sym least_pos_int_lin_comb_divides_int.
Qed.

Theorem BezoutThm: forall a b :e int, ~(a = 0 /\ b = 0) ->
  forall d, gcd_reln a b d <-> int_lin_comb a b d /\ 0 < d /\ forall d', int_lin_comb a b d' -> 0 < d' -> d <= d'.
aby gcd_reln_uniq least_pos_int_lin_comb_ex least_pos_int_lin_comb_gcd.
Qed.

Theorem gcd_id: forall m :e omega :\: {0}, gcd_reln m m m.
let m. assume Hm.
apply setminusE omega {0} m Hm.
assume Hm1: m :e omega.
assume Hm2: m /:e {0}.
claim LmN: nat_p m.
{ aby omega_nat_p Hm1. }
claim Lmo: ordinal m.
{ aby nat_p_ordinal LmN. }
claim LmZ: m :e int.
{ aby Subq_omega_int Hm1. }
claim LmS: SNo m.
{ aby int_SNo LmZ. }
claim Lmpos: 0 < m.
{ aby SingI SNoLeE omega_nonneg SNo_0 LmS Hm2 Hm1. }
prove divides_int m m /\ divides_int m m /\ forall d', divides_int d' m -> divides_int d' m -> d' <= m.
aby and3I nat_p_ordinal mul_nat_p mul_nat_0_or_Subq nat_p_omega SNoLtLe SNoLt_irref SNoLt_tra SNoLe_tra SNoLtLe_or ordinal_Subq_SNoLe SNo_0 mul_SNo_zeroR mul_nat_mul_SNo mul_SNo_pos_neg int_SNo nonneg_int_nat_p divides_int_ref Lmpos LmS LmZ.
Qed.

Theorem gcd_0: forall m :e omega :\: {0}, gcd_reln 0 m m.
aby and3I setminusE Subq_omega_int divides_int_0 gcd_id.
Qed.

Theorem gcd_sym: forall m n d, gcd_reln m n d -> gcd_reln n m d.
aby and3I.
Qed.

Theorem gcd_minus: forall m n d, gcd_reln m n d -> gcd_reln m (- n) d.
aby and3I minus_SNo_invol int_SNo divides_int_minus_SNo.
Qed.

Theorem euclidean_algorithm_prop_1: forall m n d, n :e int -> gcd_reln m (n + - m) d -> gcd_reln m n d.
aby and3I add_SNo_minus_R2' int_SNo divides_int_add_SNo divides_int_minus_SNo.
Qed.

Theorem euclidean_algorithm:
     (forall m :e omega :\: {0}, gcd_reln m m m)
  /\ (forall m :e omega :\: {0}, gcd_reln 0 m m)
  /\ (forall m :e omega :\: {0}, gcd_reln m 0 m)
  /\ (forall m n :e omega, m < n
          -> forall d, gcd_reln m (n + - m) d
                    -> gcd_reln m n d)
  /\ (forall m n :e omega, n < m
          -> forall d, gcd_reln n m d
                    -> gcd_reln m n d)
  /\ (forall m :e omega, forall n :e int, n < 0
          -> forall d, gcd_reln m (- n) d
                    -> gcd_reln m n d)
  /\ (forall m n :e int, m < 0
          -> forall d, gcd_reln (- m) n d
                    -> gcd_reln m n d).
aby and7I minus_SNo_invol int_SNo Subq_omega_int gcd_id gcd_0 gcd_sym gcd_minus euclidean_algorithm_prop_1.
Qed.

Theorem Euclid_lemma: forall p, prime_nat p -> forall a b :e int, divides_int p (a * b) -> divides_int p a \/ divides_int p b.
let p. assume Hp.
let a. assume Ha.
let b. assume Hb.
apply Hp. assume H. apply H.
assume Hp1: p :e omega.
assume Hp2: 1 :e p.
assume Hp3: forall k :e omega, divides_nat k p -> k = 1 \/ k = p.
assume H1: divides_int p (a * b).
claim LaS: SNo a.
{ aby int_SNo Ha. }
claim LbS: SNo b.
{ aby int_SNo Hb. }
claim LpZ: p :e int.
{ aby Subq_omega_int Hp1. }
apply xm (divides_int p a).
- aby.
- assume H2: ~divides_int p a. apply orIR.
  prove divides_int p b.
  claim L1: gcd_reln p a 1.
  { aby and3I nat_p_omega SNoLtLe SNoLt_tra SNoLe_ref SNoLtLe_or SNo_0 SNo_1 SNoLt_0_1 int_SNo nonneg_int_nat_p divides_int_divides_nat divides_int_1 H2 LpZ Hp3 Hp1 Ha. }
  claim L2: ~(p = 0 /\ a = 0).
  { assume H3. aby In_no2cycle In_0_1 H3 Hp2. }
  apply BezoutThm p LpZ a Ha L2 1.
  assume HBezout1: gcd_reln p a 1 ->
        int_lin_comb p a 1
     /\ 0 < 1
     /\ forall d, int_lin_comb p a d -> 0 < d -> 1 <= d.
  assume _.
  apply HBezout1 L1. assume H. apply H.
  assume H3: int_lin_comb p a 1.
  assume _.
  assume H4: forall d, int_lin_comb p a d -> 0 < d -> 1 <= d.
  apply int_lin_comb_E4 p a 1 H3.
  let m. assume Hm: m :e int.
  let n. assume Hn: n :e int.
  assume H5: m * p + n * a = 1.
  claim LnS: SNo n.
  { aby int_SNo Hn. }
  claim L3: b * m * p + b * n * a = b.
  { aby SNo_mul_SNo mul_SNo_oneR mul_SNo_distrL int_SNo LnS H5 Hm LpZ LbS LaS. }
  aby mul_SNo_rotate_3_1 divides_int_ref divides_int_add_SNo divides_int_mul_SNo_R L3 LnS Hn Hm LpZ LbS LaS H1 Hb.
Qed.

End BezoutAndGCD.

Section PrimeFactorization.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
Infix <= 490 := SNoLe.

Theorem prime_not_divides_int_1: forall p, prime_nat p -> ~divides_int p 1.
aby nat_p_ordinal omega_nat_p SNoLt_irref SNoLtLe_tra nat_p_SNo ordinal_In_SNoLt SNo_1 SNoLt_0_1 divides_int_pos_Le.
Qed.

Definition Pi_SNo : (set -> set) -> set -> set := fun f n =>
  nat_primrec 1 (fun i r => r * f i) n.

Theorem Pi_SNo_0: forall f:set -> set, Pi_SNo f 0 = 1.
aby nat_primrec_0.
Qed.

Theorem Pi_SNo_S: forall f:set -> set, forall n, nat_p n -> Pi_SNo f (ordsucc n) = Pi_SNo f n * f n.
aby nat_primrec_S.
Qed.

Theorem Pi_SNo_In_omega: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, f i :e omega)
  -> Pi_SNo f n :e omega.
let f.
apply nat_ind.
- assume _. aby nat_1 nat_p_omega Pi_SNo_0.
- aby ordsuccI1 ordsuccI2 mul_SNo_In_omega Pi_SNo_S.
Qed.

Theorem Pi_SNo_In_int: forall f:set -> set,
 forall n, nat_p n ->
     (forall i :e n, f i :e int)
  -> Pi_SNo f n :e int.
let f.
apply nat_ind.
- assume _. aby nat_1 nat_p_omega Subq_omega_int Pi_SNo_0.
- aby ordsuccI1 ordsuccI2 int_mul_SNo Pi_SNo_S.
Qed.

Theorem divides_int_prime_nat_eq: forall p q, prime_nat p -> prime_nat q -> divides_int p q -> p = q.
aby In_irref divides_int_divides_nat.
Qed.

Theorem Euclid_lemma_Pi_SNo: forall f:set->set,
  forall p, prime_nat p ->
  forall n, nat_p n ->
      (forall i :e n, f i :e int)
   -> divides_int p (Pi_SNo f n)
   -> exists i :e n, divides_int p (f i).
let f p.
assume Hp: prime_nat p.
apply nat_ind.
- assume _.
  aby prime_not_divides_int_1 Pi_SNo_0 Hp.
- aby ordsuccI1 ordsuccI2 Euclid_lemma Pi_SNo_S Pi_SNo_In_int Hp.
Qed.

Theorem divides_nat_mul_SNo_R: forall m n :e omega, divides_nat m (m * n).
aby and3I mul_nat_mul_SNo mul_SNo_In_omega.
Qed.

Theorem divides_nat_mul_SNo_L: forall m n :e omega, divides_nat n (m * n).
aby omega_SNo mul_SNo_com divides_nat_mul_SNo_R.
Qed.

Theorem Pi_SNo_divides: forall f:set->set,
  forall n, nat_p n ->
      (forall i :e n, f i :e omega)
   -> (forall i :e n, divides_nat (f i) (Pi_SNo f n)).
let f.
apply nat_ind.
- assume _. aby EmptyE.
- let n. assume Hn: nat_p n.
  aby ordsuccI1 ordsuccI2 ordsuccE divides_nat_tra Pi_SNo_S Pi_SNo_In_omega divides_nat_mul_SNo_R divides_nat_mul_SNo_L Hn.
Qed.

Definition nonincrfinseq : (set -> prop) -> set -> (set -> set) -> prop := fun A n f => forall i :e n, A (f i) /\ forall j :e i, f i <= f j.

Theorem Pi_SNo_eq: forall f g:set->set,
  forall m, nat_p m
   -> (forall i :e m, f i = g i)
   -> Pi_SNo f m = Pi_SNo g m.
let f g.
apply nat_ind.
- assume _. aby Pi_SNo_0.
- aby ordsuccI1 ordsuccI2 Pi_SNo_S.
Qed.

Theorem prime_factorization_ex_uniq: forall n, nat_p n -> 0 :e n ->
  exists k :e omega, exists f:set -> set, nonincrfinseq prime_nat k f /\ Pi_SNo f k = n
    /\ forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = n
         -> k' = k /\ forall i :e k, f' i = f i.
apply nat_complete_ind.
let n.
assume Hn: nat_p n.
assume IH: forall m :e n, 0 :e m ->
  exists k :e omega, exists f:set -> set, nonincrfinseq prime_nat k f /\ Pi_SNo f k = m
    /\ forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = m
         -> k' = k /\ forall i :e k, f' i = f i.
assume H1: 0 :e n.
claim Ln: n :e omega.
{ aby nat_p_omega Hn. }
apply xm (n = 1).
- assume H2: n = 1.
  set f : set -> set := fun i => 0.
  prove exists k :e omega, exists f:set -> set, nonincrfinseq prime_nat k f /\ Pi_SNo f k = n
          /\ forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = n
              -> k' = k /\ forall i :e k, f' i = f i.
  witness 0. apply andI.
  + aby nat_0 nat_p_omega.
  + witness f.
    apply and3I.
    * aby EmptyE.
    * aby Pi_SNo_0 H2.
    * { let k'. assume Hk': k' :e omega.
        let f'.
	assume Hf': nonincrfinseq prime_nat k' f'.
        assume H3: Pi_SNo f' k' = n.
	claim Lf'1: forall i :e k', prime_nat (f' i).
	{ aby Hf'. }
	claim Lf'2: forall i :e k', f' i :e omega.
	{ aby Lf'1. }
	aby EmptyE Empty_eq nat_p_ordinal omega_nat_p SNoLt_irref SNoLtLe_tra nat_p_SNo omega_SNo ordinal_In_SNoLt SNo_1 SNoLt_0_1 divides_nat_divides_int divides_int_pos_Le Pi_SNo_divides Lf'2 Lf'1 H3 Hk' H2 Hn.
      }
- assume H2: n <> 1.
  claim LnS: SNo n.
  { aby nat_p_SNo Hn. }
  claim Lno: ordinal n.
  { aby nat_p_ordinal Hn. }
  claim L1: 1 :e n.
  { aby set_ext nat_1 cases_1 nat_p_ordinal ordinal_In_Or_Subq Lno H2 H1. }
  claim L2: exists p, ordinal p /\ (prime_nat p /\ divides_nat p n) /\ forall q :e p, ~(prime_nat q /\ divides_nat q n).
  { apply least_ordinal_ex.
    aby nat_p_ordinal omega_nat_p prime_nat_divisor_ex L1 Hn.
  }
  apply L2.
  let p. assume H. apply H. assume H. apply H.
  assume Hpo: ordinal p. assume H. apply H.
  assume Hpp: prime_nat p.
  assume Hpn: divides_nat p n.
  assume Hpleast: forall q :e p, ~(prime_nat q /\ divides_nat q n).
  apply Hpp. assume H _. apply H.
  assume HpN: p :e omega.
  assume H1p: 1 :e p.
  apply Hpn. assume _ H. apply H.
  let m. assume H. apply H.
  assume Hm: m :e omega.
  rewrite mul_nat_mul_SNo p HpN m Hm.
  assume Hpm: p * m = n.
  claim LmS: SNo m.
  { aby omega_SNo Hm. }
  claim LmN: nat_p m.
  { aby omega_nat_p Hm. }
  claim Lmo: ordinal m.
  { aby nat_p_ordinal LmN. }
  claim LpS: SNo p.
  { aby omega_SNo HpN. }
  claim LpN: nat_p p.
  { aby omega_nat_p HpN. }
  claim Lpo: ordinal p.
  { aby nat_p_ordinal LpN. }
  claim Lmp: m * p = n.
  { aby mul_SNo_com LpS LmS Hpm. }
  claim L1p: 1 < p.
  { aby ordinal_In_SNoLt H1p Hpo. }
  claim Lmpos: 0 < m.
  { aby In_irref SNoLeE omega_nonneg SNo_0 mul_SNo_zeroR LpS LmS Hpm Hm H1. }
  claim L3: m < n.
  { aby SNo_1 mul_SNo_oneR pos_mul_SNo_Lt Lmpos L1p Lmp LpS LmS. }
  claim L4: m :e n.
  { aby ordinal_SNoLt_In L3 Lmo Lno. }
  claim L5: 0 :e m.
  { aby ordinal_Empty ordinal_SNoLt_In Lmpos Lmo. }
  apply IH m L4 L5.
  let k. assume H. apply H.
  assume Hk: k :e omega. assume H. apply H.
  let f. assume H. apply H. assume H. apply H.
  assume Hf: nonincrfinseq prime_nat k f.
  assume Hfkm: Pi_SNo f k = m.
  assume Huniq: forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = m
                 -> k' = k /\ forall i :e k, f' i = f i.
  claim LkN: nat_p k.
  { aby omega_nat_p Hk. }
  claim Lf1: forall i :e k, prime_nat (f i).
  { aby Hf. }
  claim Lf2: forall i :e k, f i :e omega.
  { aby Lf1. }
  claim Lg: exists g:set->set, g k = p /\ forall i :e k, g i = f i.
  { set g : set -> set := fun i => if i :e k then f i else p.
    aby If_i_0 If_i_1 In_irref.
  }
  apply Lg.
  let g. assume H. apply H.
  assume Hgk: g k = p.
  assume Hgi: forall i :e k, g i = f i.
  prove exists k :e omega, exists f:set -> set, nonincrfinseq prime_nat k f /\ Pi_SNo f k = n
    /\ forall k' :e omega, forall f':set -> set, nonincrfinseq prime_nat k' f' -> Pi_SNo f' k' = n
         -> k' = k /\ forall i :e k, f' i = f i.
  witness (ordsucc k). apply andI.
  + aby omega_ordsucc Hk.
  + witness g. apply and3I.
    * { prove nonincrfinseq prime_nat (ordsucc k) g.
        let i. assume Hi: i :e ordsucc k.
	apply ordsuccE k i Hi.
	- aby nat_trans Hgi LkN Hf.
	- aby nat_p_ordinal omega_nat_p divides_nat_tra SNoLtLe_or nat_p_SNo ordinal_SNoLt_In divides_nat_mul_SNo_R Pi_SNo_divides Hgi Hgk Lf2 Lf1 LkN Hfkm Lmp Lpo LpS Hm HpN Hpleast Hpp.
      }
    * aby Pi_SNo_S Pi_SNo_eq Hgi Hgk LkN Hfkm Lmp.
    * { prove forall k' :e omega, forall g':set -> set, nonincrfinseq prime_nat k' g' -> Pi_SNo g' k' = n
                -> k' = ordsucc k /\ forall i :e ordsucc k, g' i = g i.
        let k'. assume Hk': k' :e omega.
	let g'.
	assume Hg': nonincrfinseq prime_nat k' g'.
	assume Hg'k': Pi_SNo g' k' = n.
	claim Lg'1: forall i :e k', prime_nat (g' i).
	{ aby Hg'. }
	claim Lg'2: forall i :e k', g' i :e omega.
	{ aby Lg'1. }
	prove k' = ordsucc k /\ forall i :e ordsucc k, g' i = g i.
	claim Lk'N: nat_p k'.
	{ aby omega_nat_p Hk'. }
	apply nat_inv k' Lk'N.
	- aby Pi_SNo_0 Hg'k' H2.
	- assume H. apply H.
	  let k''. assume H. apply H.
	  assume Hk'': nat_p k''.
	  assume Hk'k'': k' = ordsucc k''.
	  claim L6: nonincrfinseq prime_nat k'' g'.
	  { aby ordsuccI1 Hk'k'' Hg'. }
	  claim LPg'k''N: Pi_SNo g' k'' :e omega.
	  { aby ordsuccI1 Pi_SNo_In_omega Hk'k'' Hk'' Lg'2. }
	  claim LPg'k''S: SNo (Pi_SNo g' k'').
	  { aby omega_SNo Hn IH H1 Ln H2 LnS Lno L1 L2 H H Hpo H Hpp Hpn Hpleast H HpN H1p H H Hm Hpm LmS LmN Lmo LpS LpN Lpo Lmp L1p Lmpos L3 L4 L5 H Hk H H H Hf Hfkm Huniq LkN Lf1 Lf2 Lg H Hgk Hgi Hk' Hg' Hg'k' Lg'1 Lg'2 Lk'N H H Hk'' Hk'k'' L6 LPg'k''N. }
	  claim L7: g' k'' = p.
	  { claim L7a: prime_nat (g' k'') /\ forall j :e k'', g' k'' <= g' j.
	    { aby ordsuccI2 Hk'k'' Hg'. }
	    apply L7a.
	    assume Hg'k''P: prime_nat (g' k'').
	    assume Hg'k''minimal: forall j :e k'', g' k'' <= g' j.
	    apply Hg'k''P. assume H _. apply H.
	    assume H4: g' k'' :e omega.
	    assume H5: 1 :e g' k''.
	    claim Lg'k''N: nat_p (g' k'').
	    { aby omega_nat_p H4. }
	    claim Lg'k''o: ordinal (g' k'').
	    { aby nat_p_ordinal Lg'k''N. }
	    claim Lg'k''S: SNo (g' k'').
	    { aby nat_p_SNo Lg'k''N. }
	    claim L7b: divides_nat (g' k'') n.
	    { aby Pi_SNo_S divides_nat_mul_SNo_L H4 LPg'k''N Hk'k'' Hk'' Hg'k'. }
	    claim L7c: divides_int p (Pi_SNo g' k').
	    { aby divides_nat_divides_int Hg'k' Hpn. }
	    claim L7d: divides_int p (Pi_SNo g' k'') \/ divides_int p (g' k'').
	    { aby Subq_omega_int Euclid_lemma Pi_SNo_S L7c H4 LPg'k''N Hk'k'' Hk'' Hpp. }
	    claim L7e: forall i :e k'', g' i :e int.
	    { aby ordsuccI1 Subq_omega_int Hk'k'' Lg'2. }
	    aby ordsuccI1 ordsuccI2 SNoLt_irref SNoLt_trichotomy_or_impred SNoLtLe_tra ordinal_SNoLt_In divides_int_prime_nat_eq Euclid_lemma_Pi_SNo L7e L7d L7b Lg'k''S Lg'k''o Hg'k''minimal Hg'k''P Hk'k'' Hk'' Lg'1 Lpo LpS Hpleast Hpp.
	  }
	  aby ordsuccE nat_p_omega SNoLt_irref SNoLt_tra SNo_0 SNo_1 SNoLt_0_1 mul_SNo_com mul_SNo_nonzero_cancel Pi_SNo_S L7 LPg'k''S L6 Hk'k'' Hk'' Hg'k' Hgi Hgk Huniq L1p LpS LmS Hpm.
      }
Qed.

End PrimeFactorization.

Section SurrealExp.
Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Definition exp_SNo_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.
Infix ^ 342 right := exp_SNo_nat.

Theorem exp_SNo_nat_0 : forall x, SNo x -> x ^ 0 = 1.
aby nat_primrec_0.
Qed.

Theorem exp_SNo_nat_S : forall x, SNo x -> forall n, nat_p n -> x ^ (ordsucc n) = x * x ^ n.
aby nat_primrec_S.
Qed.

Theorem exp_SNo_nat_1: forall x, SNo x -> x ^ 1 = x.
aby nat_0 mul_SNo_oneR exp_SNo_nat_0 exp_SNo_nat_S.
Qed.

Theorem SNo_exp_SNo_nat : forall x, SNo x -> forall n, nat_p n -> SNo (x ^ n).
let x. assume Hx. apply nat_ind.
- aby SNo_1 exp_SNo_nat_0 Hx.
- aby SNo_mul_SNo exp_SNo_nat_S Hx.
Qed.

Theorem nat_exp_SNo_nat : forall x, nat_p x -> forall n, nat_p n -> nat_p (x ^ n).
let x. assume Hx.
claim Lx: SNo x.
{ aby nat_p_SNo Hx. }
apply nat_ind.
- aby nat_1 exp_SNo_nat_0 Lx.
- aby mul_nat_p nat_p_omega mul_nat_mul_SNo exp_SNo_nat_S Lx Hx.
Qed.

Theorem eps_ordsucc_half_add : forall n, nat_p n -> eps_ (ordsucc n) + eps_ (ordsucc n) = eps_ n.
apply nat_complete_ind.
let n. assume Hn.
assume IH: forall m :e n, eps_ (ordsucc m) + eps_ (ordsucc m) = eps_ m.
claim Ln: n :e omega.
{ aby nat_p_omega Hn. }
rewrite eps_SNoCut n Ln.
set x := eps_ (ordsucc n).
claim Lx: SNo x.
{ aby omega_ordsucc SNo_eps_ Ln. }
claim Lx2: 0 < x.
{ aby omega_ordsucc SNo_eps_pos Ln. }
rewrite add_SNo_eq x Lx x Lx.
prove SNoCut ({w + x|w :e SNoL x} :\/: {x + w|w :e SNoL x})
             ({z + x|z :e SNoR x} :\/: {x + z|z :e SNoR x})
    = SNoCut {0} {eps_ m|m :e n}.
apply SNoCut_ext ({w + x|w :e SNoL x} :\/: {x + w|w :e SNoL x})
                 ({z + x|z :e SNoR x} :\/: {x + z|z :e SNoR x})
                 {0} {eps_ m|m :e n}
                 (add_SNo_SNoCutP x x Lx Lx)
                 (eps_SNoCutP n Ln).
- claim L1: forall w :e SNoL x, w + x < eps_ n /\ x + w < eps_ n.
  { aby ordsuccI2 nat_ordsucc nat_p_ordinal omega_ordsucc SNoLev_ SNoLt_irref SNoLt_tra SNoLeLt_tra SNoLtLe_or SNoS_I SNoL_E SNo_0 SNo_eps_ SNoLev_eps_ SNo_eps_decr SNo_pos_eps_Lt SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_0L Lx Ln Hn. }    
  aby ReplE_impred binunionE eps_SNoCut L1 Ln.
- claim L2: forall z :e SNoR x, eps_ n < z + x /\ eps_ n < x + z.
  { aby nat_ordsucc nat_p_ordinal omega_ordsucc SNoLev_ SNoLt_tra SNoLeLt_tra SNoS_I SNoR_E SNo_0 SNo_eps_ SNoLev_eps_ SNo_eps_pos SNo_pos_eps_Le SNo_add_SNo add_SNo_Lt2 add_SNo_com add_SNo_0R Lx Ln Hn. }
  aby ReplE_impred binunionE eps_SNoCut L2 Ln.
- aby SingE SNo_0 add_SNo_eq add_SNo_Lt3 add_SNo_0L Lx2 Lx.
- aby ReplE_impred nat_p_trans nat_p_ordinal ordinal_ordsucc_In nat_p_omega omega_ordsucc SNo_eps_ SNo_eps_decr add_SNo_eq add_SNo_Lt3 Lx Ln IH Hn.
Qed.

Theorem eps_1_half_eq1 : eps_ 1 + eps_ 1 = 1.
aby nat_0 eps_0_1 eps_ordsucc_half_add.
Qed.

Theorem eps_1_half_eq2 : 2 * eps_ 1 = 1.
aby SNo_1 SNo_eps_1 add_SNo_1_1_2 mul_SNo_distrR mul_SNo_oneL eps_1_half_eq1.
Qed.

Theorem double_eps_1 : forall x y z, SNo x -> SNo y -> SNo z -> x + x = y + z -> x = eps_ 1 * (y + z).
aby nat_1 neq_2_0 nat_p_omega SNo_1 SNo_2 SNo_eps_ SNo_add_SNo add_SNo_1_1_2 SNo_mul_SNo mul_SNo_distrR mul_SNo_assoc mul_SNo_oneL mul_SNo_nonzero_cancel eps_1_half_eq2.
Qed.

Theorem exp_SNo_1_bd: forall x, SNo x -> 1 <= x -> forall n, nat_p n -> 1 <= x ^ n.
let x. assume Hx Hx1.
apply nat_ind.
- aby SNoLe_ref exp_SNo_nat_0 Hx.
- aby SNoLtLe SNo_1 SNoLt_0_1 mul_SNo_oneL nonneg_mul_SNo_Le2 exp_SNo_nat_S SNo_exp_SNo_nat Hx1 Hx.
Qed.

Theorem exp_SNo_2_bd: forall n, nat_p n -> n < 2 ^ n.
apply nat_ind.
- aby SNo_2 SNoLt_0_1 exp_SNo_nat_0.
- let n. assume Hn.
  assume IHn: n < 2 ^ n.
  claim Ln: SNo n.
  { aby nat_p_SNo Hn. }
  claim L2n: SNo (2 ^ n).
  { aby SNo_2 SNo_exp_SNo_nat Hn. }
  prove ordsucc n < 2 ^ (ordsucc n).
  rewrite exp_SNo_nat_S 2 SNo_2 n Hn.
  prove ordsucc n < 2 * 2 ^ n.
  rewrite <- add_SNo_1_ordsucc n (nat_p_omega n Hn).
  prove n + 1 < 2 * 2 ^ n.
  rewrite <- add_SNo_1_1_2 at 1.
  prove n + 1 < (1 + 1) * 2 ^ n.
  aby nat_p_omega SNoLtLe SNoLtLe_tra SNo_1 SNo_2 SNoLt_1_2 SNo_add_SNo add_SNo_Lt1 add_SNo_Le2 mul_SNo_distrR mul_SNo_oneL exp_SNo_1_bd L2n Ln IHn Hn.
Qed.

Theorem mul_SNo_eps_power_2: forall n, nat_p n -> eps_ n * 2 ^ n = 1.
apply nat_ind.
- aby SNo_1 SNo_2 eps_0_1 mul_SNo_oneR exp_SNo_nat_0.
- aby nat_ordsucc nat_p_omega SNo_1 SNo_2 SNo_eps_ add_SNo_1_1_2 mul_SNo_oneR mul_SNo_distrL mul_SNo_assoc exp_SNo_nat_S SNo_exp_SNo_nat eps_ordsucc_half_add.
Qed.

Theorem eps_bd_1 : forall n :e omega, eps_ n <= 1.
aby omega_nat_p SNoLtLe SNo_1 SNo_2 SNo_eps_ SNo_eps_pos SNoLt_1_2 mul_SNo_oneR nonneg_mul_SNo_Le SNo_exp_SNo_nat exp_SNo_1_bd mul_SNo_eps_power_2.
Qed.

Theorem mul_SNo_eps_power_2': forall n, nat_p n -> 2 ^ n * eps_ n = 1.
aby nat_p_omega SNo_2 SNo_eps_ mul_SNo_com SNo_exp_SNo_nat mul_SNo_eps_power_2.
Qed.

Theorem exp_SNo_nat_mul_add : forall x, SNo x -> forall m, nat_p m -> forall n, nat_p n -> x ^ m * x ^ n = x ^ (m + n).
let x. assume Hx. let m. assume Hm.
claim Lm: SNo m.
{ aby nat_p_SNo Hm. }
apply nat_ind.
- aby add_SNo_0R mul_SNo_oneR exp_SNo_nat_0 SNo_exp_SNo_nat Lm Hm Hx.
- aby add_nat_SR add_nat_p nat_p_omega omega_ordsucc add_nat_add_SNo mul_SNo_com mul_SNo_assoc exp_SNo_nat_S SNo_exp_SNo_nat Hm Hx.
Qed.

Theorem exp_SNo_nat_mul_add' : forall x, SNo x -> forall m n :e omega, x ^ m * x ^ n = x ^ (m + n).
aby omega_nat_p exp_SNo_nat_mul_add.
Qed.

Theorem exp_SNo_nat_pos : forall x, SNo x -> 0 < x -> forall n, nat_p n -> 0 < x ^ n.
let x. assume Hx Hxpos.
apply nat_ind.
- aby SNoLt_0_1 exp_SNo_nat_0 Hx.
- aby SNo_0 mul_SNo_zeroR pos_mul_SNo_Lt exp_SNo_nat_S SNo_exp_SNo_nat Hxpos Hx.
Qed.

Theorem mul_SNo_eps_eps_add_SNo: forall m n :e omega, eps_ m * eps_ n = eps_ (m + n).
let m. assume Hm. let n. assume Hn.
claim Lmn1: m + n :e omega.
{ aby add_SNo_In_omega Hn Hm. }
claim Lmn2: nat_p (m + n).
{ aby omega_nat_p Lmn1. }
claim Lem: SNo (eps_ m).
{ aby SNo_eps_ Hm. }
claim Len: SNo (eps_ n).
{ aby SNo_eps_ Hn. }
claim Lemen: SNo (eps_ m * eps_ n).
{ aby SNo_mul_SNo Len Lem. }
claim Lemn: SNo (eps_ (m + n)).
{ aby SNo_eps_ Lmn1. }
claim L2m: SNo (2 ^ m).
{ aby omega_nat_p SNo_2 SNo_exp_SNo_nat Hm. }
aby omega_nat_p SNoLt_irref SNo_2 SNoLt_0_2 SNo_mul_SNo mul_SNo_com mul_SNo_assoc mul_SNo_oneL mul_SNo_nonzero_cancel SNo_exp_SNo_nat mul_SNo_eps_power_2' exp_SNo_nat_mul_add' exp_SNo_nat_pos L2m Lemn Lemen Len Lem Lmn2 Hn Hm.
Qed.

Theorem SNoS_omega_Lev_equip : forall n, nat_p n -> equip {x :e SNoS_ omega|SNoLev x = n} (2 ^ n).
apply nat_ind.
- prove equip {x :e SNoS_ omega|SNoLev x = 0} (2 ^ 0).
  rewrite exp_SNo_nat_0 2 SNo_2.
  prove equip {x :e SNoS_ omega|SNoLev x = 0} 1.
  apply equip_sym.
  prove exists f:set -> set, bij 1 {x :e SNoS_ omega|SNoLev x = 0} f.
  set f := fun i:set => 0.
  witness f.
  apply bijI.
  + let i. assume Hi: i :e 1.
    prove 0 :e {x :e SNoS_ omega|SNoLev x = 0}.
    apply SepI.
    * prove 0 :e SNoS_ omega.
      apply SNoS_I omega omega_ordinal 0 0 (nat_p_omega 0 nat_0).
      prove SNo_ 0 0. aby ordinal_Empty ordinal_SNo_ Hi.
    * prove SNoLev 0 = 0. aby SNoLev_0 Hi.
  + let i. assume Hi: i :e 1. let j. assume Hj: j :e 1.
    assume Hij: 0 = 0.
    prove i = j.
    apply cases_1 i Hi. apply cases_1 j Hj.
    prove 0 = 0. aby Hi Hj Hij. (** smaller proof than reflexivity, so use it **)
  + let x. assume Hx: x :e {x :e SNoS_ omega|SNoLev x = 0}.
    apply SepE (SNoS_ omega) (fun x => SNoLev x = 0) x Hx.
    assume Hx1: x :e SNoS_ omega.
    assume Hx2: SNoLev x = 0.
    apply SNoS_E2 omega omega_ordinal x Hx1.
    assume Hx1a: SNoLev x :e omega.
    assume Hx1b: ordinal (SNoLev x).
    assume Hx1c: SNo x.
    assume Hx1d: SNo_ (SNoLev x) x.
    claim L1: x = 0.
    { symmetry. apply SNo_eq 0 x SNo_0 Hx1c.
      - prove SNoLev 0 = SNoLev x. rewrite SNoLev_0. aby Hx Hx1 Hx2 Hx1a Hx1b Hx1c Hx1d.
      - prove SNoEq_ (SNoLev 0) 0 x. rewrite SNoLev_0.
        let alpha. assume Ha: alpha :e 0. prove False. aby EmptyE Hx Hx1 Hx2 Hx1a Hx1b Hx1c Hx1d Ha.
    }
    witness 0. apply andI.
    * aby In_0_1 Hx Hx1 Hx2 Hx1a Hx1b Hx1c Hx1d L1.
    * prove 0 = x. aby Hx Hx1 Hx2 Hx1a Hx1b Hx1c Hx1d L1.
- let n. assume Hn.
  assume IHn: equip {x :e SNoS_ omega|SNoLev x = n} (2 ^ n).
  prove equip {x :e SNoS_ omega|SNoLev x = ordsucc n} (2 ^ ordsucc n).
  rewrite exp_SNo_nat_S 2 SNo_2 n Hn.
  prove equip {x :e SNoS_ omega|SNoLev x = ordsucc n} (2 * 2 ^ n).
  rewrite <- add_SNo_1_1_2 at 1.
  prove equip {x :e SNoS_ omega|SNoLev x = ordsucc n} ((1 + 1) * 2 ^ n).
  rewrite mul_SNo_distrR 1 1 (2 ^ n) SNo_1 SNo_1 (SNo_exp_SNo_nat 2 SNo_2 n Hn).
  rewrite mul_SNo_oneL (2 ^ n) (SNo_exp_SNo_nat 2 SNo_2 n Hn).
  prove equip {x :e SNoS_ omega|SNoLev x = ordsucc n} (2 ^ n + 2 ^ n).
  claim L2n1: nat_p (2 ^ n).
  { aby nat_2 nat_exp_SNo_nat Hn. }
  claim L2n2: ordinal (2 ^ n).
  { aby nat_p_ordinal L2n1. }
  claim L2n3: SNo (2 ^ n).
  { aby ordinal_SNo L2n2. }
  claim L2n2n1: nat_p (2 ^ n + 2 ^ n).
  { aby omega_nat_p nat_p_omega add_SNo_In_omega L2n1. }
  claim L2n2n2: ordinal (2 ^ n + 2 ^ n).
  { aby nat_p_ordinal L2n2n1. }
  claim L2n2n3: SNo (2 ^ n + 2 ^ n).
  { aby ordinal_SNo L2n2n2. }
  claim L2npLt2n2n: forall m, SNo m -> m < 2 ^ n -> 2 ^ n + m < 2 ^ n + 2 ^ n.
  { aby add_SNo_Lt2 L2n3. }
  claim L2nLt2n2n: 2 ^ n < 2 ^ n + 2 ^ n.
  { aby SNo_0 SNo_2 SNoLt_0_2 add_SNo_0R exp_SNo_nat_pos L2npLt2n2n L2n3 Hn. }
  apply IHn.
  let f.
  assume Hf: bij {x :e SNoS_ omega|SNoLev x = n} (2 ^ n) f.
  apply bijE {x :e SNoS_ omega|SNoLev x = n} (2 ^ n) f Hf.
  assume Hf1: forall u :e {x :e SNoS_ omega|SNoLev x = n}, f u :e (2 ^ n).
  assume Hf2: forall u v :e {x :e SNoS_ omega|SNoLev x = n}, f u = f v -> u = v.
  assume Hf3: forall w :e 2 ^ n, exists u :e {x :e SNoS_ omega|SNoLev x = n}, f u = w.
  claim L2: forall x :e {x :e SNoS_ omega|SNoLev x = ordsucc n},
     forall p:prop,
          (SNo x
        -> SNoLev x = ordsucc n
        -> (x :/\: SNoElts_ n) :e {x :e SNoS_ omega|SNoLev x = n}
        -> SNo (x :/\: SNoElts_ n)
        -> SNoLev (x :/\: SNoElts_ n) = n
        -> p)
       -> p.
  { aby SepI SepE ordsuccI2 nat_p_omega omega_ordinal SNoS_I SNoS_E2 restr_SNo_ restr_SNo restr_SNoLev Hn. }
  claim Lf: forall u :e {x :e SNoS_ omega|SNoLev x = ordsucc n},
              forall p:prop,
                  (nat_p (f (u :/\: SNoElts_ n))
                -> ordinal (f (u :/\: SNoElts_ n))
                -> SNo (f (u :/\: SNoElts_ n))
                -> f (u :/\: SNoElts_ n) < 2 ^ n
                -> p)
               -> p.
  { aby nat_p_trans nat_p_ordinal ordinal_SNo ordinal_In_SNoLt L2 Hf1 L2n2 L2n1. }
  claim Lg: exists g:set -> set, (forall x, n :e x -> g x = f (x :/\: SNoElts_ n)) /\ (forall x, n /:e x -> g x = 2 ^ n + f (x :/\: SNoElts_ n)).
  { witness (fun x => if n :e x then f (x :/\: SNoElts_ n) else 2 ^ n + f (x :/\: SNoElts_ n)).
    apply andI.
    - let x. assume H1: n :e x.
      aby If_i_1 Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf H1.
    - let x. assume H1: n /:e x.
      aby If_i_0 Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf H1. }
  apply Lg. let g. assume H. apply H.
  assume Hg1: forall x, n :e x -> g x = f (x :/\: SNoElts_ n).
  assume Hg2: forall x, n /:e x -> g x = 2 ^ n + f (x :/\: SNoElts_ n).
  prove exists g:set -> set, bij {x :e SNoS_ omega|SNoLev x = ordsucc n} (2 ^ n + 2 ^ n) g.
  witness g. apply bijI.
  + aby xm SNoLt_tra ordinal_SNoLt_In add_SNo_ordinal_ordinal Hg2 Hg1 Lf L2 L2nLt2n2n L2npLt2n2n L2n2n3 L2n2n2 L2n3 L2n2.
  + let u. assume Hu: u :e {x :e SNoS_ omega|SNoLev x = ordsucc n}.
    let v. assume Hv: v :e {x :e SNoS_ omega|SNoLev x = ordsucc n}.
    apply L2 u Hu.
    assume Hu0a: SNo u.
    assume Hu0b: SNoLev u = ordsucc n.
    assume Hu1: (u :/\: SNoElts_ n) :e {x :e SNoS_ omega|SNoLev x = n}.
    assume Hu2: SNo (u :/\: SNoElts_ n).
    assume Hu3: SNoLev (u :/\: SNoElts_ n) = n.
    apply Lf u Hu.
    assume Lfu1: nat_p (f (u :/\: SNoElts_ n)).
    assume Lfu2: ordinal (f (u :/\: SNoElts_ n)).
    assume Lfu3: SNo (f (u :/\: SNoElts_ n)).
    assume Lfu4: f (u :/\: SNoElts_ n) < 2 ^ n.
    apply L2 v Hv.
    assume Hv0a: SNo v.
    assume Hv0b: SNoLev v = ordsucc n.
    assume Hv1: (v :/\: SNoElts_ n) :e {x :e SNoS_ omega|SNoLev x = n}.
    assume Hv2: SNo (v :/\: SNoElts_ n).
    assume Hv3: SNoLev (v :/\: SNoElts_ n) = n.
    apply Lf v Hv.
    assume Lfv1: nat_p (f (v :/\: SNoElts_ n)).
    assume Lfv2: ordinal (f (v :/\: SNoElts_ n)).
    assume Lfv3: SNo (f (v :/\: SNoElts_ n)).
    assume Lfv4: f (v :/\: SNoElts_ n) < 2 ^ n.
    claim LnLu: n :e SNoLev u.
    { aby ordsuccI2 Hu0b. }
    claim LnLv: n :e SNoLev v.
    { aby ordsuccI2 Hv0b. }
    apply xm (n :e u).
    * { assume H1: n :e u. rewrite Hg1 u H1.
        apply xm (n :e v).
        - aby iff_sym iff_trans ordsuccE SNo_eq restr_SNoEq H1 LnLv LnLu Hv1 Hv0b Hv0a Hu1 Hu0b Hu0a Hg1 Hf2.
        - aby nat_p_omega SNoLt_irref SNoLeLt_tra omega_nonneg SNo_0 SNo_add_SNo add_SNo_Le2 add_SNo_0R Lfv3 Lfv1 Lfu4 Hg2 L2n3.
      }
    * { assume H1: n /:e u. rewrite Hg2 u H1.
        apply xm (n :e v).
        - assume H2: n :e v. rewrite Hg1 v H2.
          assume Hguv: 2 ^ n + f (u :/\: SNoElts_ n) = f (v :/\: SNoElts_ n).
          prove False.
          apply SNoLt_irref (2 ^ n).
          prove 2 ^ n < 2 ^ n.
          apply SNoLeLt_tra (2 ^ n) (2 ^ n + f (u :/\: SNoElts_ n)) (2 ^ n)
                            L2n3
                            (SNo_add_SNo (2 ^ n) (f (u :/\: SNoElts_ n)) L2n3 Lfu3)
                            L2n3.
          + prove 2 ^ n <= 2 ^ n + f (u :/\: SNoElts_ n).
            rewrite <- add_SNo_0R (2 ^ n) L2n3 at 1.
            prove 2 ^ n + 0 <= 2 ^ n + f (u :/\: SNoElts_ n).
            apply add_SNo_Le2 (2 ^ n) 0 (f (u :/\: SNoElts_ n)) L2n3 SNo_0 Lfu3.
            prove 0 <= f (u :/\: SNoElts_ n).
            aby nat_p_omega omega_nonneg Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv.
          + prove 2 ^ n + f (u :/\: SNoElts_ n) < 2 ^ n.
            rewrite Hguv. aby Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv.
        - assume H2: n /:e v. rewrite Hg2 v H2.
          assume Hguv: 2 ^ n + f (u :/\: SNoElts_ n) = 2 ^ n + f (v :/\: SNoElts_ n).
          prove u = v.
          claim Luv: u :/\: SNoElts_ n = v :/\: SNoElts_ n.
          { apply Hf2 (u :/\: SNoElts_ n) Hu1 (v :/\: SNoElts_ n) Hv1.
            prove f (u :/\: SNoElts_ n) = f (v :/\: SNoElts_ n).
            aby add_SNo_cancel_L Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv.
          }
          apply SNo_eq u v Hu0a Hv0a.
          + prove SNoLev u = SNoLev v. rewrite Hv0b. aby Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv Luv.
          + prove SNoEq_ (SNoLev u) u v.
            rewrite Hu0b.
            prove SNoEq_ (ordsucc n) u v.
            let i. assume Hi: i :e ordsucc n.
            apply ordsuccE n i Hi.
            * { assume H3: i :e n.
                prove i :e u <-> i :e v.
                apply iff_trans (i :e u) (i :e u :/\: SNoElts_ n) (i :e v).
                - prove i :e u <-> i :e u :/\: SNoElts_ n.
                  apply iff_sym.
                  aby restr_SNoEq Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv Luv Hi H3.
                - prove i :e u :/\: SNoElts_ n <-> i :e v.
                  rewrite Luv.
                  prove i :e v :/\: SNoElts_ n <-> i :e v.
                  aby restr_SNoEq Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv Luv Hi H3.
              }
            * { assume H3: i = n. rewrite H3. apply iffI.
                - assume H4: n :e u. prove False. aby Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv Luv Hi H3 H4.
                - assume H4: n :e v. prove False. aby Hn IHn L2n1 L2n2 L2n3 L2n2n1 L2n2n2 L2n2n3 L2npLt2n2n L2nLt2n2n Hf Hf1 Hf2 Hf3 L2 Lf Lg H Hg1 Hg2 Hu Hv Hu0a Hu0b Hu1 Hu2 Hu3 Lfu1 Lfu2 Lfu3 Lfu4 Hv0a Hv0b Hv1 Hv2 Hv3 Lfv1 Lfv2 Lfv3 Lfv4 LnLu LnLv H1 H2 Hguv Luv Hi H3 H4.
              }
      }
  + prove forall m :e 2 ^ n + 2 ^ n, exists u :e {x :e SNoS_ omega|SNoLev x = ordsucc n}, g u = m.
    let m. assume Hm: m :e 2 ^ n + 2 ^ n.
    claim Lm1: nat_p m.
    { aby nat_p_trans Hm L2n2n1. }
    claim Lm2: SNo m.
    { aby nat_p_SNo Lm1. }
    apply add_SNo_omega_In_cases m (2 ^ n) (nat_p_omega (2 ^ n) L2n1) (2 ^ n) L2n1 Hm.
    * aby SepI SepE nat_p_omega omega_ordsucc omega_ordinal SNoS_I SNoS_E2 SNo_extend1_SNo_ SNo_extend1_SNo SNo_extend1_SNoLev SNo_extend1_In SNo_extend1_restr_eq Hg1 Hf3 Hn.
    * { assume H1: m + - 2 ^ n :e 2 ^ n.
        apply Hf3 (m + - 2 ^ n) H1.
        aby SepI SepE nat_p_omega omega_ordsucc omega_ordinal SNoS_I SNoS_E2 SNo_extend0_SNo_ SNo_extend0_SNo SNo_extend0_SNoLev SNo_extend0_nIn SNo_extend0_restr_eq SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0R add_SNo_minus_SNo_linv add_SNo_assoc Lm2 Hg2 L2n3 Hn.
      }
Qed.

Theorem SNoS_finite : forall n :e omega, finite (SNoS_ n).
let n. assume Hn.
claim Ln: nat_p n.
{ aby omega_nat_p Hn. }
claim Ln2: ordinal n.
{ aby nat_p_ordinal Ln. }
claim L1: SNoS_ n = \/_ i :e n, {x :e SNoS_ omega|SNoLev x = i}.
{ apply set_ext.
  - aby famunionI SepI omega_TransSet omega_ordinal SNoS_Subq SNoS_E2 Ln2 Hn.
  - aby famunionE_impred SepE omega_ordinal SNoS_I SNoS_E2 Ln2.
}
aby nat_2 nat_p_trans nat_p_omega famunion_nat_finite nat_exp_SNo_nat SNoS_omega_Lev_equip L1 Ln.
Qed.

Theorem SNoS_omega_SNoL_finite : forall x :e SNoS_ omega, finite (SNoL x).
aby omega_ordinal Subq_finite SNoS_I2 SNoS_E2 SNoL_E SNoS_finite.  
Qed.

Theorem SNoS_omega_SNoR_finite : forall x :e SNoS_ omega, finite (SNoR x).
aby omega_ordinal Subq_finite SNoS_I2 SNoS_E2 SNoR_E SNoS_finite.  
Qed.

End SurrealExp.

Opaque exp_SNo_nat.

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
aby and3I ReplI ReplE_impred SNo_minus_SNo minus_SNo_Le_contra.
Qed.

Theorem minus_SNo_max_min' : forall X y, (forall x :e X, SNo x) -> SNo_max_of {- x|x :e X} y -> SNo_min_of X (- y).
aby ReplE_impred Repl_invol_eq SNo_minus_SNo minus_SNo_invol minus_SNo_max_min.
Qed.

Theorem minus_SNo_min_max : forall X y, (forall x :e X, SNo x) -> SNo_min_of X y -> SNo_max_of {- x|x :e X} (- y).
aby and3I ReplI ReplE_impred SNo_minus_SNo minus_SNo_Le_contra.
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
{ aby SNo_add_SNo Hx. }
claim Lyz: SNo (y + z).
{ aby SNo_add_SNo Hz Hy2. }
claim L1: forall w :e SNoR y, w + z <= x + x -> False.
{ let w. assume Hw.
  assume H3: w + z <= x + x.
  apply SNoR_E y Hy2 w Hw.
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e SNoLev y.
  aby ordinal_TransSet SNoLev_ordinal SNoLt_irref SNoLtLe_tra SNoLtLe_or SNoL_I SNo_add_SNo add_SNo_Lt3b Hw2 Hw1 H3 Lxx H1 Hz Hy1b Hy3 Hy2 Hx.
}
claim L2: forall w :e SNoL x, y + z <= w + x -> False.
{ aby SNoLt_irref SNoLtLe_tra SNoLe_tra SNoL_E SNo_add_SNo add_SNo_Le1 add_SNo_Lt2 Lyz H1 Hz Hy3 Hy2 Hx. }
claim L3: forall w :e SNoR z, y + w < x + x -> exists w :e SNoR z, y + w = x + x.
{ aby ordinal_TransSet SNoLev_ordinal SNoLt_tra SNoR_E SNoR_SNoS_ SNoR_I H1 IH Hz Hx. }
apply SNoLt_SNoL_or_SNoR_impred (y + z) (x + x) Lyz Lxx H2.
- aby SNoLtLe SNoLeLt_tra SNoL_E SNoR_E SNo_add_SNo add_SNo_SNoR_interpolate L3 L1 Lxx Hz Hy2.
- aby SNoL_E add_SNo_com add_SNo_SNoL_interpolate L2 Hx.
- aby SNoLe_antisym SNoLtLe_or SNoR_E SNo_add_SNo add_SNo_SNoR_interpolate L3 L1 Lxx Hz Hy2.
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
{ aby SNo_minus_SNo Hx. }
claim Lmy: SNo (- y).
{ aby SNo_minus_SNo Hy2. }
claim Lmz: SNo (- z).
{ aby SNo_minus_SNo Hz. }
claim Lxx: SNo (x + x).
{ aby SNo_add_SNo Hx. }
claim Lyz: SNo (y + z).
{ aby SNo_add_SNo Hz Hy2. }
claim L1: SNo_max_of (SNoL (- x)) (- y).
{ aby SNoR_E SNoL_minus_SNoR minus_SNo_min_max Hy Hx. }
aby ReplI SNoR_E SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_invol SNoL_minus_SNoR minus_add_SNo_distr double_SNo_max_1 L1 Lyz Lxx Lmz Lmy Lmx H2 H1 Hz Hy2 Hx.
Qed.

Theorem finite_max_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_max_of X x.
claim L1: forall n, nat_p n -> forall X, (forall x :e X, SNo x) -> equip X (ordsucc n) -> exists x, SNo_max_of X x.
{ apply nat_ind.
  - aby and3I In_0_1 bijE equip_sym cases_1 SNoLe_ref.
  - let n. assume Hn.
    assume IHn: forall X, (forall x :e X, SNo x) -> equip X (ordsucc n) -> exists x, SNo_max_of X x.
    let X. assume HX.
    assume H1: equip X (ordsucc (ordsucc n)).
    apply equip_sym X (ordsucc (ordsucc n)) H1.
    let f. assume Hf: bij (ordsucc (ordsucc n)) X f.
    apply bijE (ordsucc (ordsucc n)) X f Hf. assume Hf1 Hf2 Hf3.
    set X' := {f i|i :e ordsucc n}.
    claim LX'1: X' c= X.
    { aby ReplE_impred ordsuccI1 Hf1. }
    claim LX'2: equip X' (ordsucc n).
    { apply equip_sym.
      aby ReplI ReplE_impred ordsuccI1 bijI Hf2.
    }
    apply IHn X' (fun x' Hx' => HX x' (LX'1 x' Hx')) LX'2.
    aby and3I ReplI ordsuccI2 ordsuccE SNoLtLe SNoLe_ref SNoLe_tra SNoLtLe_or LX'1 Hf3 Hf1 HX.
}
aby EmptyE Empty_eq nat_inv bijE omega_nat_p L1.
Qed.

Theorem finite_min_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_min_of X x.
let X.
assume HX: forall x :e X, SNo x.
assume H1: finite X.
assume H2: X <> 0.
set X' := {- x|x :e X}.
claim L1: forall z :e X', SNo z.
{ aby ReplE_impred SNo_minus_SNo HX. }
claim L2: finite X'.
{ apply H1.
  let n. assume H. apply H.
  assume Hn: n :e omega.
  aby ReplI ReplE_impred bijI equip_sym equip_tra minus_SNo_invol Hn HX.
}
aby EmptyE Empty_eq ReplI minus_SNo_max_min' finite_max_exists L2 L1 H2 HX.
Qed.

Theorem SNoS_omega_SNoL_max_exists : forall x :e SNoS_ omega, SNoL x = 0 \/ exists y, SNo_max_of (SNoL x) y.
aby xm omega_ordinal SNoS_E2 SNoL_E SNoS_omega_SNoL_finite finite_max_exists.
Qed.

Theorem SNoS_omega_SNoR_min_exists : forall x :e SNoS_ omega, SNoR x = 0 \/ exists y, SNo_min_of (SNoR x) y.
aby xm omega_ordinal SNoS_E2 SNoR_E SNoS_omega_SNoR_finite finite_min_exists.
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
{ aby SNo_eps_ Hk. }
claim Lek2: eps_ k :e SNoS_ omega.
{ aby SNo_eps_SNoS_omega Hk. }
apply nat_ind.
- aby nat_0 nat_p_omega omega_SNoS_omega mul_SNo_zeroR Lek.
- aby nat_1 nat_p_omega omega_SNo SNo_eps_SNoS_omega add_SNo_SNoS_omega add_SNo_1_ordsucc mul_SNo_oneR mul_SNo_distrL Lek Hk.
Qed.

Definition diadic_rational_p : set -> prop := fun x => exists k :e omega, exists m :e int, x = eps_ k * m.

Theorem diadic_rational_p_SNoS_omega: forall x, diadic_rational_p x -> x :e SNoS_ omega.
aby omega_nat_p omega_SNo SNo_eps_ minus_SNo_SNoS_omega mul_SNo_minus_distrR mul_minus_SNo_distrR int_SNo_cases nonneg_diadic_rational_p_SNoS_omega.
Qed.

Theorem int_diadic_rational_p : forall m :e int, diadic_rational_p m.
aby nat_0 nat_p_omega eps_0_1 mul_SNo_oneL int_SNo.
Qed.

Theorem omega_diadic_rational_p : forall m :e omega, diadic_rational_p m.
aby Subq_omega_int int_diadic_rational_p.
Qed.

Theorem eps_diadic_rational_p : forall k :e omega, diadic_rational_p (eps_ k).
aby nat_1 nat_p_omega SNo_eps_ mul_SNo_oneR Subq_omega_int.
Qed.

Theorem minus_SNo_diadic_rational_p : forall x, diadic_rational_p x -> diadic_rational_p (- x).
aby SNo_eps_ SNo_mul_SNo mul_SNo_minus_distrR mul_minus_SNo_distrR int_SNo int_minus_SNo.
Qed.

Theorem mul_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x * y).
aby SNo_eps_ add_SNo_In_omega SNo_mul_SNo mul_SNo_com_4_inner_mid int_SNo int_mul_SNo mul_SNo_eps_eps_add_SNo.
Qed.

Theorem add_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x + y).
let x y. assume Hx. apply Hx.
let k. assume H. apply H.
assume Hk: k :e omega.
claim Lek: SNo (eps_ k).
{ aby SNo_eps_ Hk. }
assume H. apply H.
let m. assume H. apply H.
assume Hm: m :e int.
assume Hxkm: x = eps_ k * m.
claim Lm: SNo m.
{ aby int_SNo Hm. }
claim Lekm: SNo (eps_ k * m).
{ aby SNo_mul_SNo Lm Lek. }
assume Hy. apply Hy.
let l. assume H. apply H.
assume Hl: l :e omega.
claim Lel: SNo (eps_ l).
{ aby SNo_eps_ Hl. }
assume H. apply H.
let n. assume H. apply H.
assume Hn: n :e int.
assume Hyln: y = eps_ l * n.
claim Ln: SNo n.
{ aby int_SNo Hn. }
claim Leln: SNo (eps_ l * n).
{ aby SNo_mul_SNo Ln Lel. }
prove exists k' :e omega, exists m' :e int, x + y = eps_ k' * m'.
witness (k + l). apply andI.
- aby add_SNo_In_omega Hl Hk.
- witness (2 ^ l * m + 2 ^ k * n).
  claim L2l: 2 ^ l :e int.
  { aby nat_2 omega_nat_p nat_p_omega Subq_omega_int nat_exp_SNo_nat Hl.
  }
  claim L2lm: 2 ^ l * m :e int.
  { aby int_mul_SNo L2l Hm.
  }
  claim L2k: 2 ^ k :e int.
  { aby nat_2 omega_nat_p nat_p_omega Subq_omega_int nat_exp_SNo_nat Hk.
  }
  claim L2kn: 2 ^ k * n :e int.
  { aby int_mul_SNo L2k Hn.
  }
  apply andI.
  + aby int_add_SNo L2kn L2lm.
  + prove x + y = eps_ (k + l) * (2 ^ l * m + 2 ^ k * n).
    rewrite <- mul_SNo_eps_eps_add_SNo k Hk l Hl.
    prove x + y = (eps_ k * eps_ l) * (2 ^ l * m + 2 ^ k * n).
    rewrite mul_SNo_distrL (eps_ k * eps_ l) (2 ^ l * m) (2 ^ k * n) (SNo_mul_SNo (eps_ k) (eps_ l) Lek Lel) (int_SNo (2 ^ l * m) L2lm) (int_SNo (2 ^ k * n) L2kn).
    aby omega_nat_p mul_SNo_assoc mul_SNo_oneL mul_SNo_com_4_inner_mid int_SNo mul_SNo_eps_power_2 L2k L2lm L2l Leln Hyln Hn Lel Hl Hxkm Hm Lek Hk.
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
{ aby nat_p_omega omega_ordinal SNoLev_ SNoS_I Hxn Hx Hn. }
claim L1: exists y, SNo_max_of (SNoL x) y.
{ apply SNoS_omega_SNoL_max_exists x LxSo.
  - aby EmptyE In_irref nat_p_omega SNoLev_ordinal SNoLt_trichotomy_or_impred SNoS_E2 SNoL_I ordinal_SNoLev SNo_max_ordinal SNo_minus_SNo minus_SNo_invol minus_SNo_Lev minus_SNo_Lt_contra1 omega_diadic_rational_p minus_SNo_diadic_rational_p HC Hxn Hx Hn.
  - assume H1. aby Hn IH Hx Hxn HC LxSo H1.
}
claim L2: exists z, SNo_min_of (SNoR x) z.
{ aby EmptyE In_irref nat_p_omega SNoLev_ordinal SNoLt_trichotomy_or_impred SNoS_E2 SNoR_I ordinal_SNoLev SNo_max_ordinal SNoS_omega_SNoR_min_exists omega_diadic_rational_p LxSo HC Hxn Hx Hn. }
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
{ aby SNo_add_SNo Hx. }
claim Lyz: SNo (y + z).
{ aby SNo_add_SNo Hz2 Hy2. }
claim Ldry: diadic_rational_p y.
{ aby Hy1b Hy2 Hxn IH. }
claim Ldrz: diadic_rational_p z.
{ aby Hz1b Hz2 Hxn IH. }
apply SNoLt_trichotomy_or_impred (x + x) (y + z) Lxx Lyz.
- rewrite add_SNo_com y z Hy2 Hz2.
  assume H1: x + x < z + y.
  apply double_SNo_min_1 x z Hx Hz y Hy2 Hy1c H1.
  aby nat_1 ordinal_TransSet nat_p_ordinal nat_p_omega SNoL_E double_eps_1 eps_diadic_rational_p mul_SNo_diadic_rational_p add_SNo_diadic_rational_p Ldrz Hz2 Hy1b Hy2 HC Hxn Hx IH Hn.
- aby nat_1 nat_p_omega double_eps_1 eps_diadic_rational_p mul_SNo_diadic_rational_p add_SNo_diadic_rational_p Ldrz Ldry Hz2 Hy2 HC Hx.
- assume H1: y + z < x + x.
  apply double_SNo_max_1 x y Hx Hy z Hz2 Hz1c H1.
  let w. assume H. aby nat_1 ordinal_TransSet nat_p_ordinal nat_p_omega SNoR_E double_eps_1 eps_diadic_rational_p mul_SNo_diadic_rational_p add_SNo_diadic_rational_p H Ldry Hz1b Hz2 Hy2 HC Hxn Hx IH Hn.
Qed.

Theorem SNoS_omega_diadic_rational_p: forall x :e SNoS_ omega, diadic_rational_p x.
aby omega_nat_p omega_ordinal SNoS_E2 SNoS_omega_diadic_rational_p_lem.
Qed.

Theorem mul_SNo_SNoS_omega : forall x y :e SNoS_ omega, x * y :e SNoS_ omega.
aby diadic_rational_p_SNoS_omega mul_SNo_diadic_rational_p SNoS_omega_diadic_rational_p.
Qed.

End DiadicRationals.

Opaque int.

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
aby neq_0_1 SNoLt_irref SNoLt_trichotomy_or_impred SNoLt_tra SNo_0 SNo_1 SNoLt_0_1 mul_SNo_zeroR mul_SNo_pos_neg.
Qed.

Theorem SNo_recip_lem1: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
aby SepE SNoL_E SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_0L add_SNo_minus_Lt1 add_SNo_minus_Lt1b add_SNo_minus_Lt2b SNo_mul_SNo mul_SNo_pos_neg mul_SNo_neg_pos SNo_recip_pos_pos.
Qed.

Theorem SNo_recip_lem2: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoL_pos x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
aby SepE SNoL_E SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_0L add_SNo_minus_Lt2 add_SNo_minus_Lt1b SNo_mul_SNo mul_SNo_neg_pos mul_SNo_neg_neg SNo_recip_pos_pos.
Qed.

Theorem SNo_recip_lem3: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> x * y < 1 -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> x * y' < 1.
aby SNoLt_tra SNoR_E SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_0L add_SNo_minus_Lt2 add_SNo_minus_Lt2b SNo_mul_SNo mul_SNo_pos_pos SNo_recip_pos_pos.
Qed.

Theorem SNo_recip_lem4: forall x x' x'i y y', SNo x -> 0 < x -> x' :e SNoR x -> SNo x'i -> x' * x'i = 1 -> SNo y -> 1 < x * y -> SNo y' -> 1 + - x * y' = (1 + - x * y) * (x' + - x) * x'i -> 1 < x * y'.
aby SNoLt_tra SNoR_E SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_0L add_SNo_minus_Lt1 add_SNo_minus_Lt1b add_SNo_minus_Lt2b SNo_mul_SNo mul_SNo_pos_pos mul_SNo_neg_pos SNo_recip_pos_pos.
Qed.

Definition SNo_recipauxset : set -> set -> set -> (set -> set) -> set := fun Y x X g => \/_ y :e Y, {(1 + (x' + - x) * y) * g x'|x' :e X}.

Theorem SNo_recipauxset_I: forall Y x X, forall g:set -> set,
 forall y :e Y, forall x' :e X, (1 + (x' + - x) * y) * g x' :e SNo_recipauxset Y x X g.
aby ReplI famunionI.
Qed.

Theorem SNo_recipauxset_E : forall Y x X, forall g:set -> set, forall z :e SNo_recipauxset Y x X g, forall p:prop, (forall y :e Y, forall x' :e X, z = (1 + (x' + - x) * y) * g x' -> p) -> p.
aby ReplE_impred famunionE_impred.
Qed.

Theorem SNo_recipauxset_ext: forall Y x X, forall g h:set -> set, (forall x' :e X, g x' = h x') -> SNo_recipauxset Y x X g = SNo_recipauxset Y x X h.
aby ReplEq_ext famunion_ext.
Qed.

Definition SNo_recipaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({0},0)
   (fun k p => (p 0 :\/: SNo_recipauxset (p 0) x (SNoR x) g
                    :\/: SNo_recipauxset (p 1) x (SNoL_pos x) g,
                p 1 :\/: SNo_recipauxset (p 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (p 1) x (SNoR x) g)).

Theorem SNo_recipaux_0: forall x, forall g:set -> set, SNo_recipaux x g 0 = ({0},0).
aby nat_primrec_0.
Qed.

Theorem SNo_recipaux_S: forall x, forall g:set -> set, forall n, nat_p n ->
   SNo_recipaux x g (ordsucc n)
 = (SNo_recipaux x g n 0 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoR x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoL_pos x) g,
    SNo_recipaux x g n 1 :\/: SNo_recipauxset (SNo_recipaux x g n 0) x (SNoL_pos x) g
        :\/: SNo_recipauxset (SNo_recipaux x g n 1) x (SNoR x) g).
aby nat_primrec_S.
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
{ aby SNoLev_ordinal SNoS_E2 SNo_1 SNo_minus_SNo SNo_add_SNo SNo_mul_SNo Hg Hx. }
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
  aby SNo_minus_SNo mul_SNo_assoc Hx Hxpos Hg L1 Hx' Hx'pos Hy Hy' Hx'1 Hgx'1 Hgx'2.
}
apply nat_ind.
- aby EmptyE SingE tuple_2_0_eq tuple_2_1_eq SNo_0 SNoLt_0_1 mul_SNo_zeroR SNo_recipaux_0 Hx.
- let k.
  assume Hk: nat_p k.
  assume IH. apply IH.
  assume IH1: forall y :e r k 0, SNo y /\ x * y < 1.
  assume IH2: forall y :e r k 1, SNo y /\ 1 < x * y.
  apply andI.
  + aby binunionE SepE tuple_2_0_eq SNoLt_tra SNoS_I2 SNoL_E SNoR_E SNo_0 SNo_recip_lem2 SNo_recip_lem3 SNo_recipauxset_E SNo_recipaux_S IH2 IH1 Hk L2 L1 Hg Hxpos Hx.
  + let y'.
    aby binunionE SepE tuple_2_1_eq SNoLt_tra SNoS_I2 SNoL_E SNoR_E SNo_0 SNo_recip_lem1 SNo_recip_lem4 SNo_recipauxset_E SNo_recipaux_S IH2 IH1 Hk L2 L1 Hg Hxpos Hx.
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
{ aby SNo_recipaux_lem1 Hx Hxpos Hg. }
apply and3I.
- aby famunionE_impred omega_nat_p L1.
- aby famunionE_impred omega_nat_p L1.
- let w. assume Hw. let z. assume Hz.
  aby famunionE_impred omega_nat_p SNoLtLe SNoLt_irref SNoLt_tra SNoLeLt_tra SNoLtLe_or SNo_1 SNo_mul_SNo nonneg_mul_SNo_Le Hz Hw L1 Hxpos Hx.
Qed.

Theorem SNo_recipaux_ext: forall x, SNo x -> forall g h:set -> set, (forall x' :e SNoS_ (SNoLev x), g x' = h x') -> forall k, nat_p k -> SNo_recipaux x g k = SNo_recipaux x h k.
let x. assume Hx. let g h.
assume Hgh.
apply nat_ind.
- aby SNo_recipaux_0.
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
  { aby SepE1 SNoS_I2 SNoL_E SNoR_E SNo_recipauxset_ext Hgh Hx. }
  claim L2: SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) g
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) g
          = SNo_recipaux x h k 1 :\/: SNo_recipauxset (SNo_recipaux x h k 0) x (SNoL_pos x) h
                    :\/: SNo_recipauxset (SNo_recipaux x h k 1) x (SNoR x) h.
  { aby SepE1 SNoS_I2 SNoL_E SNo_recipauxset_ext Hgh Hx. }
  aby L2 L1.
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
- aby famunion_ext omega_nat_p SNo_recipaux_ext Hgh Hx.
- aby famunion_ext omega_nat_p SNo_recipaux_ext Hgh Hx.
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
{ aby SNo_recipaux_lem1 Hx IH Hxpos. }
claim L1L: forall w :e L, x * w < 1.
{ aby famunionE_impred omega_nat_p L1. }
claim L1R: forall z :e R, 1 < x * z.
{ aby famunionE_impred omega_nat_p L1. }
claim L2: SNoCutP L R.
{ aby SNo_recipaux_lem2 Hx IH Hxpos L1 L1L L1R. }
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
{ aby SNo_mul_SNo Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5. }
claim L4: 0 < y.
{ aby SingI famunionI nat_0 nat_p_omega tuple_2_0_eq SNo_recipaux_0 H3. }
claim L5: 0 < x * y.
{ aby mul_SNo_pos_pos Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4. }
claim L6: forall w :e SNoL y, exists w' :e L, w <= w'.
{ aby SNoL_SNoCutP_ex Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5. }
claim L7: forall z :e SNoR y, exists z' :e R, z' <= z.
{ aby SNoR_SNoCutP_ex Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6. }
apply andI.
- aby H1.
- prove x * y = 1.
  apply dneg.
  assume HC: x * y <> 1.
  apply SNoLt_trichotomy_or_impred (x * y) 1 L3 SNo_1.
  + assume H6: x * y < 1.
    claim L8: 1 :e SNoR (x * y).
    { aby ordinal_1 ordinal_In_Or_Subq SNoLev_ordinal SNoR_I ordinal_SNoLev SNo_1 pos_low_eq_one H6 HC L5 L3. }
    claim L9: forall v w w', SNo v -> SNo w -> SNo w' -> v :e SNoS_ (SNoLev x) -> 0 < v -> v * y + x * w <= 1 + v * w -> (1 + (v + - x) * w') * recip_SNo_pos v :e L -> (- v + x) * w' <= (- v + x) * w -> False.
    { let v w w'. assume Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8.
      set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
      claim Lw''1: SNo w''.
      { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L8 Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8. }
      apply SNoLt_irref 1.
      prove 1 < 1.
      apply SNoLtLe_tra 1 (1 + v * (y + - w'')) 1 SNo_1 (SNo_add_SNo 1 (v * (y + - w'')) SNo_1 (SNo_mul_SNo v (y + - w'') Hv1 (SNo_add_SNo y (- w'') H1 (SNo_minus_SNo w'' Lw''1)))) SNo_1.
      - aby SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_Lt2 add_SNo_0R SNoLt_minus_pos SNo_mul_SNo mul_SNo_pos_pos Lw''1 Hw'' Hvpos Hv1 H3 H1.
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
        + aby SNo_minus_SNo SNo_add_SNo add_SNo_Le1 SNo_mul_SNo H8 Hw' Hw1 Hv1 H1 Hx.
        + prove (- v + x) * w + v * y <= 1.
          rewrite mul_SNo_distrR (- v) x w (SNo_minus_SNo v Hv1) Hx Hw1.
          aby SNo_1 SNo_minus_SNo minus_SNo_invol SNo_add_SNo add_SNo_com add_SNo_assoc add_SNo_minus_Le2 SNo_mul_SNo mul_SNo_minus_distrL H7 Hw1 Hv1 H1 Hx.
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
        { aby SNoS_I2 Hv2 Hv1 Hx. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        apply L7 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e R.
        assume Hw'2: w' <= w.
        claim Lw': SNo w'.
        { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L8 L9 Hv Hw H7 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 LvS Lxw Hw' Hw'1 Hw'2. }
        claim Lxw': SNo (x * w').
        { aby SNo_mul_SNo Lw' Hx. }
        claim Lvpos: 0 < v.
        { apply SNoLtLe_or 0 v SNo_0 Hv1.
          - aby.
          - assume H8: v <= 0. prove False.
            apply SNoLt_irref 1.
            prove 1 < 1.
            apply SNoLtLe_tra 1 (x * w') 1 SNo_1 Lxw' SNo_1.
            + aby Hw'1 L1R.
            + prove x * w' <= 1.
              apply SNoLe_tra (x * w') (x * w) 1 Lxw' Lxw SNo_1.
              * aby SNoLtLe nonneg_mul_SNo_Le Lw' Hw'2 Hw1 Hxpos Hx.  
              * { prove x * w <= 1.
                  apply SNoLe_tra (x * w) (v * (y + - w) + x * w) 1 Lxw (SNo_add_SNo (v * (y + - w)) (x * w) (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))) Lxw) SNo_1.
                  - aby SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_0L add_SNo_minus_Lt1b SNo_mul_SNo mul_SNo_nonpos_neg H8 Lxw Hw3 Hw1 Hv1 H1.
                  - prove v * (y + - w) + x * w <= 1.
                    rewrite mul_SNo_distrL v y (- w) Hv1 H1 (SNo_minus_SNo w Hw1).
                    aby SNo_1 SNo_minus_SNo minus_SNo_invol SNo_add_SNo add_SNo_com_3b_1_2 add_SNo_minus_Le2 SNo_mul_SNo mul_SNo_minus_distrR mul_minus_SNo_distrR Lxw Hw1 Hv1 H7 H1.
                }
        }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e L.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 1) w' Hw'1.
          aby binunionI2 famunionI SepI omega_nat_p omega_ordsucc tuple_2_0_eq SNo_recipauxset_I SNo_recipaux_S Lvpos Hv.
        }
        aby SNoLtLe SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_minus_Le2b nonneg_mul_SNo_Le Lw'' Lvpos Lw' Hw'2 LvS Hw1 Hv3 Hv1 H7 L9 Hx.
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
        { aby SNoS_I2 Hv2 Hv1 Hx. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        apply L6 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e L.
        assume Hw'2: w <= w'.
        claim Lw': SNo w'.
        { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L8 L9 Hv Hw H7 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 LvS Lxw Hw' Hw'1 Hw'2. }
        claim Lxw': SNo (x * w').
        { aby SNo_mul_SNo Lw' Hx. }
        claim Lvpos: 0 < v.
        { aby SNoLt_tra SNo_0 Hv3 Hv1 Hxpos Hx. }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e L.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 0) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 0.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 0) (ordsucc k) w'' (omega_ordsucc k Hk).
          aby binunionI1 binunionI2 omega_nat_p tuple_2_0_eq SNo_recipauxset_I SNo_recipaux_S H9 Hk Hv.
        }
        aby SNoLtLe SNo_0 SNo_minus_SNo minus_SNo_invol SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_minus_Le2 nonpos_mul_SNo_Le Lw'' Lvpos Lw' Hw'2 LvS Hw1 Hv3 Hv1 H7 L9 Hx.
      }
  + aby HC.
  + assume H6: 1 < x * y.
    claim L10: 1 :e SNoL (x * y).
    { aby ordinal_1 ordinal_In_Or_Subq SNoLev_ordinal SNoL_I ordinal_SNoLev SNo_1 pos_low_eq_one H6 HC L5 L3. }
    claim L11: forall v w w', SNo v -> SNo w -> SNo w' -> v :e SNoS_ (SNoLev x) -> 0 < v -> 1 + v * w <= v * y + x * w -> (1 + (v + - x) * w') * recip_SNo_pos v :e R -> (- v + x) * w <= (- v + x) * w' -> False.
    { let v w w'. assume Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8.
      set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
      claim Lw''1: SNo w''.
      { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L10 Hv1 Hw1 Hw' HvS Hvpos H7 Hw'' H8. }
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
          aby SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_assoc add_SNo_minus_Le2b SNo_mul_SNo mul_SNo_minus_distrL H7 Hw1 Hv1 H1 Hx.
        + aby SNo_minus_SNo SNo_add_SNo add_SNo_Le1 SNo_mul_SNo H8 Hw' Hw1 Hv1 H1 Hx.
      - aby SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_Lt2 add_SNo_0L add_SNo_0R add_SNo_minus_Lt1b SNo_mul_SNo mul_SNo_pos_neg Lw''1 Hw'' Hvpos Hv1 H4 H1.
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
        { aby SNoS_I2 Hv2 Hv1 Hx. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        apply L6 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e L.
        assume Hw'2: w <= w'.
        claim Lw': SNo w'.
        { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L10 L11 Hv Hw H7 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 LvS Lxw Hw' Hw'1 Hw'2. }
        claim Lxw': SNo (x * w').
        { aby SNo_mul_SNo Lw' Hx. }
        claim Lvpos: 0 < v.
        { apply SNoLtLe_or 0 v SNo_0 Hv1.
          - aby.
          - assume H8: v <= 0. prove False.
            apply SNoLt_irref 1.
            prove 1 < 1.
            apply SNoLeLt_tra 1 (x * w') 1 SNo_1 Lxw' SNo_1.
            + prove 1 <= x * w'.
              apply SNoLe_tra 1 (x * w) (x * w') SNo_1 Lxw Lxw'.
              * { prove 1 <= x * w.
                  apply SNoLe_tra 1 (v * (y + - w) + x * w) (x * w) SNo_1 (SNo_add_SNo (v * (y + - w)) (x * w) (SNo_mul_SNo v (y + - w) Hv1 (SNo_add_SNo y (- w) H1 (SNo_minus_SNo w Hw1))) Lxw) Lxw.
                  - aby SNo_1 SNo_minus_SNo SNo_add_SNo add_SNo_com_3b_1_2 add_SNo_minus_Le2b SNo_mul_SNo mul_SNo_minus_distrR mul_SNo_distrL mul_minus_SNo_distrR Lxw Hw1 Hv1 H7 H1.
                  - aby SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_0L add_SNo_minus_Lt2b SNo_mul_SNo mul_SNo_nonpos_pos H8 Lxw Hw3 Hw1 Hv1 H1.
                }
              * aby SNoLtLe nonneg_mul_SNo_Le Lw' Hw'2 Hw1 Hxpos Hx.
            + aby Hw'1 L1L.
        }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e R.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 0) w' Hw'1.
          let k. assume Hk: k :e omega.
          assume H9: w' :e SNo_recipaux x recip_SNo_pos k 0.
          apply famunionI omega (fun k => SNo_recipaux x recip_SNo_pos k 1) (ordsucc k) w'' (omega_ordsucc k Hk).
          aby binunionI1 binunionI2 SepI omega_nat_p tuple_2_1_eq SNo_recipauxset_I SNo_recipaux_S H9 Hk Lvpos Hv.
        }
        aby SNoLtLe SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_minus_Le2b nonneg_mul_SNo_Le Lw'' Lvpos Lw' Hw'2 LvS Hw1 Hv3 Hv1 H7 L11 Hx.
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
        { aby SNoS_I2 Hv2 Hv1 Hx. }
        claim Lvpos: 0 < v.
        { aby SNoLt_tra SNo_0 Hv3 Hv1 Hxpos Hx. }
        claim Lxw: SNo (x * w).
        { aby SNo_mul_SNo Hw1 Hx. }
        apply L7 w Hw.
        let w'. assume Hw'. apply Hw'.
        assume Hw'1: w' :e R.
        assume Hw'2: w' <= w.
        claim Lw': SNo w'.
        { aby Hx IH Hxpos L1 L1L L1R L2 HLHR HL HR HLR H1 H2 H3 H4 H5 L3 L4 L5 L6 L7 HC H6 L10 L11 Hv Hw H7 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 LvS Lvpos Lxw Hw' Hw'1 Hw'2. }
        claim Lxw': SNo (x * w').
        { aby SNo_mul_SNo Lw' Hx. }
        set w'' := (1 + (v + - x) * w') * recip_SNo_pos v.
        claim Lw'': w'' :e R.
        { apply famunionE_impred omega (fun k => SNo_recipaux x recip_SNo_pos k 1) w' Hw'1.
          aby binunionI2 famunionI omega_nat_p omega_ordsucc tuple_2_1_eq SNo_recipauxset_I SNo_recipaux_S Hv.
        }
        aby SNoLtLe SNo_0 SNo_minus_SNo minus_SNo_invol SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_minus_Le2 nonpos_mul_SNo_Le Lw'' Lw' Hw'2 Lvpos LvS Hw1 Hv3 Hv1 H7 L11 Hx.
      }
Qed.

Theorem SNo_recip_SNo_pos: forall x, SNo x -> 0 < x -> SNo (recip_SNo_pos x).
aby recip_SNo_pos_prop1.
Qed.

Theorem recip_SNo_pos_invR: forall x, SNo x -> 0 < x -> x * recip_SNo_pos x = 1.
aby recip_SNo_pos_prop1.
Qed.

Theorem recip_SNo_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
aby neq_1_0 SNoLt_irref SNoLt_trichotomy_or_impred SNoLt_tra SNo_0 SNo_1 SNoLt_0_1 mul_SNo_zeroR mul_SNo_pos_neg SNo_recip_SNo_pos recip_SNo_pos_invR.
Qed.

Theorem recip_SNo_pos_invol: forall x, SNo x -> 0 < x -> recip_SNo_pos (recip_SNo_pos x) = x.
aby SNoLt_irref mul_SNo_com mul_SNo_nonzero_cancel SNo_recip_SNo_pos recip_SNo_pos_invR recip_SNo_pos_is_pos.
Qed.

Theorem recip_SNo_pos_eps_: forall n, nat_p n -> recip_SNo_pos (eps_ n) = 2 ^ n.
aby nat_p_omega SNoLt_irref SNo_2 SNo_eps_ SNo_eps_pos mul_SNo_nonzero_cancel SNo_exp_SNo_nat mul_SNo_eps_power_2 SNo_recip_SNo_pos recip_SNo_pos_invR.
Qed.

Theorem recip_SNo_pos_pow_2: forall n, nat_p n -> recip_SNo_pos (2 ^ n) = eps_ n.
aby nat_p_omega SNo_eps_ SNo_eps_pos recip_SNo_pos_invol recip_SNo_pos_eps_.
Qed.

Theorem recip_SNo_pos_2: recip_SNo_pos 2 = eps_ 1.
aby nat_1 SNo_2 exp_SNo_nat_1 recip_SNo_pos_pow_2.
Qed.

End recip_SNo_pos.
Definition recip_SNo : set -> set := fun x => if 0 < x then recip_SNo_pos x else if x < 0 then - recip_SNo_pos (- x) else 0.

Theorem recip_SNo_poscase: forall x, 0 < x -> recip_SNo x = recip_SNo_pos x.
aby If_i_1.
Qed.

Theorem recip_SNo_negcase: forall x, SNo x -> x < 0 -> recip_SNo x = - recip_SNo_pos (- x).
aby If_i_0 If_i_1 SNoLt_irref SNoLt_tra SNo_0.
Qed.

Theorem recip_SNo_0: recip_SNo 0 = 0.
aby If_i_0 SNoLt_irref.
Qed.

Theorem SNo_recip_SNo: forall x, SNo x -> SNo (recip_SNo x).
aby SNoLt_trichotomy_or_impred SNo_0 SNo_minus_SNo minus_SNo_Lt_contra2 minus_SNo_0 SNo_recip_SNo_pos recip_SNo_poscase recip_SNo_negcase recip_SNo_0.
Qed.

Theorem recip_SNo_invR: forall x, SNo x -> x <> 0 -> x * recip_SNo x = 1.
aby SNoLt_trichotomy_or_impred SNo_0 SNo_minus_SNo minus_SNo_Lt_contra2 minus_SNo_0 mul_SNo_minus_distrL mul_SNo_minus_distrR mul_minus_SNo_distrR SNo_recip_SNo_pos recip_SNo_pos_invR recip_SNo_poscase recip_SNo_negcase.
Qed.

Theorem recip_SNo_invL: forall x, SNo x -> x <> 0 -> recip_SNo x * x = 1.
aby mul_SNo_com SNo_recip_SNo recip_SNo_invR.
Qed.

Theorem mul_SNo_nonzero_cancel_L: forall x y z, SNo x -> x <> 0 -> SNo y -> SNo z -> x * y = x * z -> y = z.
aby mul_SNo_assoc mul_SNo_oneL SNo_recip_SNo recip_SNo_invL.
Qed.

Theorem recip_SNo_pow_2 : forall n, nat_p n -> recip_SNo (2 ^ n) = eps_ n.
aby SNo_2 SNoLt_0_2 exp_SNo_nat_pos recip_SNo_pos_pow_2 recip_SNo_poscase.
Qed.

Theorem recip_SNo_of_pos_is_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo x.
aby recip_SNo_pos_is_pos recip_SNo_poscase.
Qed.

Definition div_SNo : set -> set -> set := fun x y => x * recip_SNo y.

Infix :/: 353 := div_SNo.

Theorem SNo_div_SNo: forall x y, SNo x -> SNo y -> SNo (x :/: y).
aby SNo_mul_SNo SNo_recip_SNo.
Qed.

Theorem div_SNo_0_num: forall x, SNo x -> 0 :/: x = 0.
aby mul_SNo_zeroL SNo_recip_SNo.
Qed.

Theorem div_SNo_0_denum: forall x, SNo x -> x :/: 0 = 0.
aby mul_SNo_zeroR recip_SNo_0.
Qed.

Theorem mul_div_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x :/: y) * y = x.
aby mul_SNo_oneR mul_SNo_assoc SNo_recip_SNo recip_SNo_invL.
Qed.

Theorem mul_div_SNo_invR: forall x y, SNo x -> SNo y -> y <> 0 -> y * (x :/: y) = x.
aby mul_SNo_com SNo_div_SNo mul_div_SNo_invL.
Qed.

Theorem mul_div_SNo_R: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) * z = (x * z) :/: y.
aby SNo_mul_SNo mul_SNo_assoc mul_SNo_zeroL mul_SNo_nonzero_cancel mul_SNo_nonzero_cancel_L SNo_div_SNo div_SNo_0_denum mul_div_SNo_invR.
Qed.

Theorem mul_div_SNo_L: forall x y z, SNo x -> SNo y -> SNo z -> z * (x :/: y) = (z * x) :/: y.
aby mul_SNo_com SNo_div_SNo mul_div_SNo_R.
Qed.

Theorem div_mul_SNo_invL: forall x y, SNo x -> SNo y -> y <> 0 -> (x * y) :/: y = x.
aby mul_div_SNo_invL mul_div_SNo_R.
Qed.

Theorem div_div_SNo: forall x y z, SNo x -> SNo y -> SNo z -> (x :/: y) :/: z = x :/: (y * z).
aby SNo_0 SNo_mul_SNo mul_SNo_zeroR mul_SNo_assoc mul_SNo_zeroL mul_SNo_nonzero_cancel mul_SNo_nonzero_cancel_L SNo_div_SNo div_SNo_0_num div_SNo_0_denum mul_div_SNo_invR.
Qed.

Theorem mul_div_SNo_both: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x :/: y) * (z :/: w) = (x * z) :/: (y * w).
aby SNo_mul_SNo SNo_div_SNo mul_div_SNo_R mul_div_SNo_L div_div_SNo.
Qed.

Theorem recip_SNo_pos_pos: forall x, SNo x -> 0 < x -> 0 < recip_SNo_pos x.
aby SNoLtLe SNoLt_irref SNoLtLe_tra SNoLtLe_or SNo_0 SNo_1 SNoLt_0_1 mul_SNo_zeroR nonneg_mul_SNo_Le SNo_recip_SNo_pos recip_SNo_pos_invR.
Qed.

Theorem div_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x :/: y.
aby mul_SNo_pos_pos SNo_recip_SNo recip_SNo_of_pos_is_pos.
Qed.

Theorem div_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x :/: y < 0.
aby mul_SNo_neg_pos SNo_recip_SNo recip_SNo_of_pos_is_pos.
Qed.

Theorem div_SNo_pos_LtL : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x < z * y -> x :/: y < z.
aby SNoLt_irref SNo_mul_SNo mul_SNo_oneR mul_SNo_assoc pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_invR recip_SNo_of_pos_is_pos.
Qed.

Theorem div_SNo_pos_LtR : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z * y < x -> z < x :/: y.
aby SNoLt_irref SNo_mul_SNo mul_SNo_oneR mul_SNo_assoc pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_invR recip_SNo_of_pos_is_pos.
Qed.

Theorem div_SNo_pos_LtL' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> x :/: y < z -> x < z * y.
aby SNoLt_irref mul_SNo_oneR mul_SNo_assoc pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_invL SNo_div_SNo.
Qed.

Theorem div_SNo_pos_LtR' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < y -> z < x :/: y -> z * y < x.
aby SNoLt_irref mul_SNo_oneR mul_SNo_assoc pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_invL SNo_div_SNo.
Qed.

Theorem mul_div_SNo_nonzero_eq: forall x y z, SNo x -> SNo y -> SNo z -> y <> 0 -> x = y * z -> x :/: y = z.
aby mul_SNo_nonzero_cancel mul_SNo_nonzero_cancel_L SNo_div_SNo mul_div_SNo_invR.
Qed.

End SurrealDiv.

Opaque recip_SNo_pos recip_SNo.

Section Reals.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Theorem SNoS_omega_drat_intvl : forall x :e SNoS_ omega,
  forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
let x. assume Hx.
apply SNoS_E2 omega omega_ordinal x Hx.
assume Hx1 Hx2 Hx3 Hx4.
let k. assume Hk. prove exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
claim Lk1: SNo (eps_ (ordsucc k)).
{ aby omega_ordsucc SNo_eps_ Hk. }
witness x + - eps_ (ordsucc k).
apply andI.
- aby omega_ordsucc SNo_eps_SNoS_omega minus_SNo_SNoS_omega add_SNo_SNoS_omega Hk Hx.
- aby omega_nat_p omega_ordsucc SNo_minus_SNo SNo_add_SNo add_SNo_0R add_SNo_minus_SNo_linv add_SNo_com_4_inner_mid add_SNo_minus_Lt1b add_SNo_eps_Lt eps_ordsucc_half_add Lk1 Hk Hx3.
Qed.

Theorem SNoS_ordsucc_omega_bdd_above : forall x :e SNoS_ (ordsucc omega), x < omega -> exists N :e omega, x < N.
aby In_irref In_no2cycle ordsuccI2 ordsuccE ordinal_ordsucc omega_ordsucc omega_ordinal ordsucc_omega_ordinal SNoLev_ordinal SNoLtE SNoLtLe_tra SNoS_E2 ordinal_SNo ordinal_SNoLev ordinal_SNoLev_max ordinal_SNoLev_max_2 SNo_omega.
Qed.

Theorem SNoS_ordsucc_omega_bdd_below : forall x :e SNoS_ (ordsucc omega), - omega < x -> exists N :e omega, - N < x.
aby ordsucc_omega_ordinal SNoS_E2 omega_SNo SNo_omega minus_SNo_SNoS_ minus_SNo_Lt_contra1 SNoS_ordsucc_omega_bdd_above.
Qed.

Theorem SNoS_ordsucc_omega_bdd_drat_intvl : forall x :e SNoS_ (ordsucc omega),
    - omega < x -> x < omega
 -> forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
let x. assume Hx1 Hx2 Hx3.
apply SNoS_E2 (ordsucc omega) ordsucc_omega_ordinal x Hx1.
assume Hx1a Hx1b Hx1c Hx1d.
apply dneg.
assume HC: ~(forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k).
claim L1: x /:e SNoS_ omega.
{ assume H1: x :e SNoS_ omega.
  aby SNoS_omega_drat_intvl H1 HC.
}
claim L2: forall k, nat_p k -> exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
{ apply nat_ind.
  - prove exists q :e SNoS_ omega, q < x /\ x < q + eps_ 0.
    rewrite eps_0_1.
    prove exists q :e SNoS_ omega, q < x /\ x < q + 1.
    claim L1a: forall N, nat_p N -> - N < x -> x < N -> exists q :e SNoS_ omega, q < x /\ x < q + 1.
    { apply nat_ind.
      - aby SNoLt_irref SNoLt_tra SNo_0 minus_SNo_0 Hx1c.
      - aby nat_p_omega omega_ordsucc SNoLt_trichotomy_or_impred nat_p_SNo omega_SNoS_omega SNo_1 SNo_minus_SNo minus_SNo_SNoS_omega add_SNo_minus_R2' minus_add_SNo_distr add_SNo_1_ordsucc L1 Hx1c.
    }
    aby omega_nat_p SNoLt_trichotomy_or_impred SNoLt_tra omega_SNo SNo_minus_SNo minus_SNo_Lt_contra SNoS_ordsucc_omega_bdd_above SNoS_ordsucc_omega_bdd_below L1a Hx1c Hx3 Hx2 Hx1.
  - aby nat_p_omega omega_ordsucc omega_ordinal SNoLt_trichotomy_or_impred SNoS_E2 SNo_eps_ SNo_eps_SNoS_omega SNo_add_SNo add_SNo_assoc add_SNo_SNoS_omega eps_ordsucc_half_add L1 Hx1c.
}
aby omega_nat_p L2 HC.
Qed.

Definition real : set := {x :e SNoS_ (ordsucc omega)| x <> omega /\ x <> - omega /\ (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)}.

Theorem real_I : forall x :e SNoS_ (ordsucc omega),
    x <> omega
 -> x <> - omega
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> x :e real.
aby and3I SepI.
Qed.

Theorem real_E : forall x :e real,
 forall p:prop,
      (SNo x
    -> SNoLev x :e ordsucc omega
    -> x :e SNoS_ (ordsucc omega)
    -> - omega < x
    -> x < omega
    -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
    -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
    -> p)
   -> p.
aby SepE omega_ordinal ordsucc_omega_ordinal SNoLeE SNoS_E2 ordinal_SNoLev_max_2 SNo_omega SNo_minus_SNo mordinal_SNoLev_min_2 SNoS_ordsucc_omega_bdd_drat_intvl.
Qed.

Theorem real_SNo : forall x :e real, SNo x.
aby real_E.
Qed.

Theorem real_SNoS_omega_prop : forall x :e real, forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
aby real_E.
Qed.

Theorem SNoS_omega_real : SNoS_ omega c= real.
let x. assume Hx: x :e SNoS_ omega.
apply SNoS_E2 omega omega_ordinal x Hx.
assume Hx1 Hx2 Hx3 Hx4.
apply real_I.
- aby ordsuccI1 omega_ordinal ordsucc_omega_ordinal SNoS_Subq Hx.
- aby In_irref omega_ordinal ordinal_SNoLev Hx1.
- aby In_irref omega_ordinal ordinal_SNoLev SNo_omega minus_SNo_Lev Hx1.
- aby ordsuccI2 ordinal_ordsucc omega_nat_p omega_ordinal SNoLt_irref SNoLt_trichotomy_or_impred SNoLt_tra SNoS_I SNoS_E2 SNo_eps_ SNo_pos_eps_Lt minus_SNo_SNoS_omega add_SNo_SNoS_omega SNoLt_minus_pos pos_abs_SNo abs_SNo_dist_swap Hx3 Hx.
Qed.

Theorem real_0 : 0 :e real.
aby nat_0 nat_p_omega omega_SNoS_omega SNoS_omega_real.
Qed.

Theorem real_1 : 1 :e real.
aby nat_1 nat_p_omega omega_SNoS_omega SNoS_omega_real.
Qed.

Theorem SNoLev_In_real_SNoS_omega : forall x :e real, forall w, SNo w -> SNoLev w :e SNoLev x -> w :e SNoS_ omega.
aby ordsuccE omega_TransSet omega_ordinal SNoLev_ SNoS_I real_E.
Qed.

Theorem real_SNoCut_SNoS_omega: forall L R c= SNoS_ omega, SNoCutP L R
 -> L <> 0
 -> R <> 0
 -> (forall w :e L, exists w' :e L, w < w')
 -> (forall z :e R, exists z' :e R, z' < z)
 -> SNoCut L R :e real.
let L. assume HL. let R. assume HR.
assume HLR. apply HLR. assume H. apply H.
assume HLR1: forall w :e L, SNo w.
assume HLR2: forall z :e R, SNo z.
assume HLR3: forall w :e L, forall z :e R, w < z.
assume HL0: L <> 0.
assume HR0: R <> 0.
assume HL1: forall w :e L, exists w' :e L, w < w'.
assume HR1: forall z :e R, exists z' :e R, z' < z.
set x := SNoCut L R.
apply SNoCutP_SNoCut_impred L R HLR.
assume H1: SNo x.
assume H2: SNoLev x :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall w :e L, w < x.
assume H4: forall z :e R, x < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u.
claim Lo: ordinal ((\/_ w :e L, ordsucc (SNoLev w)) :\/: (\/_ z :e R, ordsucc (SNoLev z))).
{ aby ordinal_ordsucc ordinal_famunion ordinal_binunion SNoLev_ordinal HLR2 HLR1. }
claim LLRsoo: ordsucc ((\/_ w :e L, ordsucc (SNoLev w)) :\/: (\/_ z :e R, ordsucc (SNoLev z))) c= ordsucc omega.
{ aby binunionE famunionE_impred In_irref In_no2cycle ordsuccI2 ordsuccE ordinal_ordsucc_In_Subq ordinal_In_Or_Subq omega_ordinal ordsucc_omega_ordinal SNoS_E2 Lo HR HL. }
apply ordsuccE omega (SNoLev x) (LLRsoo (SNoLev x) H2).
- aby omega_ordinal SNoLev_ SNoS_I SNoS_omega_real H1.
- assume H6: SNoLev x = omega.
  prove x :e real.
  apply real_I.
  + aby ordsuccI2 ordsucc_omega_ordinal SNoLev_ SNoS_I H6 H1.
  + assume H7: x = omega.
    aby Empty_eq omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 ordinal_SNoLev_max H7 H4 H1 HR0 HLR2 HR.
  + assume H7: x = - omega.
    aby Empty_eq omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 ordinal_SNoLev_max SNo_omega SNo_minus_SNo minus_SNo_Lev minus_SNo_Lt_contra1 H7 H3 H1 HL0 HLR1 HL.
  + let q. assume Hq: q :e SNoS_ omega.
    assume H7: forall k :e omega, abs_SNo (q + - x) < eps_ k.
    prove False.
    apply SNoS_E2 omega omega_ordinal q Hq.
    assume Hq1: SNoLev q :e omega.
    assume Hq2: ordinal (SNoLev q).
    assume Hq3: SNo q.
    assume Hq4: SNo_ (SNoLev q) q.
    claim LqL: forall w :e L, w < q.
    { let w. assume Hw: w :e L.
      apply SNoLtLe_or w q (HLR1 w Hw) Hq3.
      - aby.
      - assume H8: q <= w. prove False.
        apply HL1 w Hw.
        let w'. assume H. apply H.
        assume H9: w' :e L.
        assume H10: w < w'.
        claim LqL1: w' + - q :e SNoS_ omega.
        { aby minus_SNo_SNoS_omega add_SNo_SNoS_omega H9 Hq HL. }
        apply SNoS_E2 omega omega_ordinal (w' + - q) LqL1.
        assume Hw'q1: SNoLev (w' + - q) :e omega.
        assume Hw'q2: ordinal (SNoLev (w' + - q)).
        assume Hw'q3: SNo (w' + - q).
        assume Hw'q4: SNo_ (SNoLev (w' + - q)) (w' + - q).
        claim LqL2: 0 < w' + - q.
        { aby SNoLeLt_tra SNoLt_minus_pos H10 H9 H8 Hw Hq3 HLR1. }
        set k := SNoLev (w' + - q).
        claim LqL3: w' + - q :e SNoS_ (ordsucc k).
        { aby ordsuccI2 ordinal_ordsucc nat_p_ordinal omega_nat_p SNoS_I Hw'q4 Hw'q1. }
        aby omega_nat_p SNoLt_irref SNoLt_tra SNoLtLe_or SNo_0 SNo_eps_ SNo_eps_pos SNo_pos_eps_Lt SNo_minus_SNo SNo_add_SNo add_SNo_Lt1 nonneg_abs_SNo abs_SNo_dist_swap LqL3 LqL2 Hw'q3 Hw'q1 H9 Hq3 H7 H3 H1 HLR1.
    }
    claim LqR: forall z :e R, q < z.
    { let z. assume Hz: z :e R.
      apply SNoLtLe_or q z Hq3 (HLR2 z Hz).
      - aby.
      - assume H8: z <= q. prove False.
        apply HR1 z Hz.
        let z'. assume H. apply H.
        assume H9: z' :e R.
        assume H10: z' < z.
        claim LqR1: q + - z' :e SNoS_ omega.
        { aby minus_SNo_SNoS_omega add_SNo_SNoS_omega H9 Hq HR. }
        apply SNoS_E2 omega omega_ordinal (q + - z') LqR1.
        aby ordsuccI2 ordinal_ordsucc nat_p_ordinal omega_nat_p SNoLt_irref SNoLt_tra SNoLtLe_tra SNoLtLe_or SNoS_I SNo_0 SNo_eps_ SNo_eps_pos SNo_pos_eps_Lt SNo_minus_SNo minus_SNo_Lt_contra SNo_add_SNo add_SNo_Lt2 SNoLt_minus_pos nonneg_abs_SNo H10 H9 H8 Hz Hq3 H7 H4 H1 HLR2.
    }
    aby In_irref LqR LqL Hq3 Hq1 H6 H5.
Qed.

Theorem real_SNoCut: forall L R c= real, SNoCutP L R
 -> L <> 0
 -> R <> 0
 -> (forall w :e L, exists w' :e L, w < w')
 -> (forall z :e R, exists z' :e R, z' < z)
 -> SNoCut L R :e real.
let L. assume HL. let R. assume HR.
assume HLR. apply HLR. assume H. apply H.
assume HLR1: forall w :e L, SNo w.
assume HLR2: forall z :e R, SNo z.
assume HLR3: forall w :e L, forall z :e R, w < z.
assume HL0: L <> 0.
assume HR0: R <> 0.
assume HL1: forall w :e L, exists w' :e L, w < w'.
assume HR1: forall z :e R, exists z' :e R, z' < z.
set x := SNoCut L R.
apply SNoCutP_SNoCut_impred L R HLR.
assume H1: SNo x.
assume H2: SNoLev x :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume H3: forall w :e L, w < x.
assume H4: forall z :e R, x < z.
assume H5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev x c= SNoLev u /\ SNoEq_ (SNoLev x) x u.
set L_ : set -> set := fun n => {w' :e SNoS_ n|exists w :e L, w' <= w}.
set R_ : set -> set := fun n => {z' :e SNoS_ n|exists z :e R, z <= z'}.
set L' := \/_ n :e omega, L_ n.
set R' := \/_ n :e omega, R_ n.
set x' := SNoCut L' R'.
claim LL'L: forall w' :e L', exists w :e L, w' <= w.
{ aby famunionE_impred SepE2. }
claim LR'R: forall z' :e R', exists z :e R, z <= z'.
{ aby famunionE_impred SepE2. }
claim LL'o: L' c= SNoS_ omega.
{ let w'. assume Hw'.
  apply famunionE_impred omega L_ w' Hw'.
  aby SepE1 nat_p_ordinal omega_nat_p omega_TransSet omega_ordinal SNoS_I SNoS_E2.
}
claim LR'o: R' c= SNoS_ omega.
{ let z'. assume Hz'.
  apply famunionE_impred omega R_ z' Hz'.
  aby SepE1 nat_p_ordinal omega_nat_p omega_TransSet omega_ordinal SNoS_I SNoS_E2.
}
claim LL': forall w' :e L', SNo w'.
{ aby omega_ordinal SNoS_E2 LL'o. }
claim LR': forall z :e R', SNo z.
{ aby omega_ordinal SNoS_E2 LR'o. }
claim LLR': SNoCutP L' R'.
{ aby and3I SNoLtLe_tra SNoLeLt_tra LR' LL' LR'R LL'L HLR3 HLR2 HLR1. }
apply SNoCutP_SNoCut_impred L' R' LLR'.
assume H1': SNo x'.
assume H2': SNoLev x' :e ordsucc ((\/_ x :e L', ordsucc (SNoLev x)) :\/: (\/_ y :e R', ordsucc (SNoLev y))).
assume H3': forall w :e L', w < x'.
assume H4': forall z :e R', x' < z.
assume H5': forall u, SNo u -> (forall w :e L', w < u) -> (forall z :e R', u < z) -> SNoLev x' c= SNoLev u /\ SNoEq_ (SNoLev x') x' u.
claim L1: forall w :e L, exists w' :e L', w <= w'.
{ let w. assume Hw.
  apply real_E w (HL w Hw).
  assume Hw1: SNo w.
  assume Hw2: SNoLev w :e ordsucc omega.
  assume _ _ _ _ _.
  apply ordsuccE omega (SNoLev w) Hw2.
  - aby famunionI SepI omega_ordsucc SNoLe_ref SNoS_SNoLev Hw1 Hw.
  - assume H6: SNoLev w = omega.
    apply HL1 w Hw.
    let w'. assume H. apply H.
    assume Hw': w' :e L.
    assume Hww': w < w'.
    apply real_E w' (HL w' Hw').
    aby famunionI SepI binintersectE1 In_irref ordsuccE omega_ordsucc SNoLtLe SNoLtE SNoLe_ref SNoS_SNoLev Hww' Hw' H6 Hw1.
}
claim L2: forall z :e R, exists z' :e R', z' <= z.
{ let z. assume Hz.
  apply real_E z (HR z Hz).
  assume Hz1: SNo z.
  assume Hz2: SNoLev z :e ordsucc omega.
  assume _ _ _ _ _.
  apply ordsuccE omega (SNoLev z) Hz2.
  - aby famunionI SepI omega_ordsucc SNoLe_ref SNoS_SNoLev Hz1 Hz.
  - assume H6: SNoLev z = omega.
    apply HR1 z Hz.
    let z'. assume H. apply H.
    assume Hz': z' :e R.
    assume Hz'z: z' < z.
    apply real_E z' (HR z' Hz').
    aby famunionI SepI binintersectE1 In_irref ordsuccE omega_ordsucc SNoLtLe SNoLtE SNoLe_ref SNoS_SNoLev Hz'z Hz' H6 Hz1.
}
claim L3: L' <> 0.
{ assume H6: L' = 0.
  aby EmptyE Empty_eq H6 L1 HL0.
}
claim L4: R' <> 0.
{ assume H6: R' = 0.
  aby EmptyE Empty_eq H6 L2 HR0.
}
claim L5: forall w :e L', exists w' :e L', w < w'.
{ aby SNoLtLe_tra SNoLeLt_tra L1 LL' LL'L HL1 HLR1. }
claim L6: forall z :e R', exists z' :e R', z' < z.
{ aby SNoLtLe_tra SNoLeLt_tra L2 LR' LR'R HR1 HLR2. }
claim Lxx': x = x'.
{ apply SNoCut_ext.
  - aby HLR.
  - aby HL HR HLR H HLR1 HLR2 HLR3 HL0 HR0 HL1 HR1 H1 H2 H3 H4 H5 LL'L LR'R LL'o LR'o LL' LR' LLR' H1' H2' H3' H4' H5' L1 L2 L3 L4 L5 L6.
  - aby SNoLeLt_tra L1 H3' H1' LL' HLR1.
  - aby SNoLtLe_tra L2 H4' H1' LR' HLR2.
  - aby SNoLeLt_tra LL' LL'L H3 H1 HLR1.
  - aby SNoLtLe_tra LR' LR'R H4 H1 HLR2.
}
aby real_SNoCut_SNoS_omega Lxx' L6 L5 L4 L3 LLR' LR'o LL'o.
Qed.

Theorem minus_SNo_prereal_1 : forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - - x) < eps_ k) -> q = - x).
aby omega_ordinal SNoS_E2 SNo_minus_SNo minus_SNo_invol minus_SNo_SNoS_omega add_SNo_com abs_SNo_dist_swap.
Qed.

Theorem minus_SNo_prereal_2 : forall x, SNo x ->
    (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < - x /\ - x < q + eps_ k).
aby omega_ordinal SNoS_E2 SNo_eps_ SNo_eps_SNoS_omega SNo_minus_SNo minus_SNo_Lt_contra minus_SNo_SNoS_omega SNo_add_SNo add_SNo_minus_R2' minus_add_SNo_distr add_SNo_SNoS_omega.
Qed.

Theorem SNo_prereal_incr_lower_pos: forall x, SNo x -> 0 < x
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> forall k :e omega,
     forall p:prop,
         (forall q :e SNoS_ omega, 0 < q -> q < x -> x < q + eps_ k -> p)
      -> p.
let x. assume Hx Hx0 Hx2 Hx3.
let k. assume Hk. let p. assume Hp.
apply Hx3 k Hk.
let q. assume H. apply H.
assume Hq1: q :e SNoS_ omega. assume H. apply H.
assume Hq2: q < x.
assume Hq3: x < q + eps_ k.
apply SNoS_E2 omega omega_ordinal q Hq1.
assume Hq1a Hq1b Hq1c Hq1d.
apply SNoLtLe_or 0 q SNo_0 Hq1c.
- aby Hq3 Hq2 Hq1 Hp.
- assume H1: q <= 0.
  apply xm (forall k' :e omega, x < eps_ k').
  + aby nat_0 nat_p_omega SNoLt_irref omega_SNoS_omega SNo_minus_SNo add_SNo_0L pos_abs_SNo abs_SNo_minus Hx2 Hx0 Hx.
  + aby dneg ordsuccI2 omega_ordsucc SNoLt_tra SNoLtLe_tra SNoLeLt_tra SNoLtLe_or SNo_0 SNo_eps_ SNo_eps_SNoS_omega SNo_eps_decr SNo_eps_pos SNo_add_SNo add_SNo_Lt1 H1 Hq1c Hq3 Hp Hk Hx.
Qed.

Theorem real_minus_SNo : forall x :e real, - x :e real.
aby ordsucc_omega_ordinal SNoLt_irref SNo_omega minus_SNo_invol minus_SNo_SNoS_ real_I real_E minus_SNo_prereal_1.
Qed.

Theorem SNo_prereal_incr_lower_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists f :e SNoS_ omega :^: omega,
       forall n :e omega, f n < x /\ x < f n + eps_ n
                       /\ forall i :e n, f i < f n.
let x. assume H1 H2 H3.
set f' : set -> set
 := nat_primrec (Eps_i (fun q => q :e SNoS_ omega /\ q < x /\ x < q + eps_ 0))
                (fun n r => (Eps_i (fun q => q :e SNoS_ omega /\ q < x /\ x < q + eps_ (ordsucc n) /\ r < q))).
set f := fun n :e omega => f' n.
claim Lf'0: f' 0 = Eps_i (fun q => q :e SNoS_ omega /\ q < x /\ x < q + eps_ 0).
{ aby nat_primrec_0 H1 H2 H3. }
claim Lf'0b: f' 0 :e SNoS_ omega /\ f' 0 < x /\ x < f' 0 + eps_ 0.
{ aby and3I Eps_i_ex nat_0 nat_p_omega Lf'0 H3. }
claim Lf'S: forall n, nat_p n -> f' (ordsucc n) = Eps_i (fun q => q :e SNoS_ omega /\ q < x /\ x < q + eps_ (ordsucc n) /\ f' n < q).
{ aby nat_primrec_S H1 H2 H3 Lf'0 Lf'0b. }
claim L1: forall n, nat_p n -> f' n :e SNoS_ omega /\ f' n < x /\ x < f' n + eps_ n /\ forall i :e n, SNo (f i) -> f i < f' n.
{ apply nat_ind.
  - aby EmptyE and4I Lf'0b.
  - let n. assume Hn.
    assume IHn: f' n :e SNoS_ omega /\ f' n < x /\ x < f' n + eps_ n /\ forall i :e n, SNo (f i) -> f i < f' n.
    prove f' (ordsucc n) :e SNoS_ omega /\ f' (ordsucc n) < x /\ x < f' (ordsucc n) + eps_ (ordsucc n)
       /\ forall i :e ordsucc n, SNo (f i) -> f i < f' (ordsucc n).
    apply IHn. assume IHn123 IHn4. apply IHn123. assume IHn12 IHn3. apply IHn12. assume IHn1 IHn2.
    apply SNoS_E2 omega omega_ordinal (f' n) IHn1.
    assume _ _.
    assume IHn1c: SNo (f' n).
    assume _.
    claim L1b: exists q, q :e SNoS_ omega /\ q < x /\ x < q + eps_ (ordsucc n) /\ f' n < q.
    { apply H3 (ordsucc n) (nat_p_omega (ordsucc n) (nat_ordsucc n Hn)).
      let q. assume Hq. apply Hq.
      assume Hq1 Hq. apply Hq.
      assume Hq2 Hq3.
      apply SNoS_E2 omega omega_ordinal q Hq1.
      assume Hq1a Hq1b Hq1c Hq1d.
      apply SNoLtLe_or (f' n) q IHn1c Hq1c.
      - aby and4I Hq3 Hq2 Hq1.
      - assume H4: q <= f' n.
        claim L1ba: SNo (- f' n).
        { aby SNo_minus_SNo H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4. }
        claim L1bb: SNo (x + - f' n).
        { aby SNo_add_SNo H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba. }
        claim L1bc: SNo (eps_ (ordsucc n)).
        { aby nat_p_omega omega_ordsucc SNo_eps_ Hn. }
        apply xm (exists k :e omega, eps_ k <= x + - f' n).
        + assume H5. apply H5. let k. assume H5. apply H5.
          assume Hk1: k :e omega.
          assume Hk2: eps_ k <= x + - f' n.
          witness (f' n + eps_ (ordsucc k)).
          claim Lk1: ordsucc k :e omega.
          { aby omega_ordsucc Hk1. }
          claim Lk2: SNo (eps_ (ordsucc k)).
          { aby SNo_eps_ Lk1. }
          claim Lk3: f' n + eps_ (ordsucc k) :e SNoS_ omega.
          { aby omega_ordsucc SNo_eps_SNoS_omega add_SNo_SNoS_omega H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2. }
          apply SNoS_E2 omega omega_ordinal (f' n + eps_ (ordsucc k)) Lk3.
          assume _ _.
          assume H6: SNo (f' n + eps_ (ordsucc k)).
          assume _.
          apply and4I.
          * aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
          * aby ordsuccI2 SNoLtLe_tra SNo_eps_ SNo_eps_decr SNo_add_SNo add_SNo_Lt2 add_SNo_Le2 add_SNo_com add_SNo_minus_L2' add_SNo_minus_SNo_prop2 H6 Lk2 Lk1 Hk2 Hk1 L1bb L1ba IHn1c H1.
          * prove x < (f' n + eps_ (ordsucc k)) + eps_ (ordsucc n).
              rewrite add_SNo_com_3b_1_2 (f' n) (eps_ (ordsucc k)) (eps_ (ordsucc n))
                          IHn1c Lk2 L1bc.
              prove x < (f' n + eps_ (ordsucc n)) + eps_ (ordsucc k).
              apply add_SNo_eps_Lt' x (f' n + eps_ (ordsucc n)) H1 (SNo_add_SNo (f' n) (eps_ (ordsucc n)) IHn1c L1bc) (ordsucc k) Lk1.
              prove x < f' n + eps_ (ordsucc n).
              apply SNoLtLe_tra x (q + (eps_ (ordsucc n))).
              - aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
              - aby SNo_add_SNo H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
              - aby SNo_add_SNo H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
              - prove x < q + eps_ (ordsucc n). aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
              - prove q + eps_ (ordsucc n) <= f' n + eps_ (ordsucc n).
                aby add_SNo_Le1 H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 H5 Hk1 Hk2 Lk1 Lk2 Lk3 H6.
          * aby omega_ordsucc add_SNo_eps_Lt Hk1 IHn1c.
        + assume H5: ~(exists k :e omega, eps_ k <= x + - f' n).
          prove False.
          apply SNoLt_irref x.
          prove x < x.
          claim L1bd: 0 < x + - f' n.
          { apply add_SNo_Lt1_cancel 0 (f' n) (x + - f' n) SNo_0 IHn1c L1bb.
            prove 0 + f' n < (x + - f' n) + f' n.
            rewrite add_SNo_0L (f' n) IHn1c.
            rewrite add_SNo_minus_R2' x (f' n) H1 IHn1c.
            prove f' n < x. aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5.
          }
          claim L1be: f' n = x.
          { apply H2 (f' n) IHn1.
            let k. assume Hk.
            prove abs_SNo (f' n + - x) < eps_ k.
            apply SNoLtLe_or (x + - f' n) (eps_ k) L1bb (SNo_eps_ k Hk).
            - assume H6: x + - f' n < eps_ k.
              prove abs_SNo (f' n + - x) < eps_ k.
              rewrite abs_SNo_dist_swap (f' n) x IHn1c H1.
              prove abs_SNo (x + - f' n) < eps_ k.
              rewrite pos_abs_SNo (x + - f' n) L1bd. aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 L1bd Hk H6.
            - assume H6: eps_ k <= x + - f' n.
              apply H5. witness k. apply andI.
              + aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 L1bd Hk H6.
              + aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 L1bd Hk H6.
          }
          rewrite <- L1be at 1.
          aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c Hq Hq1 Hq Hq2 Hq3 Hq1a Hq1b Hq1c Hq1d H4 L1ba L1bb L1bc H5 L1bd L1be.
    }
    claim L1c: f' (ordsucc n) :e SNoS_ omega /\ f' (ordsucc n) < x /\ x < f' (ordsucc n) + eps_ (ordsucc n) /\ f' n < f' (ordsucc n).
    { rewrite Lf'S n Hn.
      aby Eps_i_ex H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b.
    }
    apply L1c. assume H H7. apply H. assume H H6. apply H. assume H4 H5.
    apply and4I.
    + aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5.
    + aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5.
    + aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5.
    + let i. assume Hi: i :e ordsucc n. assume Hfi: SNo (f i).
      apply ordsuccE n i Hi.
      * { assume H8: i :e n.
          prove f i < f' (ordsucc n).
          apply SNoLt_tra (f i) (f' n) (f' (ordsucc n)).
          - prove SNo (f i). aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8.
          - aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8.
          - apply SNoS_E2 omega omega_ordinal (f' (ordsucc n)) H4. assume _ _ H9 _. aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8 H9.
          - apply IHn. assume _.
            assume IHn4: forall i :e n, SNo (f i) -> f i < f' n.
            aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8 IHn4.
          - aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8.
        }
      * assume H8: i = n. rewrite H8.
        prove f n < f' (ordsucc n).
        rewrite beta omega f' n (nat_p_omega n Hn).
        aby H1 H2 H3 Lf'0 Lf'0b Lf'S Hn IHn IHn123 IHn4 IHn12 IHn3 IHn1 IHn2 IHn1c L1b L1c H H7 H H6 H4 H5 Hi Hfi H8.
}
claim L2: forall n :e omega, f' n :e SNoS_ omega /\ f n < x /\ x < f n + eps_ n /\ forall i :e n, SNo (f i) -> f i < f n.
{ let n. assume Hn.
  exact beta omega f' n Hn
         (fun u v => f' n :e SNoS_ omega /\ v < x /\ x < v + eps_ n /\ forall i :e n, SNo (f i) -> f i < v)
         (L1 n (omega_nat_p n Hn)).
}
aby and3I nat_p_trans omega_nat_p nat_p_omega omega_ordinal beta lam_Pi SNoS_E2 L2.
Qed.

Theorem SNo_prereal_decr_upper_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists g :e SNoS_ omega :^: omega,
       forall n :e omega, g n + - eps_ n < x /\ x < g n
                       /\ forall i :e n, g n < g i.
let x. assume H1 H2 H3.
claim L1: SNo (- x).
{ aby SNo_minus_SNo H1. }
apply SNo_prereal_incr_lower_approx (- x) L1
       (minus_SNo_prereal_1 x H1 H2)
       (minus_SNo_prereal_2 x H1 H3).
let f. assume Hf. apply Hf.
assume Hf1: f :e SNoS_ omega :^: omega.
assume Hf2: forall n :e omega, f n < - x /\ - x < f n + eps_ n
                       /\ forall i :e n, f i < f n.
claim Lf: forall n :e omega, SNo (f n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hf1. }
set g := fun n :e omega => - f n.
witness g.
aby and3I nat_p_trans omega_nat_p nat_p_omega beta lam_Pi ap_Pi SNo_eps_ minus_SNo_Lt_contra minus_SNo_Lt_contra1 minus_SNo_Lt_contra2 minus_SNo_SNoS_omega SNo_add_SNo minus_add_SNo_distr Lf Hf2 Hf1 H1.
Qed.

Theorem SNoCutP_SNoCut_lim : forall lambda, ordinal lambda
 -> (forall alpha :e lambda, ordsucc alpha :e lambda)
 -> forall L R c= SNoS_ lambda, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc lambda.
let lambda. assume Hl1 Hl2.
let L. assume HL. let R. assume HR HLR.
claim L1: forall x :e L, SNoLev x :e lambda.
{ aby SNoS_E2 HL Hl1. }
claim L2: forall y :e R, SNoLev y :e lambda.
{ aby SNoS_E2 HR Hl1. }
claim L3: ordinal ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
{ aby ordinal_ordsucc ordinal_famunion ordinal_binunion SNoS_E2 HR HL Hl1. }
claim L4: ordinal (ordsucc lambda).
{ aby ordinal_ordsucc Hl1. }
claim L5: ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))) c= ordsucc lambda.
{ aby binunionE famunionE_impred In_no2cycle ordsuccI2 ordinal_ordsucc_In_Subq ordinal_In_Or_Subq L4 L3 L2 L1 Hl2.
}
aby SNoCutP_SNoCut_impred L5 HLR.
Qed.

Theorem SNoCutP_SNoCut_omega : forall L R c= SNoS_ omega, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc omega.
aby omega_ordsucc omega_ordinal SNoCutP_SNoCut_lim.
Qed.

Theorem SNo_approx_real_lem:
  forall f g :e SNoS_ omega :^: omega,
     (forall n m :e omega, f n < g m)
  -> forall p:prop,
         (SNoCutP {f n|n :e omega} {g n|n :e omega}
       -> SNo (SNoCut {f n|n :e omega} {g n|n :e omega})
       -> SNoLev (SNoCut {f n|n :e omega} {g n|n :e omega}) :e ordsucc omega
       -> SNoCut {f n|n :e omega} {g n|n :e omega} :e SNoS_ (ordsucc omega)
       -> (forall n :e omega, f n < SNoCut {f n|n :e omega} {g n|n :e omega})
       -> (forall n :e omega, SNoCut {f n|n :e omega} {g n|n :e omega} < g n)
       -> p)
      -> p.
let f. assume Hf1. let g. assume Hg1 Hfg.
let p. assume Hp.
set L := {f n|n :e omega}.
set R := {g n|n :e omega}.
set x := SNoCut L R.
claim Lf: forall n :e omega, SNo (f n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hf1. }
claim Lg: forall n :e omega, SNo (g n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hg1. }
claim L1: SNoCutP L R.
{ aby and3I ReplE_impred Lg Lf Hfg. }
apply SNoCutP_SNoCut_impred L R L1.
assume HLR1: SNo x.
assume HLR2: SNoLev x :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
assume HLR3: forall w :e L, w < x.
assume HLR4: forall y :e R, x < y.
assume HLR5: forall z, SNo z -> (forall w :e L, w < z) -> (forall y :e R, z < y) -> SNoLev x c= SNoLev z /\ SNoEq_ (SNoLev x) x z.
claim L2: L c= SNoS_ omega.
{ aby ReplE_impred ap_Pi Hf1. }
claim L3: R c= SNoS_ omega.
{ aby ReplE_impred ap_Pi Hg1. }
aby ReplI ordsucc_omega_ordinal SNoLev_ SNoS_I SNoCutP_SNoCut_omega L3 L2 HLR4 HLR3 HLR1 L1 Hp.
Qed.

Theorem SNo_approx_real: forall x, SNo x ->
 forall f g :e SNoS_ omega :^: omega,
     (forall n :e omega, f n < x)
  -> (forall n :e omega, x < f n + eps_ n)
  -> (forall n :e omega, forall i :e n, f i < f n)
  -> (forall n :e omega, x < g n)
  -> (forall n :e omega, forall i :e n, g n < g i)
  -> x = SNoCut {f n|n :e omega} {g n|n :e omega}
  -> x :e real.
let x. assume Hx. let f. assume Hf1. let g. assume Hg1 Hf2 Hf3 Hf4 Hg3 Hg4.
set L := {f n|n :e omega}.
set R := {g n|n :e omega}.
assume Hxfg: x = SNoCut L R.
claim Lmx: SNo (- x).
{ aby SNo_minus_SNo Hx. }
claim Lf: forall n :e omega, SNo (f n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hf1. }
claim Lg: forall n :e omega, SNo (g n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hg1. }
claim Lfg: forall n m :e omega, f n < g m.
{ aby SNoLt_tra Lg Lf Hg3 Hf2 Hx. }
apply SNo_approx_real_lem f Hf1 g Hg1 Lfg.
rewrite <- Hxfg.
assume H1: SNoCutP L R.
assume H2: SNo x.
rewrite <- Hxfg.
assume H3: SNoLev x :e ordsucc omega.
rewrite <- Hxfg.
assume H4: x :e SNoS_ (ordsucc omega).
rewrite <- Hxfg.
assume H5: forall n :e omega, f n < x.
rewrite <- Hxfg.
assume H6: forall n :e omega, x < g n.
apply SNoCutP_SNoCut_impred L R H1.
assume _ _ _ _.
assume H7: forall z, SNo z -> (forall w :e L, w < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z.
apply ordsuccE omega (SNoLev x) H3.
- aby omega_ordinal SNoLev_ SNoS_I SNoS_omega_real Hx.
- assume H8: SNoLev x = omega.
  apply real_I.
  + aby H4.
  + aby nat_0 nat_p_omega ap_Pi SNoLt_irref SNoLt_tra real_E SNoS_omega_real Hg3 Hg1 Hx.
  + aby nat_0 nat_p_omega ap_Pi SNoLt_irref SNoLt_tra real_E SNoS_omega_real Hf2 Hf1 Hx.
  + prove forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
    let q. assume Hq1 Hq2. prove q = x.
    apply SNoS_E2 omega omega_ordinal q Hq1.
    assume Hq1a Hq1b Hq1c Hq1d.
    claim Lmq: SNo (- q).
    { aby SNo_minus_SNo Hq1c. }
    claim Lxmq: SNo (x + - q).
    { aby SNo_add_SNo Lmq Hx. }
    claim Lqmx: SNo (q + - x).
    { aby SNo_add_SNo Hq1c Lmx. }
    claim L5: forall w :e L, w < q.
    { let w. assume Hw.
      apply ReplE_impred omega (fun n => f n) w Hw.
      let n. assume Hn.
      assume Hwn: w = f n.
      rewrite Hwn.
      prove f n < q.
      apply SNoLtLe_or (f n) q (Lf n Hn) Hq1c.
      - aby.
      - assume H9: q <= f n.
        apply real_E (f (ordsucc n)) (SNoS_omega_real (f (ordsucc n)) (ap_Pi omega (fun _ => SNoS_ omega) f (ordsucc n) Hf1 (omega_ordsucc n Hn))).
        assume _ _ _ _ _.
        aby ordsuccI2 omega_ordsucc SNoLt_irref SNoLt_tra SNoLeLt_tra SNo_eps_ SNo_add_SNo add_SNo_Lt1 SNoLt_minus_pos pos_abs_SNo abs_SNo_dist_swap H9 Hn Lxmq Lmq Hq1c Hq2 Hq1 Lf Hf4 Hf2 Hx.
    }
    claim L6: forall z :e R, q < z.
    { let z. assume Hz: z :e R.
      apply ReplE_impred omega (fun n => g n) z Hz.
      let m. assume Hm.
      assume Hzm: z = g m.
      rewrite Hzm.
      prove q < g m.
      apply SNoLtLe_or q (g m) Hq1c (Lg m Hm).
      - aby.
      - assume H9: g m <= q.
        apply real_E (g (ordsucc m)) (SNoS_omega_real (g (ordsucc m)) (ap_Pi omega (fun _ => SNoS_ omega) g (ordsucc m) Hg1 (omega_ordsucc m Hm))).
        assume _ _ _ _ _.
        aby ordsuccI2 omega_ordsucc SNoLt_irref SNoLt_tra SNoLtLe_tra SNo_eps_ SNo_minus_SNo minus_SNo_Lt_contra SNo_add_SNo add_SNo_Lt2 SNoLt_minus_pos pos_abs_SNo H9 Hm Lqmx Hq1c Hq2 Hq1 Lg Lmx Hg4 Hg3 Hx.
    }
    aby In_irref L6 L5 Hq1c Hq1a H8 H7 Hxfg.
Qed.

Theorem SNo_approx_real_rep : forall x :e real,
 forall p:prop,
     (forall f g :e SNoS_ omega :^: omega,
           (forall n :e omega, f n < x)
        -> (forall n :e omega, x < f n + eps_ n)
        -> (forall n :e omega, forall i :e n, f i < f n)
        -> (forall n :e omega, g n + - eps_ n < x)
        -> (forall n :e omega, x < g n)
        -> (forall n :e omega, forall i :e n, g n < g i)
        -> SNoCutP {f n|n :e omega} {g n|n :e omega}
        -> x = SNoCut {f n|n :e omega} {g n|n :e omega}
        -> p)
  -> p.
let x. assume Hx. let p. assume Hp.
apply real_E x Hx.
assume Hx1 Hx2 Hx3 _ _ Hx4 Hx5.
apply SNo_prereal_incr_lower_approx x Hx1 Hx4 Hx5.
let f. assume Hf. apply Hf.
assume Hf1 Hf2.
apply SNo_prereal_decr_upper_approx x Hx1 Hx4 Hx5.
let g. assume Hg. apply Hg.
assume Hg1 Hg2.
claim Lf: forall n :e omega, SNo (f n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hf1. }
claim Lg: forall n :e omega, SNo (g n).
{ aby omega_ordinal ap_Pi SNoS_E2 Hg1. }
claim Lf1: forall n :e omega, f n < x.
{ aby Hf2. }
claim Lf2: forall n :e omega, x < f n + eps_ n.
{ aby Hf2. }
claim Lf3: forall n :e omega, forall i :e n, f i < f n.
{ aby Hf2. }
claim Lg1: forall n :e omega, g n + - eps_ n < x.
{ aby Hg2. }
claim Lg2: forall n :e omega, x < g n.
{ aby Hg2. }
claim Lg3: forall n :e omega, forall i :e n, g n < g i.
{ aby Hg2. }
claim Lfg: forall n m :e omega, f n < g m.
{ aby SNoLt_tra Lg2 Lf1 Lg Lf Hx1. }
set L := {f n|n :e omega}.
set R := {g n|n :e omega}.
apply SNo_approx_real_lem f Hf1 g Hg1 Lfg.
assume H1: SNoCutP L R.
assume H2: SNo (SNoCut L R).
assume H3: SNoLev (SNoCut L R) :e ordsucc omega.
assume H4: SNoCut L R :e SNoS_ (ordsucc omega).
assume H5: forall n :e omega, f n < SNoCut L R.
assume H6: forall n :e omega, SNoCut L R < g n.
claim Lxfg: x = SNoCut L R.
{ rewrite SNo_eta x Hx1.
  apply SNoCut_ext (SNoL x) (SNoR x) L R (SNoCutP_SNoL_SNoR x Hx1) H1.
  - let w. assume Hw: w :e SNoL x. prove w < SNoCut L R.
    apply SNoL_E x Hx1 w Hw.
    assume Hw1: SNo w.
    assume Hw2: SNoLev w :e SNoLev x.
    assume Hw3: w < x.
    claim Lw1: w :e SNoS_ omega.
    { aby SNoLev_In_real_SNoS_omega Hw2 Hw1 Hx. }
    claim Lw2: 0 < x + - w.
    { aby SNoLt_minus_pos Hw3 Hw1 Hx1. }
    claim Lw3: exists k :e omega, w + eps_ k <= x.
    { aby SNoLt_irref SNoLtLe_or SNo_eps_ SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_minus_R2' pos_abs_SNo abs_SNo_dist_swap Lw2 Lw1 Hw3 Hw1 Hx4 Hx1. }
    aby SNoLt_tra SNoLeLt_tra SNo_eps_ SNo_add_SNo add_SNo_Lt1_cancel Lw3 Hw1 H5 H2 Lf Hf2 Hx1.
  - let z. assume Hz: z :e SNoR x. aby dneg SNoLt_irref SNoLt_tra SNoLtLe_tra SNoLtLe_or SNoR_E SNo_eps_ SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_minus_R2' add_SNo_minus_Lt1 SNoLt_minus_pos pos_abs_SNo SNoLev_In_real_SNoS_omega Hz H6 H2 Lg1 Lg Hx4 Hx1 Hx.
  - aby ReplE_impred SNo_eta Lf1 Hx1.
  - aby ReplE_impred SNo_eta Lg2 Hx1.
}
aby Hx Hp Hx1 Hx2 Hx3 Hx4 Hx5 Hf Hf1 Hf2 Hg Hg1 Hg2 Lf Lg Lf1 Lf2 Lf3 Lg1 Lg2 Lg3 Lfg H1 H2 H3 H4 H5 H6 Lxfg.
Qed.

Theorem real_add_SNo : forall x y :e real, x + y :e real.
let x. assume Hx. let y. assume Hy.
apply SNo_approx_real_rep x Hx.
let fL. assume HfL. let fR. assume HfR HfL1 HfL2 HfL3 HfR1 HfR2 HfR3 HfLR HxfLR.
apply SNo_approx_real_rep y Hy.
let gL. assume HgL. let gR. assume HgR HgL1 HgL2 HgL3 HgR1 HgR2 HgR3 HgLR HygLR.
set hL := fun n :e omega => fL (ordsucc n) + gL (ordsucc n).
set hR := fun n :e omega => fR (ordsucc n) + gR (ordsucc n).
set L := {hL n|n :e omega}.
set R := {hR n|n :e omega}.
claim Lx: SNo x.
{ aby real_SNo Hx. }
claim Ly: SNo y.
{ aby real_SNo Hy. }
claim Lxy: SNo (x + y).
{ aby SNo_add_SNo Ly Lx. }
claim Lx2: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
{ aby real_SNoS_omega_prop Hx. }
claim Ly2: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - y) < eps_ k) -> q = y.
{ aby real_SNoS_omega_prop Hy. }
claim LfLa: forall n :e omega, fL (ordsucc n) :e SNoS_ omega.
{ aby omega_ordsucc ap_Pi HfL. }
claim LfLb: forall n :e omega, SNo (fL (ordsucc n)).
{ aby omega_ordinal SNoS_E2 LfLa. }
claim LgLa: forall n :e omega, gL (ordsucc n) :e SNoS_ omega.
{ aby omega_ordsucc ap_Pi HgL. }
claim LgLb: forall n :e omega, SNo (gL (ordsucc n)).
{ aby omega_ordinal SNoS_E2 LgLa. }
claim LfRa: forall n :e omega, fR (ordsucc n) :e SNoS_ omega.
{ aby omega_ordsucc ap_Pi HfR. }
claim LfRb: forall n :e omega, SNo (fR (ordsucc n)).
{ aby omega_ordinal SNoS_E2 LfRa. }
claim LgRa: forall n :e omega, gR (ordsucc n) :e SNoS_ omega.
{ aby omega_ordsucc ap_Pi HgR. }
claim LgRb: forall n :e omega, SNo (gR (ordsucc n)).
{ aby omega_ordinal SNoS_E2 LgRa. }
claim LhL: forall n :e omega, hL n = fL (ordsucc n) + gL (ordsucc n).
{ aby beta. }
claim LhR: forall n :e omega, hR n = fR (ordsucc n) + gR (ordsucc n).
{ aby beta. }
claim LhLb: forall n :e omega, SNo (hL n).
{ aby SNo_add_SNo LhL LgLb LfLb. }
claim LhRb: forall n :e omega, SNo (hR n).
{ aby SNo_add_SNo LhR LgRb LfRb. }
claim L1: hL :e SNoS_ omega :^: omega.
{ aby lam_Pi add_SNo_SNoS_omega LgLa LfLa. }
claim L2: hR :e SNoS_ omega :^: omega.
{ aby lam_Pi add_SNo_SNoS_omega LgRa LfRa. }
claim L3: forall n :e omega, hL n < x + y.
{ aby omega_ordsucc add_SNo_Lt3 LhL LgLb LfLb Ly Lx HgL1 HfL1. }
claim L4: forall n :e omega, x + y < hL n + eps_ n.
{ let n. assume Hn.
  rewrite LhL n Hn.
  prove x + y < (fL (ordsucc n) + gL (ordsucc n)) + eps_ n.
  rewrite <- eps_ordsucc_half_add n (omega_nat_p n Hn).
  aby omega_ordsucc SNo_eps_ SNo_add_SNo add_SNo_Lt3 add_SNo_com_4_inner_mid Hn LgLb LfLb Ly Lx HgL2 HfL2.
}
claim L5: forall n :e omega, forall i :e n, hL i < hL n.
{ aby nat_ordsucc_in_ordsucc nat_p_trans omega_nat_p nat_p_omega omega_ordsucc add_SNo_Lt3 LhL LgLb LfLb HgL3 HfL3. }
claim L6: forall n :e omega, hR n + - eps_ n < x + y.
{ let n. assume Hn. rewrite LhR n Hn.
  prove (fR (ordsucc n) + gR (ordsucc n)) + - eps_ n < x + y.
  rewrite <- eps_ordsucc_half_add n (omega_nat_p n Hn).
  aby omega_ordsucc SNo_eps_ SNo_minus_SNo SNo_add_SNo add_SNo_Lt3 minus_add_SNo_distr add_SNo_com_4_inner_mid Hn LgRb LfRb Ly Lx HgR1 HfR1.
}
claim L7: forall n :e omega, x + y < hR n.
{ aby omega_ordsucc add_SNo_Lt3 LhR LgRb LfRb Ly Lx HgR2 HfR2. }
claim L8: forall n :e omega, forall i :e n, hR n < hR i.
{ aby nat_ordsucc_in_ordsucc nat_p_trans omega_nat_p nat_p_omega omega_ordsucc add_SNo_Lt3 LhR LgRb LfRb HgR3 HfR3. }
claim LLR: SNoCutP L R.
{ aby and3I ReplE_impred SNoLt_tra SNo_add_SNo L7 L3 LhRb LhLb Ly Lx. }
apply SNoCutP_SNoCut_impred L R LLR.
assume HLR1 HLR2 HLR3 HLR4 HLR5.
claim L9: x + y = SNoCut L R.
{ rewrite add_SNo_eq x Lx y Ly.
  prove SNoCut ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y})
      = SNoCut L R.
  apply SNoCut_ext ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y})
                   ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y})
                   L R
                   (add_SNo_SNoCutP x y Lx Ly)
                   LLR.
  - prove forall w :e {w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}, w < SNoCut L R.
    let w. assume Hw.
    apply binunionE {w + y|w :e SNoL x} {x + w|w :e SNoL y} w Hw.
    + assume Hw: w :e {w + y|w :e SNoL x}.
      apply ReplE_impred (SNoL x) (fun w => w + y) w Hw.
      let w'. assume Hw': w' :e SNoL x.
      assume Hww'. rewrite Hww'.
      prove w' + y < SNoCut L R.
      apply SNoL_E x Lx w' Hw'.
      assume Hw'1 Hw'2 Hw'3.
      claim Lw'1: w' :e SNoS_ omega.
      { aby SNoLev_In_real_SNoS_omega Hw'2 Hw'1 Hx. }
      claim Lw'2: exists n :e omega, w' + y <= hL n.
      { apply dneg. assume HC: ~(exists n :e omega, w' + y <= hL n).
        claim Lw'2a: 0 < x + - w'.
        { aby SNoLt_minus_pos Hw'3 Hw'1 Lx. }
        claim Lw'2b: w' = x.
        { apply Lx2 w' Lw'1.
          let k. assume Hk.
          prove abs_SNo (w' + - x) < eps_ k.
          rewrite abs_SNo_dist_swap w' x Hw'1 Lx.
          prove abs_SNo (x + - w') < eps_ k.
          rewrite pos_abs_SNo (x + - w') Lw'2a.
          prove x + - w' < eps_ k.
          apply add_SNo_minus_Lt1b x w' (eps_ k) Lx Hw'1 (SNo_eps_ k Hk).
          prove x < eps_ k + w'.
          apply SNoLtLe_or x (eps_ k + w') Lx (SNo_add_SNo (eps_ k) w' (SNo_eps_ k Hk) Hw'1).
          - assume H2. aby H2.
          - assume H2: eps_ k + w' <= x. prove False.
            apply HC.
            witness k. apply andI.
            + aby Hk.
            + prove w' + y <= hL k.
              apply SNoLtLe.
              aby SNoLeLt_tra SNo_eps_ SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_Lt1_cancel add_SNo_com_3b_1_2 H2 Hk Hw'1 L4 LhLb Lxy Ly Lx.
        }
        aby SNoLt_irref Lw'2b Hw'3.
      }
      aby ReplI SNoLeLt_tra SNo_add_SNo Lw'2 Hw'1 HLR3 HLR1 LhLb Ly.
    + assume Hw: w :e {x + w|w :e SNoL y}.
      apply ReplE_impred (SNoL y) (fun w => x + w) w Hw.
      let w'. assume Hw': w' :e SNoL y.
      assume Hww'. rewrite Hww'.
      prove x + w' < SNoCut L R.
      apply SNoL_E y Ly w' Hw'.
      assume Hw'1 Hw'2 Hw'3.
      claim Lw'1: w' :e SNoS_ omega.
      { aby SNoLev_In_real_SNoS_omega Hw'2 Hw'1 Hy. }
      claim Lw'2: exists n :e omega, x + w' <= hL n.
      { apply dneg. assume HC: ~(exists n :e omega, x + w' <= hL n).
        claim Lw'2a: 0 < y + - w'.
        { aby SNoLt_minus_pos Hw'3 Hw'1 Ly. }
        claim Lw'2b: w' = y.
        { apply Ly2 w' Lw'1.
          let k. assume Hk.
          prove abs_SNo (w' + - y) < eps_ k.
          rewrite abs_SNo_dist_swap w' y Hw'1 Ly.
          prove abs_SNo (y + - w') < eps_ k.
          rewrite pos_abs_SNo (y + - w') Lw'2a.
          prove y + - w' < eps_ k.
          apply add_SNo_minus_Lt1b y w' (eps_ k) Ly Hw'1 (SNo_eps_ k Hk).
          prove y < eps_ k + w'.
          apply SNoLtLe_or y (eps_ k + w') Ly (SNo_add_SNo (eps_ k) w' (SNo_eps_ k Hk) Hw'1).
          - assume H2. aby H2.
          - assume H2: eps_ k + w' <= y. prove False.
            apply HC.
            aby SNoLtLe SNoLeLt_tra SNo_eps_ SNo_add_SNo add_SNo_Le2 add_SNo_com add_SNo_assoc add_SNo_Lt1_cancel H2 Hk Hw'1 L4 LhLb Lxy Ly Lx.
        }
        aby SNoLt_irref Lw'2b Hw'3.
      }
      aby ReplI SNoLeLt_tra SNo_add_SNo Lw'2 Hw'1 HLR3 HLR1 LhLb Lx.
  - prove forall z :e {z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}, SNoCut L R < z.
    let z. assume Hz.
    apply binunionE {z + y|z :e SNoR x} {x + z|z :e SNoR y} z Hz.
    + assume Hz: z :e {z + y|z :e SNoR x}.
      apply ReplE_impred (SNoR x) (fun z => z + y) z Hz.
      let z'. assume Hz': z' :e SNoR x.
      assume Hzz'. rewrite Hzz'.
      prove SNoCut L R < z' + y.
      apply SNoR_E x Lx z' Hz'.
      assume Hz'1 Hz'2 Hz'3.
      claim Lz'1: z' :e SNoS_ omega.
      { aby SNoLev_In_real_SNoS_omega Hz'2 Hz'1 Hx. }
      claim Lz'2: exists n :e omega, hR n <= z' + y.
      { apply dneg. assume HC: ~(exists n :e omega, hR n <= z' + y).
        claim Lz'2a: 0 < z' + - x.
        { aby SNoLt_minus_pos Hz'3 Hz'1 Lx. }
        claim Lz'2b: z' = x.
        { apply Lx2 z' Lz'1.
          let k. assume Hk.
          prove abs_SNo (z' + - x) < eps_ k.
          rewrite pos_abs_SNo (z' + - x) Lz'2a.
          prove z' + - x < eps_ k.
          apply add_SNo_minus_Lt1b z' x (eps_ k) Hz'1 Lx (SNo_eps_ k Hk).
          prove z' < eps_ k + x.
          apply SNoLtLe_or z' (eps_ k + x) Hz'1 (SNo_add_SNo (eps_ k) x (SNo_eps_ k Hk) Lx).
          - assume H2. aby H2.
          - assume H2: eps_ k + x <= z'. prove False.
            apply HC.
            witness k. apply andI.
            + aby Hk.
            + prove hR k <= z' + y.
              apply SNoLtLe.
              apply add_SNo_Lt1_cancel (hR k) (- eps_ k) (z' + y) (LhRb k Hk) (SNo_minus_SNo (eps_ k) (SNo_eps_ k Hk)) (SNo_add_SNo z' y Hz'1 Ly).
              aby SNoLtLe_tra SNo_eps_ SNo_minus_SNo SNo_add_SNo add_SNo_Le1 add_SNo_com add_SNo_com_3b_1_2 add_SNo_minus_Le2b H2 Hk Hz'1 L6 LhRb Lxy Ly Lx.
        }
        aby SNoLt_irref Lz'2b Hz'3.
      }
      aby ReplI SNoLtLe_tra SNo_add_SNo Lz'2 Hz'1 HLR4 HLR1 LhRb Ly.
    + assume Hz: z :e {x + z|z :e SNoR y}.
      apply ReplE_impred (SNoR y) (fun z => x + z) z Hz.
      let z'. assume Hz': z' :e SNoR y.
      assume Hzz'. rewrite Hzz'.
      prove SNoCut L R < x + z'.
      apply SNoR_E y Ly z' Hz'.
      assume Hz'1 Hz'2 Hz'3.
      claim Lz'1: z' :e SNoS_ omega.
      { aby SNoLev_In_real_SNoS_omega Hz'2 Hz'1 Hy. }
      claim Lz'2: exists n :e omega, hR n <= x + z'.
      { apply dneg. assume HC: ~(exists n :e omega, hR n <= x + z').
        claim Lz'2a: 0 < z' + - y.
        { aby SNoLt_minus_pos Hz'3 Hz'1 Ly. }
        claim Lz'2b: z' = y.
        { apply Ly2 z' Lz'1.
          let k. assume Hk.
          prove abs_SNo (z' + - y) < eps_ k.
          rewrite pos_abs_SNo (z' + - y) Lz'2a.
          prove z' + - y < eps_ k.
          apply add_SNo_minus_Lt1b z' y (eps_ k) Hz'1 Ly (SNo_eps_ k Hk).
          prove z' < eps_ k + y.
          apply SNoLtLe_or z' (eps_ k + y) Hz'1 (SNo_add_SNo (eps_ k) y (SNo_eps_ k Hk) Ly).
          - assume H2. aby H2.
          - assume H2: eps_ k + y <= z'. prove False.
            apply HC.
            witness k. apply andI.
            + aby Hk.
            + prove hR k <= x + z'.
              apply SNoLtLe.
              apply add_SNo_Lt1_cancel (hR k) (- eps_ k) (x + z') (LhRb k Hk) (SNo_minus_SNo (eps_ k) (SNo_eps_ k Hk)) (SNo_add_SNo x z' Lx Hz'1).
              aby SNoLtLe_tra SNo_eps_ SNo_minus_SNo SNo_add_SNo add_SNo_Le2 add_SNo_com add_SNo_assoc add_SNo_minus_Le2b H2 Hk Hz'1 L6 LhRb Lxy Ly Lx.
        }
        aby SNoLt_irref Lz'2b Hz'3.
      }
      aby ReplI SNoLtLe_tra SNo_add_SNo Lz'2 Hz'1 HLR4 HLR1 LhRb Lx.
  - aby ReplE_impred add_SNo_eq L3 Ly Lx.
  - aby ReplE_impred add_SNo_eq L7 Ly Lx.
}
aby SNo_add_SNo SNo_approx_real Hx Hy HfL HfR HfL1 HfL2 HfL3 HfR1 HfR2 HfR3 HfLR HxfLR HgL HgR HgL1 HgL2 HgL3 HgR1 HgR2 HgR3 HgLR HygLR Lx Ly Lxy Lx2 Ly2 LfLa LfLb LgLa LgLb LfRa LfRb LgRa LgRb LhL LhR LhLb LhRb L1 L2 L3 L4 L5 L6 L7 L8 LLR HLR1 HLR2 HLR3 HLR4 HLR5 L9.
Qed.

Theorem SNoS_ordsucc_omega_bdd_eps_pos : forall x :e SNoS_ (ordsucc omega), 0 < x -> x < omega -> exists N :e omega, eps_ N * x < 1.
let x. assume Hx1 Hx2 Hx3.
apply SNoS_E2 (ordsucc omega) ordsucc_omega_ordinal x Hx1.
assume Hx1a Hx1b Hx1c Hx1d.
apply SNoS_ordsucc_omega_bdd_above x Hx1 Hx3.
let N. assume HN. apply HN.
assume HN1: N :e omega.
assume HN2: x < N.
claim LN: SNo N.
{ aby omega_SNo HN1. }
witness N. apply andI.
- aby HN1.
- prove eps_ N * x < 1.
  apply SNoLt_tra (eps_ N * x) (eps_ N * N) 1
                  (SNo_mul_SNo (eps_ N) x (SNo_eps_ N HN1) Hx1c)
                  (SNo_mul_SNo (eps_ N) N (SNo_eps_ N HN1) LN)
                  SNo_1.
  + aby SNo_eps_ SNo_eps_pos pos_mul_SNo_Lt LN HN2 HN1 Hx1c.
  + prove eps_ N * N < 1.
    apply SNoLtLe_or (eps_ N * N) 1
                  (SNo_mul_SNo (eps_ N) N (SNo_eps_ N HN1) LN) SNo_1.
    * aby.
    * aby omega_nat_p SNoLtLe SNoLt_irref SNoLeLt_tra SNo_1 SNo_2 SNo_eps_ SNoLt_0_2 SNo_mul_SNo mul_SNo_oneR mul_SNo_assoc mul_SNo_oneL nonneg_mul_SNo_Le SNo_exp_SNo_nat exp_SNo_2_bd mul_SNo_eps_power_2' exp_SNo_nat_pos LN HN1.
Qed.

Theorem real_mul_SNo_pos : forall x y :e real, 0 < x -> 0 < y -> x * y :e real.
let x. assume Hx. let y. assume Hy Hx0 Hy0.
apply dneg.
assume HC: x * y /:e real.
apply real_E x Hx.
assume Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7.
apply real_E y Hy.
assume Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7.
claim Lx7: forall k :e omega,
  forall p:prop,
      (forall q :e SNoS_ omega, 0 < q -> q < x -> x < q + eps_ k -> p)
   -> p.
{ aby SNo_prereal_incr_lower_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7. }
claim Ly7: forall k :e omega,
  forall p:prop,
      (forall q :e SNoS_ omega, 0 < q -> q < y -> y < q + eps_ k -> p)
   -> p.
{ aby SNo_prereal_incr_lower_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7. }
claim Lxy: SNo (x * y).
{ aby SNo_mul_SNo Hy1 Hx1. }
claim Lmxy: SNo (- x * y).
{ aby SNo_minus_SNo Lxy. }
claim Lxy2: SNoLev (x * y) /:e omega.
{ assume H1: SNoLev (x * y) :e omega.
  aby omega_ordinal SNoLev_ SNoS_I SNoS_omega_real H1 Lxy HC.
}
claim Lxy3: forall q, SNo q -> SNoLev q :e omega -> SNoLev q :e SNoLev (x * y).
{ aby nat_p_trans ordinal_trichotomy_or_impred omega_nat_p nat_p_omega SNoLev_ordinal Lxy2 Lxy. }
claim LLx: SNoL x c= SNoS_ omega.
{ aby ordsuccE omega_TransSet omega_ordinal SNoLev_ SNoS_I SNoL_E Hx2 Hx1. }
claim LRx: SNoR x c= SNoS_ omega.
{ aby ordsuccE omega_TransSet omega_ordinal SNoLev_ SNoS_I SNoR_E Hx2 Hx1. }
claim LLy: SNoL y c= SNoS_ omega.
{ aby ordsuccE omega_TransSet omega_ordinal SNoLev_ SNoS_I SNoL_E Hy2 Hy1. }
claim LRy: SNoR y c= SNoS_ omega.
{ aby ordsuccE omega_TransSet omega_ordinal SNoLev_ SNoS_I SNoR_E Hy2 Hy1. }
claim LLx2: forall v :e SNoL x, forall p:prop, (forall k, k :e omega -> eps_ k <= x + - v -> p) -> p.
{ aby xm dneg SNoLt_irref SNoLtLe_or SNoL_E SNo_eps_ SNo_minus_SNo SNo_add_SNo SNoLt_minus_pos pos_abs_SNo abs_SNo_dist_swap LLx Hx6 Hx1. }
claim LRx2: forall v :e SNoR x, forall p:prop, (forall k, k :e omega -> eps_ k <= v + - x -> p) -> p.
{ aby xm dneg SNoLt_irref SNoLtLe_or SNoR_E SNo_eps_ SNo_minus_SNo SNo_add_SNo SNoLt_minus_pos pos_abs_SNo LRx Hx6 Hx1. }
claim LLy2: forall v :e SNoL y, forall p:prop, (forall k, k :e omega -> eps_ k <= y + - v -> p) -> p.
{ aby xm dneg SNoLt_irref SNoLtLe_or SNoL_E SNo_eps_ SNo_minus_SNo SNo_add_SNo SNoLt_minus_pos pos_abs_SNo abs_SNo_dist_swap LLy Hy6 Hy1. }
claim LRy2: forall v :e SNoR y, forall p:prop, (forall k, k :e omega -> eps_ k <= v + - y -> p) -> p.
{ aby xm dneg SNoLt_irref SNoLtLe_or SNoR_E SNo_eps_ SNo_minus_SNo SNo_add_SNo SNoLt_minus_pos pos_abs_SNo LRy Hy6 Hy1. }
apply mul_SNo_eq_3 x y Hx1 Hy1.
let L R.
assume HLR: SNoCutP L R.
assume HLE: forall u, u :e L -> forall q:prop,
                (forall w0 :e SNoL x, forall w1 :e SNoL y, u = w0 * y + x * w1 + - w0 * w1 -> q)
             -> (forall z0 :e SNoR x, forall z1 :e SNoR y, u = z0 * y + x * z1 + - z0 * z1 -> q)
             -> q.
assume HLI1: forall w0 :e SNoL x, forall w1 :e SNoL y, w0 * y + x * w1 + - w0 * w1 :e L.
assume HLI2: forall z0 :e SNoR x, forall z1 :e SNoR y, z0 * y + x * z1 + - z0 * z1 :e L.
assume HRE: forall u, u :e R -> forall q:prop,
                (forall w0 :e SNoL x, forall z1 :e SNoR y, u = w0 * y + x * z1 + - w0 * z1 -> q)
             -> (forall z0 :e SNoR x, forall w1 :e SNoL y, u = z0 * y + x * w1 + - z0 * w1 -> q)
             -> q.
assume HRI1: forall w0 :e SNoL x, forall z1 :e SNoR y, w0 * y + x * z1 + - w0 * z1 :e R.
assume HRI2: forall z0 :e SNoR x, forall w1 :e SNoL y, z0 * y + x * w1 + - z0 * w1 :e R.
assume HxyLR: x * y = SNoCut L R.
claim L1: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - (x * y)) < eps_ k) -> q = x * y.
{ let q. assume Hq1 Hq2.
  prove q = x * y.
  apply SNoS_E2 omega omega_ordinal q Hq1.
  assume Hq1a Hq1b Hq1c Hq1d.
  apply SNoLt_trichotomy_or_impred q (x * y) Hq1c Lxy.
  - assume H1: q < x * y. prove False.
    claim Lq1: q :e SNoL (x * y).
    { aby SNoL_I H1 Hq1c Hq1a Lxy3 Lxy. }
    apply mul_SNo_SNoL_interpolate_impred x y Hx1 Hy1 q Lq1.
    + let v. assume Hv: v :e SNoL x. let w. assume Hw: w :e SNoL y.
      apply SNoL_E x Hx1 v Hv.
      assume Hv1 _ _.
      apply SNoL_E y Hy1 w Hw.
      assume Hw1 _ _.
      assume H2: q + v * w <= v * y + x * w.
      claim Lvw: SNo (v * w).
      { aby SNo_mul_SNo Hw1 Hv1. }
      claim Lxw: SNo (x * w).
      { aby SNo_mul_SNo Hw1 Hx1. }
      claim Lmxw: SNo (- x * w).
      { aby SNo_minus_SNo Lxw. }
      claim Lvy: SNo (v * y).
      { aby SNo_mul_SNo Hv1 Hy1. }
      claim Lmvy: SNo (- v * y).
      { aby SNo_minus_SNo Lvy. }
      claim Lxmv: SNo (x + - v).
      { aby SNo_minus_SNo SNo_add_SNo Hv1 Hx1. }
      claim Lymw: SNo (y + - w).
      { aby SNo_minus_SNo SNo_add_SNo Hw1 Hy1. }
      apply LLx2 v Hv.
      let k. assume Hk1: k :e omega. assume Hk2: eps_ k <= x + - v.
      apply LLy2 w Hw.
      let k'. assume Hk'1: k' :e omega. assume Hk'2: eps_ k' <= y + - w.
      claim Lek: SNo (eps_ k).
      { aby SNo_eps_ Hk1. }
      claim Lek': SNo (eps_ k').
      { aby SNo_eps_ Hk'1. }
      claim Lkk': k + k' :e omega.
      { aby add_SNo_In_omega Hk'1 Hk1. }
      claim Lekk': SNo (eps_ (k + k')).
      { aby SNo_eps_ Lkk'. }
      claim Lekek': SNo (eps_ k * eps_ k').
      { aby SNo_mul_SNo Lek' Lek. }
      claim L1a: abs_SNo (q + - (x * y)) < eps_ (k + k').
      { aby add_SNo_In_omega Hk'1 Hk1 Hq2. }
      claim L1b: eps_ (k + k') <= abs_SNo (q + - (x * y)).
      { rewrite abs_SNo_dist_swap q (x * y) Hq1c Lxy.
        prove eps_ (k + k') <= abs_SNo (x * y + - q).
        rewrite pos_abs_SNo (x * y + - q) (SNoLt_minus_pos q (x * y) Hq1c Lxy H1).
        prove eps_ (k + k') <= x * y + - q.
        apply add_SNo_minus_Le2b (x * y) q (eps_ (k + k')) Lxy Hq1c Lekk'.
        prove eps_ (k + k') + q <= x * y.
        rewrite <- mul_SNo_eps_eps_add_SNo k Hk1 k' Hk'1.
        prove eps_ k * eps_ k' + q <= x * y.
        apply SNoLe_tra (eps_ k * eps_ k' + q)
                        ((x + - v) * (y + - w) + q)
                        (x * y)
                        (SNo_add_SNo (eps_ k * eps_ k') q ?? ??)
                        (SNo_add_SNo ((x + - v) * (y + - w)) q
                            (SNo_mul_SNo (x + - v) (y + - w) Lxmv Lymw)
                            Hq1c)
                        Lxy.
        - aby SNoLtLe SNo_eps_pos add_SNo_Le1 SNo_mul_SNo nonneg_mul_SNo_Le2 Lekek' Lek' Lek Hk'2 Hk'1 Hk2 Hk1 Lymw Lxmv Hq1c.
        - prove (x + - v) * (y + - w) + q <= x * y.
          rewrite SNo_foil_mm x v y w Hx1 Hv1 Hy1 Hw1.
          prove (x * y + - x * w + - v * y + v * w) + q <= x * y.
          rewrite add_SNo_assoc_4 (x * y) (- x * w) (- v * y) (v * w)
                         ?? ?? ?? ??.
          aby SNoLe_ref SNoLe_tra SNo_add_SNo SNo_add_SNo_3 add_SNo_Le2 add_SNo_com add_SNo_0R add_SNo_minus_SNo_linv add_SNo_assoc add_SNo_minus_SNo_prop5 SNo_mul_SNo Lmvy Lvy Lmxw Lxw Lvw H2 Hq1c Lxy Hy1 Hx1.
      }
      aby SNoLt_irref SNoLeLt_tra SNo_add_SNo SNo_abs_SNo L1b L1a Lekk' Hq1c Lmxy.
    + let v. assume Hv: v :e SNoR x. let w. assume Hw: w :e SNoR y.
      apply SNoR_E x Hx1 v Hv.
      assume Hv1 _ _.
      apply SNoR_E y Hy1 w Hw.
      assume Hw1 _ _.
      assume H2: q + v * w <= v * y + x * w.
      claim Lvw: SNo (v * w).
      { aby SNo_mul_SNo Hw1 Hv1. }
      claim Lxw: SNo (x * w).
      { aby SNo_mul_SNo Hw1 Hx1. }
      claim Lmxw: SNo (- x * w).
      { aby SNo_minus_SNo Lxw. }
      claim Lvy: SNo (v * y).
      { aby SNo_mul_SNo Hv1 Hy1. }
      claim Lmvy: SNo (- v * y).
      { aby SNo_minus_SNo Lvy. }
      claim Lvmx: SNo (v + - x).
      { aby SNo_minus_SNo SNo_add_SNo Hv1 Hx1. }
      claim Lwmy: SNo (w + - y).
      { aby SNo_minus_SNo SNo_add_SNo Hw1 Hy1. }
      apply LRx2 v Hv.
      let k. assume Hk1: k :e omega. assume Hk2: eps_ k <= v + - x.
      apply LRy2 w Hw.
      let k'. assume Hk'1: k' :e omega. assume Hk'2: eps_ k' <= w + - y.
      claim Lek: SNo (eps_ k).
      { aby SNo_eps_ Hk1. }
      claim Lek': SNo (eps_ k').
      { aby SNo_eps_ Hk'1. }
      claim Lkk': k + k' :e omega.
      { aby add_SNo_In_omega Hk'1 Hk1. }
      claim Lekk': SNo (eps_ (k + k')).
      { aby SNo_eps_ Lkk'. }
      claim Lekek': SNo (eps_ k * eps_ k').
      { aby SNo_mul_SNo Lek' Lek. }
      claim L1c: abs_SNo (q + - (x * y)) < eps_ (k + k').
      { aby add_SNo_In_omega Hk'1 Hk1 Hq2. }
      claim L1d: eps_ (k + k') <= abs_SNo (q + - (x * y)).
      { rewrite abs_SNo_dist_swap q (x * y) Hq1c Lxy.
        prove eps_ (k + k') <= abs_SNo (x * y + - q).
        rewrite pos_abs_SNo (x * y + - q) (SNoLt_minus_pos q (x * y) Hq1c Lxy H1).
        prove eps_ (k + k') <= x * y + - q.
        apply add_SNo_minus_Le2b (x * y) q (eps_ (k + k')) Lxy Hq1c Lekk'.
        prove eps_ (k + k') + q <= x * y.
        rewrite <- mul_SNo_eps_eps_add_SNo k Hk1 k' Hk'1.
        prove eps_ k * eps_ k' + q <= x * y.
        apply SNoLe_tra (eps_ k * eps_ k' + q)
                        ((v + - x) * (w + - y) + q)
                        (x * y)
                        (SNo_add_SNo (eps_ k * eps_ k') q ?? Hq1c)
                        (SNo_add_SNo ((v + - x) * (w + - y)) q
                            (SNo_mul_SNo (v + - x) (w + - y) ?? ??)
                            Hq1c)
                        Lxy.
        - aby SNoLtLe SNo_eps_pos add_SNo_Le1 SNo_mul_SNo nonneg_mul_SNo_Le2 Lekek' Lek' Lek Hk'2 Hk'1 Hk2 Hk1 Lwmy Lvmx Hq1c.
        - prove (v + - x) * (w + - y) + q <= x * y.
          rewrite SNo_foil_mm v x w y Hv1 Hx1 Hw1 Hy1.
          prove (v * w + - v * y + - x * w + x * y) + q <= x * y.
          rewrite add_SNo_assoc_4 (v * w) (- v * y) (- x * w) (x * y) ?? ?? ?? ??.
          prove ((v * w + - v * y + - x * w) + x * y) + q <= x * y.
          rewrite <- add_SNo_assoc
                       (v * w + - v * y + - x * w) (x * y) q
                       (SNo_add_SNo_3 (v * w) (- v * y) (- x * w) ?? ?? ??)
                       ??
                       Hq1c.                           
          aby SNoLe_ref SNoLe_tra SNo_add_SNo SNo_add_SNo_3 add_SNo_Le2 add_SNo_com add_SNo_0R add_SNo_minus_SNo_linv add_SNo_minus_SNo_prop5 add_SNo_3a_2b Lmvy Lvy Lmxw Lxw Lvw H2 Hq1c Lxy.
      }
      aby SNoLt_irref SNoLeLt_tra SNo_minus_SNo SNo_add_SNo SNo_abs_SNo L1d L1c Lekk' Hq1c Lxy.
  - aby.
  - assume H1: x * y < q. prove False.
    claim Lq2: q :e SNoR (x * y).
    { aby SNoR_I H1 Hq1c Hq1a Lxy3 Lxy. }
    apply mul_SNo_SNoR_interpolate_impred x y Hx1 Hy1 q Lq2.
    + let v. assume Hv: v :e SNoL x. let w. assume Hw: w :e SNoR y.
      apply SNoL_E x Hx1 v Hv.
      assume Hv1 _ _.
      apply SNoR_E y Hy1 w Hw.
      assume Hw1 _ _.
      assume H2: v * y + x * w <= q + v * w.
      claim Lvy: SNo (v * y).
      { aby SNo_mul_SNo Hv1 Hy1. }
      claim Lxw: SNo (x * w).
      { aby SNo_mul_SNo Hw1 Hx1. }
      claim Lmxw: SNo (- x * w).
      { aby SNo_minus_SNo Lxw. }
      claim Lvw: SNo (v * w).
      { aby SNo_mul_SNo Hw1 Hv1. }
      claim Lmvw: SNo (- v * w).
      { aby SNo_minus_SNo Lvw. }
      claim Lxmv: SNo (x + - v).
      { aby SNo_minus_SNo SNo_add_SNo Hv1 Hx1. }
      claim Lwmy: SNo (w + - y).
      { aby SNo_minus_SNo SNo_add_SNo Hw1 Hy1. }
      apply LLx2 v Hv.
      let k. assume Hk1: k :e omega. assume Hk2: eps_ k <= x + - v.
      apply LRy2 w Hw.
      let k'. assume Hk'1: k' :e omega. assume Hk'2: eps_ k' <= w + - y.
      claim Lek: SNo (eps_ k).
      { aby SNo_eps_ Hk1. }
      claim Lek': SNo (eps_ k').
      { aby SNo_eps_ Hk'1. }
      claim Lkk': k + k' :e omega.
      { aby add_SNo_In_omega Hk'1 Hk1. }
      claim Lekk': SNo (eps_ (k + k')).
      { aby SNo_eps_ Lkk'. }
      claim Lekek': SNo (eps_ k * eps_ k').
      { aby SNo_mul_SNo Lek' Lek. }
      claim L1e: abs_SNo (q + - (x * y)) < eps_ (k + k').
      { aby add_SNo_In_omega Hk'1 Hk1 Hq2. }
      claim L1f: eps_ (k + k') <= abs_SNo (q + - (x * y)).
      { rewrite pos_abs_SNo (q + - x * y) (SNoLt_minus_pos (x * y) q Lxy Hq1c H1).
        prove eps_ (k + k') <= q + - x * y.
        apply add_SNo_minus_Le2b q (x * y) (eps_ (k + k')) Hq1c Lxy Lekk'.
        prove eps_ (k + k') + x * y <= q.
        rewrite <- mul_SNo_eps_eps_add_SNo k Hk1 k' Hk'1.
        prove eps_ k * eps_ k' + x * y <= q.
        apply SNoLe_tra (eps_ k * eps_ k' + x * y)
                        ((x + - v) * (w + - y) + x * y)
                        q
                        (SNo_add_SNo (eps_ k * eps_ k') (x * y) ?? ??)
                        (SNo_add_SNo ((x + - v) * (w + - y)) (x * y)
                            (SNo_mul_SNo (x + - v) (w + - y) Lxmv Lwmy)
                            Lxy)
                        Hq1c.
        - aby SNoLtLe SNo_eps_pos add_SNo_Le1 SNo_mul_SNo nonneg_mul_SNo_Le2 Lekek' Lek' Lek Hk'2 Hk'1 Hk2 Hk1 Lwmy Lxmv Lxy.
        - prove (x + - v) * (w + - y) + x * y <= q.
          rewrite SNo_foil_mm x v w y Hx1 Hv1 Hw1 Hy1.
          aby SNoLe_ref SNoLe_tra SNo_add_SNo SNo_add_SNo_3 SNo_add_SNo_4 add_SNo_Le2 add_SNo_com add_SNo_minus_L2 add_SNo_minus_L2' add_SNo_rotate_4_1 add_SNo_minus_SNo_prop2 Lmvw Lvw Lxw Lvy H2 Hq1c Lmxy Lxy.
      }
      aby SNoLt_irref SNoLeLt_tra SNo_add_SNo SNo_abs_SNo L1f L1e Lekk' Hq1c Lmxy.
    + let v. assume Hv: v :e SNoR x. let w. assume Hw: w :e SNoL y.
      apply SNoR_E x Hx1 v Hv.
      assume Hv1 _ _.
      apply SNoL_E y Hy1 w Hw.
      assume Hw1 _ _.
      assume H2: v * y + x * w <= q + v * w.
      claim Lvy: SNo (v * y).
      { aby SNo_mul_SNo Hv1 Hy1. }
      claim Lxw: SNo (x * w).
      { aby SNo_mul_SNo Hw1 Hx1. }
      claim Lvw: SNo (v * w).
      { aby SNo_mul_SNo Hw1 Hv1. }
      claim Lmvw: SNo (- v * w).
      { aby SNo_minus_SNo Lvw. }
      claim Lvmx: SNo (v + - x).
      { aby SNo_minus_SNo SNo_add_SNo Hv1 Hx1. }
      claim Lymw: SNo (y + - w).
      { aby SNo_minus_SNo SNo_add_SNo Hw1 Hy1. }
      apply LRx2 v Hv.
      let k. assume Hk1: k :e omega. assume Hk2: eps_ k <= v + - x.
      apply LLy2 w Hw.
      let k'. assume Hk'1: k' :e omega. assume Hk'2: eps_ k' <= y + - w.
      claim Lek: SNo (eps_ k).
      { aby SNo_eps_ Hk1. }
      claim Lek': SNo (eps_ k').
      { aby SNo_eps_ Hk'1. }
      claim Lkk': k + k' :e omega.
      { aby add_SNo_In_omega Hk'1 Hk1. }
      claim Lekk': SNo (eps_ (k + k')).
      { aby SNo_eps_ Lkk'. }
      claim Lekek': SNo (eps_ k * eps_ k').
      { aby SNo_mul_SNo Lek' Lek. }
      claim L1g: abs_SNo (q + - (x * y)) < eps_ (k + k').
      { aby add_SNo_In_omega Hk'1 Hk1 Hq2. }
      claim L1h: eps_ (k + k') <= abs_SNo (q + - (x * y)).
      { rewrite pos_abs_SNo (q + - x * y) (SNoLt_minus_pos (x * y) q Lxy Hq1c H1).
        prove eps_ (k + k') <= q + - x * y.
        apply add_SNo_minus_Le2b q (x * y) (eps_ (k + k')) Hq1c Lxy Lekk'.
        prove eps_ (k + k') + x * y <= q.
        rewrite <- mul_SNo_eps_eps_add_SNo k Hk1 k' Hk'1.
        prove eps_ k * eps_ k' + x * y <= q.
        apply SNoLe_tra (eps_ k * eps_ k' + x * y)
                        ((v + - x) * (y + - w) + x * y)
                        q
                        (SNo_add_SNo (eps_ k * eps_ k') (x * y) ?? Lxy)
                        (SNo_add_SNo ((v + - x) * (y + - w)) (x * y)
                            (SNo_mul_SNo (v + - x) (y + - w) ?? ??)
                            Lxy)
                        Hq1c.
        - aby SNoLtLe SNo_eps_pos add_SNo_Le1 SNo_mul_SNo nonneg_mul_SNo_Le2 Lekek' Lek' Lek Hk'2 Hk'1 Hk2 Hk1 Lymw Lvmx Lxy.
        - prove (v + - x) * (y + - w) + x * y <= q.
          rewrite SNo_foil_mm v x y w Hv1 Hx1 Hy1 Hw1.
          prove (v * y + - v * w + - x * y + x * w) + x * y <= q.
          rewrite add_SNo_rotate_4_1 (v * y) (- v * w) (- x * y) (x * w) ?? ?? ?? ??.
          rewrite add_SNo_rotate_4_1 (x * w) (v * y) (- v * w) (- x * y) ?? ?? ?? ??.
          prove (- x * y + x * w + v * y + - v * w) + x * y <= q.
          rewrite add_SNo_com (- x * y + x * w + v * y + - v * w) (x * y)
                              (SNo_add_SNo_4 (- x * y) (x * w) (v * y) (- v * w) ?? ?? ?? ??)
                              ??.
          prove x * y + - x * y + x * w + v * y + - v * w <= q.
          rewrite add_SNo_minus_L2' (x * y) (x * w + v * y + - v * w) ?? (SNo_add_SNo_3 (x * w) (v * y) (- v * w) ?? ?? ??).
          prove x * w + v * y + - v * w <= q.
          rewrite add_SNo_rotate_3_1 (x * w) (v * y) (- v * w) ?? ?? ??.
          prove - v * w + x * w + v * y <= q.
          apply SNoLe_tra (- v * w + x * w + v * y)
                          (- v * w + q + v * w)
                          q
                          (SNo_add_SNo_3 (- v * w) (x * w) (v * y) ?? ?? ??)
                          (SNo_add_SNo_3 (- v * w) q (v * w) ?? ?? ??)
                          ??.
          + prove - v * w + x * w + v * y
               <= - v * w + q + v * w.
            apply add_SNo_Le2 (- v * w) (x * w + v * y) (q + v * w)
                              ??
                              (SNo_add_SNo (x * w) (v * y) ?? ??)
                              (SNo_add_SNo q (v * w) ?? ??).
            prove x * w + v * y <= q + v * w.
            rewrite add_SNo_com (x * w) (v * y) ?? ??. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR Hq1 Hq2 Hq1a Hq1b Hq1c Hq1d H1 Lq2 Hv Hw Hv1 Hw1 H2 Lvy Lxw Lvw Lmvw Lvmx Lymw Hk1 Hk2 Hk'1 Hk'2 Lek Lek' Lkk' Lekk' Lekek' L1g.
          + prove - v * w + q + v * w <= q.
            rewrite add_SNo_com q (v * w) ?? ??.
            prove - v * w + v * w + q <= q.
            rewrite add_SNo_minus_L2 (v * w) q ?? ??.
            prove q <= q.
            apply SNoLe_ref.
      }
      aby SNoLt_irref SNoLeLt_tra SNo_minus_SNo SNo_add_SNo SNo_abs_SNo L1h L1g Lekk' Hq1c Lxy.
}
claim LNex: exists N :e omega, eps_ N * x < 1 /\ eps_ N * y < 1.
{ aby nat_p_ordinal ordinal_trichotomy_or_impred omega_nat_p SNoLt_tra SNo_1 SNo_eps_ SNo_eps_decr SNo_mul_SNo pos_mul_SNo_Lt' SNoS_ordsucc_omega_bdd_eps_pos Hy5 Hy3 Hy1 Hx5 Hx3 Hx1 Hy0 Hx0. }
apply LNex.
let N. assume HN. apply HN.
assume HN1: N :e omega. assume HN. apply HN.
assume HN2: eps_ N * x < 1.
assume HN3: eps_ N * y < 1.
claim L2: forall k :e omega, exists q :e SNoS_ omega, q < x * y /\ x * y < q + eps_ k.
{ let k. assume Hk.
  claim Lek: SNo (eps_ k).
  { aby SNo_eps_ Hk. }
  claim Lk1: k + 1 :e omega.
  { aby nat_1 nat_p_omega add_SNo_In_omega Hk. }
  claim Lk2: k + 2 :e omega.
  { aby nat_2 nat_p_omega add_SNo_In_omega Hk. }
  set k' := N + k + 2.
  claim Lk': k' :e omega.
  { aby add_SNo_In_omega Lk2 HN1. }
  claim Lek': SNo (eps_ k').
  { aby SNo_eps_ Lk'. }
  apply Lx7 k' Lk'.
  let q.
  assume Hq1: q :e SNoS_ omega.
  assume Hqpos: 0 < q.
  assume Hq2: q < x.
  assume Hq3: x < q + eps_ k'.
  apply SNoS_E2 omega omega_ordinal q Hq1.
  assume Hq1a Hq1b Hq1c Hq1d.
  apply Ly7 k' Lk'.
  let q'.
  assume Hq'1: q' :e SNoS_ omega.
  assume Hq'pos: 0 < q'.
  assume Hq'2: q' < y.
  assume Hq'3: y < q' + eps_ k'.
  apply SNoS_E2 omega omega_ordinal q' Hq'1.
  assume Hq'1a Hq'1b Hq'1c Hq'1d.
  claim Lqq': SNo (q * q').
  { aby SNo_mul_SNo Hq'1c Hq1c. }
  witness (q * q'). apply andI.
  + aby mul_SNo_SNoS_omega Hq'1 Hq1.
  + apply andI.
    * aby pos_mul_SNo_Lt2 Hq'1c Hq'2 Hq'pos Hq1c Hq2 Hqpos Hy1 Hx1.
    * { prove x * y < q * q' + eps_ k.
        apply SNoLt_tra (x * y) ((q + eps_ k') * (q' + eps_ k')) (q * q' + eps_ k)
                        Lxy
                        (SNo_mul_SNo
                          (q + eps_ k')
                          (q' + eps_ k')
                          (SNo_add_SNo q (eps_ k') Hq1c Lek')
                          (SNo_add_SNo q' (eps_ k') Hq'1c Lek'))
                        (SNo_add_SNo (q * q') (eps_ k) (SNo_mul_SNo q q' Hq1c Hq'1c) Lek).
        - aby SNo_add_SNo pos_mul_SNo_Lt2 Hq'1c Hq'3 Hq1c Hq3 Lek' Hy1 Hx1 Hy0 Hx0.
        - prove (q + eps_ k') * (q' + eps_ k') < q * q' + eps_ k.
          rewrite SNo_foil q (eps_ k') q' (eps_ k') Hq1c Lek' Hq'1c Lek'.
          prove q * q' + q * eps_ k' + eps_ k' * q' + eps_ k' * eps_ k' < q * q' + eps_ k.
          apply add_SNo_Lt2 (q * q') (q * eps_ k' + eps_ k' * q' + eps_ k' * eps_ k') (eps_ k)
                            Lqq'
                            (SNo_add_SNo_3 (q * eps_ k') (eps_ k' * q') (eps_ k' * eps_ k')
                                           (SNo_mul_SNo q (eps_ k') Hq1c Lek')
                                           (SNo_mul_SNo (eps_ k') q' Lek' Hq'1c)
                                           (SNo_mul_SNo (eps_ k') (eps_ k') Lek' Lek'))
                            Lek.
          prove q * eps_ k' + eps_ k' * q' + eps_ k' * eps_ k' < eps_ k.
          prove q * eps_ (N + k + 2) + eps_ (N + k + 2) * q' + eps_ (N + k + 2) * eps_ (N + k + 2) < eps_ k.
          rewrite <- mul_SNo_eps_eps_add_SNo N HN1 (k + 2) Lk2.
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < eps_ k.
          rewrite <- eps_ordsucc_half_add k (omega_nat_p k Hk).
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < eps_ (ordsucc k) + eps_ (ordsucc k).
          rewrite <- eps_ordsucc_half_add (ordsucc k) (nat_ordsucc k (omega_nat_p k Hk)) at 1.
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < (eps_ (ordsucc (ordsucc k)) + eps_ (ordsucc (ordsucc k))) + eps_ (ordsucc k).
          rewrite <- add_SNo_1_ordsucc k Hk.
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < (eps_ (ordsucc (k + 1)) + eps_ (ordsucc (k + 1))) + eps_ (k + 1).
          rewrite <- add_SNo_1_ordsucc (k+1) (add_SNo_In_omega k Hk 1 (nat_p_omega 1 nat_1)).
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < (eps_ (((k + 1) + 1)) + eps_ (((k + 1) + 1))) + eps_ (k + 1).
          rewrite <- add_SNo_assoc k 1 1 (omega_SNo k Hk) SNo_1 SNo_1.
          rewrite add_SNo_1_1_2.
          prove q * eps_ N * eps_ (k + 2) + (eps_ N * eps_ (k + 2)) * q' + (eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)) < (eps_ (k + 2) + eps_ (k + 2)) + eps_ (k + 1).
          claim LeN: SNo (eps_ N).
          { aby SNo_eps_ HN1. }
          claim Lek1: SNo (eps_ (k + 1)).
          { aby SNo_eps_ Lk1. }
          claim Lek2: SNo (eps_ (k + 2)).
          { aby SNo_eps_ Lk2. }
          claim LeNek2: SNo (eps_ N * eps_ (k + 2)).
          { aby SNo_mul_SNo Lek2 LeN. }
          claim LeNek2sq: SNo ((eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2))).
          { aby SNo_mul_SNo LeNek2. }
          rewrite <- add_SNo_assoc (eps_ (k + 2)) (eps_ (k + 2)) (eps_ (k + 1))
                                   Lek2 Lek2 Lek1.
          apply add_SNo_Lt4 (q * eps_ N * eps_ (k + 2))
                            ((eps_ N * eps_ (k + 2)) * q')
                            ((eps_ N * eps_ (k + 2)) * (eps_ N * eps_ (k + 2)))
                            (eps_ (k + 2))
                            (eps_ (k + 2))
                            (eps_ (k + 1))
                            (SNo_mul_SNo q (eps_ N * eps_ (k + 2)) Hq1c LeNek2)
                            (SNo_mul_SNo (eps_ N * eps_ (k + 2)) q' LeNek2 Hq'1c)
                            LeNek2sq Lek2 Lek2 Lek1.
          + aby SNoLt_tra SNo_1 SNo_eps_ SNo_eps_pos SNo_mul_SNo mul_SNo_com mul_SNo_assoc pos_mul_SNo_Lt' mul_SNo_Lt1_pos_Lt Lek2 LeN Hq1c Hq2 Lk2 HN2 HN1 Hx1.
          + aby SNoLt_tra SNo_1 SNo_eps_ SNo_eps_pos SNo_mul_SNo mul_SNo_com mul_SNo_assoc pos_mul_SNo_Lt' mul_SNo_Lt1_pos_Lt Lek2 LeN Hq'1c Hq'2 Lk2 HN3 HN1 Hy1.
          + aby nat_p_ordinal omega_nat_p SNoLtLe SNoLeLt_tra SNoLe_tra omega_SNo ordinal_SNoLt_In SNo_1 SNo_2 SNo_eps_decr SNo_eps_pos SNoLt_1_2 add_SNo_Lt2 mul_SNo_oneL mul_SNo_Le1_nonneg_Le nonneg_mul_SNo_Le2 mul_SNo_pos_pos eps_bd_1 LeNek2sq LeNek2 Lek2 Lek1 LeN Lk2 Lk1 Hk HN1.
      }
}      
apply SNo_prereal_incr_lower_approx (x * y) Lxy L1 L2.
let hL. assume HhL. apply HhL.
assume HhL1: hL :e SNoS_ omega :^: omega.
assume HhL2: forall n :e omega, hL n < x * y /\ x * y < hL n + eps_ n
                             /\ forall i :e n, hL i < hL n.
apply SNo_prereal_decr_upper_approx (x * y) Lxy L1 L2.
let hR. assume HhR. apply HhR.
assume HhR1: hR :e SNoS_ omega :^: omega.
assume HhR2: forall n :e omega, hR n + - eps_ n < x * y /\ x * y < hR n
                             /\ forall i :e n, hR n < hR i.
claim LhL: forall n :e omega, SNo (hL n).
{ aby omega_ordinal ap_Pi SNoS_E2 HhL1. }
claim LhR: forall n :e omega, SNo (hR n).
{ aby omega_ordinal ap_Pi SNoS_E2 HhR1. }
claim L3: forall n :e omega, hL n < x * y.
{ aby HhL2. }
claim L4: forall n :e omega, x * y < hR n.
{ aby HhR2. }
claim L5: forall n m :e omega, hL n < hR m.
{ aby SNoLt_tra L4 L3 LhR LhL Lxy. }
apply SNo_approx_real_lem hL HhL1 hR HhR1 L5.
assume HhLR1: SNoCutP {hL n|n :e omega} {hR n|n :e omega}.
assume HhLR2: SNo (SNoCut {hL n|n :e omega} {hR n|n :e omega}).
assume _ _.
assume HhLR5: forall n :e omega, hL n < SNoCut {hL n|n :e omega} {hR n|n :e omega}.
assume HhLR6: forall n :e omega, SNoCut {hL n|n :e omega} {hR n|n :e omega} < hR n.
claim L6: forall n :e omega, x * y < hL n + eps_ n.
{ aby HhL2. }
claim L7: forall n :e omega, forall i :e n, hL i < hL n.
{ aby HhL2. }
claim L8: forall n :e omega, hR n + - eps_ n < x * y.
{ aby HhR2. }
claim L9: forall n :e omega, forall i :e n, hR n < hR i.
{ aby HhR2. }
claim L10: x * y = SNoCut {hL n|n :e omega} {hR n|n :e omega}.
{ rewrite HxyLR.
  prove SNoCut L R = SNoCut {hL n|n :e omega} {hR n|n :e omega}.
  apply SNoCut_ext L R {hL n|n :e omega} {hR n|n :e omega}
                   HLR HhLR1.
  - let w. assume Hw: w :e L.
    prove w < SNoCut {hL n|n :e omega} {hR n|n :e omega}.
    apply HLE w Hw.
    + let w0. assume Hw0: w0 :e SNoL x.
      let w1. assume Hw1: w1 :e SNoL y.
      assume Hwe: w = w0 * y + x * w1 + - w0 * w1.
      apply LLx2 w0 Hw0.
      let k0. assume Hk0: k0 :e omega.
      assume Hk0b: eps_ k0 <= x + - w0.
      apply LLy2 w1 Hw1.
      let k1. assume Hk1: k1 :e omega.
      assume Hk1b: eps_ k1 <= y + - w1.
      apply SNoL_E x Hx1 w0 Hw0.
      assume Hw01: SNo w0.
      assume Hw02: SNoLev w0 :e SNoLev x.
      assume Hw03: w0 < x.
      apply SNoL_E y Hy1 w1 Hw1.
      assume Hw11: SNo w1.
      assume Hw12: SNoLev w1 :e SNoLev y.
      assume Hw13: w1 < y.
      claim Lek0: SNo (eps_ k0).
      { aby SNo_eps_ Hk0. }
      claim Lek1: SNo (eps_ k1).
      { aby SNo_eps_ Hk1. }
      claim Lk0k1: k0 + k1 :e omega.
      { aby add_SNo_In_omega Hk1 Hk0. }
      claim Lek0k1: SNo (eps_ (k0 + k1)).
      { aby SNo_eps_ Lk0k1. }
      claim LhLk0k1: SNo (hL (k0 + k1)).
      { aby Lk0k1 LhL. }
      claim Lw0y: SNo (w0 * y).
      { aby SNo_mul_SNo Hw01 Hy1. }
      claim Lxw1: SNo (x * w1).
      { aby SNo_mul_SNo Hw11 Hx1. }
      claim Lw0w1: SNo (w0 * w1).
      { aby SNo_mul_SNo Hw11 Hw01. }
      claim Lmw0w1: SNo (- w0 * w1).
      { aby SNo_minus_SNo Lw0w1. }
      claim Lw0yxw1mw0w1: SNo (w0 * y + x * w1 + - w0 * w1).
      { aby SNo_add_SNo_3 Lmw0w1 Lxw1 Lw0y. }
      rewrite Hwe.
      apply SNoLeLt_tra (w0 * y + x * w1 + - w0 * w1)
                        (hL (k0 + k1))
                        (SNoCut {hL n|n :e omega} {hR n|n :e omega})
                        Lw0yxw1mw0w1
                        LhLk0k1
                        HhLR2.
      * { prove w0 * y + x * w1 + - w0 * w1 <= hL (k0 + k1).
          apply SNoLtLe_or (hL (k0 + k1)) (w0 * y + x * w1 + - w0 * w1) LhLk0k1 Lw0yxw1mw0w1.
          - assume H1: hL (k0 + k1) < w0 * y + x * w1 + - w0 * w1. prove False.
            apply SNoLt_irref (x * y).
            prove x * y < x * y.
            apply SNoLt_tra (x * y) (hL (k0 + k1) + eps_ (k0 + k1)) (x * y)
                            Lxy (SNo_add_SNo (hL (k0 + k1)) (eps_ (k0 + k1)) LhLk0k1 Lek0k1) Lxy
                            (L6 (k0 + k1) Lk0k1).
            prove hL (k0 + k1) + eps_ (k0 + k1) < x * y.
            apply SNoLtLe_tra (hL (k0 + k1) + eps_ (k0 + k1))
                              ((w0 * y + x * w1 + - w0 * w1) + eps_ (k0 + k1))
                              (x * y)
                              (SNo_add_SNo (hL (k0 + k1)) (eps_ (k0 + k1)) LhLk0k1 Lek0k1)
                              (SNo_add_SNo (w0 * y + x * w1 + - w0 * w1) (eps_ (k0 + k1)) Lw0yxw1mw0w1 Lek0k1)
                              Lxy.
            + aby add_SNo_Lt1 H1 Lw0yxw1mw0w1 LhLk0k1 Lek0k1.
            + prove (w0 * y + x * w1 + - w0 * w1) + eps_ (k0 + k1) <= x * y.
              rewrite add_SNo_com (w0 * y + x * w1 + - w0 * w1) (eps_ (k0 + k1)) Lw0yxw1mw0w1 Lek0k1.
              apply add_SNo_minus_Le2 (x * y) (w0 * y + x * w1 + - w0 * w1) (eps_ (k0 + k1)) Lxy Lw0yxw1mw0w1 Lek0k1.
              prove eps_ (k0 + k1) <= x * y + - (w0 * y + x * w1 + - w0 * w1).
              rewrite add_SNo_com_3_0_1 (w0 * y) (x * w1) (- w0 * w1) Lw0y Lxw1 Lmw0w1.
              prove eps_ (k0 + k1) <= x * y + - (x * w1 + w0 * y + - w0 * w1).
              rewrite minus_add_SNo_distr_3 (x * w1) (w0 * y) (- w0 * w1) Lxw1 Lw0y Lmw0w1.
              prove eps_ (k0 + k1) <= x * y + - x * w1 + - w0 * y + - - w0 * w1.
              rewrite <- mul_SNo_minus_distrL w0 y Hw01 Hy1.
              rewrite <- mul_SNo_minus_distrL w0 w1 Hw01 Hw11.
              prove eps_ (k0 + k1) <= x * y + - x * w1 + (- w0) * y + - (- w0) * w1.
              rewrite <- mul_SNo_minus_distrR x w1 Hx1 Hw11.
              rewrite <- mul_SNo_minus_distrR (- w0) w1 (SNo_minus_SNo w0 Hw01) Hw11.
              prove eps_ (k0 + k1) <= x * y + x * (- w1) + (- w0) * y + (- w0) * (- w1).
              rewrite <- SNo_foil x (- w0) y (- w1) Hx1 (SNo_minus_SNo w0 Hw01) Hy1 (SNo_minus_SNo w1 Hw11).
              prove eps_ (k0 + k1) <= (x + - w0) * (y + - w1).
              rewrite <- mul_SNo_eps_eps_add_SNo k0 Hk0 k1 Hk1.
              prove eps_ k0 * eps_ k1 <= (x + - w0) * (y + - w1).
              apply nonneg_mul_SNo_Le2 (eps_ k0) (eps_ k1) (x + - w0) (y + - w1) Lek0 Lek1 (SNo_add_SNo x (- w0) Hx1 (SNo_minus_SNo w0 Hw01)) (SNo_add_SNo y (- w1) Hy1 (SNo_minus_SNo w1 Hw11)).
              * prove 0 <= eps_ k0. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hw0 Hw1 Hwe Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lw0y Lxw1 Lw0w1 Lmw0w1 Lw0yxw1mw0w1 H1.
              * prove 0 <= eps_ k1. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hw0 Hw1 Hwe Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lw0y Lxw1 Lw0w1 Lmw0w1 Lw0yxw1mw0w1 H1.
              * prove eps_ k0 <= x + - w0. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hw0 Hw1 Hwe Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lw0y Lxw1 Lw0w1 Lmw0w1 Lw0yxw1mw0w1 H1.
              * prove eps_ k1 <= y + - w1. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hw0 Hw1 Hwe Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lw0y Lxw1 Lw0w1 Lmw0w1 Lw0yxw1mw0w1 H1.
          - aby.
        }
      * aby Lk0k1 HhLR5.
    + let z0. assume Hz0: z0 :e SNoR x.
      let z1. assume Hz1: z1 :e SNoR y.
      assume Hwe: w = z0 * y + x * z1 + - z0 * z1.
      apply LRx2 z0 Hz0.
      let k0. assume Hk0: k0 :e omega.
      assume Hk0b: eps_ k0 <= z0 + - x.
      apply LRy2 z1 Hz1.
      let k1. assume Hk1: k1 :e omega.
      assume Hk1b: eps_ k1 <= z1 + - y.
      apply SNoR_E x Hx1 z0 Hz0.
      assume Hz01: SNo z0.
      assume Hz02: SNoLev z0 :e SNoLev x.
      assume Hz03: x < z0.
      apply SNoR_E y Hy1 z1 Hz1.
      assume Hz11: SNo z1.
      assume Hz12: SNoLev z1 :e SNoLev y.
      assume Hz13: y < z1.
      claim Lek0: SNo (eps_ k0).
      { aby SNo_eps_ Hk0. }
      claim Lek1: SNo (eps_ k1).
      { aby SNo_eps_ Hk1. }
      claim Lk0k1: k0 + k1 :e omega.
      { aby add_SNo_In_omega Hk1 Hk0. }
      claim Lek0k1: SNo (eps_ (k0 + k1)).
      { aby SNo_eps_ Lk0k1. }
      claim LhLk0k1: SNo (hL (k0 + k1)).
      { aby Lk0k1 LhL. }
      claim Lz0y: SNo (z0 * y).
      { aby SNo_mul_SNo Hz01 Hy1. }
      claim Lxz1: SNo (x * z1).
      { aby SNo_mul_SNo Hz11 Hx1. }
      claim Lz0z1: SNo (z0 * z1).
      { aby SNo_mul_SNo Hz11 Hz01. }
      claim Lmz0z1: SNo (- z0 * z1).
      { aby SNo_minus_SNo Lz0z1. }
      claim Lz0yxz1mz0z1: SNo (z0 * y + x * z1 + - z0 * z1).
      { aby SNo_add_SNo_3 Lmz0z1 Lxz1 Lz0y. }
      rewrite Hwe.
      apply SNoLeLt_tra (z0 * y + x * z1 + - z0 * z1)
                        (hL (k0 + k1))
                        (SNoCut {hL n|n :e omega} {hR n|n :e omega})
                        Lz0yxz1mz0z1
                        LhLk0k1
                        HhLR2.
      * { prove z0 * y + x * z1 + - z0 * z1 <= hL (k0 + k1).
          apply SNoLtLe_or (hL (k0 + k1)) (z0 * y + x * z1 + - z0 * z1) LhLk0k1 Lz0yxz1mz0z1.
          - assume H1: hL (k0 + k1) < z0 * y + x * z1 + - z0 * z1. prove False.
            apply SNoLt_irref (x * y).
            prove x * y < x * y.
            apply SNoLt_tra (x * y) (hL (k0 + k1) + eps_ (k0 + k1)) (x * y)
                            Lxy (SNo_add_SNo (hL (k0 + k1)) (eps_ (k0 + k1)) LhLk0k1 Lek0k1) Lxy
                            (L6 (k0 + k1) Lk0k1).
            prove hL (k0 + k1) + eps_ (k0 + k1) < x * y.
            apply SNoLtLe_tra (hL (k0 + k1) + eps_ (k0 + k1))
                              ((z0 * y + x * z1 + - z0 * z1) + eps_ (k0 + k1))
                              (x * y)
                              (SNo_add_SNo (hL (k0 + k1)) (eps_ (k0 + k1)) LhLk0k1 Lek0k1)
                              (SNo_add_SNo (z0 * y + x * z1 + - z0 * z1) (eps_ (k0 + k1)) Lz0yxz1mz0z1 Lek0k1)
                              Lxy.
            + aby add_SNo_Lt1 H1 Lz0yxz1mz0z1 LhLk0k1 Lek0k1.
            + prove (z0 * y + x * z1 + - z0 * z1) + eps_ (k0 + k1) <= x * y.
              rewrite add_SNo_com (z0 * y + x * z1 + - z0 * z1) (eps_ (k0 + k1)) Lz0yxz1mz0z1 Lek0k1.
              apply add_SNo_minus_Le2 (x * y) (z0 * y + x * z1 + - z0 * z1) (eps_ (k0 + k1)) Lxy Lz0yxz1mz0z1 Lek0k1.
              prove eps_ (k0 + k1) <= x * y + - (z0 * y + x * z1 + - z0 * z1).
              rewrite add_SNo_com (x * y) (- (z0 * y + x * z1 + - z0 * z1))
                                  Lxy (SNo_minus_SNo (z0 * y + x * z1 + - z0 * z1) Lz0yxz1mz0z1).
              rewrite add_SNo_rotate_3_1 (z0 * y) (x * z1) (- z0 * z1) Lz0y Lxz1 Lmz0z1.
              rewrite minus_add_SNo_distr_3 (- z0 * z1) (z0 * y) (x * z1) Lmz0z1 Lz0y Lxz1.
              rewrite minus_SNo_invol (z0 * z1) Lz0z1.
              prove eps_ (k0 + k1) <= (z0 * z1 + - z0 * y + - x * z1) + x * y.
              rewrite <- add_SNo_assoc_4 (z0 * z1) (- z0 * y) (- x * z1) (x * y)
                                         Lz0z1
                                         (SNo_minus_SNo (z0 * y) Lz0y)
                                         (SNo_minus_SNo (x * z1) Lxz1)
                                         Lxy.
              prove eps_ (k0 + k1) <= z0 * z1 + - z0 * y + - x * z1 + x * y.
              rewrite <- mul_SNo_minus_distrR z0 y Hz01 Hy1.
              rewrite <- mul_SNo_minus_distrL x z1 Hx1 Hz11.
              prove eps_ (k0 + k1) <= z0 * z1 + z0 * (- y) + (- x) * z1 + x * y.
              rewrite <- mul_SNo_minus_minus x y Hx1 Hy1.
              prove eps_ (k0 + k1) <= z0 * z1 + z0 * (- y) + (- x) * z1 + (- x) * (- y).
              rewrite <- SNo_foil z0 (- x) z1 (- y) Hz01 (SNo_minus_SNo x Hx1) Hz11 (SNo_minus_SNo y Hy1).
              prove eps_ (k0 + k1) <= (z0 + - x) * (z1 + - y).
              rewrite <- mul_SNo_eps_eps_add_SNo k0 Hk0 k1 Hk1.
              prove eps_ k0 * eps_ k1 <= (z0 + - x) * (z1 + - y).
              apply nonneg_mul_SNo_Le2 (eps_ k0) (eps_ k1) (z0 + - x) (z1 + - y) Lek0 Lek1 (SNo_add_SNo z0 (- x) Hz01 (SNo_minus_SNo x Hx1)) (SNo_add_SNo z1 (- y) Hz11 (SNo_minus_SNo y Hy1)).
              * prove 0 <= eps_ k0. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hz0 Hz1 Hwe Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lz0y Lxz1 Lz0z1 Lmz0z1 Lz0yxz1mz0z1 H1.
              * prove 0 <= eps_ k1. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hz0 Hz1 Hwe Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lz0y Lxz1 Lz0z1 Lmz0z1 Lz0yxz1mz0z1 H1.
              * prove eps_ k0 <= z0 + - x. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hz0 Hz1 Hwe Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lz0y Lxz1 Lz0z1 Lmz0z1 Lz0yxz1mz0z1 H1.
              * prove eps_ k1 <= z1 + - y. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hw Hz0 Hz1 Hwe Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 LhLk0k1 Lz0y Lxz1 Lz0z1 Lmz0z1 Lz0yxz1mz0z1 H1.
          - aby.
        }
      * aby Lk0k1 HhLR5.
  - let z. assume Hz: z :e R.
    prove SNoCut {hL n|n :e omega} {hR n|n :e omega} < z.
    apply HRE z Hz.
    + let w0. assume Hw0: w0 :e SNoL x.
      let z1. assume Hz1: z1 :e SNoR y.
      assume Hze: z = w0 * y + x * z1 + - w0 * z1.
      apply LLx2 w0 Hw0.
      let k0. assume Hk0: k0 :e omega.
      assume Hk0b: eps_ k0 <= x + - w0.
      apply LRy2 z1 Hz1.
      let k1. assume Hk1: k1 :e omega.
      assume Hk1b: eps_ k1 <= z1 + - y.
      apply SNoL_E x Hx1 w0 Hw0.
      assume Hw01: SNo w0.
      assume Hw02: SNoLev w0 :e SNoLev x.
      assume Hw03: w0 < x.
      apply SNoR_E y Hy1 z1 Hz1.
      assume Hz11: SNo z1.
      assume Hz12: SNoLev z1 :e SNoLev y.
      assume Hz13: y < z1.
      claim Lek0: SNo (eps_ k0).
      { aby SNo_eps_ Hk0. }
      claim Lek1: SNo (eps_ k1).
      { aby SNo_eps_ Hk1. }
      claim Lk0k1: k0 + k1 :e omega.
      { aby add_SNo_In_omega Hk1 Hk0. }
      claim Lek0k1: SNo (eps_ (k0 + k1)).
      { aby SNo_eps_ Lk0k1. }
      claim Lmek0k1: SNo (- eps_ (k0 + k1)).
      { aby SNo_minus_SNo Lek0k1. }
      claim LhRk0k1: SNo (hR (k0 + k1)).
      { aby Lk0k1 LhR. }
      claim Lw0y: SNo (w0 * y).
      { aby SNo_mul_SNo Hw01 Hy1. }
      claim Lxz1: SNo (x * z1).
      { aby SNo_mul_SNo Hz11 Hx1. }
      claim Lw0z1: SNo (w0 * z1).
      { aby SNo_mul_SNo Hz11 Hw01. }
      claim Lmw0z1: SNo (- w0 * z1).
      { aby SNo_minus_SNo Lw0z1. }
      claim Lw0yxz1mw0z1: SNo (w0 * y + x * z1 + - w0 * z1).
      { aby SNo_add_SNo_3 Lmw0z1 Lxz1 Lw0y. }
      rewrite Hze.
      apply SNoLtLe_tra (SNoCut {hL n|n :e omega} {hR n|n :e omega})
                        (hR (k0 + k1))
                        (w0 * y + x * z1 + - w0 * z1)
                        HhLR2
                        LhRk0k1
                        Lw0yxz1mw0z1.
      * aby Lk0k1 HhLR6.
      * { prove hR (k0 + k1) <= w0 * y + x * z1 + - w0 * z1.
          apply SNoLtLe_or (w0 * y + x * z1 + - w0 * z1) (hR (k0 + k1)) Lw0yxz1mw0z1 LhRk0k1.
          - assume H1: w0 * y + x * z1 + - w0 * z1 < hR (k0 + k1). prove False.
            apply SNoLt_irref (x * y).
            prove x * y < x * y.
            apply SNoLt_tra (x * y) (hR (k0 + k1) + - eps_ (k0 + k1)) (x * y)
                            Lxy (SNo_add_SNo (hR (k0 + k1)) (- eps_ (k0 + k1)) LhRk0k1 Lmek0k1) Lxy.
            + prove x * y < hR (k0 + k1) + - eps_ (k0 + k1).
              apply SNoLeLt_tra (x * y)
                                ((w0 * y + x * z1 + - w0 * z1) + - eps_ (k0 + k1))
                                (hR (k0 + k1) + - eps_ (k0 + k1))
                                Lxy
                                (SNo_add_SNo (w0 * y + x * z1 + - w0 * z1) (- eps_ (k0 + k1)) Lw0yxz1mw0z1 Lmek0k1)
                                (SNo_add_SNo (hR (k0 + k1)) (- eps_ (k0 + k1)) LhRk0k1 Lmek0k1).
              * { prove x * y <= (w0 * y + x * z1 + - w0 * z1) + - eps_ (k0 + k1).
                  apply add_SNo_minus_Le2b (w0 * y + x * z1 + - w0 * z1) (eps_ (k0 + k1)) (x * y)
                                           Lw0yxz1mw0z1 Lek0k1 Lxy.
                  prove x * y + eps_ (k0 + k1) <= w0 * y + x * z1 + - w0 * z1.
                  rewrite add_SNo_com (x * y) (eps_ (k0 + k1)) Lxy Lek0k1.
                  apply add_SNo_minus_Le2 (w0 * y + x * z1 + - w0 * z1) (x * y) (eps_ (k0 + k1)) Lw0yxz1mw0z1 Lxy Lek0k1.
                  prove eps_ (k0 + k1) <= (w0 * y + x * z1 + - w0 * z1) + - x * y.
                  rewrite add_SNo_rotate_3_1 (w0 * y) (x * z1) (- w0 * z1) Lw0y Lxz1 Lmw0z1.
                  prove eps_ (k0 + k1) <= (- w0 * z1 + w0 * y + x * z1) + - x * y.
                  rewrite <- add_SNo_assoc_4 (- w0 * z1) (w0 * y) (x * z1) (- x * y) Lmw0z1 Lw0y Lxz1 Lmxy.
                  prove eps_ (k0 + k1) <= - w0 * z1 + w0 * y + x * z1 + - x * y.
                  rewrite add_SNo_rotate_4_1 (- w0 * z1) (w0 * y) (x * z1) (- x * y) Lmw0z1 Lw0y Lxz1 Lmxy.
                  prove eps_ (k0 + k1) <= - x * y + - w0 * z1 + w0 * y + x * z1.
                  rewrite add_SNo_rotate_4_1 (- x * y) (- w0 * z1) (w0 * y) (x * z1) Lmxy Lmw0z1 Lw0y Lxz1.
                  prove eps_ (k0 + k1) <= x * z1 + - x * y + - w0 * z1 + w0 * y.
                  rewrite <- mul_SNo_minus_distrR x y Hx1 Hy1.
                  rewrite <- mul_SNo_minus_distrL w0 z1 Hw01 Hz11.
                  rewrite <- mul_SNo_minus_minus w0 y Hw01 Hy1.
                  prove eps_ (k0 + k1) <= x * z1 + x * (- y) + (- w0) * z1 + (- w0) * (- y).
                  rewrite <- SNo_foil x (- w0) z1 (- y) Hx1 (SNo_minus_SNo w0 Hw01) Hz11 (SNo_minus_SNo y Hy1).
                  rewrite <- mul_SNo_eps_eps_add_SNo k0 Hk0 k1 Hk1.
                  prove eps_ k0 * eps_ k1 <= (x + - w0) * (z1 + - y).
                  apply nonneg_mul_SNo_Le2 (eps_ k0) (eps_ k1) (x + - w0) (z1 + - y) Lek0 Lek1 (SNo_add_SNo x (- w0) Hx1 (SNo_minus_SNo w0 Hw01)) (SNo_add_SNo z1 (- y) Hz11 (SNo_minus_SNo y Hy1)).
                  - prove 0 <= eps_ k0. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hw0 Hz1 Hze Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lw0y Lxz1 Lw0z1 Lmw0z1 Lw0yxz1mw0z1 H1.
                  - prove 0 <= eps_ k1. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hw0 Hz1 Hze Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lw0y Lxz1 Lw0z1 Lmw0z1 Lw0yxz1mw0z1 H1.
                  - prove eps_ k0 <= x + - w0. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hw0 Hz1 Hze Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lw0y Lxz1 Lw0z1 Lmw0z1 Lw0yxz1mw0z1 H1.
                  - prove eps_ k1 <= z1 + - y. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hw0 Hz1 Hze Hk0 Hk0b Hk1 Hk1b Hw01 Hw02 Hw03 Hz11 Hz12 Hz13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lw0y Lxz1 Lw0z1 Lmw0z1 Lw0yxz1mw0z1 H1.
                }
              * aby add_SNo_Lt1 H1 Lw0yxz1mw0z1 LhRk0k1 Lmek0k1.
            + aby Lk0k1 L8.
          - aby.
        }
    + let z0. assume Hz0: z0 :e SNoR x.
      let w1. assume Hw1: w1 :e SNoL y.
      assume Hze: z = z0 * y + x * w1 + - z0 * w1.
      apply LRx2 z0 Hz0.
      let k0. assume Hk0: k0 :e omega.
      assume Hk0b: eps_ k0 <= z0 + - x.
      apply LLy2 w1 Hw1.
      let k1. assume Hk1: k1 :e omega.
      assume Hk1b: eps_ k1 <= y + - w1.
      apply SNoR_E x Hx1 z0 Hz0.
      assume Hz01: SNo z0.
      assume Hz02: SNoLev z0 :e SNoLev x.
      assume Hz03: x < z0.
      apply SNoL_E y Hy1 w1 Hw1.
      assume Hw11: SNo w1.
      assume Hw12: SNoLev w1 :e SNoLev y.
      assume Hw13: w1 < y.
      claim Lek0: SNo (eps_ k0).
      { aby SNo_eps_ Hk0. }
      claim Lek1: SNo (eps_ k1).
      { aby SNo_eps_ Hk1. }
      claim Lk0k1: k0 + k1 :e omega.
      { aby add_SNo_In_omega Hk1 Hk0. }
      claim Lek0k1: SNo (eps_ (k0 + k1)).
      { aby SNo_eps_ Lk0k1. }
      claim Lmek0k1: SNo (- eps_ (k0 + k1)).
      { aby SNo_minus_SNo Lek0k1. }
      claim LhRk0k1: SNo (hR (k0 + k1)).
      { aby Lk0k1 LhR. }
      claim Lz0y: SNo (z0 * y).
      { aby SNo_mul_SNo Hz01 Hy1. }
      claim Lxw1: SNo (x * w1).
      { aby SNo_mul_SNo Hw11 Hx1. }
      claim Lz0w1: SNo (z0 * w1).
      { aby SNo_mul_SNo Hw11 Hz01. }
      claim Lmz0w1: SNo (- z0 * w1).
      { aby SNo_minus_SNo Lz0w1. }
      claim Lz0yxw1mz0w1: SNo (z0 * y + x * w1 + - z0 * w1).
      { aby SNo_add_SNo_3 Lmz0w1 Lxw1 Lz0y. }
      rewrite Hze.
      apply SNoLtLe_tra (SNoCut {hL n|n :e omega} {hR n|n :e omega})
                        (hR (k0 + k1))
                        (z0 * y + x * w1 + - z0 * w1)
                        HhLR2
                        LhRk0k1
                        Lz0yxw1mz0w1.
      * aby Lk0k1 HhLR6.
      * { prove hR (k0 + k1) <= z0 * y + x * w1 + - z0 * w1.
          apply SNoLtLe_or (z0 * y + x * w1 + - z0 * w1) (hR (k0 + k1)) Lz0yxw1mz0w1 LhRk0k1.
          - assume H1: z0 * y + x * w1 + - z0 * w1 < hR (k0 + k1). prove False.
            apply SNoLt_irref (x * y).
            prove x * y < x * y.
            apply SNoLt_tra (x * y) (hR (k0 + k1) + - eps_ (k0 + k1)) (x * y)
                            Lxy (SNo_add_SNo (hR (k0 + k1)) (- eps_ (k0 + k1)) LhRk0k1 Lmek0k1) Lxy.
            + prove x * y < hR (k0 + k1) + - eps_ (k0 + k1).
              apply SNoLeLt_tra (x * y)
                                ((z0 * y + x * w1 + - z0 * w1) + - eps_ (k0 + k1))
                                (hR (k0 + k1) + - eps_ (k0 + k1))
                                Lxy
                                (SNo_add_SNo (z0 * y + x * w1 + - z0 * w1) (- eps_ (k0 + k1)) Lz0yxw1mz0w1 Lmek0k1)
                                (SNo_add_SNo (hR (k0 + k1)) (- eps_ (k0 + k1)) LhRk0k1 Lmek0k1).
              * { prove x * y <= (z0 * y + x * w1 + - z0 * w1) + - eps_ (k0 + k1).
                  apply add_SNo_minus_Le2b (z0 * y + x * w1 + - z0 * w1) (eps_ (k0 + k1)) (x * y)
                                           Lz0yxw1mz0w1 Lek0k1 Lxy.
                  prove x * y + eps_ (k0 + k1) <= z0 * y + x * w1 + - z0 * w1.
                  rewrite add_SNo_com (x * y) (eps_ (k0 + k1)) Lxy Lek0k1.
                  apply add_SNo_minus_Le2 (z0 * y + x * w1 + - z0 * w1) (x * y) (eps_ (k0 + k1)) Lz0yxw1mz0w1 Lxy Lek0k1.
                  prove eps_ (k0 + k1) <= (z0 * y + x * w1 + - z0 * w1) + - x * y.
                  rewrite <- add_SNo_assoc_4 (z0 * y) (x * w1) (- z0 * w1) (- x * y) Lz0y Lxw1 Lmz0w1 Lmxy.
                  prove eps_ (k0 + k1) <= z0 * y + x * w1 + - z0 * w1 + - x * y.
                  rewrite <- add_SNo_rotate_3_1 (- z0 * w1) (- x * y) (x * w1) Lmz0w1 Lmxy Lxw1.
                  prove eps_ (k0 + k1) <= z0 * y + - z0 * w1 + - x * y + x * w1.
                  rewrite <- mul_SNo_minus_distrR z0 w1 Hz01 Hw11.
                  rewrite <- mul_SNo_minus_distrL x y Hx1 Hy1.
                  rewrite <- mul_SNo_minus_minus x w1 Hx1 Hw11.
                  prove eps_ (k0 + k1) <= z0 * y + z0 * (- w1) + (- x) * y + (- x) * (- w1).
                  rewrite <- SNo_foil z0 (- x) y (- w1) Hz01 (SNo_minus_SNo x Hx1) Hy1 (SNo_minus_SNo w1 Hw11).
                  rewrite <- mul_SNo_eps_eps_add_SNo k0 Hk0 k1 Hk1.
                  prove eps_ k0 * eps_ k1 <= (z0 + - x) * (y + - w1).
                  apply nonneg_mul_SNo_Le2 (eps_ k0) (eps_ k1) (z0 + - x) (y + - w1) Lek0 Lek1 (SNo_add_SNo z0 (- x) Hz01 (SNo_minus_SNo x Hx1)) (SNo_add_SNo y (- w1) Hy1 (SNo_minus_SNo w1 Hw11)).
                  - prove 0 <= eps_ k0. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hz0 Hw1 Hze Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lz0y Lxw1 Lz0w1 Lmz0w1 Lz0yxw1mz0w1 H1.
                  - prove 0 <= eps_ k1. apply SNoLtLe. aby SNo_eps_pos Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hz0 Hw1 Hze Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lz0y Lxw1 Lz0w1 Lmz0w1 Lz0yxw1mz0w1 H1.
                  - prove eps_ k0 <= z0 + - x. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hz0 Hw1 Hze Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lz0y Lxw1 Lz0w1 Lmz0w1 Lz0yxw1mz0w1 H1.
                  - prove eps_ k1 <= y + - w1. aby Hx Hy Hx0 Hy0 HC Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hy1 Hy2 Hy3 Hy4 Hy5 Hy6 Hy7 Lx7 Ly7 Lxy Lmxy Lxy2 Lxy3 LLx LRx LLy LRy LLx2 LRx2 LLy2 LRy2 HLR HLE HLI1 HLI2 HRE HRI1 HRI2 HxyLR L1 LNex HN HN1 HN HN2 HN3 L2 HhL HhL1 HhL2 HhR HhR1 HhR2 LhL LhR L3 L4 L5 HhLR1 HhLR2 HhLR5 HhLR6 L6 L7 L8 L9 Hz Hz0 Hw1 Hze Hk0 Hk0b Hk1 Hk1b Hz01 Hz02 Hz03 Hw11 Hw12 Hw13 Lek0 Lek1 Lk0k1 Lek0k1 Lmek0k1 LhRk0k1 Lz0y Lxw1 Lz0w1 Lmz0w1 Lz0yxw1mz0w1 H1.
                }
              * aby add_SNo_Lt1 H1 Lz0yxw1mz0w1 LhRk0k1 Lmek0k1.
            + aby Lk0k1 L8.
          - aby.
        }
  - aby ReplE_impred L3 HxyLR.
  - aby ReplE_impred L4 HxyLR.
}
aby SNo_approx_real L10 L9 L7 L6 L4 L3 HhR1 HhL1 Lxy HC.
Qed.

Theorem real_mul_SNo : forall x y :e real, x * y :e real.
aby SNoLt_trichotomy_or_impred SNo_0 minus_SNo_invol minus_SNo_Lt_contra2 minus_SNo_0 SNo_mul_SNo mul_SNo_zeroR mul_SNo_minus_distrL mul_SNo_minus_distrR mul_SNo_zeroL mul_SNo_minus_minus mul_minus_SNo_distrR real_SNo real_0 real_minus_SNo real_mul_SNo_pos.
Qed.

Theorem nonneg_real_nat_interval: forall x :e real, 0 <= x -> exists n :e omega, n <= x /\ x < ordsucc n.
let x. assume HxR Hxnn.
apply real_E x HxR.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc omega.
assume Hx3: x :e SNoS_ (ordsucc omega).
assume Hx4: - omega < x.
assume Hx5: x < omega.
assume Hx6: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
assume Hx7: forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
claim L1: forall m, nat_p m -> x < m -> exists n :e omega, n <= x /\ x < ordsucc n.
{ aby nat_ind nat_p_omega SNoLt_irref SNoLeLt_tra SNoLtLe_or nat_p_SNo SNo_0 Hx1 Hxnn. }
aby set_ext Subq_ref Subq_tra ordsuccI1 ordsuccI2 nat_0 nat_ordsucc nat_1 nat_p_ordinal ordinal_In_Or_Subq omega_nat_p nat_p_omega omega_ordinal SNo_SNo SNoLev_ordinal SNoLtLe_tra SNoS_E SNoLev_uniq2 ordinal_SNoLev nat_p_SNo ordinal_SNoLev_max_2 SNo_1 eps_0_1 SNo_add_SNo add_SNo_Lev_bd add_SNo_1_ordsucc L1 Hx7 Hx1.
Qed.

Theorem pos_real_left_approx_double: forall x :e real, 0 < x
 -> x <> 2 -> (forall m :e omega, x <> eps_ m)
 -> exists w :e SNoL_pos x, x < 2 * w.
let x. assume HxR Hxpos Hxn2 Hxne.
apply real_E x HxR.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc omega.
assume Hx3: x :e SNoS_ (ordsucc omega).
assume Hx4: - omega < x.
assume Hx5: x < omega.
assume Hx6: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
assume Hx7: forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
claim L1: forall m, nat_p m -> eps_ m < x -> exists w :e SNoL_pos x, x < 2 * w.
{ apply nat_ind.
  - prove eps_ 0 < x -> exists w :e SNoL_pos x, x < 2 * w.
    rewrite eps_0_1.
    assume H1: 1 < x.
    apply SNoLt_trichotomy_or_impred x 2 Hx1 SNo_2.
    + aby SepI nat_0 nat_1 nat_p_ordinal ordinal_In_Or_Subq nat_p_omega SNoLev_ordinal SNoL_I ordinal_SNoLev SNo_1 SNo_2 pos_low_eq_one eps_0_1 SNoLt_0_1 mul_SNo_oneR H1 Hx1 Hxne Hxpos.
    + aby Hxn2.
    + assume H2: 2 < x.
      apply nonneg_real_nat_interval x HxR (SNoLtLe 0 x Hxpos).
      let m. assume H. apply H.
      assume Hm: m :e omega. assume H. apply H.
      assume Hmx: m <= x.
      assume Hxm1: x < ordsucc m.
      claim Lm: nat_p m.
      { aby omega_nat_p Hm. }
      apply nat_inv m Lm.
      * { aby SNoLt_irref SNoLt_tra SNo_1 Hxm1 H1 Hx1.
        }
      * { assume H. apply H.
          let m'. assume H. apply H.
          assume Hm': nat_p m'.
          assume Hmm': m = ordsucc m'.
          apply nat_inv m' Hm'.
          - aby SNoLt_irref SNoLt_tra SNo_2 Hmm' Hxm1 H2 Hx1.
          - assume H. apply H.
            let m''. assume H. apply H.
            assume Hm'': nat_p m''.
            assume Hm'm'': m' = ordsucc m''.
            claim L1a: exists k :e omega, 2 <= k /\ k < x /\ x <= ordsucc k.
            { aby Subq_Empty ordsuccI2 neq_ordsucc_0 ordsucc_inj nat_2 nat_inv ordinal_Empty nat_p_ordinal nat_p_omega SNoLtLe SNoLeE SNoLe_ref SNoLtLe_or nat_p_SNo ordinal_In_SNoLt ordinal_Subq_SNoLe ordinal_SNoLt_In SNo_0 SNo_1 SNo_2 add_SNo_Le2 add_SNo_0R add_SNo_1_1_2 add_SNo_assoc ordinal_ordsucc_SNo_eq Hm'm'' Hm'' Hmm' Hm' Lm Hxm1 Hmx Hm Hx1 Hxn2. }
            apply L1a.
            let k. assume H. apply H.
            assume Hk: k :e omega. assume H. apply H. assume H. apply H.
            assume H2k: 2 <= k.
            assume Hkx: k < x.
            assume HxSk: x <= ordsucc k.
            claim Lk: nat_p k.
            { aby omega_nat_p Hk. }
            claim LkS: SNo k.
            { aby nat_p_SNo Lk. }
            witness k.
            apply andI.
            + prove k :e SNoL_pos x.
              prove k :e {w :e SNoL x|0 < w}.
              apply SepI.
              * { prove k :e SNoL x.
                  apply SNoL_I.
                  - aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS.
                  - aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS.
                  - prove SNoLev k :e SNoLev x.
                    rewrite ordinal_SNoLev k (nat_p_ordinal k Lk).
                    prove k :e SNoLev x.
                    apply ordinal_trichotomy_or_impred k (SNoLev x) (nat_p_ordinal k Lk) (SNoLev_ordinal x Hx1).
                    + assume H4: k :e SNoLev x. aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS H4.
                    + assume H4: k = SNoLev x. prove False.
                      apply SNoLt_irref k.
                      apply SNoLtLe_tra k x k LkS Hx1 LkS Hkx.
                      prove x <= k.
                      apply ordinal_SNoLev_max_2 k (nat_p_ordinal k Lk) x Hx1.
                      rewrite <- H4. apply ordsuccI2.
                    + assume H4: SNoLev x :e k. prove False.
                      apply SNoLt_irref k.
                      apply SNoLt_tra k x k LkS Hx1 LkS Hkx.
                      prove x < k.
                      aby nat_p_ordinal ordinal_SNoLev_max HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS H4.
                  - prove k < x. aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS.
                }
              * prove 0 < k.
                apply SNoLtLe_tra 0 2 k SNo_0 SNo_2 LkS SNoLt_0_2.
                prove 2 <= k. aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS.
            + prove x < 2 * k.
              rewrite <- add_SNo_1_1_2.
              rewrite mul_SNo_distrR 1 1 k SNo_1 SNo_1 LkS.
              rewrite mul_SNo_oneL k LkS.
              prove x < k + k.
              apply SNoLeLt_tra x (ordsucc k) (k + k) Hx1 (nat_p_SNo (ordsucc k) (nat_ordsucc k Lk)) (SNo_add_SNo k k LkS LkS) HxSk.
              prove ordsucc k < k + k.
              rewrite ordinal_ordsucc_SNo_eq k (nat_p_ordinal k Lk).
              prove 1 + k < k + k.
              apply add_SNo_Lt1 1 k k SNo_1 LkS LkS.
              prove 1 < k.
              apply SNoLtLe_tra 1 2 k SNo_1 SNo_2 LkS SNoLt_1_2.
              prove 2 <= k. aby HxR Hxpos Hxn2 Hxne Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H1 H2 H Hm H Hmx Hxm1 Lm H H Hm' Hmm' H H Hm'' Hm'm'' L1a H Hk H H H2k Hkx HxSk Lk LkS.
        }
  - let m. assume Hm.
    assume IHm: eps_ m < x -> exists w :e SNoL_pos x, x < 2 * w.
    assume H1: eps_ (ordsucc m) < x.
    claim Lm: m :e omega.
    { aby nat_p_omega Hm. }
    claim Lem: SNo (eps_ m).
    { aby SNo_eps_ Lm. }
    apply SNoLt_trichotomy_or_impred x (eps_ m) Hx1 Lem.
    + assume H2: x < eps_ m.
      claim LSm: ordsucc m :e omega.
      { aby omega_ordsucc Lm. }
      claim LeSm: SNo (eps_ (ordsucc m)).
      { aby SNo_eps_ LSm. }
      witness (eps_ (ordsucc m)).
      apply andI.
      * { prove eps_ (ordsucc m) :e SNoL_pos x.
          prove eps_ (ordsucc m) :e {w :e SNoL x|0 < w}.
          apply SepI.
          - aby binintersectE1 In_irref In_no2cycle ordsuccE SNoLev_ordinal SNoLtE SNoLt_irref SNoLt_tra SNoL_I SNoLev_0_eq_0 eps_ordinal_In_eq_0 SNoLev_eps_ SNo_eps_pos LeSm LSm H2 Lem Lm H1 Hx1 Hxpos.
          - aby SNo_eps_pos LSm.
        }
      * aby SNo_1 add_SNo_1_1_2 mul_SNo_distrR mul_SNo_oneL eps_ordsucc_half_add LeSm H2 Hm.
    + aby nat_p_omega Hm Hxne.
    + aby IHm.
}
aby dneg nat_0 ordinal_Empty omega_nat_p nat_p_omega omega_ordinal SNoLt_irref SNoLt_trichotomy_or_impred SNoS_I ordinal_SNo_ SNo_eps_ SNo_minus_SNo add_SNo_0L pos_abs_SNo abs_SNo_minus L1 Hx6 Hx1 Hxne Hxpos.
Qed.

Theorem real_recip_SNo_lem1: forall x, SNo x -> x :e real -> 0 < x ->
    recip_SNo_pos x :e real
 /\ forall k, nat_p k ->
         (SNo_recipaux x recip_SNo_pos k 0 c= real)
      /\ (SNo_recipaux x recip_SNo_pos k 1 c= real).
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IHx: forall u :e SNoS_ (SNoLev x), u :e real -> 0 < u ->
    recip_SNo_pos u :e real
 /\ forall k, nat_p k ->
         (forall y :e SNo_recipaux u recip_SNo_pos k 0, y :e real)
      /\ (forall y :e SNo_recipaux u recip_SNo_pos k 1, y :e real).
assume HxR: x :e real.
assume Hxpos: 0 < x.
apply real_E x HxR.
assume _.
assume HxR2: SNoLev x :e ordsucc omega.
assume _ _ _ _ _.
claim Lmx: SNo (- x).
{ aby SNo_minus_SNo Hx. }
claim L1: forall y :e real, forall z :e SNoS_ (SNoLev x), 0 < z -> (1 + (z + - x) * y) * recip_SNo_pos z :e real.
{ aby ordsuccE nat_p_trans omega_nat_p nat_p_omega omega_ordinal SNoLev_ordinal SNoS_I SNoS_E2 SNoS_omega_real real_1 real_minus_SNo real_add_SNo real_mul_SNo HxR2 HxR IHx Hx. }
claim L2: forall k, nat_p k ->
    (SNo_recipaux x recip_SNo_pos k 0 c= real)
 /\ (SNo_recipaux x recip_SNo_pos k 1 c= real).
{ apply nat_ind.
  + aby EmptyE SingE tuple_2_0_eq tuple_2_1_eq SNo_recipaux_0 real_0.
  + let k. aby binunionE' SepE tuple_2_0_eq tuple_2_1_eq SNoLt_tra SNoS_I2 SNoL_E SNoR_E SNo_0 SNo_recipauxset_E SNo_recipaux_S L1 Hxpos Hx.
}
apply andI.
- prove recip_SNo_pos x :e real.
  claim L3: forall u :e SNoS_ (SNoLev x), 0 < u -> SNo (recip_SNo_pos u) /\ u * recip_SNo_pos u = 1.
  { aby SNoLev_ordinal SNoS_E2 recip_SNo_pos_prop1 Hx. }
  set L := (\/_ k :e omega, SNo_recipaux x recip_SNo_pos k 0).
  set R := (\/_ k :e omega, SNo_recipaux x recip_SNo_pos k 1).
  claim LrxLR: recip_SNo_pos x = SNoCut L R.
  { aby recip_SNo_pos_eq Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3. }
  claim LLR: SNoCutP L R.
  { aby SNo_recipaux_lem2 Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR. }
  apply SNoCutP_SNoCut_impred L R LLR.
  set y := SNoCut L R.
  assume HLR1: SNo y.
  assume HLR2: SNoLev y :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y))).
  assume HLR3: forall w :e L, w < y.
  assume HLR4: forall z :e R, y < z.
  assume HLR5: forall u, SNo u -> (forall w :e L, w < u) -> (forall z :e R, u < z) -> SNoLev y c= SNoLev u /\ SNoEq_ (SNoLev y) y u.
  claim LLI: forall k :e omega, SNo_recipaux x recip_SNo_pos k 0 c= L.
  { aby famunionI. }
  claim LRI: forall k :e omega, SNo_recipaux x recip_SNo_pos k 1 c= R.
  { aby famunionI. }
  claim LLE: forall w :e L, forall p:prop, (forall k :e omega, w :e SNo_recipaux x recip_SNo_pos k 0 -> p) -> p.
  { aby famunionE_impred. }
  claim LRE: forall z :e R, forall p:prop, (forall k :e omega, z :e SNo_recipaux x recip_SNo_pos k 1 -> p) -> p.
  { aby famunionE_impred. }
  claim LLreal: L c= real.
  { aby omega_nat_p LLE L2. }
  claim LRreal: R c= real.
  { aby omega_nat_p LRE L2. }
  claim LL0: L <> 0.
  { assume H1: L = 0.
    aby EmptyE SingI nat_0 nat_p_omega tuple_2_0_eq SNo_recipaux_0 H1 LLI.
  }
  apply xm (exists m :e omega, x = eps_ m).
  + assume H. aby nat_2 omega_nat_p nat_p_omega omega_SNoS_omega nat_exp_SNo_nat recip_SNo_pos_eps_ SNoS_omega_real H.
  + assume H1: ~(exists m :e omega, x = eps_ m).
    apply xm (x = 2).
    * aby nat_1 nat_p_omega SNo_eps_SNoS_omega recip_SNo_pos_2 SNoS_omega_real.
    * { assume H2: x <> 2.
        claim L4: forall m :e omega, x <> eps_ m.
        { aby H1. }
        apply pos_real_left_approx_double x HxR Hxpos H2 L4.
        let u. assume H. apply H.
        assume Hu: u :e SNoL_pos x.
        apply SepE (SNoL x) (fun w => 0 < w) u Hu.
        assume Hua: u :e SNoL x.
        assume Hub: 0 < u.
        apply SNoL_E x Hx u Hua.
        assume Hua1: SNo u.
        assume Hua2: SNoLev u :e SNoLev x.
        assume Hua3: u < x.
        assume H3: x < 2 * u.
        claim Lru: SNo (recip_SNo_pos u).
        { aby SNo_recip_SNo_pos Hua1 Hub. }
        claim Lumx: SNo (u + - x).
        { aby SNo_add_SNo Hua1 Lmx. }
        set f:set -> set := fun v => (1 + (u + - x) * v) * recip_SNo_pos u.
        claim L5: forall w :e L, f w :e R.
        { let w. assume Hw.
          apply LLE w Hw.
          let k. assume Hk: k :e omega.
          assume Hwk: w :e SNo_recipaux x recip_SNo_pos k 0.
          apply LRI (ordsucc k) (omega_ordsucc k Hk).
          aby binunionI1 binunionI2 omega_nat_p tuple_2_1_eq SNo_recipauxset_I SNo_recipaux_S Hwk Hk Hu.
        }
        claim L6: forall z :e R, f z :e L.
        { let z. assume Hz.
          apply LRE z Hz.
          let k. assume Hk: k :e omega.
          assume Hzk: z :e SNo_recipaux x recip_SNo_pos k 1.
          apply LLI (ordsucc k) (omega_ordsucc k Hk).
          aby binunionI2 omega_nat_p tuple_2_0_eq SNo_recipauxset_I SNo_recipaux_S Hzk Hk Hu.
        }
        claim Luu: SNo (u * u).
        { aby SNo_mul_SNo Hua1. }
        claim Luupos: 0 < u * u.
        { aby mul_SNo_pos_pos Hua1 Hub. }
        claim Luun0: u * u <> 0.
        { assume H. aby SNoLt_irref H Luupos. }
        claim L2u: SNo (2 * u).
        { aby SNo_2 SNo_mul_SNo Hua1. }
        claim Lf: forall v, SNo v -> forall p:prop, (SNo ((u + - x) * v) -> SNo (1 + ((u + - x) * v)) -> SNo (f v) -> p) -> p.
        { aby SNo_1 SNo_add_SNo SNo_mul_SNo Lumx Lru. }
        claim Luf: forall v, SNo v -> u * f v = 1 + (u + - x) * v.
        { aby mul_SNo_com mul_SNo_assoc mul_SNo_oneL recip_SNo_pos_invR Lf Lru Hua1 Hub. }
        claim L7: forall v, SNo v -> f (f v) = (v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x)) :/: (u * u).
        { let v. assume Hv.
          set v' := f v.
          apply Lf v Hv.
          assume Humxv: SNo ((u + - x) * v).
          assume H1umxv: SNo (1 + (u + - x) * v).
          assume Hv': SNo v'.
          apply Lf v' Hv'.
          assume Humxv': SNo ((u + - x) * v').
          assume H1umxv': SNo (1 + (u + - x) * v').
          assume Hfv': SNo (f v').
          claim Lxv: SNo (x * v).
          { aby SNo_mul_SNo Hv Hx. }
          claim Lxxv: SNo (x * x * v).
          { aby SNo_mul_SNo Lxv Hx. }
          claim L2uxv: SNo ((2 * u) * x * v).
          { aby SNo_mul_SNo Lxv L2u. }
          claim Lvuu: SNo (v * u * u).
          { aby SNo_mul_SNo Hv Luu. }
          claim Luxv: SNo (u * x * v).
          { aby SNo_mul_SNo Lxv Hua1. }
          claim Luv: SNo (u * v).
          { aby SNo_mul_SNo Hv Hua1. }
          claim Lxuv: SNo (x * u * v).
          { aby SNo_mul_SNo Luv Hx. }
          claim Lmuxv: SNo (- u * x * v).
          { aby SNo_minus_SNo Luxv. }
          claim Lmxuv: SNo (- x * u * v).
          { aby SNo_minus_SNo Lxuv. }
          claim Lmxmxuv: SNo (- x + - x * u * v).
          { aby SNo_add_SNo Lmxuv Lmx. }
          claim Lmxmxuvxxv: SNo (- x + - x * u * v + x * x * v).
          { aby SNo_add_SNo_3 Lmxuv Lxxv Lmx. }
          prove f v' = (v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x)) :/: (u * u).
          symmetry.
          apply mul_div_SNo_nonzero_eq (v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x)) (u * u) (f v')
                           (SNo_add_SNo_4 (v * u * u) (x * x * v) (2 * u) (- ((2 * u) * x * v + x))
                                          Lvuu Lxxv L2u (SNo_minus_SNo ((2 * u) * x * v + x) (SNo_add_SNo ((2 * u) * x * v) x L2uxv Hx)))
                           Luu
                           Hfv' Luun0.
          prove v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x) = (u * u) * f v'.
          transitivity u + u * (1 + (u + - x) * v) + - x * (1 + (u + - x) * v),
                       u + u * u * v' + - x * u * v',
                       u * (1 + (u + - x) * v'),
                       u * (u * f v').
          - prove v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x)
                = u + u * (1 + (u + - x) * v) + - x * (1 + (u + - x) * v).
            transitivity v * u * u + u + u + - u * x * v + (- x + - x * u * v + x * x * v),
                         u + (v * u * u + u + - u * x * v) + (- x + - x * u * v + x * x * v).
            + prove v * u * u + x * x * v + 2 * u + - ((2 * u) * x * v + x)
                  = v * u * u + u + u + - u * x * v + (- x + - x * u * v + x * x * v).
              f_equal.
              prove x * x * v + 2 * u + - ((2 * u) * x * v + x)
                  = u + u + - u * x * v + (- x + - x * u * v + x * x * v).
              rewrite add_SNo_com_3_0_1 (x * x * v) (2 * u) (- ((2 * u) * x * v + x))
                                        Lxxv L2u (SNo_minus_SNo ((2 * u) * x * v + x) (SNo_add_SNo ((2 * u) * x * v) x L2uxv Hx)).
              prove 2 * u + x * x * v + - ((2 * u) * x * v + x)
                  = u + u + - u * x * v + (- x + - x * u * v + x * x * v).
              rewrite <- add_SNo_1_1_2 at 1.
              rewrite mul_SNo_distrR 1 1 u SNo_1 SNo_1 Hua1.
              rewrite mul_SNo_oneL u Hua1.
              prove (u + u) + x * x * v + - ((2 * u) * x * v + x)
                  = u + u + - u * x * v + (- x + - x * u * v + x * x * v).
              transitivity u + u + x * x * v + - ((2 * u) * x * v + x).
              * { symmetry.
                  apply add_SNo_assoc u u (x * x * v + - ((2 * u) * x * v + x)) Hua1 Hua1.
                  prove SNo (x * x * v + - ((2 * u) * x * v + x)).
                  apply SNo_add_SNo.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - apply SNo_minus_SNo.
                    apply SNo_add_SNo.
                    + aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                    + aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
              * { f_equal. f_equal.
                  prove x * x * v + - ((2 * u) * x * v + x) = - u * x * v + (- x + - x * u * v + x * x * v).
                  transitivity x * x * v + - u * x * v + - x + - x * u * v.
                  - prove x * x * v + - ((2 * u) * x * v + x) = x * x * v + - u * x * v + - x + - x * u * v.
                    f_equal.
                    prove - ((2 * u) * x * v + x) = - u * x * v + - x + - x * u * v.
                    rewrite <- minus_add_SNo_distr_3 (u * x * v) x (x * u * v) Luxv Hx Lxuv.
                    prove - ((2 * u) * x * v + x) = - (u * x * v + x + x * u * v).
                    f_equal.
                    prove (2 * u) * x * v + x = u * x * v + x + x * u * v.
                    rewrite mul_SNo_com_3_0_1 x u v Hx Hua1 Hv.
                    prove (2 * u) * x * v + x = u * x * v + x + u * x * v.
                    rewrite add_SNo_com x (u * x * v) Hx Luxv.
                    rewrite add_SNo_assoc (u * x * v) (u * x * v) x Luxv Luxv Hx.
                    f_equal.
                    prove (2 * u) * x * v = u * x * v + u * x * v.
                    rewrite <- add_SNo_1_1_2 at 1.
                    rewrite mul_SNo_distrR 1 1 u SNo_1 SNo_1 Hua1.
                    rewrite mul_SNo_oneL u Hua1.
                    prove (u + u) * x * v = u * x * v + u * x * v.
                    aby mul_SNo_distrR Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - prove x * x * v + - u * x * v + - x + - x * u * v = - u * x * v + (- x + - x * u * v + x * x * v).
                    rewrite add_SNo_com_3_0_1 (x * x * v) (- u * x * v) (- x + - x * u * v)
                                              Lxxv Lmuxv Lmxmxuv.
                    f_equal.
                    prove x * x * v + - x + - x * u * v = - x + - x * u * v + x * x * v.
                    rewrite add_SNo_com_3_0_1 (x * x * v) (- x) (- x * u * v) Lxxv Lmx Lmxuv.
                    f_equal.
                    prove x * x * v + - x * u * v = - x * u * v + x * x * v.
                    aby add_SNo_com Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
            + prove v * u * u + u + u + - u * x * v + (- x + - x * u * v + x * x * v)
                  = u + (v * u * u + u + - u * x * v) + (- x + - x * u * v + x * x * v).
              rewrite add_SNo_com_3_0_1 (v * u * u) u (u + - u * x * v + (- x + - x * u * v + x * x * v)) Lvuu Hua1.
              * { prove u + v * u * u + u + - u * x * v + (- x + - x * u * v + x * x * v)
                      = u + (v * u * u + u + - u * x * v) + (- x + - x * u * v + x * x * v).
                  f_equal.
                  prove v * u * u + u + - u * x * v + (- x + - x * u * v + x * x * v)
                      = (v * u * u + u + - u * x * v) + (- x + - x * u * v + x * x * v).
                  apply add_SNo_assoc_4.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
              * { apply SNo_add_SNo_3.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
            + prove u + (v * u * u + u + - u * x * v) + (- x + - x * u * v + x * x * v)
                  = u + u * (1 + (u + - x) * v) + - x * (1 + (u + - x) * v).
              f_equal. f_equal.
              * { prove v * u * u + u + - u * x * v = u * (1 + (u + - x) * v).
                  rewrite mul_SNo_distrL u 1 ((u + - x) * v) Hua1 SNo_1 Humxv.
                  prove v * u * u + u + - u * x * v = u * 1 + u * (u + - x) * v.
                  rewrite mul_SNo_oneR u Hua1.
                  prove v * u * u + u + - u * x * v = u + u * (u + - x) * v.
                  rewrite add_SNo_com_3_0_1 (v * u * u) u (- u * x * v) Lvuu Hua1 (SNo_minus_SNo (u * x * v) Luxv).
                  prove u + v * u * u + - u * x * v = u + u * (u + - x) * v.
                  f_equal.
                  prove v * u * u + - u * x * v = u * (u + - x) * v.
                  rewrite mul_SNo_distrR u (- x) v Hua1 Lmx Hv.
                  prove v * u * u + - u * x * v = u * (u * v + (- x) * v).
                  rewrite mul_SNo_distrL u (u * v) ((- x) * v) Hua1 Luv (SNo_mul_SNo (- x) v Lmx Hv).
                  prove v * u * u + - u * x * v = u * u * v + u * (- x) * v.
                  f_equal.
                  - prove v * u * u = u * u * v.
                    rewrite mul_SNo_com u v Hua1 Hv.
                    aby mul_SNo_com_3_0_1 Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                  - prove - u * x * v = u * (- x) * v.
                    rewrite mul_SNo_minus_distrL x v Hx Hv.
                    aby mul_SNo_minus_distrR mul_minus_SNo_distrR Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
              * { prove - x + - x * u * v + x * x * v = - x * (1 + (u + - x) * v).
                  rewrite <- mul_SNo_minus_distrL x (1 + (u + - x) * v) Hx H1umxv.
                  prove - x + - x * u * v + x * x * v = (- x) * (1 + (u + - x) * v).
                  apply mul_SNo_distrL (- x) 1 ((u + - x) * v) Lmx SNo_1 Humxv (fun w z => - x + - x * u * v + x * x * v = z).
                  prove - x + - x * u * v + x * x * v = (- x) * 1 + (- x) * (u + - x) * v.
                  rewrite mul_SNo_oneR (- x) Lmx.
                  prove - x + - x * u * v + x * x * v = - x + (- x) * (u + - x) * v.
                  f_equal.
                  prove - x * u * v + x * x * v = (- x) * (u + - x) * v.
                  rewrite mul_SNo_distrR u (- x) v Hua1 Lmx Hv.
                  rewrite mul_SNo_distrL (- x) (u * v) ((- x) * v) Lmx Luv (SNo_mul_SNo (- x) v Lmx Hv).
                  prove - x * u * v + x * x * v = (- x) * u * v + (- x) * (- x) * v.
                  rewrite mul_SNo_minus_distrL x (u * v) Hx Luv.
                  prove - x * u * v + x * x * v = - x * u * v + (- x) * (- x) * v.
                  f_equal.
                  prove x * x * v = (- x) * (- x) * v.
                  rewrite mul_SNo_assoc (- x) (- x) v Lmx Lmx Hv.
                  rewrite mul_SNo_minus_minus x x Hx Hx.
                  aby mul_SNo_assoc Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
                }
          - aby Hv Luf.
          - aby SNo_1 SNo_mul_SNo mul_SNo_oneR mul_SNo_minus_distrL mul_SNo_distrR mul_SNo_distrL mul_SNo_com_3_0_1 Humxv' Hv' Hua1 Lmx Hx.
          - aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
          - aby mul_SNo_assoc Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf Hv Humxv H1umxv Hv' Humxv' H1umxv' Hfv' Lxv Lxxv L2uxv Lvuu Luxv Luv Lxuv Lmuxv Lmxuv Lmxmxuv Lmxmxuvxxv.
        }
        claim L8: forall w :e L, exists w' :e L, w < w'.
        { let w. assume Hw.
          claim Lw: SNo w.
          { aby real_SNo Hw LLreal. }
          claim Lxw: SNo (x * w).
          { aby SNo_mul_SNo Lw Hx. }
          claim Lxxw: SNo (x * x * w).
          { aby SNo_mul_SNo Lxw Hx. }
          claim L2uxw: SNo ((2 * u) * x * w).
          { aby SNo_mul_SNo Lxw L2u. }
          claim Lwuu: SNo (w * u * u).
          { aby SNo_mul_SNo Lw Luu. }
          witness f (f w). apply andI.
          - aby Hw L6 L5.
          - prove w < f (f w).
            claim L8a: w < (w * u * u + x * x * w + 2 * u + - ((2 * u) * x * w + x)) :/: (u * u).
            { aby SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo SNo_add_SNo_3 SNo_add_SNo_4 add_SNo_Lt2 add_SNo_com add_SNo_0L add_SNo_0R add_SNo_minus_Lt2b3 SNo_mul_SNo mul_SNo_Lt mul_SNo_oneR mul_SNo_com mul_SNo_oneL recip_SNo_poscase SNo_recip_SNo div_SNo_pos_LtR div_SNo_pos_LtR' Lwuu L2uxw Lxxw Lxw Lw Hw L2u Luupos Luu H3 HLR3 LrxLR Hxpos Hx. }
            aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf L7 Hw Lw Lxw Lxxw L2uxw Lwuu L8a.
        }
        claim L9: forall z :e R, exists z' :e R, z' < z.
        { let z. assume Hz.
          claim Lz: SNo z.
          { aby real_SNo Hz LRreal. }
          claim Lxz: SNo (x * z).
          { aby SNo_mul_SNo Lz Hx. }
          claim Lxxz: SNo (x * x * z).
          { aby SNo_mul_SNo Lxz Hx. }
          claim L2uxz: SNo ((2 * u) * x * z).
          { aby SNo_mul_SNo Lxz L2u. }
          claim Lzuu: SNo (z * u * u).
          { aby SNo_mul_SNo Lz Luu. }
          witness f (f z). apply andI.
          - aby Hz L6 L5.
          - prove f (f z) < z.
            claim L9a: (z * u * u + x * x * z + 2 * u + - ((2 * u) * x * z + x)) :/: (u * u) < z.
            { aby SNo_0 SNo_1 SNo_minus_SNo SNo_add_SNo SNo_add_SNo_3 SNo_add_SNo_4 add_SNo_Lt2 add_SNo_0L add_SNo_0R add_SNo_minus_Lt1b3 SNo_mul_SNo mul_SNo_Lt mul_SNo_oneR mul_SNo_com mul_SNo_oneL recip_SNo_poscase SNo_recip_SNo div_SNo_pos_LtL div_SNo_pos_LtL' Lzuu L2uxz Lxxz Lxz Lz Hz L2u Luupos Luu H3 HLR4 LrxLR Hxpos Hx. }
            aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2 L3 LrxLR LLR HLR1 HLR2 HLR3 HLR4 HLR5 LLI LRI LLE LRE LLreal LRreal LL0 H1 H2 L4 H Hu Hua Hub Hua1 Hua2 Hua3 H3 Lru Lumx L5 L6 Luu Luupos Luun0 L2u Lf Luf L7 L8 Hz Lz Lxz Lxxz L2uxz Lzuu L9a.
        }
        aby EmptyE SingI nat_0 nat_p_omega tuple_2_0_eq SNo_recipaux_0 recip_SNo_pos_eq real_SNoCut L9 L8 L5 LL0 LRreal LLreal LLI LLR Hx.
      }
- aby Hx IHx HxR Hxpos HxR2 Lmx L1 L2.
Qed.

Theorem real_recip_SNo_pos: forall x :e real, 0 < x -> recip_SNo_pos x :e real.
aby real_SNo real_recip_SNo_lem1.
Qed.

Theorem real_recip_SNo: forall x :e real, recip_SNo x :e real.
aby SNoLt_trichotomy_or_impred SNo_0 minus_SNo_Lt_contra2 minus_SNo_0 recip_SNo_poscase recip_SNo_negcase recip_SNo_0 real_SNo real_0 real_minus_SNo real_recip_SNo_pos.
Qed.

Theorem real_div_SNo: forall x y :e real, x :/: y :e real.
aby real_mul_SNo real_recip_SNo.
Qed.

End Reals.

Opaque real.

Section even_odd.

Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Theorem nat_le2_cases: forall m, nat_p m -> m c= 2 -> m = 0 \/ m = 1 \/ m = 2.
apply nat_inv_impred.
- assume _. aby.
- aby In_irref nat_ordsucc nat_0_in_ordsucc nat_ordsucc_in_ordsucc nat_inv_impred.
Qed.

Theorem prime_nat_2_lem: forall m, nat_p m -> forall n, nat_p n -> m * n = 2 -> m = 1 \/ m = 2.
aby neq_2_0 mul_nat_0R mul_nat_0L mul_nat_0_or_Subq nat_le2_cases.
Qed.

Theorem prime_nat_2: prime_nat 2.
aby and3I In_1_2 nat_2 omega_nat_p nat_p_omega prime_nat_2_lem.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Theorem not_eq_2m_2n1: forall m n :e int, 2 * m <> 2 * n + 1.
let m. assume Hm: m :e int.
let n. assume Hn: n :e int.
assume H1: 2 * m = 2 * n + 1.
apply prime_not_divides_int_1 2 prime_nat_2.
prove divides_int 2 1.
claim LmS: SNo m.
{ aby int_SNo Hm Hn H1. }
claim LnS: SNo n.
{ aby int_SNo Hm Hn H1 LmS. }
claim L2nS: SNo (2 * n).
{ aby SNo_2 SNo_mul_SNo Hm Hn H1 LmS LnS. }
aby nat_2 nat_p_omega SNo_1 SNo_2 SNo_minus_SNo SNo_add_SNo add_SNo_minus_L2 add_SNo_cancel_L add_SNo_rotate_3_1 SNo_mul_SNo mul_SNo_minus_distrR mul_SNo_distrL mul_minus_SNo_distrR Subq_omega_int int_add_SNo int_minus_SNo divides_int_ref divides_int_mul_SNo_L L2nS LnS LmS H1 Hn Hm.
Qed.

End even_odd.

Section form100_22b.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Theorem atleastp_SNoS_ordsucc_omega_Power_omega: atleastp (SNoS_ (ordsucc omega)) (Power omega).
set f:set->set := fun u => {2 * n|n :e omega, n :e u} :\/: {2 * n + 1|n :e omega, n ' :e u}.
claim L1: forall u v, SNoLev u c= omega -> u c= SNoElts_ (SNoLev u) -> f u = f v -> u c= v.
{ let u v.
  assume HLuo: SNoLev u c= omega.
  assume HuELu: u c= SNoElts_ (SNoLev u).
  assume Huv: f u = f v.
  let x. assume Hx: x :e u.
  prove x :e v.
  apply binunionE (SNoLev u) {n '|n :e SNoLev u} x (HuELu x Hx).
  - assume H1: x :e SNoLev u.
    claim Lx: x :e omega.
    { aby HLuo HuELu Huv Hx H1. }
    claim L2x: 2 * x :e f v.
    { aby binunionI1 ReplSepI Lx Hx Huv. }
    aby binunionE ReplSepE_impred nat_2 neq_2_0 nat_p_ordinal omega_nat_p nat_p_omega omega_SNo SNo_2 mul_SNo_In_omega mul_SNo_nonzero_cancel Subq_omega_int mul_SNo_nonzero_cancel_L not_eq_2m_2n1 L2x Lx.
  - assume H1: x :e {n '|n :e SNoLev u}.
    apply ReplE_impred (SNoLev u) (fun n => n ') x H1.
    let n.
    assume Hn: n :e SNoLev u.
    assume Hxn: x = n '.
    claim Lnomega: n :e omega.
    { aby HLuo HuELu Huv Hx H1 Hn Hxn. }
    claim L2nomega: 2 * n :e omega.
    { aby nat_2 nat_p_omega mul_SNo_In_omega Lnomega. }
    claim L2no: ordinal (2 * n).
    { aby nat_p_ordinal omega_nat_p L2nomega. }
    claim Ln'u: n ' :e u.
    { aby Hxn Hx. }
    claim L2x1: 2 * n + 1 :e f v.
    { aby binunionI2 ReplSepI Ln'u Lnomega Huv. }
    aby binunionE ReplSepE_impred neq_2_0 omega_SNo SNo_1 SNo_2 add_SNo_cancel_R SNo_mul_SNo mul_SNo_nonzero_cancel Subq_omega_int mul_SNo_nonzero_cancel_L not_eq_2m_2n1 L2x1 L2nomega Lnomega Hxn.
}
prove exists f:set->set, inj (SNoS_ (ordsucc omega)) (Power omega) f.
witness f.
prove (forall u :e SNoS_ (ordsucc omega), f u :e Power omega)
   /\ (forall u v :e SNoS_ (ordsucc omega), f u = f v -> u = v).
apply andI.
- let u. assume Hu: u :e SNoS_ (ordsucc omega).
  prove f u :e Power omega.
  apply PowerI.
  prove {2 * n|n :e omega, n :e u} :\/: {2 * n + 1|n :e omega, n ' :e u} c= omega.
  apply binunion_Subq_min.
  + aby ReplSepE_impred nat_2 nat_p_omega mul_SNo_In_omega.
  + aby ReplSepE_impred nat_1 nat_2 nat_p_omega add_SNo_In_omega mul_SNo_In_omega.
- aby set_ext TransSet_In_ordsucc_Subq omega_TransSet ordsucc_omega_ordinal SNoS_E2 L1.
Qed.

Theorem Repl_finite: forall f:set -> set, forall X, finite X -> finite {f x|x :e X}.
let f. apply finite_ind.
- aby Repl_Empty finite_Empty.
- let X y.
  assume HX: finite X.
  assume Hy: y /:e X.
  assume IH: finite {f x|x :e X}.
  prove finite {f x|x :e X :\/: {y}}.
  claim L1: {f x|x :e X :\/: {y}} = {f x|x :e X} :\/: {f y}.
  { apply set_ext.
    - aby ReplI ReplE_impred SingI SingE binunionI1 binunionI2 binunionE.
    - aby ReplI ReplE_impred SingI SingE binunionI1 binunionI2 binunionE.
  }
  aby Sing_finite binunion_finite L1 IH.
Qed.

Theorem infinite_bigger: forall X c= omega, infinite X -> forall m :e omega, exists n :e X, m :e n.
aby dneg ordsuccI1 ordsuccI2 nat_ordsucc nat_p_ordinal ordinal_trichotomy_or_impred omega_nat_p nat_finite Subq_finite.
Qed.

Theorem equip_real_Power_omega: equip real (Power omega).
apply atleastp_antisym_equip.
- aby atleastp_tra Subq_atleastp ordsucc_omega_ordinal SNoLev_ SNoS_I real_E atleastp_SNoS_ordsucc_omega_Power_omega.
- prove atleastp (Power omega) real.
  set L_ : set -> set -> set := fun X n => nat_primrec {0} (fun n r => if n :e X then r :\/: {x + eps_ (ordsucc n)|x :e r} else r) n.
  set R_ : set -> set -> set := fun X n => nat_primrec {1} (fun n r => if n :e X then r else r :\/: {x + - eps_ (ordsucc n)|x :e r}) n.
  claim L_0: forall X, L_ X 0 = {0}.
  { aby nat_primrec_0. }
  claim R_0: forall X, R_ X 0 = {1}.
  { aby nat_primrec_0. }
  claim L_ordsucc: forall X, forall n :e omega, L_ X (ordsucc n) = if n :e X then L_ X n :\/: {x + eps_ (ordsucc n)|x :e L_ X n} else L_ X n.
  { aby nat_primrec_S omega_nat_p. }
  claim R_ordsucc: forall X, forall n :e omega, R_ X (ordsucc n) = if n :e X then R_ X n else R_ X n :\/: {x + - eps_ (ordsucc n)|x :e R_ X n}.
  { aby nat_primrec_S omega_nat_p. }
  claim L_ordsucc_pos: forall X, forall n :e omega, n :e X -> L_ X (ordsucc n) = L_ X n :\/: {x + eps_ (ordsucc n)|x :e L_ X n}.
  { aby If_i_1 L_ordsucc. }
  claim L_ordsucc_neg: forall X, forall n :e omega, n /:e X -> L_ X (ordsucc n) = L_ X n.
  { aby If_i_0 L_ordsucc. }
  claim R_ordsucc_pos: forall X, forall n :e omega, n :e X -> R_ X (ordsucc n) = R_ X n.
  { aby If_i_1 R_ordsucc. }
  claim R_ordsucc_neg: forall X, forall n :e omega, n /:e X -> R_ X (ordsucc n) = R_ X n :\/: {x + - eps_ (ordsucc n)|x :e R_ X n}.
  { aby If_i_0 R_ordsucc. }
  claim L_SNo1: forall X, forall n, nat_p n -> forall u :e L_ X n, SNo u.
  { let X. apply nat_ind.
    - aby SingE SNo_0 L_0.
    - aby xm ReplE_impred binunionE nat_p_omega omega_ordsucc SNo_eps_ SNo_add_SNo L_ordsucc_neg L_ordsucc_pos.
  }
  claim R_SNo1: forall X, forall n, nat_p n -> forall u :e R_ X n, SNo u.
  { let X. apply nat_ind.
    - aby SingE SNo_1 R_0.
    - aby xm ReplE_impred binunionE nat_p_omega omega_ordsucc SNo_eps_ SNo_minus_SNo SNo_add_SNo R_ordsucc_neg R_ordsucc_pos.
  }
  claim L_fin: forall X, forall n, nat_p n -> finite (L_ X n).
  { let X. apply nat_ind.
    - aby Sing_finite L_0.
    - aby xm nat_p_omega binunion_finite Repl_finite L_ordsucc_neg L_ordsucc_pos.
  }
  claim R_fin: forall X, forall n, nat_p n -> finite (R_ X n).
  { let X. apply nat_ind.
    - aby Sing_finite R_0.
    - aby xm nat_p_omega binunion_finite Repl_finite R_ordsucc_neg R_ordsucc_pos.
  }
  claim L_ordsucc_Subq: forall X, forall n, nat_p n -> L_ X n c= L_ X (ordsucc n).
  { aby xm Subq_ref binunion_Subq_1 nat_p_omega L_ordsucc_neg L_ordsucc_pos. }
  claim R_ordsucc_Subq: forall X, forall n, nat_p n -> R_ X n c= R_ X (ordsucc n).
  { aby xm Subq_ref binunion_Subq_1 nat_p_omega R_ordsucc_neg R_ordsucc_pos. }
  claim L_Subq: forall X, forall n, nat_p n -> forall m :e n, L_ X m c= L_ X n.
  { let X.
    apply nat_ind.
    - aby EmptyE.
    - aby Subq_tra ordsuccE L_ordsucc_Subq.
  }
  claim R_Subq: forall X, forall n, nat_p n -> forall m :e n, R_ X m c= R_ X n.
  { let X.
    apply nat_ind.
    - aby EmptyE.
    - aby Subq_tra ordsuccE R_ordsucc_Subq.
  }
  claim L_0_In: forall X, forall n, nat_p n -> 0 :e L_ X n.
  { aby SingI nat_ordsucc nat_0_in_ordsucc nat_inv_impred L_Subq L_0. }
  claim R_1_In: forall X, forall n, nat_p n -> 1 :e R_ X n.
  { aby SingI nat_ordsucc nat_0_in_ordsucc nat_inv_impred R_Subq R_0. }
  claim L_ne: forall X, forall n, nat_p n -> L_ X n <> 0.
  { aby EmptyE L_0_In. }
  claim R_ne: forall X, forall n, nat_p n -> R_ X n <> 0.
  { aby EmptyE R_1_In. }
  claim L_R_dist: forall X, forall n, nat_p n -> forall w z, SNo_max_of (L_ X n) w -> SNo_min_of (R_ X n) z -> z = w + eps_ n.
  { let X. apply nat_ind.
    - aby SingE SNo_1 eps_0_1 add_SNo_0L R_0 L_0.
    - let n. assume Hn.
      assume IHn: forall w z, SNo_max_of (L_ X n) w -> SNo_min_of (R_ X n) z -> z = w + eps_ n.
      claim LSn: ordsucc n :e omega.
      { aby nat_p_omega omega_ordsucc Hn. }
      claim Len: SNo (eps_ n).
      { aby nat_p_omega SNo_eps_ Hn. }
      claim LeSn: SNo (eps_ (ordsucc n)).
      { aby SNo_eps_ LSn. }
      claim LmeSn: SNo (- eps_ (ordsucc n)).
      { aby SNo_minus_SNo LeSn. }
      let w z.
      apply xm (n :e X).
      + assume H1: n :e X.
        apply L_ordsucc_pos X n (nat_p_omega n Hn) H1
                  (fun _ v => SNo_max_of v w -> SNo_min_of (R_ X (ordsucc n)) z -> z = w + eps_ (ordsucc n)).
        assume Hw: SNo_max_of (L_ X n :\/: {w + eps_ (ordsucc n)|w :e L_ X n}) w.
        apply R_ordsucc_pos X n (nat_p_omega n Hn) H1
                  (fun _ v => SNo_min_of v z -> z = w + eps_ (ordsucc n)).
        assume Hz: SNo_min_of (R_ X n) z.
        apply finite_max_exists (L_ X n) (L_SNo1 X n Hn) (L_fin X n Hn) (L_ne X n Hn).
        let w'.
        assume Hw': SNo_max_of (L_ X n) w'.
        apply Hw'. assume H. apply H.
        assume Hw'1: w' :e L_ X n.
        assume Hw'2: SNo w'.
        assume Hw'3: forall y :e L_ X n, SNo y -> y <= w'.
        claim Lww': w = w' + eps_ (ordsucc n).
        { apply Hw. assume H. apply H.
          assume Hw1: w :e L_ X n :\/: {w + eps_ (ordsucc n)|w :e L_ X n}.
          assume Hw2: SNo w.
          assume Hw3: forall y :e L_ X n :\/: {w + eps_ (ordsucc n)|w :e L_ X n}, SNo y -> y <= w.
          apply binunionE (L_ X n) {w + eps_ (ordsucc n)|w :e L_ X n} w Hw1.
          - aby ReplI binunionI2 SNoLt_irref SNoLtLe_tra SNo_add_SNo add_SNo_eps_Lt Hw3 Hw2 LeSn LSn.
          - aby ReplI ReplE_impred binunionI2 SNoLe_antisym SNo_add_SNo add_SNo_Le1 Hw3 Hw2 Hw'3 Hw'2 Hw'1 LeSn Hn L_SNo1.
        }
        aby add_SNo_assoc eps_ordsucc_half_add Lww' Hw'2 Hw' Hz LeSn IHn Hn.
      + assume H1: n /:e X.
        apply L_ordsucc_neg X n (nat_p_omega n Hn) H1
                  (fun _ v => SNo_max_of v w -> SNo_min_of (R_ X (ordsucc n)) z -> z = w + eps_ (ordsucc n)).
        assume Hw: SNo_max_of (L_ X n) w.
        apply R_ordsucc_neg X n (nat_p_omega n Hn) H1
                  (fun _ v => SNo_min_of v z -> z = w + eps_ (ordsucc n)).
        assume Hz: SNo_min_of (R_ X n :\/: {w + - eps_ (ordsucc n)|w :e R_ X n}) z.
        apply finite_min_exists (R_ X n) (R_SNo1 X n Hn) (R_fin X n Hn) (R_ne X n Hn).
        let z'.
        assume Hz': SNo_min_of (R_ X n) z'.
        apply Hz'. assume H. apply H.
        assume Hz'1: z' :e R_ X n.
        assume Hz'2: SNo z'.
        assume Hz'3: forall y :e R_ X n, SNo y -> z' <= y.
        claim Lzz': z = z' + - eps_ (ordsucc n).
        { apply Hz. assume H. apply H.
          assume Hz1: z :e R_ X n :\/: {z + - eps_ (ordsucc n)|z :e R_ X n}.
          assume Hz2: SNo z.
          assume Hz3: forall y :e R_ X n :\/: {z + - eps_ (ordsucc n)|z :e R_ X n}, SNo y -> z <= y.
          apply binunionE (R_ X n) {z + - eps_ (ordsucc n)|z :e R_ X n} z Hz1.
          - aby ReplI binunionI2 nat_p_omega omega_ordsucc SNoLt_irref SNoLeLt_tra SNo_0 SNo_eps_pos minus_SNo_Lt_contra SNo_add_SNo add_SNo_Lt2 add_SNo_0R minus_SNo_0 Hz3 Hz2 LmeSn LeSn Hn.
          - aby ReplI ReplE_impred binunionI2 SNoLe_antisym SNo_add_SNo add_SNo_Le1 Hz3 Hz2 Hz'3 Hz'2 Hz'1 LmeSn Hn R_SNo1.
        }
        aby add_SNo_assoc add_SNo_minus_R2 eps_ordsucc_half_add Lzz' Hz' Hw LmeSn LeSn Len IHn Hn.
  }
  claim L_SNo: forall X, forall n, nat_p n -> L_ X n c= SNoS_ omega.
  { let X. apply nat_ind.
    - aby SingE nat_0 ordinal_Empty nat_p_omega omega_ordinal SNoS_I ordinal_SNo_ L_0.
    - let n. assume Hn.
      assume IHn: L_ X n c= SNoS_ omega.
      prove L_ X (ordsucc n) c= SNoS_ omega.
      apply xm (n :e X).
      + assume H1: n :e X.
        apply L_ordsucc_pos X n (nat_p_omega n Hn) H1
                  (fun _ v => v c= SNoS_ omega).
        prove L_ X n :\/: {w + eps_ (ordsucc n)|w :e L_ X n} c= SNoS_ omega.
        apply binunion_Subq_min.
        * aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist Hn IHn H1.
        * aby ReplE_impred nat_p_omega omega_ordsucc SNo_eps_SNoS_omega add_SNo_SNoS_omega IHn Hn.
      + aby nat_p_omega IHn Hn L_ordsucc_neg.
  }
  claim R_SNo: forall X, forall n, nat_p n -> R_ X n c= SNoS_ omega.
  { let X. apply nat_ind.
    - aby SingE nat_1 nat_p_ordinal nat_p_omega omega_ordinal SNoS_I ordinal_SNo_ R_0.
    - let n. assume Hn.
      assume IHn: R_ X n c= SNoS_ omega.
      prove R_ X (ordsucc n) c= SNoS_ omega.
      apply xm (n :e X).
      + aby nat_p_omega IHn Hn R_ordsucc_pos.
      + assume H1: n /:e X.
        apply R_ordsucc_neg X n (nat_p_omega n Hn) H1
                  (fun _ v => v c= SNoS_ omega).
        prove R_ X n :\/: {w + - eps_ (ordsucc n)|w :e R_ X n} c= SNoS_ omega.
        apply binunion_Subq_min.
        * aby L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo Hn IHn H1.
        * { prove {w + - eps_ (ordsucc n)|w :e R_ X n} c= SNoS_ omega.
            let u. assume Hu.
            apply ReplE_impred (R_ X n) (fun w => w + - eps_ (ordsucc n)) u Hu.
            let w.
            assume Hw: w :e R_ X n.
            assume Huw: u = w + - eps_ (ordsucc n).
            rewrite Huw.
            prove w + - eps_ (ordsucc n) :e SNoS_ omega.
            apply add_SNo_SNoS_omega.
            - aby L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo Hn IHn H1 Hu Hw Huw.
            - prove - eps_ (ordsucc n) :e SNoS_ omega.
              apply minus_SNo_SNoS_omega.
              prove eps_ (ordsucc n) :e SNoS_ omega.
              aby nat_p_omega omega_ordsucc SNo_eps_SNoS_omega L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo Hn IHn H1 Hu Hw Huw.
          }
  }
  set L : set -> set := fun X => \/_ n :e omega, L_ X n.
  set R : set -> set := fun X => \/_ n :e omega, R_ X n.
  claim LSo: forall X, L X c= SNoS_ omega.
  { aby famunionE_impred omega_nat_p L_SNo. }
  claim RSo: forall X, R X c= SNoS_ omega.
  { aby famunionE_impred omega_nat_p R_SNo. }
  claim LSNo: forall X, forall w :e L X, SNo w.
  { aby famunionE_impred omega_nat_p L_SNo1. }
  claim RSNo: forall X, forall z :e R X, SNo z.
  { aby famunionE_impred omega_nat_p R_SNo1. }
  claim LLR: forall X, SNoCutP (L X) (R X).
  { let X.
    prove (forall w :e L X, SNo w)
       /\ (forall z :e R X, SNo z)
       /\ (forall w :e L X, forall z :e R X, w < z).
    apply and3I.
    - aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo.
    - aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo.
    - let w. assume Hw.
      let z. assume Hz.
      claim Lw: SNo w.
      { aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo Hw Hz. }
      claim Lz: SNo z.
      { aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo Hw Hz Lw. }
      claim Lwzn: forall n, nat_p n -> w :e L_ X n -> z :e R_ X n -> w < z.
      { let n. assume Hn.
        assume H1: w :e L_ X n.
        assume H2: z :e R_ X n.
        prove w < z.
        apply finite_max_exists (L_ X n) (L_SNo1 X n Hn) (L_fin X n Hn) (L_ne X n Hn).
        let w'.
        assume Hw': SNo_max_of (L_ X n) w'.
        apply Hw'. assume H. apply H.
        assume Hw'1: w' :e L_ X n.
        assume Hw'2: SNo w'.
        assume Hw'3: forall y :e L_ X n, SNo y -> y <= w'.
        apply finite_min_exists (R_ X n) (R_SNo1 X n Hn) (R_fin X n Hn) (R_ne X n Hn).
        let z'.
        assume Hz': SNo_min_of (R_ X n) z'.
        apply Hz'. assume H. apply H.
        assume Hz'1: z' :e R_ X n.
        assume Hz'2: SNo z'.
        assume Hz'3: forall y :e R_ X n, SNo y -> z' <= y.
        prove w < z.
        apply SNoLeLt_tra w w' z Lw Hw'2 Lz (Hw'3 w H1 Lw).
        prove w' < z.
        apply SNoLtLe_tra w' z' z Hw'2 Hz'2 Lz.
        - prove w' < z'.
          rewrite L_R_dist X n Hn w' z' Hw' Hz'.
          prove w' < w' + eps_ n.
          aby nat_p_omega add_SNo_eps_Lt L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo R_SNo LSo RSo LSNo RSNo Hw Hz Lw Lz Hn H1 H2 Hw' H Hw'1 Hw'2 Hw'3 Hz' H Hz'1 Hz'2 Hz'3.
        - prove z' <= z. aby L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo R_SNo LSo RSo LSNo RSNo Hw Hz Lw Lz Hn H1 H2 Hw' H Hw'1 Hw'2 Hw'3 Hz' H Hz'1 Hz'2 Hz'3.
      }
      apply famunionE_impred omega (L_ X) w Hw.
      let n.
      assume Hn: n :e omega.
      assume Hw': w :e L_ X n.
      apply famunionE_impred omega (R_ X) z Hz.
      aby nat_p_ordinal ordinal_trichotomy_or_impred omega_nat_p Hw' Hn Lwzn R_Subq L_Subq.
  }
  claim L0_In: forall X, 0 :e L X.
  { aby famunionI nat_0 nat_p_omega L_0_In. }
  claim R1_In: forall X, 1 :e R X.
  { aby famunionI nat_0 nat_p_omega R_1_In. }
  claim Lne: forall X, L X <> 0.
  { aby EmptyE L0_In. }
  claim Rne: forall X, R X <> 0.
  { aby EmptyE R1_In. }
  claim L_nomax: forall X c= omega, infinite X ->
          forall w :e L X, exists w' :e L X, w < w'.
  { let X. assume HX1 HX2.
    let w. assume Hw.
    claim Lw: SNo w.
    { aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo LLR L0_In Lne Rne HX1 HX2 Hw. }
    apply famunionE_impred omega (L_ X) w Hw.
    let n.
    assume Hn: n :e omega.
    assume Hw': w :e L_ X n.
    apply infinite_bigger X HX1 HX2 n Hn.
    aby ReplI binunionI2 famunionI omega_nat_p omega_ordsucc add_SNo_eps_Lt Hw' Lw HX1 L_Subq L_ordsucc_pos.
  }
  claim R_nomin: forall X c= omega, infinite (omega :\: X) ->
       forall z :e R X, exists z' :e R X, z' < z.
  { let X. assume HX1 HX2.
    let z. assume Hz.
    claim Lz: SNo z.
    { aby L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo LLR L0_In Lne Rne L_nomax HX1 HX2 Hz. }
    apply famunionE_impred omega (R_ X) z Hz.
    let n.
    assume Hn: n :e omega.
    assume Hz': z :e R_ X n.
    apply infinite_bigger (omega :\: X) (setminus_Subq omega X) HX2 n Hn.
    aby ReplI binunionI2 famunionI setminusE omega_nat_p omega_ordsucc SNo_0 SNo_eps_ SNo_eps_pos SNo_minus_SNo minus_SNo_Lt_contra add_SNo_Lt2 add_SNo_0R minus_SNo_0 Hz' Lz R_Subq R_ordsucc_neg.
  }
  claim L_R_real: forall X c= omega, infinite X -> infinite (omega :\: X) -> SNoCut (L X) (R X) :e real.
  { aby real_SNoCut_SNoS_omega R_nomin L_nomax Rne Lne LLR RSo LSo. }
  claim L_R_pos: forall X, 0 < SNoCut (L X) (R X).
  { aby SNoCutP_SNoCut_impred L0_In LLR. }
  claim L_R_lt1: forall X, SNoCut (L X) (R X) < 1.
  { aby SNoCutP_SNoCut_impred R1_In LLR. }
  claim L_R_inj: forall X Y c= omega,
          SNoCut (L X) (R X) = SNoCut (L Y) (R Y)
       -> forall n, nat_p n -> L_ X n = L_ Y n /\ R_ X n = R_ Y n /\ (forall i :e n, i :e X <-> i :e Y).
  { let X. assume HX. let Y. assume HY.
    assume HXY: SNoCut (L X) (R X) = SNoCut (L Y) (R Y).
    prove forall n, nat_p n -> L_ X n = L_ Y n /\ R_ X n = R_ Y n /\ (forall i :e n, i :e X <-> i :e Y).
    apply SNoCutP_SNoCut_impred (L X) (R X) (LLR X).
    assume HLRX1: SNo (SNoCut (L X) (R X)).
    assume HLRX2.
    assume HLRX3: forall w :e L X, w < SNoCut (L X) (R X).
    assume HLRX4: forall z :e R X, SNoCut (L X) (R X) < z.
    assume HLRX5.
    apply SNoCutP_SNoCut_impred (L Y) (R Y) (LLR Y).
    assume HLRY1: SNo (SNoCut (L Y) (R Y)).
    assume HLRY2.
    assume HLRY3: forall w :e L Y, w < SNoCut (L Y) (R Y).
    assume HLRY4: forall z :e R Y, SNoCut (L Y) (R Y) < z.
    assume HLRY5.
    apply nat_ind.
    - aby EmptyE and3I R_0 L_0.
    - let n. assume Hn. assume IHn. apply IHn. assume H. apply H.
      assume IHLn: L_ X n = L_ Y n.
      assume IHRn: R_ X n = R_ Y n.
      assume IHnXY: forall i :e n, i :e X <-> i :e Y.
      prove L_ X (ordsucc n) = L_ Y (ordsucc n) /\ R_ X (ordsucc n) = R_ Y (ordsucc n) /\ (forall i :e ordsucc n, i :e X <-> i :e Y).
      claim Ln: n :e omega.
      { aby nat_p_omega Hn. }
      claim Len: SNo (eps_ n).
      { aby SNo_eps_ Ln. }
      claim LSn: ordsucc n :e omega.
      { aby omega_ordsucc Ln. }
      claim LeSn: SNo (eps_ (ordsucc n)).
      { aby SNo_eps_ LSn. }
      apply xm (n :e X).
      + assume H1: n :e X.
        apply xm (n :e Y).
        * aby and3I ordsuccE H1 Ln IHnXY IHRn IHLn R_ordsucc_pos L_ordsucc_pos.
        * { assume H2: n /:e Y. prove False.
            apply finite_max_exists (L_ X n) (L_SNo1 X n Hn) (L_fin X n Hn) (L_ne X n Hn).
            let w.
            assume Hw: SNo_max_of (L_ X n) w.
            apply Hw. assume H. apply H.
            assume Hw1: w :e L_ X n.
            assume Hw2: SNo w.
            assume Hw3: forall y :e L_ X n, SNo y -> y <= w.
            apply finite_min_exists (R_ X n) (R_SNo1 X n Hn) (R_fin X n Hn) (R_ne X n Hn).
            let z.
            assume Hz: SNo_min_of (R_ X n) z.
            apply Hz. assume H. apply H.
            assume Hz1: z :e R_ X n.
            assume Hz2: SNo z.
            assume Hz3: forall y :e R_ X n, SNo y -> z <= y.
            claim LweSn: SNo (w + eps_ (ordsucc n)).
            { aby SNo_add_SNo Hw2 LeSn. }
            apply SNoLt_irref (w + eps_ (ordsucc n)).
            prove w + eps_ (ordsucc n) < w + eps_ (ordsucc n).
            apply SNoLt_tra (w + eps_ (ordsucc n)) (SNoCut (L X) (R X)) (w + eps_ (ordsucc n)) ?? ?? ??.
            - aby ReplI binunionI2 famunionI Hw1 H1 LSn Ln HLRX3 L_ordsucc_pos.
            - aby ReplI binunionI2 famunionI add_SNo_assoc add_SNo_minus_R2 eps_ordsucc_half_add LweSn Hz1 Hz Hw2 Hw H2 LeSn LSn Ln IHRn Hn HLRY4 HXY L_R_dist R_ordsucc_neg.
          }
      + assume H1: n /:e X.
        apply xm (n :e Y).
        * { assume H2: n :e Y. prove False.
            apply finite_max_exists (L_ X n) (L_SNo1 X n Hn) (L_fin X n Hn) (L_ne X n Hn).
            let w.
            assume Hw: SNo_max_of (L_ X n) w.
            apply Hw. assume H. apply H.
            assume Hw1: w :e L_ X n.
            assume Hw2: SNo w.
            assume Hw3: forall y :e L_ X n, SNo y -> y <= w.
            apply finite_min_exists (R_ X n) (R_SNo1 X n Hn) (R_fin X n Hn) (R_ne X n Hn).
            let z.
            assume Hz: SNo_min_of (R_ X n) z.
            apply Hz. assume H. apply H.
            assume Hz1: z :e R_ X n.
            assume Hz2: SNo z.
            assume Hz3: forall y :e R_ X n, SNo y -> z <= y.
            claim LweSn: SNo (w + eps_ (ordsucc n)).
            { aby SNo_add_SNo Hw2 LeSn. }
            apply SNoLt_irref (w + eps_ (ordsucc n)).
            prove w + eps_ (ordsucc n) < w + eps_ (ordsucc n).
            apply SNoLt_tra (w + eps_ (ordsucc n)) (SNoCut (L X) (R X)) (w + eps_ (ordsucc n)) ?? ?? ??.
            - aby ReplI binunionI2 famunionI Hw1 H2 LSn Ln IHLn HLRY3 HXY L_ordsucc_pos.
            - aby ReplI binunionI2 famunionI add_SNo_assoc add_SNo_minus_R2 eps_ordsucc_half_add LweSn Hz1 Hz Hw2 Hw H1 LeSn LSn Ln Hn HLRX4 L_R_dist R_ordsucc_neg.
          }
        * aby and3I ordsuccE H1 Ln IHnXY IHRn IHLn R_ordsucc_neg L_ordsucc_neg.
  }
  set s:set->set := fun X => {0} :\/: {ordsucc n|n :e X}.
  claim Ls: forall X :e Power omega, s X :e Power omega.
  { aby PowerI PowerE ReplE_impred SingE binunion_Subq_min nat_0 nat_p_omega omega_ordsucc. }
  claim Lsinj: forall X Y, s X = s Y -> X = Y.
  { aby set_ext ReplI ReplE_impred SingE binunionI2 binunionE neq_ordsucc_0 ordsucc_inj. }
  claim Ls0: forall X, 0 :e s X.
  { aby SingI binunionI1. }
  claim Lsfin: forall X, finite X -> finite (s X).
  { aby Sing_finite binunion_finite Repl_finite.
  }
  set h:set->set := fun X => X :\/: \/_ i :e X, {n '|n :e i, n /:e X}.
  claim Lh0: h 0 = 0.
  { aby binunion_idl famunion_Empty. }
  claim LhSa: forall X :e Power omega,
              forall alpha, ordinal alpha -> X c= alpha -> (forall n :e alpha, ~(X c= n))
           -> SNo_ alpha (h X).
  { let X. assume HX: X :e Power omega.
    let alpha.
    assume Ha1: ordinal alpha.
    assume Ha2: X c= alpha.
    assume Ha3: forall n :e alpha, ~(X c= n).
    apply Ha1.
    assume Ha1a Ha1b.
    prove SNo_ alpha (h X).
    prove h X c= SNoElts_ alpha
       /\ forall n :e alpha, exactly1of2 (n ' :e h X) (n :e h X).
    apply andI.
    - let u. assume Hu: u :e h X.
      prove u :e SNoElts_ alpha.
      apply binunionE X (\/_ i :e X, {n '|n :e i, n /:e X}) u Hu.
      + assume H1: u :e X.
        prove u :e alpha :\/: {n '|n :e alpha}.
        apply binunionI1.
        aby L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo R_SNo LSo RSo LSNo RSNo LLR L0_In R1_In Lne Rne L_nomax R_nomin L_R_real L_R_pos L_R_lt1 L_R_inj Ls Lsinj Ls0 Lsfin Lh0 HX Ha1 Ha2 Ha3 Ha1a Ha1b Hu H1.
      + assume H1: u :e \/_ i :e X, {n '|n :e i, n /:e X}.
        prove u :e alpha :\/: {n '|n :e alpha}.
        apply binunionI2.
        prove u :e {n '|n :e alpha}.
        apply famunionE_impred X (fun i => {n '|n :e i, n /:e X}) u H1.
        let i. assume Hi: i :e X.
        assume H2: u :e {n '|n :e i, n /:e X}.
        apply ReplSepE_impred i (fun n => n /:e X) (fun n => n ') u H2.
        let n. assume Hn: n :e i.
        assume H3: n /:e X.
        assume H4: u = n '.
        prove u :e {n '|n :e alpha}.
        rewrite H4.
        claim Lna: n :e alpha.
        { aby L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo R_SNo LSo RSo LSNo RSNo LLR L0_In R1_In Lne Rne L_nomax R_nomin L_R_real L_R_pos L_R_lt1 L_R_inj Ls Lsinj Ls0 Lsfin Lh0 HX Ha1 Ha2 Ha3 Ha1a Ha1b Hu H1 Hi H2 Hn H3 H4. }
        aby ReplI L_0 R_0 L_ordsucc R_ordsucc L_ordsucc_pos L_ordsucc_neg R_ordsucc_pos R_ordsucc_neg L_SNo1 R_SNo1 L_fin R_fin L_ordsucc_Subq R_ordsucc_Subq L_Subq R_Subq L_0_In R_1_In L_ne R_ne L_R_dist L_SNo R_SNo LSo RSo LSNo RSNo LLR L0_In R1_In Lne Rne L_nomax R_nomin L_R_real L_R_pos L_R_lt1 L_R_inj Ls Lsinj Ls0 Lsfin Lh0 HX Ha1 Ha2 Ha3 Ha1a Ha1b Hu H1 Hi H2 Hn H3 H4 Lna.
    - let n. assume Hn: n :e alpha.
      prove exactly1of2 (n ' :e h X) (n :e h X).
      claim Lno: ordinal n.
      { aby ordinal_Hered Hn Ha1. }
      apply xm (n :e X).
      + assume H1: n :e X.
        apply exactly1of2_I2.
        * aby binunionE famunionE_impred ReplSepE_impred ordinal_Hered tagged_not_ordinal tagged_eqE_eq H1 Lno Ha1a Ha2 Ha1.
        * aby binunionI1 H1.
      + assume H1: n /:e X.
        apply exactly1of2_I1.
        * aby xm binunionI2 famunionI ReplSepI ordinal_Hered ordinal_trichotomy_or_impred H1 Lno Hn Ha3 Ha2 Ha1.
        * aby binunionE famunionE_impred ReplSepE_impred tagged_not_ordinal H1 Lno.
  }
  claim LhS: forall X :e Power omega, SNo (h X).
  { aby PowerE least_ordinal_ex omega_ordinal SNo_SNo LhSa. }
  claim Lh: forall X :e Power omega, finite X -> h X :e SNoS_ omega.
  { let X. assume HX: X :e Power omega.
    assume HXfin: finite X.
    prove h X :e SNoS_ omega.
    apply xm (X = 0).
    - aby nat_0 ordinal_Empty nat_p_omega omega_ordinal SNoS_I ordinal_SNo_ Lh0.
    - assume H1: X <> 0.
      claim LXS: forall x :e X, SNo x.
      { aby PowerE omega_nat_p nat_p_SNo HX. }
      apply finite_max_exists X LXS HXfin H1.
      let n. assume Hn: SNo_max_of X n.
      apply Hn. assume H. apply H.
      assume Hn1: n :e X.
      assume Hn2: SNo n.
      assume Hn3: forall x :e X, SNo x -> x <= n.
      claim Ln: n :e omega.
      { aby PowerE L_0 L_ordsucc L_ordsucc_pos L_ordsucc_neg L_SNo1 L_fin L_ordsucc_Subq L_Subq L_0_In L_ne L_R_dist L_SNo LSo RSo LSNo RSNo LLR L0_In Lne Rne L_nomax L_R_real L_R_pos L_R_lt1 L_R_inj Ls Lsinj Ls0 Lsfin Lh0 LhSa LhS HX HXfin H1 LXS Hn H Hn1 Hn2 Hn3. }
      claim Lno: ordinal n.
      { aby nat_p_ordinal omega_nat_p Ln. }
      claim LSn: ordsucc n :e omega.
      { aby omega_ordsucc Ln. }
      claim LSno: ordinal (ordsucc n).
      { aby nat_p_ordinal omega_nat_p LSn. }
      claim LSnhX: SNo_ (ordsucc n) (h X).
      { apply LhSa X HX (ordsucc n) LSno.
        - aby PowerE ordsuccI2 ordinal_Hered ordinal_In_Or_Subq omega_ordinal SNoLt_irref SNoLtLe_tra SNoLeLt_tra ordinal_SNo ordinal_In_SNoLt ordinal_Subq_SNoLe LSno Lno Hn3 Hn2 HX.
        - aby In_irref In_no2cycle ordsuccE Hn1.
      }
      aby omega_ordinal SNoS_I LSnhX LSn.
  }
  claim Lh0pos: forall X :e Power omega, 0 :e X -> 0 < h X.
  { aby EmptyE ReplE_impred binunionI1 binunionE ordinal_Empty tagged_not_ordinal SNoLev_ SNoLtI2 SNoLev_0 LhS. }
  claim Lhinj1: forall X Y :e Power omega, h X = h Y -> X c= Y.
  { aby PowerE binunionI1 binunionE famunionE_impred ReplSepE_impred nat_p_ordinal omega_nat_p tagged_not_ordinal. }
  claim Lhinj: forall X Y :e Power omega, h X = h Y -> X = Y.
  { aby set_ext Lhinj1. }
  set g:set->set := fun X => if finite X then h (s X) + 1 else if finite (omega :\: X) then - h (s (omega :\: X)) else SNoCut (L X) (R X).
  prove exists g:set->set, inj (Power omega) real g.
  witness g.  
  prove (forall u :e Power omega, g u :e real)
     /\ (forall u v :e Power omega, g u = g v -> u = v).
  apply andI.
  + let X. assume HX: X :e Power omega.
    apply xm (finite X).
    * aby If_i_1 nat_1 nat_p_omega omega_SNoS_omega SNoS_omega_real real_add_SNo HX Lh Lsfin Ls.
    * aby PowerI xm PowerE If_i_0 If_i_1 setminus_Subq SNoS_omega_real real_minus_SNo HX Lh Lsfin Ls L_R_real.
  + let X. assume HX: X :e Power omega.
    let Y. assume HY: Y :e Power omega.
    claim LX: X c= omega.
    { aby PowerE HX. }
    claim LY: Y c= omega.
    { aby PowerE HY. }
    claim LoX: omega :\: X :e Power omega.
    { aby PowerI setminus_Subq. }
    claim LoY: omega :\: Y :e Power omega.
    { aby PowerI setminus_Subq. }
    apply xm (finite X).
    * aby xm If_i_0 If_i_1 SingI binunionI1 omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 SNo_0 SNo_1 SNoLt_0_1 minus_SNo_Lt_contra1 SNo_add_SNo add_SNo_Lt1 add_SNo_Lt2 add_SNo_0L add_SNo_0R add_SNo_cancel_R minus_SNo_0 LoY HY HX Lhinj Lh0pos Lh Lsfin Lsinj Ls L_R_lt1.
    * { assume H1: infinite X.
        prove (if finite X then h (s X) + 1 else if finite (omega :\: X) then - h (s (omega :\: X)) else SNoCut (L X) (R X))
            = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
         -> X = Y.
        apply If_i_0 (finite X) (h (s X) + 1) (if finite (omega :\: X) then - h (s (omega :\: X)) else SNoCut (L X) (R X)) H1
           (fun _ u =>
              u = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y)) -> X = Y).
        prove (if finite (omega :\: X) then - h (s (omega :\: X)) else SNoCut (L X) (R X))
            = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
         -> X = Y.
        apply xm (finite (omega :\: X)).
        - assume H2: finite (omega :\: X).
          apply SNoS_E2 omega omega_ordinal (h (s (omega :\: X))) (Lh (s (omega :\: X)) (Ls (omega :\: X) LoX) (Lsfin (omega :\: X) H2)).
          assume HhsX1: SNoLev (h (s (omega :\: X))) :e omega.
          assume HhsX2: ordinal (SNoLev (h (s (omega :\: X)))).
          assume HhsX3: SNo (h (s (omega :\: X))).
          assume HhsX4: SNo_ (SNoLev (h (s (omega :\: X)))) (h (s (omega :\: X))).
          prove (if finite (omega :\: X) then - h (s (omega :\: X)) else SNoCut (L X) (R X))
              = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
           -> X = Y.
          apply If_i_1 (finite (omega :\: X)) (- h (s (omega :\: X))) (SNoCut (L X) (R X)) H2
                    (fun _ u =>
                       u = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y)) -> X = Y).
          prove (- h (s (omega :\: X)))
              = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
           -> X = Y.
          apply xm (finite Y).
          + aby If_i_1 SingI binunionI1 omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 SNo_0 SNo_1 SNoLt_0_1 minus_SNo_Lt_contra1 SNo_add_SNo add_SNo_Lt2 add_SNo_0R minus_SNo_0 HhsX3 LoX HY Lh0pos Lh Lsfin Ls.
          + assume H3: infinite Y.
            apply If_i_0 (finite Y) (h (s Y) + 1) (if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y)) H3 (fun _ u => - h (s (omega :\: X)) = u -> X = Y).
            prove (- h (s (omega :\: X)))
                = (if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
             -> X = Y.
            apply xm (finite (omega :\: Y)).
            * aby set_ext PowerI dneg If_i_1 setminusI setminusE2 setminus_Subq omega_ordinal SNoS_E2 minus_SNo_invol HhsX3 LoY LoX LY LX Lhinj Lh Lsfin Lsinj Ls.
            * aby If_i_0 SingI binunionI1 SNoLt_irref SNoLt_tra SNo_0 SNo_minus_SNo minus_SNo_Lt_contra1 minus_SNo_0 HhsX3 LoX Lh0pos Ls L_R_pos.
        - assume H2: infinite (omega :\: X).
          apply If_i_0 (finite (omega :\: X)) (- h (s (omega :\: X))) (SNoCut (L X) (R X)) H2
                    (fun _ u =>
                       u = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y)) -> X = Y).
          prove (SNoCut (L X) (R X))
              = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
           -> X = Y.
          apply xm (finite Y).
          + aby If_i_1 SingI binunionI1 omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 SNo_0 SNo_1 SNo_add_SNo add_SNo_Lt1 add_SNo_0L HY Lh0pos Lh Lsfin Ls L_R_lt1.
          + assume H3: infinite Y.
            prove (SNoCut (L X) (R X))
                = (if finite Y then h (s Y) + 1 else if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y))
             -> X = Y.
            apply If_i_0 (finite Y) (h (s Y) + 1) (if finite (omega :\: Y) then - h (s (omega :\: Y)) else SNoCut (L Y) (R Y)) H3 (fun _ u => SNoCut (L X) (R X) = u -> X = Y).
            apply xm (finite (omega :\: Y)).
            * aby PowerI If_i_1 SingI binunionI1 setminus_Subq omega_ordinal SNoLt_irref SNoLt_tra SNoS_E2 SNo_0 SNo_minus_SNo minus_SNo_Lt_contra1 minus_SNo_0 LoY Lh0pos Lh Lsfin Ls L_R_pos.
            * aby set_ext If_i_0 ordsuccI2 nat_ordsucc omega_nat_p LY LX L_R_inj.
      }
Qed.

Theorem form100_22_real_uncountable_atleastp: ~atleastp real omega.
aby inj_comp bij_inj equip_sym form100_22_v2 equip_real_Power_omega.
Qed.

Theorem form100_22_real_uncountable_equip: ~equip real omega.
aby equip_atleastp form100_22_real_uncountable_atleastp.
Qed.

Theorem form100_22_real_uncountable: atleastp omega real /\ ~equip real omega.
aby Subq_tra Subq_atleastp omega_SNoS_omega SNoS_omega_real form100_22_real_uncountable_equip.
Qed.

End form100_22b.

Section rational.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix ^ 342 right := exp_SNo_nat.
Infix :/: 353 := div_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Definition rational : set := {x :e real | exists m :e int, exists n :e omega :\: {0}, x = m :/: n}.

End rational.

Section form100_3.

(** The Denumerability of the Rational Numbers **)

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.
Infix ^ 342 right := exp_SNo_nat.

Theorem Subq_int_SNoS_omega: int c= SNoS_ omega.
aby diadic_rational_p_SNoS_omega int_diadic_rational_p.
Qed.

Theorem Subq_SNoS_omega_rational: SNoS_ omega c= rational.
aby SingE SepI setminusI nat_2 neq_1_0 omega_nat_p nat_p_omega nat_p_SNo SNo_eps_ mul_SNo_zeroR mul_SNo_com int_SNo nat_exp_SNo_nat mul_SNo_eps_power_2 SNoS_omega_diadic_rational_p recip_SNo_pow_2 SNoS_omega_real.
Qed.

Theorem Subq_rational_real: rational c= real.
aby Sep_Subq.
Qed.

Theorem rational_minus_SNo: forall q :e rational, - q :e rational.
aby SingI SepI SepE setminusE omega_SNo mul_SNo_minus_distrR mul_SNo_nonzero_cancel mul_minus_SNo_distrR int_SNo int_minus_SNo mul_SNo_nonzero_cancel_L SNo_div_SNo mul_div_SNo_invR real_SNo real_minus_SNo.
Qed.

Definition nat_pair : set -> set -> set := fun m n => 2 ^ m * (2 * n + 1).

Theorem nat_pair_In_omega: forall m n :e omega, nat_pair m n :e omega.
aby nat_1 nat_2 omega_nat_p nat_p_omega add_SNo_In_omega mul_SNo_In_omega nat_exp_SNo_nat.
Qed.

Theorem nat_pair_0: forall m n m' n' :e omega, nat_pair m n = nat_pair m' n' -> m = m'.
claim L1: forall m n k, nat_p m -> nat_p n -> nat_p k -> 2 ^ (ordsucc m) * (2 * n + 1) <> 2 ^ 0 * (2 * k + 1).
{ let m n k. assume Hm Hn Hk.
  assume H1: 2 ^ (ordsucc m) * (2 * n + 1) = 2 ^ 0 * (2 * k + 1).
  claim L1a: 2 ^ m :e omega.
  { prove 2 ^ m :e omega.
    apply nat_p_omega.
    aby nat_2 nat_exp_SNo_nat Hm Hn Hk H1.
  }
  claim L1b: 2 * n :e omega.
  { apply mul_SNo_In_omega.
    - apply nat_p_omega. aby nat_2 Hm Hn Hk H1 L1a.
    - apply nat_p_omega. aby Hm Hn Hk H1 L1a.
  }
  claim L1c: 2 * n + 1 :e omega.
  { apply add_SNo_In_omega.
    - aby Hm Hn Hk H1 L1a L1b.
    - apply nat_p_omega. aby nat_1 Hm Hn Hk H1 L1a L1b.
  }
  claim L1d: 2 ^ m * (2 * n + 1) :e int.
  { apply Subq_omega_int. apply mul_SNo_In_omega.
    - aby Hm Hn Hk H1 L1a L1b L1c.
    - aby Hm Hn Hk H1 L1a L1b L1c.
  }
  apply not_eq_2m_2n1 (2 ^ m * (2 * n + 1)) L1d
                      k (Subq_omega_int k (nat_p_omega k Hk)).
  transitivity (2 * (2 ^ m)) * (2 * n + 1),
               2 ^ (ordsucc m) * (2 * n + 1),
               2 ^ 0 * (2 * k + 1).
  - prove 2 * (2 ^ m * (2 * n + 1)) = (2 * (2 ^ m)) * (2 * n + 1).
    aby omega_SNo SNo_2 mul_SNo_assoc Hm Hn Hk H1 L1a L1b L1c L1d.
  - prove (2 * (2 ^ m)) * (2 * n + 1) = 2 ^ (ordsucc m) * (2 * n + 1).
    f_equal.
    prove 2 * (2 ^ m) = 2 ^ (ordsucc m).
    aby SNo_2 exp_SNo_nat_S Hm Hn Hk H1 L1a L1b L1c L1d.
  - prove 2 ^ (ordsucc m) * (2 * n + 1) = 2 ^ 0 * (2 * k + 1).
    aby Hm Hn Hk H1 L1a L1b L1c L1d.
  - prove 2 ^ 0 * (2 * k + 1) = 2 * k + 1.
    rewrite exp_SNo_nat_0 2 SNo_2.
    prove 1 * (2 * k + 1) = 2 * k + 1.
    apply mul_SNo_oneL (2 * k + 1).
    prove SNo (2 * k + 1).
    apply SNo_add_SNo.
    + apply SNo_mul_SNo.
      * aby SNo_2 Hm Hn Hk H1 L1a L1b L1c L1d.
      * aby nat_p_SNo Hm Hn Hk H1 L1a L1b L1c L1d.
    + aby SNo_1 Hm Hn Hk H1 L1a L1b L1c L1d.
}
claim L2: forall k, nat_p k ->
          forall m, nat_p m ->
          forall m', nat_p m' ->
          forall n, nat_p n ->
          forall n', nat_p n' ->
             nat_pair m n = k -> nat_pair m' n' = k -> m = m'.
{ apply nat_complete_ind.
  let k. assume Hk.
  assume IHk: forall k' :e k,
          forall m, nat_p m ->
          forall m', nat_p m' ->
          forall n, nat_p n ->
          forall n', nat_p n' ->
             nat_pair m n = k' -> nat_pair m' n' = k' -> m = m'.
  apply nat_inv_impred.
  - aby nat_1 nat_2 nat_inv_impred nat_p_omega add_SNo_In_omega mul_SNo_In_omega Subq_omega_int nat_exp_SNo_nat L1.
  - let m. assume Hm.
    apply nat_inv_impred.
    + aby nat_1 nat_2 nat_p_omega add_SNo_In_omega mul_SNo_In_omega Subq_omega_int nat_exp_SNo_nat Hm L1.
    + let m'. assume Hm'. let n. assume Hn. let n'. assume Hn'.
      assume H1: 2 ^ (ordsucc m) * (2 * n + 1) = k.
      assume H2: 2 ^ (ordsucc m') * (2 * n' + 1) = k.
      prove ordsucc m = ordsucc m'.
      f_equal.
      set k' := 2 ^ m * (2 * n + 1).
      claim L2mS: SNo (2 ^ m).
      { aby SNo_2 SNo_exp_SNo_nat Hm. }
      claim L2m'S: SNo (2 ^ m').
      { aby SNo_2 SNo_exp_SNo_nat Hm'. }
      claim L2mpos: 0 < 2 ^ m.
      { aby SNo_2 SNoLt_0_2 exp_SNo_nat_pos Hm. }
      claim L2SmS: SNo (2 ^ ordsucc m).
      { aby nat_ordsucc SNo_2 SNo_exp_SNo_nat Hm. }
      claim L2nS: SNo (2 * n).
      { aby nat_p_SNo SNo_2 SNo_mul_SNo Hn. }
      claim L2n1S: SNo (2 * n + 1).
      { aby SNo_1 SNo_add_SNo L2nS. }
      claim L2n'S: SNo (2 * n').
      { aby nat_p_SNo SNo_2 SNo_mul_SNo Hn'. }
      claim L2n'1S: SNo (2 * n' + 1).
      { aby SNo_1 SNo_add_SNo L2n'S. }
      claim L2n1pos: 0 < 2 * n + 1.
      { aby nat_p_omega SNoLtLe SNoLeLt_tra nat_p_SNo omega_nonneg SNo_0 SNo_1 SNo_2 SNoLt_0_1 SNoLt_0_2 add_SNo_Lt2 add_SNo_0R mul_SNo_nonneg_nonneg L2n1S L2nS Hn. }
      claim L2: k' < k.
      { aby SNo_1 SNo_2 SNoLt_1_2 mul_SNo_oneL pos_mul_SNo_Lt' exp_SNo_nat_S L2n1pos L2n1S L2SmS L2mpos L2mS H1 Hm. }
      claim L3: k' :e k.
      { aby nat_p_ordinal omega_nat_p nat_p_omega ordinal_SNoLt_In nat_pair_In_omega L2 Hn Hm Hk. }
      aby neq_2_0 SNo_2 SNo_mul_SNo mul_SNo_assoc mul_SNo_nonzero_cancel exp_SNo_nat_S mul_SNo_nonzero_cancel_L L3 L2n'1S L2n1S L2m'S L2mS H2 H1 Hn' Hn Hm' Hm IHk.
}
aby omega_nat_p nat_pair_In_omega L2.
Qed.

Theorem nat_pair_1: forall m n m' n' :e omega, nat_pair m n = nat_pair m' n' -> n = n'.
aby neq_1_0 neq_2_0 omega_nat_p omega_SNo SNo_1 SNo_2 SNo_eps_ SNo_add_SNo add_SNo_cancel_R SNo_mul_SNo mul_SNo_zeroR mul_SNo_nonzero_cancel SNo_exp_SNo_nat mul_SNo_eps_power_2 mul_SNo_nonzero_cancel_L nat_pair_0.
Qed.

Theorem form100_3: equip omega rational.
apply atleastp_antisym_equip.
- aby Subq_tra Subq_atleastp Subq_omega_int Subq_int_SNoS_omega Subq_SNoS_omega_rational.
- prove atleastp rational omega.
  set denom:set->set := fun q => Eps_i (fun n => n :e omega /\ exists m :e omega, q = m :/: n).
  set num:set->set := fun q => Eps_i (fun m => m :e omega /\ q = m :/: denom q).
  claim L1: forall q :e rational, 0 <= q -> exists n :e omega, exists m :e omega, q = m :/: n.
  { let q. assume Hq Hqnn.
    apply SepE real (fun q => exists m :e int, exists n :e omega :\: {0}, q = m :/: n) q Hq.
    assume HqR: q :e real.
    assume HqQ. apply HqQ.
    let m. assume H. apply H.
    assume Hm: m :e int. assume H. apply H.
    let n. assume H. apply H.
    assume Hn: n :e omega :\: {0}.
    assume H1: q = m :/: n.
    apply setminusE omega {0} n Hn.
    assume Hno: n :e omega.
    assume Hnz: n /:e {0}.
    claim LnS: SNo n.
    { aby omega_SNo Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz. }
    claim LqS: SNo q.
    { aby real_SNo Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS. }
    claim Lnpos: 0 < n.
    { apply SNoLeE 0 n SNo_0 LnS (omega_nonneg n Hno).
      - assume H2: 0 < n. aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS H2.
      - assume H2: 0 = n. prove False.
        apply Hnz.
        prove n :e {0}.
        rewrite <- H2.
        apply SingI.
    }
    claim Lrnpos: 0 < recip_SNo n.
    { aby recip_SNo_of_pos_is_pos Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos. }
    apply int_3_cases m Hm.
    - let m'. assume Hm': m' :e omega.
      assume H2: m = - ordsucc m'.
      prove False.
      apply SNoLt_irref 0.
      prove 0 < 0.
      apply SNoLeLt_tra 0 q 0 SNo_0 LqS SNo_0 Hqnn.
      prove q < 0.
      rewrite H1.
      prove m :/: n < 0.
      prove m * recip_SNo n < 0.
      rewrite <- mul_SNo_zeroL (recip_SNo n) (SNo_recip_SNo n LnS).
      prove m * recip_SNo n < 0 * recip_SNo n.
      apply pos_mul_SNo_Lt' m 0 (recip_SNo n) (int_SNo m Hm) SNo_0 (SNo_recip_SNo n LnS) Lrnpos.
      prove m < 0.
      rewrite H2.
      prove - ordsucc m' < 0.
      apply minus_SNo_Lt_contra1 0 (ordsucc m') SNo_0 (omega_SNo (ordsucc m') (omega_ordsucc m' Hm')).
      prove - 0 < ordsucc m'.
      rewrite minus_SNo_0.
      prove 0 < ordsucc m'.
      apply ordinal_In_SNoLt (ordsucc m') (nat_p_ordinal (ordsucc m') (nat_ordsucc m' (omega_nat_p m' Hm'))) 0.
      prove 0 :e ordsucc m'.
      aby nat_0_in_ordsucc omega_nat_p Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos Hm' H2.
    - assume H2: m = 0.
      prove exists n :e omega, exists m :e omega, q = m :/: n.
      witness n. apply andI.
      + aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos H2.
      + prove exists m :e omega, q = m :/: n.
        witness m. apply andI.
        * prove m :e omega. rewrite H2. apply nat_p_omega. aby nat_0 Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos H2.
        * prove q = m :/: n. aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos H2.      
    - let m'. assume Hm': m' :e omega.
      assume H2: m = ordsucc m'.
      prove exists n :e omega, exists m :e omega, q = m :/: n.
      witness n. apply andI.
      + aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos Hm' H2.
      + prove exists m :e omega, q = m :/: n.
        witness m. apply andI.
        * prove m :e omega. rewrite H2.
          prove ordsucc m' :e omega.
          apply omega_ordsucc.
          aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos Hm' H2.
        * prove q = m :/: n. aby Hq Hqnn HqR HqQ H Hm H H Hn H1 Hno Hnz LnS LqS Lnpos Lrnpos Hm' H2.      
  }
  claim L2: forall q :e rational, 0 <= q -> denom q :e omega /\ exists n :e omega, q = n :/: denom q.
  { aby Eps_i_ex L1. }
  claim L3: forall q :e rational, 0 <= q -> num q :e omega /\ q = num q :/: denom q.
  { aby Eps_i_ex L2. }
  claim Lnum: forall q :e rational, 0 <= q -> num q :e omega.
  { aby L3. }
  claim Ldenom: forall q :e rational, 0 <= q -> denom q :e omega.
  { aby L2. }
  set g:set->set := fun q => if 0 <= q then nat_pair 0 (nat_pair (num q) (denom q)) else nat_pair 1 (nat_pair (num (- q)) (denom (- q))).
  claim Lgnneg: forall q, 0 <= q -> g q = nat_pair 0 (nat_pair (num q) (denom q)).
  { aby If_i_1. }
  claim Lgneg: forall q, SNo q -> q < 0 -> g q = nat_pair 1 (nat_pair (num (- q)) (denom (- q))).
  { aby If_i_0 SNoLt_irref SNoLtLe_tra SNo_0. }
  claim L_nat_pair_3: forall k m n :e omega, nat_pair k (nat_pair m n) :e omega.
  { aby nat_pair_In_omega. }
  claim L_nat_pair_3_inj: forall k m n k' m' n' :e omega, nat_pair k (nat_pair m n) = nat_pair k' (nat_pair m' n')
     -> forall p:prop,
            (k = k' -> m = m' -> n = n' -> p)
         -> p.
  { aby nat_pair_In_omega nat_pair_0 nat_pair_1. }
  prove exists g:set->set, inj rational omega g.
  witness g.
  prove inj rational omega g.
  apply injI.
  + let q. assume Hq: q :e rational.
    claim LqS: SNo q.
    { aby real_SNo Subq_rational_real L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq. }
    prove g q :e omega.
    apply SNoLtLe_or q 0 LqS SNo_0.
    * { assume H1: q < 0.
        claim LmqQ: - q :e rational.
        { aby rational_minus_SNo L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq LqS H1. }
        claim Lmqnn: 0 <= - q.
        { apply SNoLtLe.
          prove 0 < - q.
          apply minus_SNo_Lt_contra2 q 0 LqS SNo_0.
          prove q < - 0.
          rewrite minus_SNo_0.
          aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq LqS H1 LmqQ.
        }
        prove g q :e omega.
        exact Lgneg q LqS H1 (fun _ u => u :e omega)
                     (L_nat_pair_3
                       1 (nat_p_omega 1 nat_1)
                       (num (- q)) (Lnum (- q) LmqQ Lmqnn)
                       (denom (- q)) (Ldenom (- q) LmqQ Lmqnn)).
      }
    * { assume H1: 0 <= q.
        prove g q :e omega.
        exact Lgnneg q H1 (fun _ u => u :e omega)
                     (L_nat_pair_3
                       0 (nat_p_omega 0 nat_0)
                       (num q) (Lnum q Hq H1)
                       (denom q) (Ldenom q Hq H1)).
      }
  + let q. assume Hq: q :e rational.
    let q'. assume Hq': q' :e rational.
    claim LqS: SNo q.
    { aby real_SNo Subq_rational_real L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq'. }
    claim Lq'S: SNo q'.
    { aby real_SNo Subq_rational_real L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS. }
    assume H1: g q = g q'.
    prove q = q'.
    apply SNoLtLe_or q 0 LqS SNo_0.
    * { assume H2: q < 0.
        claim LmqQ: - q :e rational.
        { aby rational_minus_SNo Hq. }
        claim Lmqnn: 0 <= - q.
        { aby SNoLtLe SNo_0 minus_SNo_Lt_contra2 minus_SNo_0 H2 LqS. }
        apply SNoLtLe_or q' 0 Lq'S SNo_0.
        - assume H3: q' < 0.
          claim Lmq'Q: - q' :e rational.
          { aby rational_minus_SNo Hq'. }
          claim Lmq'nn: 0 <= - q'.
          { aby SNoLtLe SNo_0 minus_SNo_Lt_contra2 minus_SNo_0 H3 Lq'S. }
          claim L4a: nat_pair 1 (nat_pair (num (- q)) (denom (- q)))
                  = nat_pair 1 (nat_pair (num (- q')) (denom (- q'))).
          { transitivity g q, g q'.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3 Lmq'Q Lmq'nn.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3 Lmq'Q Lmq'nn.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3 Lmq'Q Lmq'nn.
          }
          apply L_nat_pair_3_inj 1 (nat_p_omega 1 nat_1)
                                 (num (- q)) (Lnum (- q) LmqQ Lmqnn)
                                 (denom (- q)) (Ldenom (- q) LmqQ Lmqnn)
                                 1 (nat_p_omega 1 nat_1)
                                 (num (- q')) (Lnum (- q') Lmq'Q Lmq'nn)
                                 (denom (- q')) (Ldenom (- q') Lmq'Q Lmq'nn)
                                 L4a.
          assume _.
          aby minus_SNo_invol Lmq'nn Lmq'Q Lmqnn LmqQ Lq'S LqS L3.
        - assume H3: 0 <= q'. prove False.
          claim L4b: nat_pair 1 (nat_pair (num (- q)) (denom (- q)))
                  = nat_pair 0 (nat_pair (num q') (denom q')).
          { transitivity g q, g q'.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3.
          }
          apply L_nat_pair_3_inj 1 (nat_p_omega 1 nat_1)
                                 (num (- q)) (Lnum (- q) LmqQ Lmqnn)
                                 (denom (- q)) (Ldenom (- q) LmqQ Lmqnn)
                                 0 (nat_p_omega 0 nat_0)
                                 (num q') (Lnum q' Hq' H3)
                                 (denom q') (Ldenom q' Hq' H3)
                                 L4b.
          assume H4: 1 = 0. prove False.
          apply neq_1_0.
          aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 LmqQ Lmqnn H3 L4b H4.
      }
    * { assume H2: 0 <= q.
        apply SNoLtLe_or q' 0 Lq'S SNo_0.
        - assume H3: q' < 0. prove False.
          claim Lmq'Q: - q' :e rational.
          { aby rational_minus_SNo Hq'. }
          claim Lmq'nn: 0 <= - q'.
          { aby SNoLtLe SNo_0 minus_SNo_Lt_contra2 minus_SNo_0 H3 Lq'S. }
          claim L4c: nat_pair 0 (nat_pair (num q) (denom q))
                  = nat_pair 1 (nat_pair (num (- q')) (denom (- q'))).
          { transitivity g q, g q'.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3 Lmq'Q Lmq'nn.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3 Lmq'Q Lmq'nn.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3 Lmq'Q Lmq'nn.
          }
          apply L_nat_pair_3_inj 0 (nat_p_omega 0 nat_0)
                                 (num q) (Lnum q Hq H2)
                                 (denom q) (Ldenom q Hq H2)
                                 1 (nat_p_omega 1 nat_1)
                                 (num (- q')) (Lnum (- q') Lmq'Q Lmq'nn)
                                 (denom (- q')) (Ldenom (- q') Lmq'Q Lmq'nn)
                                 L4c.
          assume H4: 0 = 1. prove False.
          apply neq_0_1.
          aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3 Lmq'Q Lmq'nn L4c H4.
        - assume H3: 0 <= q'.
          claim L4d: nat_pair 0 (nat_pair (num q) (denom q))
                  = nat_pair 0 (nat_pair (num q') (denom q')).
          { transitivity g q, g q'.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3.
            - aby L1 L2 L3 Lnum Ldenom Lgnneg Lgneg L_nat_pair_3 L_nat_pair_3_inj Hq Hq' LqS Lq'S H1 H2 H3.
          }
          apply L_nat_pair_3_inj 0 (nat_p_omega 0 nat_0)
                                 (num q) (Lnum q Hq H2)
                                 (denom q) (Ldenom q Hq H2)
                                 0 (nat_p_omega 0 nat_0)
                                 (num q') (Lnum q' Hq' H3)
                                 (denom q') (Ldenom q' Hq' H3)
                                 L4d.
          assume _.
          aby H3 H2 Hq' Hq L3.
      }
Qed.

End form100_3.

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
aby Sep_Empty SNoL_0.
Qed.

Theorem SNoL_nonneg_1: SNoL_nonneg 1 = 1.
aby set_ext SepI Sep_Subq In_0_1 cases_1 SNoLe_ref SNoL_1.
Qed.

Definition SNo_sqrtauxset : set -> set -> set -> set := fun Y Z x => \/_ y :e Y, {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.

Theorem SNo_sqrtauxset_I : forall Y Z x,
 forall y :e Y, forall z :e Z, 0 < y + z -> (x + y * z) :/: (y + z) :e SNo_sqrtauxset Y Z x.
aby famunionI ReplSepI.
Qed.

Theorem SNo_sqrtauxset_E : forall Y Z x,
 forall u :e SNo_sqrtauxset Y Z x, forall p:prop,
     (forall y :e Y, forall z :e Z, 0 < y + z -> u = (x + y * z) :/: (y + z) -> p)
  -> p.
aby famunionE_impred ReplSepE_impred.
Qed.

Theorem SNo_sqrtauxset_0: forall Z x, SNo_sqrtauxset 0 Z x = 0.
aby EmptyE Empty_eq SNo_sqrtauxset_E.
Qed.

Theorem SNo_sqrtauxset_0': forall Y x, SNo_sqrtauxset Y 0 x = 0.
aby EmptyE Empty_eq SNo_sqrtauxset_E.
Qed.

Definition SNo_sqrtaux : set -> (set -> set) -> set -> set :=
 fun x g =>
  nat_primrec ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x})
   (fun k p => (p 0 :\/: SNo_sqrtauxset (p 0) (p 1) x,
                p 1 :\/: SNo_sqrtauxset (p 0) (p 0) x
                    :\/: SNo_sqrtauxset (p 1) (p 1) x)).

Theorem SNo_sqrtaux_0: forall x, forall g:set -> set, SNo_sqrtaux x g 0 = ({g w|w :e SNoL_nonneg x},{g z|z :e SNoR x}).
aby nat_primrec_0.
Qed.

Theorem SNo_sqrtaux_S: forall x, forall g:set -> set, forall n, nat_p n
 -> SNo_sqrtaux x g (ordsucc n)
  = (SNo_sqrtaux x g n 0
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 1) x,
     SNo_sqrtaux x g n 1
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 0) (SNo_sqrtaux x g n 0) x
       :\/: SNo_sqrtauxset (SNo_sqrtaux x g n 1) (SNo_sqrtaux x g n 1) x).
aby nat_primrec_S.
Qed.

Theorem SNo_sqrtaux_mon_lem: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g (add_nat m n) 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g (add_nat m n) 1.
let x g m. assume Hm.
apply nat_ind.
- aby Subq_ref add_nat_0R.
- aby Subq_tra binunion_Subq_1 add_nat_SR add_nat_p tuple_2_0_eq tuple_2_1_eq SNo_sqrtaux_S Hm.
Qed.

Theorem SNo_sqrtaux_mon: forall x, forall g:set -> set,
  forall m, nat_p m -> forall n, nat_p n -> m c= n
   -> SNo_sqrtaux x g m 0 c= SNo_sqrtaux x g n 0
   /\ SNo_sqrtaux x g m 1 c= SNo_sqrtaux x g n 1.
aby add_nat_com nat_Subq_add_ex SNo_sqrtaux_mon_lem.
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
    aby SNoS_I2 Hx Hgh Hw Hw1 Hw2 Hw3.
  }
  claim L2: {g w|w :e SNoR x} = {h w|w :e SNoR x}.
  { apply ReplEq_ext (SNoR x) g h.
    let w. assume Hw: w :e SNoR x.
    prove g w = h w.
    apply SNoR_E x Hx w Hw.
    assume Hw1 Hw2 Hw3.
    apply Hgh.
    prove w :e SNoS_ (SNoLev x).
    aby SNoS_I2 Hx Hgh L1 Hw Hw1 Hw2 Hw3.
  }
  rewrite L1. rewrite L2. reflexivity.
- aby SNo_sqrtaux_S.
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
- aby famunion_ext omega_nat_p SNo_sqrtaux_ext Hgh Hx.
- aby famunion_ext omega_nat_p SNo_sqrtaux_ext Hgh Hx.
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
- aby and3I ReplE_impred SepE tuple_2_0_eq tuple_2_1_eq SNoLtLe SNoLe_tra SNoS_I2 SNoL_E SNoR_E SNo_0 SNo_sqrtaux_0 IH Hxnonneg Hx.
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
    * aby Hx Hxnonneg IH Hk IHk IHk0 IHk1.
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
        { aby SNo_mul_SNo Hz1 Hw1. }
        claim Lxpwz: SNo (x + w * z).
        { aby SNo_add_SNo Lwz Hx. }
        claim Lwpz: SNo (w + z).
        { aby SNo_add_SNo Hz1 Hw1. }
        claim Ly: SNo y.
        { aby SNo_div_SNo Lwpz Lxpwz Hywz. }
        claim Lxpwznonneg: 0 <= x + w * z.
        { aby SNo_0 add_SNo_Le3 add_SNo_0L mul_SNo_nonneg_nonneg Lwz Hz2 Hz1 Hw2 Hw1 Hxnonneg Hx. }
        claim Lynonneg: 0 <= y.
        { aby SNoLtLe SNoLeE SNoLe_ref SNo_0 div_SNo_0_num div_SNo_pos_pos Lxpwznonneg Lwpz Lxpwz Hywz Hwpzpos. }
        apply and3I.
        - aby Ly.
        - aby Lynonneg.
        - prove y * y < x.
          rewrite Hywz.
          prove ((x + w * z) :/: (w + z)) * ((x + w * z) :/: (w + z)) < x.
          rewrite mul_div_SNo_both (x + w * z) (w + z) (x + w * z) (w + z) Lxpwz Lwpz Lxpwz Lwpz.
          prove ((x + w * z) * (x + w * z)) :/: ((w + z) * (w + z)) < x.
          apply div_SNo_pos_LtL ((x + w * z) * (x + w * z)) ((w + z) * (w + z)) x (SNo_mul_SNo (x + w * z) (x + w * z) Lxpwz Lxpwz) (SNo_mul_SNo (w + z) (w + z) Lwpz Lwpz) Hx.
          + aby mul_SNo_pos_pos Lwpz Hwpzpos.
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
            { aby SNo_mul_SNo Lwz Hx. }
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
            { aby SNo_mul_SNo_3 Hz1 Hw1 Hx. }
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
            aby SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_rotate_3_1 SNoLt_minus_pos SNo_mul_SNo mul_SNo_assoc mul_SNo_pos_pos mul_SNo_com_3_0_1 SNo_foil_mm Lwz Hz3 Hz1 Hw3 Hw1 Hx.
            * aby Hx.
            * aby Lwz.
      }
  + let y. rewrite tuple_2_1_eq.
    apply binunionE'.
    * { apply binunionE'.
        - aby Hx Hxnonneg IH Hk IHk IHk0 IHk1.
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
          { aby SNo_mul_SNo Hw'1 Hw1. }
          claim Lxpww': SNo (x + w * w').
          { aby SNo_add_SNo Lww' Hx. }
          claim Lwpw': SNo (w + w').
          { aby SNo_add_SNo Hw'1 Hw1. }
          claim Ly: SNo y.
          { aby SNo_div_SNo Lwpw' Lxpww' Hyww'. }
          claim Lxpww'nonneg: 0 <= x + w * w'.
          { aby SNo_0 add_SNo_Le3 add_SNo_0L mul_SNo_nonneg_nonneg Lww' Hw'2 Hw'1 Hw2 Hw1 Hxnonneg Hx. }
          claim Lynonneg: 0 <= y.
          { aby SNoLtLe SNoLeE SNoLe_ref SNo_0 div_SNo_0_num div_SNo_pos_pos Lxpww'nonneg Lwpw' Lxpww' Hyww' Hww'pos. }
          apply and3I.
          + aby Ly.
          + aby Lynonneg.
          + prove x < y * y.
            rewrite Hyww'.
            prove x < ((x + w * w') :/: (w + w')) * ((x + w * w') :/: (w + w')).
            rewrite mul_div_SNo_both (x + w * w') (w + w') (x + w * w') (w + w') Lxpww' Lwpw' Lxpww' Lwpw'.
            prove x < ((x + w * w') * (x + w * w')) :/: ((w + w') * (w + w')).
            apply div_SNo_pos_LtR ((x + w * w') * (x + w * w')) ((w + w') * (w + w')) x (SNo_mul_SNo (x + w * w') (x + w * w') Lxpww' Lxpww') (SNo_mul_SNo (w + w') (w + w') Lwpw' Lwpw') Hx.
            * aby mul_SNo_pos_pos Lwpw' Hww'pos.
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
                { aby SNo_mul_SNo Lww' Hx. }
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
                { aby SNo_mul_SNo_3 Hw'1 Hw1 Hx. }
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
                aby SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_rotate_3_1 add_SNo_minus_Lt1b SNoLt_minus_pos SNo_mul_SNo mul_SNo_assoc mul_SNo_pos_neg mul_SNo_com_3_0_1 SNo_foil_mm Lww' Hw'3 Hw'1 Hw3 Hw1 Hx.
                - aby Hx.
                - aby Lww'.
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
        { aby SNo_mul_SNo Hz'1 Hz1. }
        claim Lxpzz': SNo (x + z * z').
        { aby SNo_add_SNo Lzz' Hx. }
        claim Lzpz': SNo (z + z').
        { aby SNo_add_SNo Hz'1 Hz1. }
        claim Ly: SNo y.
        { aby SNo_div_SNo Lzpz' Lxpzz' Hyzz'. }
        claim Lxpzz'nonneg: 0 <= x + z * z'.
        { aby SNo_0 add_SNo_Le3 add_SNo_0L mul_SNo_nonneg_nonneg Lzz' Hz'2 Hz'1 Hz2 Hz1 Hxnonneg Hx. }
        claim Lynonneg: 0 <= y.
        { aby SNoLtLe SNoLeE SNoLe_ref SNo_0 div_SNo_0_num div_SNo_pos_pos Lxpzz'nonneg Lzpz' Lxpzz' Hyzz' Hzz'pos. }
        apply and3I.
        - aby Ly.
        - aby Lynonneg.
        - prove x < y * y.
          rewrite Hyzz'.
          prove x < ((x + z * z') :/: (z + z')) * ((x + z * z') :/: (z + z')).
          rewrite mul_div_SNo_both (x + z * z') (z + z') (x + z * z') (z + z') Lxpzz' Lzpz' Lxpzz' Lzpz'.
          prove x < ((x + z * z') * (x + z * z')) :/: ((z + z') * (z + z')).
          apply div_SNo_pos_LtR ((x + z * z') * (x + z * z')) ((z + z') * (z + z')) x (SNo_mul_SNo (x + z * z') (x + z * z') Lxpzz' Lxpzz') (SNo_mul_SNo (z + z') (z + z') Lzpz' Lzpz') Hx.
          + aby mul_SNo_pos_pos Lzpz' Hzz'pos.
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
            { aby SNo_mul_SNo Lzz' Hx. }
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
            { aby SNo_mul_SNo_3 Hz'1 Hz1 Hx. }
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
            aby SNo_0 SNo_minus_SNo SNo_add_SNo add_SNo_com add_SNo_0L add_SNo_rotate_3_1 add_SNo_minus_Lt1b SNoLt_minus_pos SNo_mul_SNo mul_SNo_assoc mul_SNo_neg_pos mul_SNo_com_3_0_1 SNo_foil_mm Lzz' Hz'3 Hz'1 Hz3 Hz1 Hx.
            * aby Hx.
            * aby Lzz'.
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
aby and3I famunionE_impred omega_nat_p SNoLt_irref SNoLt_tra SNoLeLt_tra SNoLtLe_or SNo_mul_SNo nonneg_mul_SNo_Le2 H0 Hx.
Qed.

Theorem sqrt_SNo_nonneg_prop1c: forall x, SNo x -> 0 <= x ->
    SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1)
 -> (forall z :e (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1), forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p)
 -> 0 <= G x sqrt_SNo_nonneg.
aby EmptyE SNoLeE SNoLt_irref SNoLtLe_tra SNoCutP_0_0 SNoCut_Le SNo_0 SNoCut_0_0 mul_SNo_zeroR.
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
{ aby SNo_mul_SNo Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5. }
claim Lyynn: 0 <= y * y.
{ aby mul_SNo_nonneg_nonneg Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy. }
claim LL_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> L_ k c= L_ k'.
{ aby SNo_sqrtaux_mon. }
claim LR_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> R_ k c= R_ k'.
{ aby SNo_sqrtaux_mon. }
claim L1: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
{ aby sqrt_SNo_nonneg_prop1a Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon. }
claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
{ aby famunionE_impred omega_nat_p L1. }
claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
{ aby famunionE_impred omega_nat_p L1. }
apply SNoLtE (y * y) x Lyy Hx H6.
- aby ReplI famunionI SepI binintersectE2 nat_0 nat_p_omega tuple_2_0_eq SNoLtLe SNoLt_irref SNoLtLe_tra SNoLeLt_tra SNoS_I2 SNoL_I SNo_0 nonneg_mul_SNo_Le2 SNo_sqrtaux_0 Lyynn Lyy H3 H1 IH Hx.
- aby ReplI famunionI SepI nat_0 nat_p_omega tuple_2_0_eq SNoLt_irref SNoS_I2 SNoL_I SNo_nonneg_sqr_uniq SNo_sqrtaux_0 Lyynn Lyy H3 H1 H6 Hynn IH Hx.
- assume H7: SNoLev x :e SNoLev (y * y).
  assume H8: SNoEq_ (SNoLev x) (y * y) x.
  assume H9: SNoLev x /:e y * y.
  claim L3: x :e SNoR (y * y).
  { aby SNoR_I Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9. }
  claim L4: forall p:prop, (forall v :e L, forall w :e R, v * y + y * w <= x + v * w -> p) -> p.
  { aby add_SNo_com SNo_mul_SNo mul_SNo_com mul_SNo_SNoCut_SNoR_interpolate_impred L3 H1 HR HL HLR. }
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
      + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
      + prove v :e L_ k''.
        aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
      + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
    - assume H1: k'' c= k'.
      witness k'.
      apply and3I.
      + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
      + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
      + prove w :e R_ k'.
        aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
  }
  apply L5. let k. assume H. apply H. assume H. apply H.
  assume Hk: nat_p k.
  assume Hvk: v :e L_ k.
  assume Hwk: w :e R_ k.
  claim Lvwpos: 0 < v + w.
  { aby famunionI nat_p_omega SNoLeLt_tra SNo_0 SNo_add_SNo add_SNo_Lt2 add_SNo_0R Hwk Hk Hw1 Hv2 Hv1 H4 H1 Hynn. }
  claim Lvw0: v + w <> 0.
  { assume H. aby SNoLt_irref H Lvwpos. }
  claim L6: (x + v * w) :/: (v + w) :e L_ (ordsucc k).
  { aby binunionI2 tuple_2_0_eq SNo_sqrtauxset_I SNo_sqrtaux_S Lvwpos Hwk Hvk Hk. }
  claim L7: (x + v * w) :/: (v + w) :e L.
  { aby famunionI nat_ordsucc nat_p_omega Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L3 L4 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L5 H H Hk Hvk Hwk Lvwpos Lvw0 L6. }
  aby SNoLt_irref SNoLeLt_tra SNo_add_SNo SNo_mul_SNo mul_SNo_com mul_SNo_distrL pos_mul_SNo_Lt' SNo_div_SNo mul_div_SNo_invL L7 Lvw0 Lvwpos Hw1 Hv1 H10 H3 H1 Hx.
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
{ aby SNo_mul_SNo Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5. }
claim Lyynn: 0 <= y * y.
{ aby mul_SNo_nonneg_nonneg Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy. }
claim LL_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> L_ k c= L_ k'.
{ aby SNo_sqrtaux_mon. }
claim LR_mon: forall k k', nat_p k -> nat_p k' -> k c= k' -> R_ k c= R_ k'.
{ aby SNo_sqrtaux_mon. }
claim L1: forall k, nat_p k ->
              (forall y :e L_ k, SNo y /\ 0 <= y /\ y * y < x)
           /\ (forall y :e R_ k, SNo y /\ 0 <= y /\ x < y * y).
{ aby sqrt_SNo_nonneg_prop1a Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon. }
claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
{ aby famunionE_impred omega_nat_p L1. }
claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
{ aby famunionE_impred omega_nat_p L1. }
apply SNoLtE x (y * y) Hx Lyy H6.
- aby ReplI famunionI binintersectE1 nat_0 nat_p_omega tuple_2_1_eq SNoLtLe SNoLt_irref SNoLtLe_tra SNoLeLt_tra SNoS_I2 SNoR_I SNo_0 nonneg_mul_SNo_Le2 SNo_sqrtaux_0 Lyy H4 H1 Hynn IH Hxnonneg Hx.
- assume H7: SNoLev x :e SNoLev (y * y).
  assume H8: SNoEq_ (SNoLev x) x (y * y).
  assume H9: SNoLev x :e y * y.
  claim L10: x :e SNoL (y * y).
  { aby SNoL_I Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9. }
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
          + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
          + prove v :e L_ k''.
            aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
          + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
        - assume H1: k'' c= k'.
          witness k'.
          apply and3I.
          + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
          + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
          + prove w :e L_ k'.
            aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 H Hk'1 Hk'2 H Hk''1 Hk''2 H1. }
      apply L11. let k. assume H. apply H. assume H. apply H.
      assume Hk: nat_p k.
      assume Hvk: v :e L_ k.
      assume Hwk: w :e L_ k.
      claim Lvw0: v + w <> 0.
      { assume H. aby SNoLt_irref H H11. }
      claim L12: (x + v * w) :/: (v + w) :e R_ (ordsucc k).
      { aby binunionI1 binunionI2 tuple_2_1_eq SNo_sqrtauxset_I SNo_sqrtaux_S Hwk Hvk Hk H11. }
      claim L13: (x + v * w) :/: (v + w) :e R.
      { aby famunionI nat_ordsucc nat_p_omega Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H11 L11 H H Hk Hvk Hwk Lvw0 L12. }
      aby SNoLt_irref SNoLeLt_tra SNo_add_SNo SNo_mul_SNo mul_SNo_com mul_SNo_distrL pos_mul_SNo_Lt' SNo_div_SNo mul_div_SNo_invL L13 Lvw0 H11 Hw1 Hv1 H10 H4 H1 Hx.
    * aby SNoLt_irref SNoLe_antisym SNoLtLe_tra SNoLe_tra SNoLtLe_or SNo_0 SNo_add_SNo add_SNo_Le1 add_SNo_Le2 add_SNo_0L add_SNo_0R mul_SNo_zeroR mul_SNo_zeroL Hw2 Hw1 Hv3 Hv2 Hv1 H10 H1 Hxnonneg Hx.
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
        + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
        + prove v :e R_ k''.
          aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
        + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
      - assume H1: k'' c= k'.
        witness k'.
        apply and3I.
        + aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
        + aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1.
        + prove w :e R_ k'.
          aby omega_nat_p Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 H Hk'1 Hk'2 H Hk''1 Hk''2 H1. }
    apply L21. let k. assume H. apply H. assume H. apply H.
    assume Hk: nat_p k.
    assume Hvk: v :e R_ k.
    assume Hwk: w :e R_ k.
    claim Lvwpos: 0 < v + w.
    { aby famunionI nat_p_omega SNoLeLt_tra SNo_0 SNo_add_SNo add_SNo_Lt2 add_SNo_0R Hwk Hk Hw1 Hv2 Hv1 H4 H1 Hynn. }
    claim Lvw0: v + w <> 0.
    { assume H. aby SNoLt_irref H Lvwpos. }
    claim L22: (x + v * w) :/: (v + w) :e R_ (ordsucc k).
    { aby binunionI2 tuple_2_1_eq SNo_sqrtauxset_I SNo_sqrtaux_S Lvwpos Hwk Hvk Hk. }
    claim L23: (x + v * w) :/: (v + w) :e R.
    { aby famunionI nat_ordsucc nat_p_omega Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L21 H H Hk Hvk Hwk Lvwpos Lvw0 L22. }
    claim L24: y < (x + v * w) :/: (v + w).
    { aby Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L21 H H Hk Hvk Hwk Lvwpos Lvw0 L22 L23. }
    claim L25: v * y + y * w = y * (v + w).
    { transitivity y * v + y * w.
      - f_equal. prove v * y = y * v. aby mul_SNo_com Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L21 H H Hk Hvk Hwk Lvwpos Lvw0 L22 L23 L24.
      - prove y * v + y * w = y * (v + w).
        aby mul_SNo_distrL Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L21 H H Hk Hvk Hwk Lvwpos Lvw0 L22 L23 L24.
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
    aby SNo_add_SNo SNo_mul_SNo pos_mul_SNo_Lt' SNo_div_SNo Hx Hxnonneg IH HLR Hynn H6 HLHR HL HR HLR' H1 H2 H3 H4 H5 Lyy Lyynn LL_mon LR_mon L1 L1L L1R H7 H8 H9 L10 Hv Hw H10 Hv1 Hv2 Hv3 Hw1 Hw2 Hw3 L21 H H Hk Hvk Hwk Lvwpos Lvw0 L22 L23 L24 L25.
- aby ReplI famunionI nat_0 nat_p_omega tuple_2_1_eq SNoLt_irref SNoS_I2 SNoR_I SNo_nonneg_sqr_uniq SNo_sqrtaux_0 Lyynn Lyy H4 H1 H6 Hynn IH Hx.
Qed.

Theorem sqrt_SNo_nonneg_prop1: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x) /\ 0 <= sqrt_SNo_nonneg x /\ sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
apply SNoLev_ind.
let x. assume Hx: SNo x.
assume IH: forall w :e SNoS_ (SNoLev x), 0 <= w -> SNo (sqrt_SNo_nonneg w) /\ 0 <= sqrt_SNo_nonneg w /\ sqrt_SNo_nonneg w * sqrt_SNo_nonneg w = w.
assume Hxnonneg: 0 <= x.
prove SNo (sqrt_SNo_nonneg x) /\ 0 <= sqrt_SNo_nonneg x /\ sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
aby and3I famunionE_impred omega_nat_p SNoLt_trichotomy_or_impred SNoCutP_SNoCut_impred SNo_mul_SNo mul_SNo_nonneg_nonneg SNo_sqrtaux_mon sqrt_SNo_nonneg_eq sqrt_SNo_nonneg_prop1a sqrt_SNo_nonneg_prop1b sqrt_SNo_nonneg_prop1c sqrt_SNo_nonneg_prop1d sqrt_SNo_nonneg_prop1e Hxnonneg IH Hx.
Qed.

End sqrt_SNo_nonneg.

Theorem SNo_sqrtaux_0_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
      (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x)
   /\ (forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y).
aby SNoLev_ordinal SNoS_E2 sqrt_SNo_nonneg_prop1a sqrt_SNo_nonneg_prop1.
Qed.

Theorem SNo_sqrtaux_0_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 0, SNo y /\ 0 <= y /\ y * y < x.
aby SNo_sqrtaux_0_1_prop.
Qed.

Theorem SNo_sqrtaux_1_prop: forall x, SNo x -> 0 <= x ->
  forall k, nat_p k ->
  forall y :e SNo_sqrtaux x sqrt_SNo_nonneg k 1, SNo y /\ 0 <= y /\ x < y * y.
aby SNo_sqrtaux_0_1_prop.
Qed.

Theorem SNo_sqrt_SNo_SNoCutP: forall x, SNo x -> 0 <= x ->
  SNoCutP (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0)
          (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1).
aby sqrt_SNo_nonneg_prop1b SNo_sqrtaux_0_1_prop.
Qed.

Theorem SNo_sqrt_SNo_nonneg: forall x, SNo x -> 0 <= x -> SNo (sqrt_SNo_nonneg x).
aby sqrt_SNo_nonneg_prop1.
Qed.

Theorem sqrt_SNo_nonneg_nonneg: forall x, SNo x -> 0 <= x -> 0 <= sqrt_SNo_nonneg x.
aby sqrt_SNo_nonneg_prop1.
Qed.

Theorem sqrt_SNo_nonneg_sqr: forall x, SNo x -> 0 <= x -> sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
aby sqrt_SNo_nonneg_prop1.
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
  - aby Repl_Empty tuple_2_0_eq tuple_2_1_eq SNoR_0 SNoL_nonneg_0 SNo_sqrtaux_0.
  - aby binunion_idl tuple_2_0_eq tuple_2_1_eq SNo_sqrtauxset_0 SNo_sqrtaux_S.
}
aby EmptyE Empty_eq famunionE_impred omega_nat_p SNoCut_0_0 L1.
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
      aby set_ext ReplI ReplE_impred In_0_1 cases_1 sqrt_SNo_nonneg_0.
    + aby Repl_Empty tuple_2_1_eq SNoR_1 SNo_sqrtaux_0.
  - let k. assume Hk.
    assume IHk. apply IHk.
    aby Empty_eq binunion_idl binunion_idr cases_1 tuple_2_0_eq tuple_2_1_eq SNoLt_irref SNo_0 add_SNo_0R SNo_sqrtauxset_E SNo_sqrtauxset_0 SNo_sqrtauxset_0' SNo_sqrtaux_S Hk.
}
claim L2: L = 1.
{ apply set_ext.
  - aby famunionE_impred omega_nat_p L1.
  - aby famunionI In_0_1 nat_0 cases_1 nat_p_omega L1.
}
aby EmptyE Empty_eq famunionE_impred omega_nat_p SNo_eta SNo_1 SNoL_1 SNoR_1 L2 L1.
Qed.

Theorem sqrt_SNo_nonneg_0inL0: forall x, SNo x -> 0 <= x -> 0 :e SNoLev x -> 0 :e SNo_sqrtaux x sqrt_SNo_nonneg 0 0.
aby EmptyE ReplI SepI tuple_2_0_eq SNoLeE SNoLe_ref SNoL_I SNo_0 SNoLev_0 SNo_sqrtaux_0 sqrt_SNo_nonneg_0.
Qed.

Theorem sqrt_SNo_nonneg_Lnonempty: forall x, SNo x -> 0 <= x -> 0 :e SNoLev x -> (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0) <> 0.
aby EmptyE famunionI nat_0 nat_p_omega sqrt_SNo_nonneg_0 sqrt_SNo_nonneg_0inL0.
Qed.

Theorem sqrt_SNo_nonneg_Rnonempty: forall x, SNo x -> 0 <= x -> 1 :e SNoLev x -> (\/_ k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1) <> 0.
let x. assume Hx Hxnn H1.
set L_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
set R_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
set L := \/_ k :e omega, L_ k.
set R := \/_ k :e omega, R_ k.
prove R <> 0.
assume H2: R = 0.
apply SNoLt_trichotomy_or_impred x 1 Hx SNo_1.
- aby EmptyE ReplI famunionI nat_0 nat_1 nat_p_ordinal nat_p_omega tuple_2_1_eq SNoR_I ordinal_SNoLev SNo_1 SNo_sqrtaux_0 H2 H1 Hx.
- aby In_irref nat_1 nat_p_ordinal ordinal_SNoLev H1.
- assume H3: 1 < x.
  claim L3: 1 :e SNoL_nonneg x.
  { aby SepI nat_1 nat_p_ordinal SNoLtLe SNoL_I ordinal_SNoLev SNo_1 SNoLt_0_1 H3 H1 Hx. }
  claim L4: (x + 1 * 0) :/: (1 + 0) :e R_ 1.
  { prove (x + 1 * 0) :/: (1 + 0) :e SNo_sqrtaux x sqrt_SNo_nonneg 1 1.
    rewrite SNo_sqrtaux_S x sqrt_SNo_nonneg 0 nat_0.
    aby ReplI binunionI1 binunionI2 In_0_1 ordinal_TransSet tuple_2_0_eq tuple_2_1_eq SNoLev_ordinal SNo_1 SNoLt_0_1 add_SNo_0R SNo_sqrtauxset_I SNo_sqrtaux_0 sqrt_SNo_nonneg_1 sqrt_SNo_nonneg_0inL0 L3 H1 Hxnn Hx.
  }
  aby EmptyE famunionI nat_1 nat_p_omega L4 H2.
Qed.

Theorem SNo_sqrtauxset_real: forall Y Z x, Y c= real -> Z c= real -> x :e real -> SNo_sqrtauxset Y Z x c= real.
aby famunionE_impred ReplSepE_impred real_add_SNo real_mul_SNo real_div_SNo.
Qed.

Theorem SNo_sqrtauxset_real_nonneg: forall Y Z x, Y c= {w :e real|0 <= w} -> Z c= {z :e real|0 <= z} -> x :e real -> 0 <= x -> SNo_sqrtauxset Y Z x c= {w :e real|0 <= w}.
let Y Z x. assume HY HZ Hx Hxnneg.
prove (\/_ y :e Y, {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}) c= {w :e real|0 <= w}.
claim LY: Y c= real.
{ aby SepE1 HY. }
claim LZ: Z c= real.
{ aby SepE1 HZ. }
claim LxS: SNo x.
{ aby real_SNo Hx. }
let w. assume Hw.
apply SepI.
- aby SNo_sqrtauxset_real Hw LZ LY Hx.
- prove 0 <= w.
  apply famunionE_impred Y (fun y => {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}) w Hw.
  let y.
  assume Hy: y :e Y.
  assume Hw2: w :e {(x + y * z) :/: (y + z)|z :e Z, 0 < y + z}.
  apply ReplSepE_impred Z (fun z => 0 < y + z) (fun z => (x + y * z) :/: (y + z)) w Hw2.
  aby SepE SNoLtLe SNoLeE SNoLe_ref SNo_0 SNo_add_SNo add_SNo_Le3 add_SNo_0R SNo_mul_SNo mul_SNo_zeroR mul_SNo_zeroL mul_SNo_pos_pos div_SNo_0_num div_SNo_pos_pos real_SNo Hy LxS Hxnneg Hx HZ HY.
Qed.

Theorem sqrt_SNo_nonneg_SNoS_omega: forall x :e SNoS_ omega, 0 <= x -> sqrt_SNo_nonneg x :e real.
claim L1: forall x, SNo x -> SNoLev x :e omega -> 0 <= x -> sqrt_SNo_nonneg x :e real.
{ apply SNoLev_ind.
  let x. assume Hx: SNo x.
  assume IH: forall w :e SNoS_ (SNoLev x), SNoLev w :e omega -> 0 <= w -> sqrt_SNo_nonneg w :e real.
  assume Hx1: SNoLev x :e omega.
  assume Hx2: 0 <= x.
  claim Lx: x :e real.
  { aby omega_ordinal SNoLev_ SNoS_I SNoS_omega_real Hx1 Hx. }
  prove sqrt_SNo_nonneg x :e real.
  apply ordinal_In_Or_Subq 0 (SNoLev x) ordinal_Empty (SNoLev_ordinal x Hx).
  - assume H1: 0 :e SNoLev x.
    apply ordinal_In_Or_Subq 1 (SNoLev x) ordinal_1 (SNoLev_ordinal x Hx).
    + assume H2: 1 :e SNoLev x.
      prove sqrt_SNo_nonneg x :e real.
      rewrite sqrt_SNo_nonneg_eq x Hx.
      set L_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
      set R_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
      set L := \/_ k :e omega, L_ k.
      set R := \/_ k :e omega, R_ k.
      prove SNoCut L R :e real.
      claim L_L_R_real: forall k, nat_p k -> L_ k c= real /\ R_ k c= real.
      { prove forall k, nat_p k ->
                   SNo_sqrtaux x sqrt_SNo_nonneg k 0 c= real
                /\ SNo_sqrtaux x sqrt_SNo_nonneg k 1 c= real.
        apply nat_ind.
        - aby ReplE_impred SepE omega_TransSet tuple_2_0_eq tuple_2_1_eq SNoLtLe SNoLeLt_tra SNoS_I2 SNoL_E SNoR_E SNo_0 SNo_sqrtaux_0 Hx2 Hx1 IH Hx.
        - aby binunion_Subq_min tuple_2_0_eq tuple_2_1_eq SNo_sqrtaux_S SNo_sqrtauxset_real Lx.
      }
      claim L1L: forall w :e L, forall p:prop, (SNo w -> 0 <= w -> w * w < x -> p) -> p.
      { aby famunionE_impred omega_nat_p SNo_sqrtaux_0_prop Hx2 Hx. }
      claim L1R: forall z :e R, forall p:prop, (SNo z -> 0 <= z -> x < z * z -> p) -> p.
      { aby famunionE_impred omega_nat_p SNo_sqrtaux_1_prop Hx2 Hx. }
      claim LLR: SNoCutP L R.
      { aby SNo_sqrt_SNo_SNoCutP Hx IH Hx1 Hx2 Lx H1 H2 L_L_R_real L1L L1R. }
      apply LLR.
      assume HLHR. apply HLHR.
      assume HL: forall w :e L, SNo w.
      assume HR: forall z :e R, SNo z.
      assume HLR: forall w :e L, forall z :e R, w < z.
      apply real_SNoCut.
      * aby famunionE_impred omega_nat_p L_L_R_real.
      * aby famunionE_impred omega_nat_p L_L_R_real.
      * aby LLR.
      * aby sqrt_SNo_nonneg_Lnonempty H1 Hx2 Hx.
      * aby sqrt_SNo_nonneg_Rnonempty H2 Hx2 Hx.
      * prove forall w :e L, exists w' :e L, w < w'.
        let w. assume Hw.
        apply famunionE_impred omega L_ w Hw.
        let k. assume Hk: k :e omega.
        assume H3: w :e L_ k.
        apply L1L w Hw.
        assume Hw1: SNo w.
        assume Hw2: 0 <= w.
        assume Hw3: w * w < x.
        claim Lwmw: SNo (w * w).
        { aby SNo_mul_SNo Hw1. }
        claim Lwpw: SNo (w + w).
        { aby SNo_add_SNo Hw1. }
        claim L1a: exists z, z :e R_ (ordsucc k).
        { apply SNoLt_trichotomy_or_impred x 1 Hx SNo_1.
          - aby Subq_Empty ReplI SepI nat_0 nat_ordsucc ordinal_1 omega_nat_p tuple_2_1_eq SNoS_I2 ordinal_SNoLev SNo_1 SNo_sqrtaux_0 SNo_sqrtaux_mon sqrt_SNo_nonneg_1 Hk H2 Hx.
          - aby In_irref ordinal_1 ordinal_SNoLev H2.
          - assume H4: 1 < x.
            claim L1a1: 1 :e L_ k.
            { aby Subq_Empty ReplI SepI nat_0 ordinal_1 omega_nat_p tuple_2_0_eq SNoLtLe SNoS_I2 ordinal_SNoLev SNo_1 SNoLt_0_1 SNo_sqrtaux_0 SNo_sqrtaux_mon sqrt_SNo_nonneg_1 H4 Hk H2 Hx. }
            aby binunionI1 binunionI2 omega_nat_p tuple_2_1_eq SNoLt_0_2 add_SNo_1_1_2 SNo_sqrtauxset_I SNo_sqrtaux_S L1a1 Hk.
        }
        apply L1a.
        let z. assume Hz: z :e R_ (ordsucc k).
        claim Lz: z :e R.
        { aby famunionI omega_ordsucc Hx IH Hx1 Hx2 Lx H1 H2 L_L_R_real L1L L1R LLR HLHR HL HR HLR Hw Hk H3 Hw1 Hw2 Hw3 Lwmw Lwpw L1a Hz. }
        apply L1R z Lz.
        assume Hz1: SNo z.
        assume Hz2: 0 <= z.
        assume Hz3: x < z * z.
        claim Lwmz: SNo (w * z).
        { aby SNo_mul_SNo Hz1 Hw1. }
        claim Lwpz: SNo (w + z).
        { aby SNo_add_SNo Hz1 Hw1. }
        claim Lzpos: 0 < z.
        { aby SNoLeE SNoLt_irref SNoLeLt_tra SNo_0 mul_SNo_zeroR Hz3 Hz2 Hz1 Hx2 Hx. }
        claim Lwpzpos: 0 < w + z.
        { aby SNoLtLe_tra SNo_0 add_SNo_Le1 add_SNo_0L Lzpos Lwpz Hz1 Hw2 Hw1. }
        claim Lwpzn0: w + z <> 0.
        { assume H4: w + z = 0.
          aby SNoLt_irref H4 Lwpzpos.
        }
        set w' := (x + w * z) :/: (w + z).
        claim Lw': w' :e L_ (ordsucc (ordsucc k)).
        { prove w' :e SNo_sqrtaux x sqrt_SNo_nonneg (ordsucc (ordsucc k)) 0.
          aby binunionI2 ordsuccI1 nat_ordsucc omega_nat_p tuple_2_0_eq SNo_sqrtauxset_I SNo_sqrtaux_S SNo_sqrtaux_mon Lwpzpos Hz H3 Hk.
        }
        aby famunionI omega_ordsucc SNo_add_SNo add_SNo_Lt1 SNo_mul_SNo mul_SNo_distrL pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_of_pos_is_pos div_mul_SNo_invL Lw' Lwpzn0 Lwpzpos Lwpz Lwmz Hz1 Lwmw Hw3 Hw1 Hk Hx.
      * { prove forall z :e R, exists z' :e R, z' < z.
          let z. assume Hz.
          apply famunionE_impred omega R_ z Hz.
          let k. assume Hk: k :e omega.
          assume H3: z :e R_ k.
          apply L1R z Hz.
          assume Hz1: SNo z.
          assume Hz2: 0 <= z.
          assume Hz3: x < z * z.
          claim Lzmz: SNo (z * z).
          { aby SNo_mul_SNo Hz1. }
          claim Lzpz: SNo (z + z).
          { aby SNo_add_SNo Hz1. }
          claim Lzpos: 0 < z.
          { aby SNoLeE SNoLt_irref SNoLeLt_tra SNo_0 mul_SNo_zeroR Hz3 Hz2 Hz1 Hx2 Hx. }
          claim Lzpzpos: 0 < z + z.
          { aby SNo_0 add_SNo_Lt3 add_SNo_0L Lzpos Hz1. }
          claim Lzpzn0: z + z <> 0.
          { assume H4: z + z = 0.
            aby SNoLt_irref H4 Lzpzpos.
          }
          set z' := (x + z * z) :/: (z + z).
          claim Lz': z' :e R_ (ordsucc k).
          { aby binunionI2 omega_nat_p tuple_2_1_eq SNo_sqrtauxset_I SNo_sqrtaux_S Lzpzpos H3 Hk. }
          aby famunionI omega_ordsucc SNo_add_SNo add_SNo_Lt1 SNo_mul_SNo mul_SNo_distrL pos_mul_SNo_Lt' SNo_recip_SNo recip_SNo_of_pos_is_pos div_mul_SNo_invL Lz' Lzpzn0 Lzpzpos Lzpz Lzmz Hz3 Hz1 Hk Hx.
          }
    + aby set_ext EmptyE dneg cases_1 ordinal_1 SNo_eq SNoLtI3 SNoLt_irref SNoLeLt_tra ordinal_SNoLev SNo_0 SNo_1 SNoLev_0 real_1 sqrt_SNo_nonneg_1 H1 Hx2 Hx.
  - aby Empty_Subq_eq SNoLev_0_eq_0 real_0 sqrt_SNo_nonneg_0 Hx.
}
aby omega_ordinal SNoS_E2 L1.
Qed.

Theorem sqrt_SNo_nonneg_real: forall x :e real, 0 <= x -> sqrt_SNo_nonneg x :e real.
let x. assume Hx Hxnn.
apply real_E x Hx.
assume Hx1: SNo x.
assume Hx2: SNoLev x :e ordsucc omega.
assume Hx3: x :e SNoS_ (ordsucc omega).
assume Hx4: - omega < x.
assume Hx5: x < omega.
assume Hx6: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
assume Hx7: forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
apply sqrt_SNo_nonneg_prop1 x Hx1 Hxnn. assume H. apply H.
assume H1: SNo (sqrt_SNo_nonneg x).
assume H2: 0 <= sqrt_SNo_nonneg x.
assume H3: sqrt_SNo_nonneg x * sqrt_SNo_nonneg x = x.
apply ordsuccE omega (SNoLev x) Hx2.
- aby omega_ordinal SNoLev_ SNoS_I sqrt_SNo_nonneg_SNoS_omega Hx1 Hxnn.
- assume H4: SNoLev x = omega.
  prove sqrt_SNo_nonneg x :e real.
  rewrite sqrt_SNo_nonneg_eq x Hx1.
  set L_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 0.
  set R_ := fun k:set => SNo_sqrtaux x sqrt_SNo_nonneg k 1.
  set L := \/_ k :e omega, L_ k.
  set R := \/_ k :e omega, R_ k.
  prove SNoCut L R :e real.
  claim LLI: forall k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 0 c= L.
  { aby famunionI. }
  claim LRI: forall k :e omega, SNo_sqrtaux x sqrt_SNo_nonneg k 1 c= R.
  { aby famunionI. }
  claim LLE: forall w :e L, forall p:prop, (forall k :e omega, w :e SNo_sqrtaux x sqrt_SNo_nonneg k 0 -> p) -> p.
  { aby famunionE_impred. }
  claim LRE: forall z :e R, forall p:prop, (forall k :e omega, z :e SNo_sqrtaux x sqrt_SNo_nonneg k 1 -> p) -> p.
  { aby famunionE_impred. }
  claim L_L_Subq: forall k, nat_p k -> L_ k c= L_ (ordsucc k).
  { aby binunionI1 tuple_2_0_eq SNo_sqrtaux_S. }
  claim L_R_Subq: forall k, nat_p k -> R_ k c= R_ (ordsucc k).
  { aby binunionI1 tuple_2_1_eq SNo_sqrtaux_S. }
  claim L_L_R_Subq: forall k, nat_p k -> forall k' :e k, L_ k' c= L_ k /\ R_ k' c= R_ k.
  { prove forall k, nat_p k ->
          forall k' :e k,
               SNo_sqrtaux x sqrt_SNo_nonneg k' 0 c= SNo_sqrtaux x sqrt_SNo_nonneg k 0
            /\ SNo_sqrtaux x sqrt_SNo_nonneg k' 1 c= SNo_sqrtaux x sqrt_SNo_nonneg k 1.
    apply nat_ind.
    - aby EmptyE.
    - aby Subq_tra ordsuccE L_R_Subq L_L_Subq.
  }
  claim L_L_R_real: forall k, nat_p k -> L_ k c= {w :e real|0 <= w} /\ R_ k c= {w :e real|0 <= w}.
  { prove forall k, nat_p k ->
               SNo_sqrtaux x sqrt_SNo_nonneg k 0 c= {w :e real|0 <= w}
            /\ SNo_sqrtaux x sqrt_SNo_nonneg k 1 c= {w :e real|0 <= w}.
    apply nat_ind.
    - rewrite SNo_sqrtaux_0. rewrite tuple_2_0_eq. rewrite tuple_2_1_eq.
      apply andI.
      + aby ReplE_impred SepI SepE omega_ordinal SNoLev_ SNoS_I SNoL_E sqrt_SNo_nonneg_nonneg sqrt_SNo_nonneg_SNoS_omega H4 Hx1.
      + aby ReplE_impred SepI omega_ordinal SNoLev_ SNoLtLe SNoLeLt_tra SNoS_I SNoR_E SNo_0 sqrt_SNo_nonneg_nonneg sqrt_SNo_nonneg_SNoS_omega H4 Hx1 Hxnn.
    - aby binunion_Subq_min tuple_2_0_eq tuple_2_1_eq SNo_sqrtaux_S SNo_sqrtauxset_real_nonneg Hxnn Hx.
  }
  claim LLsR: L c= real.
  { aby SepE1 omega_nat_p L_L_R_real LLE. }
  claim LRsR: R c= real.
  { aby SepE1 omega_nat_p L_L_R_real LRE. }
  claim LLR: SNoCutP L R.
  { aby SNo_sqrt_SNo_SNoCutP Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR. }
  apply SNoCutP_SNoCut_impred L R LLR.
  rewrite <- sqrt_SNo_nonneg_eq x Hx1.
  assume HLR1 HLR2.
  assume HLR3: forall w :e L, w < sqrt_SNo_nonneg x.
  assume HLR4: forall z :e R, sqrt_SNo_nonneg x < z.
  assume HLR5.
  claim L0Lx: 0 :e SNoLev x.
  { aby nat_0 nat_p_omega H4. }
  claim L1Lx: 1 :e SNoLev x.
  { aby nat_1 nat_p_omega H4. }
  claim LLne: L <> 0.
  { aby sqrt_SNo_nonneg_Lnonempty Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx. }
  claim LRne: R <> 0.
  { aby sqrt_SNo_nonneg_Rnonempty Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne. }
  prove SNoCut L R :e real.
  claim LRE': forall z :e R, SNo z /\ 0 < z.
  { aby SNoLeLt_tra SNo_0 real_SNo HLR4 LRsR H2 H1. }
  claim LLnomax: forall w :e L, exists w' :e L, w < w'.
  { let w. assume Hw. apply LLE w Hw.
    let k. assume Hk.
    assume Hwk: w :e L_ k.
    apply L_L_R_real k (omega_nat_p k Hk).
    assume H _.
    apply SepE real (fun w => 0 <= w) w (H w Hwk).
    assume HwR: w :e real.
    assume Hwnn: 0 <= w.
    claim Lw: SNo w.
    { aby real_SNo HwR. }
    apply xm (exists z, z :e R).
    - assume H5. apply H5.
      let z. assume Hz: z :e R.
      apply LRE z Hz.
      let k'. assume Hk'.
      assume Hzk': z :e R_ k'.
      apply LRE' z Hz.
      assume HzS: SNo z.
      assume Hzpos: 0 < z.
      apply L_L_R_real k' (omega_nat_p k' Hk').
      assume _ H.
      claim LzR: z :e real.
      { aby SepE1 Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H. }
      claim Lz: SNo z.
      { aby real_SNo LzR. }
      claim Lzpos: 0 < z.
      { aby SNoLeLt_tra SNo_0 Lz Hz HLR4 H2 H1. }
      claim Lwz: SNo (w + z).
      { aby SNo_add_SNo Lz Lw. }
      claim Lwmz: SNo (w * z).
      { aby SNo_mul_SNo Lz Lw. }
      claim Lwzpos: 0 < w + z.
      { aby SNo_0 add_SNo_Lt3b add_SNo_0R Lzpos Lz Lw Hwnn. }
      set w' := (x + w * z) :/: (w + z).
      witness w'. apply andI.
      + prove w' :e L.
        claim Lwzk'': exists k'' :e omega, w :e L_ k'' /\ z :e R_ k''.
        { apply ordinal_trichotomy_or_impred k k' (nat_p_ordinal k (omega_nat_p k Hk)) (nat_p_ordinal k' (omega_nat_p k' Hk')).
          - assume H6: k :e k'. witness k'. apply andI.
            + aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
            + apply andI.
              * prove w :e L_ k'.
                apply L_L_R_Subq k' (omega_nat_p k' Hk') k H6.
                assume H _. aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6 H.
              * aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
          - assume H6: k = k'. witness k. apply andI.
            + aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
            + apply andI.
              * aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
              * prove z :e R_ k. rewrite H6. aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
          - assume H6: k' :e k. witness k. apply andI.
            + aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
            + apply andI.
              * aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6.
              * prove z :e R_ k.
                apply L_L_R_Subq k (omega_nat_p k Hk) k' H6.
                assume _ H. aby Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' Hw Hk Hwk H HwR Hwnn Lw H5 Hz Hk' Hzk' HzS Hzpos H LzR Lz Lzpos Lwz Lwmz Lwzpos H6 H. }
        aby binunionI2 famunionI omega_nat_p omega_ordsucc tuple_2_0_eq SNo_sqrtauxset_I SNo_sqrtaux_S Lwzk'' Lwzpos.
      + aby SNoLeE SNo_0 SNo_add_SNo add_SNo_Lt1 SNo_mul_SNo mul_SNo_zeroR mul_SNo_distrL pos_mul_SNo_Lt2 mul_SNo_pos_pos div_SNo_pos_LtR Lwzpos Lwmz Lwz HzS Lw Hwnn Hw HLR3 H3 H1 Hx1.
    - aby Empty_eq LRne.
  }
  claim LRnomin: forall z :e R, exists z' :e R, z' < z.
  { let z. assume Hz. apply LRE z Hz.
    let k. assume Hk.
    assume Hzk: z :e R_ k.
    apply LRE' z Hz.
    assume HzS: SNo z.
    assume Hzpos: 0 < z.
    claim Lzz: SNo (z + z).
    { aby SNo_add_SNo HzS. }
    claim Lzzpos: 0 < z + z.
    { aby SNo_0 add_SNo_Lt3 add_SNo_0R Hzpos HzS. }
    claim Lzzn0: z + z <> 0.
    { assume H5. aby SNoLt_irref H5 Lzzpos. }
    claim Lzmz: SNo (z * z).
    { aby SNo_mul_SNo HzS. }
    set z' := (x + z * z) :/: (z + z).
    claim Lz': z' :e R_ (ordsucc k).
    { aby binunionI2 omega_nat_p tuple_2_1_eq SNo_sqrtauxset_I SNo_sqrtaux_S Lzzpos Hzk Hk. }
    aby famunionI omega_ordsucc SNoLeE SNo_0 SNo_add_SNo add_SNo_Lt1 mul_SNo_zeroR mul_SNo_distrL pos_mul_SNo_Lt2 mul_SNo_pos_pos div_SNo_pos_LtL real_SNo Lz' Lzmz Lzzpos Lzz Hzpos HzS Hk Hz HLR4 LRsR H3 H2 H1 Hx1.
  }
  aby real_SNoCut Hx Hxnn Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 H H1 H2 H3 H4 LLI LRI LLE LRE L_L_Subq L_R_Subq L_L_R_Subq L_L_R_real LLsR LRsR LLR HLR1 HLR2 HLR3 HLR4 HLR5 L0Lx L1Lx LLne LRne LRE' LLnomax LRnomin.
Qed.

End SurrealSqrt.
Opaque sqrt_SNo_nonneg.

Section form100_1.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

Theorem divides_int_div_SNo_int: forall m n, divides_int m n -> n :/: m :e int.
aby xm nat_0 nat_p_omega mul_SNo_nonzero_cancel int_SNo Subq_omega_int mul_SNo_nonzero_cancel_L SNo_div_SNo div_SNo_0_denum mul_div_SNo_invR.
Qed.

(** If m times m = 2 times n times n for naturals m and n, then n = 0. **)
Theorem form100_1_lem1 : forall m, nat_p m -> forall n, nat_p n -> m * m = 2 * n * n -> n = 0.
apply nat_complete_ind.
let m.
assume Hm: nat_p m.
assume IHm: forall m' :e m, forall n, nat_p n -> m' * m' = 2 * n * n -> n = 0.
let n.
assume Hn: nat_p n.
assume H1: m * m = 2 * n * n.
claim Ln: n :e omega.
{ aby nat_p_omega Hn. }
claim LnS: SNo n.
{ aby nat_p_SNo Hn. }
apply SNoLeE 0 n SNo_0 LnS (omega_nonneg n Ln).
- assume H2: 0 < n.
  prove False.
  claim LnZ: n :e int.
  { aby Subq_omega_int Hm IHm Hn H1 Ln LnS H2. }
  claim LnnS: SNo (n * n).
  { aby SNo_mul_SNo LnS. }
  claim Lm: m :e omega.
  { aby nat_p_omega Hm. }
  claim LmZ: m :e int.
  { aby Subq_omega_int Hm IHm Hn H1 Ln LnS H2 LnZ LnnS Lm. }
  claim LmS: SNo m.
  { aby nat_p_SNo Hm. }
  claim Lmpos: 0 < m.
  { aby SNoLeE SNoLt_irref omega_nonneg SNo_0 SNo_2 SNoLt_0_2 mul_SNo_zeroR mul_SNo_pos_pos LmS Lm LnnS H2 LnS H1. }
  claim Lm2pos: 0 < m :/: 2.
  { aby SNo_2 SNoLt_0_2 div_SNo_pos_pos Lmpos LmS. }
  claim Ln2pos: 0 < n :/: 2.
  { aby SNo_2 SNoLt_0_2 div_SNo_pos_pos H2 LnS. }
  claim L2mm: divides_int 2 (m * m).
  { aby nat_2 nat_p_omega mul_SNo_In_omega Subq_omega_int divides_int_ref divides_int_mul_SNo_L Ln H1. }
  claim L2m: divides_int 2 m.
  { aby Euclid_lemma prime_nat_2 L2mm LmZ. }
  claim Lm2Z: m :/: 2 :e int.
  { aby divides_int_div_SNo_int L2m. }
  claim Lm2N: nat_p (m :/: 2).
  { aby SNoLtLe nonneg_int_nat_p Lm2Z Lm2pos. }
  claim Lm2S: SNo (m :/: 2).
  { aby nat_p_SNo Lm2N. }
  claim Lm2m: m :/: 2 :e m.
  { aby nat_p_ordinal ordinal_SNoLt_In SNo_1 SNo_2 SNoLt_0_2 SNo_minus_SNo add_SNo_minus_SNo_rinv add_SNo_1_1_2 add_SNo_minus_R2 add_SNo_Lt1_cancel SNo_mul_SNo mul_SNo_oneR mul_SNo_minus_distrR mul_SNo_distrL mul_minus_SNo_distrR div_SNo_pos_LtL Lm2N Lmpos LmS Hm. }
  claim L2nn: divides_int 2 (n * n).
  { aby and3I nat_2 neq_2_0 nat_p_omega SNo_2 mul_SNo_com mul_SNo_assoc Subq_omega_int int_mul_SNo mul_div_SNo_invR mul_div_SNo_L div_mul_SNo_invL Lm2S Lm2Z LmS LnnS LnZ H1. }
  claim L2n: divides_int 2 n.
  { aby Euclid_lemma prime_nat_2 L2nn LnZ. }
  claim Ln2Z: n :/: 2 :e int.
  { aby divides_int_div_SNo_int L2n. }
  claim Ln2N: nat_p (n :/: 2).
  { aby SNoLtLe nonneg_int_nat_p Ln2Z Ln2pos. }
  aby SNoLt_irref SNo_2 SNoLt_0_2 SNo_mul_SNo mul_div_SNo_L mul_div_SNo_both div_SNo_pos_pos Ln2N Lm2m LmS LnnS H2 LnS H1 IHm.
- aby.
Qed.

(** There are no nonzero naturals m and n such that m times m = 2 times n times n. **)
Theorem form100_1_lem2 : forall m :e omega, forall n :e omega :\: 1, m * m <> 2 * n * n.
aby setminusE In_0_1 omega_nat_p form100_1_lem1.
Qed.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

Theorem sqrt_2_irrational: sqrt_SNo_nonneg 2 :e real :\: rational.
claim LS2R: sqrt_SNo_nonneg 2 :e real.
{ aby nat_2 nat_p_omega SNoLtLe omega_SNoS_omega SNoLt_0_2 SNoS_omega_real sqrt_SNo_nonneg_real. }
claim LS2: SNo (sqrt_SNo_nonneg 2).
{ aby real_SNo LS2R. }
claim LS2nn: 0 <= sqrt_SNo_nonneg 2.
{ aby SNoLtLe SNo_2 SNoLt_0_2 sqrt_SNo_nonneg_nonneg. }
claim LS2pos: 0 < sqrt_SNo_nonneg 2.
{ aby neq_0_2 SNoLtLe SNoLeE SNo_0 SNo_2 SNoLt_0_2 mul_SNo_zeroR sqrt_SNo_nonneg_sqr LS2nn LS2. }
apply setminusI.
- aby LS2R.
- assume H1: sqrt_SNo_nonneg 2 :e rational.
  apply SepE real (fun x => exists m :e int, exists n :e omega :\: {0}, x = m :/: n) (sqrt_SNo_nonneg 2) H1.
  assume H2: sqrt_SNo_nonneg 2 :e real.
  assume H3: exists m :e int, exists n :e omega :\: {0}, sqrt_SNo_nonneg 2 = m :/: n.
  claim LnQ: forall m :e int, forall n :e omega :\: {0}, sqrt_SNo_nonneg 2 <> m :/: n.
  { apply int_SNo_cases.
    - aby SingI setminusE eq_1_Sing0 omega_nat_p SNoLtLe omega_SNo SNo_2 SNoLt_0_2 mul_SNo_com_4_inner_mid mul_div_SNo_invL sqrt_SNo_nonneg_sqr form100_1_lem2 LS2.
    - aby SingI setminusE SNoLtLe SNoLeE SNoLt_irref SNoLe_ref SNoLtLe_tra omega_SNo omega_nonneg SNo_0 SNo_minus_SNo minus_SNo_Lt_contra1 minus_SNo_0 div_SNo_0_num div_SNo_neg_pos LS2pos LS2.
  }
  aby LnQ H3.
Qed.

End form100_1.
