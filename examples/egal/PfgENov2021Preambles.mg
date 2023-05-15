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

Axiom FalseE : False -> forall p:prop, p.

Axiom TrueI : True.

Axiom notI : forall A:prop, (A -> False) -> ~A.

Axiom notE : forall A:prop, ~A -> A -> False.

Axiom andI : forall (A B : prop), A -> B -> A /\ B.

Axiom andEL : forall (A B : prop), A /\ B -> A.

Axiom andER : forall (A B : prop), A /\ B -> B.

Axiom orIL : forall (A B : prop), A -> A \/ B.

Axiom orIR : forall (A B : prop), B -> A \/ B.

Axiom orE : forall (A B C:prop), (A -> C) -> (B -> C) -> A \/ B -> C.

Section PropN.

Variable P1 P2 P3:prop.

Axiom and3I : P1 -> P2 -> P3 -> P1 /\ P2 /\ P3.
Axiom and3E : P1 /\ P2 /\ P3 -> (forall p:prop, (P1 -> P2 -> P3 -> p) -> p).
Axiom or3I1 : P1 -> P1 \/ P2 \/ P3.
Axiom or3I2 : P2 -> P1 \/ P2 \/ P3.
Axiom or3I3 : P3 -> P1 \/ P2 \/ P3.
Axiom or3E : P1 \/ P2 \/ P3 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> p).

Variable P4:prop.

Axiom and4I : P1 -> P2 -> P3 -> P4 -> P1 /\ P2 /\ P3 /\ P4.
Axiom and4E : P1 /\ P2 /\ P3 /\ P4 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> p) -> p).
Axiom or4I1 : P1 -> P1 \/ P2 \/ P3 \/ P4.
Axiom or4I2 : P2 -> P1 \/ P2 \/ P3 \/ P4.
Axiom or4I3 : P3 -> P1 \/ P2 \/ P3 \/ P4.
Axiom or4I4 : P4 -> P1 \/ P2 \/ P3 \/ P4.
Axiom or4E : P1 \/ P2 \/ P3 \/ P4 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> (P4 -> p) -> p).

Variable P5:prop.

Axiom and5I : P1 -> P2 -> P3 -> P4 -> P5 -> P1 /\ P2 /\ P3 /\ P4 /\ P5.
Axiom and5E : P1 /\ P2 /\ P3 /\ P4 /\ P5 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> P5 -> p) -> p).
Axiom or5I1 : P1 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
Axiom or5I2 : P2 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
Axiom or5I3 : P3 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
Axiom or5I4 : P4 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
Axiom or5I5 : P5 -> P1 \/ P2 \/ P3 \/ P4 \/ P5.
Axiom or5E : P1 \/ P2 \/ P3 \/ P4 \/ P5 -> (forall p:prop, (P1 -> p) -> (P2 -> p) -> (P3 -> p) -> (P4 -> p) -> (P5 -> p) -> p).

Variable P6:prop.

Axiom and6I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6.
Axiom and6E : P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> p) -> p).

Variable P7:prop.

Axiom and7I: P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7.
Axiom and7E : P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7 -> (forall p:prop, (P1 -> P2 -> P3 -> P4 -> P5 -> P6 -> P7 -> p) -> p).

End PropN.

Axiom iffI : forall A B:prop, (A -> B) -> (B -> A) -> (A <-> B).
Axiom iffEL : forall A B:prop, (A <-> B) -> A -> B.
Axiom iffER : forall A B:prop, (A <-> B) -> B -> A.
Axiom iff_ref : forall A:prop, A <-> A.

Axiom neq_i_sym: forall x y, x <> y -> y <> x.

Definition nIn : set->set->prop :=
fun x X => ~In x X.

(* Unicode /:e "2209" *)
Infix /:e 502 := nIn.

Axiom Eps_i_ex : forall P:set -> prop, (exists x, P x) -> P (Eps_i P).

Axiom pred_ext : forall P Q:set -> prop, (forall x, P x <-> Q x) -> P = Q.
Axiom prop_ext_2 : forall p q:prop, (p -> q) -> (q -> p) -> p = q.
Axiom pred_ext_2 : forall P Q:set -> prop, P c= Q -> Q c= P -> P = Q.

Axiom Subq_ref : forall X:set, X c= X.
Axiom Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
Axiom Subq_contra : forall X Y z:set, X c= Y -> z /:e Y -> z /:e X.

Axiom EmptyE : forall x:set, x /:e Empty.
Axiom Subq_Empty : forall X:set, Empty c= X.
Axiom Empty_Subq_eq : forall X:set, X c= Empty -> X = Empty.
Axiom Empty_eq : forall X:set, (forall x, x /:e X) -> X = Empty.

Axiom UnionI : forall X x Y:set, x :e Y -> Y :e X -> x :e Union X.
Axiom UnionE : forall X x:set, x :e Union X -> exists Y:set, x :e Y /\ Y :e X.
Axiom UnionE_impred : forall X x:set, x :e Union X -> forall p:prop, (forall Y:set, x :e Y -> Y :e X -> p) -> p.

Axiom Union_Empty : Union Empty = Empty.

Axiom PowerI : forall X Y:set, Y c= X -> Y :e Power X.
Axiom PowerE : forall X Y:set, Y :e Power X -> Y c= X.
Axiom Power_Subq : forall X Y:set, X c= Y -> Power X c= Power Y.
Axiom Empty_In_Power : forall X:set, Empty :e Power X.
Axiom Self_In_Power : forall X:set, X :e Power X.

Axiom Union_Power_Subq : forall X:set, Union (Power X) c= X.

Axiom xm : forall P:prop, P \/ ~P.
Axiom dneg : forall P:prop, ~~P -> P.
Axiom imp_not_or : forall p q:prop, (p -> q) -> ~p \/ q.
Axiom not_and_or_demorgan : forall p q:prop, ~(p /\ q) -> ~p \/ ~q.

(* Parameter exactly1of2 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "163602f90de012a7426ee39176523ca58bc964ccde619b652cb448bd678f7e21" *)
Parameter exactly1of2 : prop->prop->prop.

Axiom exactly1of2_I1 : forall A B:prop, A -> ~B -> exactly1of2 A B.
Axiom exactly1of2_I2 : forall A B:prop, ~A -> B -> exactly1of2 A B.
Axiom exactly1of2_impI1 : forall A B:prop, (A -> ~B) -> (~A -> B) -> exactly1of2 A B.
Axiom exactly1of2_impI2 : forall A B:prop, (B -> ~A) -> (~B -> A) -> exactly1of2 A B.

Axiom exactly1of2_E : forall A B:prop, exactly1of2 A B ->
forall p:prop,
(A -> ~B -> p) ->
(~A -> B -> p) ->
p.

Axiom exactly1of2_or : forall A B:prop, exactly1of2 A B -> A \/ B.
Axiom exactly1of2_impn12 : forall A B:prop, exactly1of2 A B -> A -> ~B.
Axiom exactly1of2_impn21 : forall A B:prop, exactly1of2 A B -> B -> ~A.
Axiom exactly1of2_nimp12 : forall A B:prop, exactly1of2 A B -> ~A -> B.
Axiom exactly1of2_nimp21 : forall A B:prop, exactly1of2 A B -> ~B -> A.

(* Parameter exactly1of3 "d2a0e4530f6e4a8ef3d5fadfbb12229fa580c2add302f925c85ede027bb4b175" "aa4bcd059b9a4c99635877362627f7d5998ee755c58679934cc62913f8ef06e0" *)
Parameter exactly1of3 : prop->prop->prop->prop.

Axiom exactly1of3_I1 : forall A B C:prop, A -> ~B -> ~C -> exactly1of3 A B C.
Axiom exactly1of3_I2 : forall A B C:prop, ~A -> B -> ~C -> exactly1of3 A B C.
Axiom exactly1of3_I3 : forall A B C:prop, ~A -> ~B -> C -> exactly1of3 A B C.
Axiom exactly1of3_impI1 : forall A B C:prop, (A -> ~B) -> (A -> ~C) -> (B -> ~C) -> (~A -> B \/ C) -> exactly1of3 A B C.
Axiom exactly1of3_impI2 : forall A B C:prop, (B -> ~A) -> (B -> ~C) -> (A -> ~C) -> (~B -> A \/ C) -> exactly1of3 A B C.
Axiom exactly1of3_impI3 : forall A B C:prop, (C -> ~A) -> (C -> ~B) -> (A -> ~B) -> (~A -> B) -> exactly1of3 A B C.

Axiom exactly1of3_E : forall A B C:prop, exactly1of3 A B C ->
forall p:prop,
(A -> ~B -> ~C -> p) ->
(~A -> B -> ~C -> p) ->
(~A -> ~B -> C -> p) ->
p.

Axiom exactly1of3_or : forall A B C:prop, exactly1of3 A B C -> A \/ B \/ C.
Axiom exactly1of3_impn12 : forall A B C:prop, exactly1of3 A B C -> A -> ~B.
Axiom exactly1of3_impn13 : forall A B C:prop, exactly1of3 A B C -> A -> ~C.
Axiom exactly1of3_impn21 : forall A B C:prop, exactly1of3 A B C -> B -> ~A.
Axiom exactly1of3_impn23 : forall A B C:prop, exactly1of3 A B C -> B -> ~C.
Axiom exactly1of3_impn31 : forall A B C:prop, exactly1of3 A B C -> C -> ~A.
Axiom exactly1of3_impn32 : forall A B C:prop, exactly1of3 A B C -> C -> ~B.
Axiom exactly1of3_nimp1 : forall A B C:prop, exactly1of3 A B C -> ~A -> B \/ C.
Axiom exactly1of3_nimp2 : forall A B C:prop, exactly1of3 A B C -> ~B -> A \/ C.
Axiom exactly1of3_nimp3 : forall A B C:prop, exactly1of3 A B C -> ~C -> A \/ B.

Axiom ReplI : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F x|x :e A}.

Axiom ReplE : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> exists x :e A, y = F x.
Axiom ReplE_impred : forall A:set, forall F:set->set, forall y:set, y :e {F x|x :e A} -> forall p:prop, (forall x:set, x :e A -> y = F x -> p) -> p.
Axiom ReplE' : forall X, forall f:set -> set, forall p:set -> prop, (forall x :e X, p (f x)) -> forall y :e {f x|x :e X}, p y.

Axiom Repl_Empty : forall F:set -> set, {F x|x :e Empty} = Empty.

Axiom ReplEq_ext_sub : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} c= {G x|x :e X}.

Axiom ReplEq_ext : forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> {F x|x :e X} = {G x|x :e X}.

(* Parameter If_i "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf" "b8ff52f838d0ff97beb955ee0b26fad79602e1529f8a2854bda0ecd4193a8a3c" *)
Parameter If_i : prop->set->set->set.

Notation IfThenElse If_i.

Axiom If_i_correct : forall p:prop, forall x y:set,
p /\ (if p then x else y) = x \/ ~p /\ (if p then x else y) = y.

Axiom If_i_0 : forall p:prop, forall x y:set,
~ p -> (if p then x else y) = y.

Axiom If_i_1 : forall p:prop, forall x y:set,
p -> (if p then x else y) = x.

Axiom If_i_or : forall p:prop, forall x y:set, (if p then x else y) = x \/ (if p then x else y) = y.

Axiom If_i_eta : forall p:prop, forall x:set, (if p then x else x) = x.

(* Parameter UPair "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d" "74243828e4e6c9c0b467551f19c2ddaebf843f72e2437cc2dea41d079a31107f" *)
Parameter UPair : set->set->set.

Notation SetEnum2 UPair.

Axiom UPairE :
forall x y z:set, x :e {y,z} -> x = y \/ x = z.

Axiom UPairI1 : forall y z:set, y :e {y,z}.

Axiom UPairI2 : forall y z:set, z :e {y,z}.

Axiom UPair_com : forall x y:set, {x,y} = {y,x}.

(* Parameter Sing "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "bd01a809e97149be7e091bf7cbb44e0c2084c018911c24e159f585455d8e6bd0" *)
Parameter Sing : set -> set.
Notation SetEnum1 Sing.

Axiom SingI : forall x:set, x :e {x}. 
Axiom SingE : forall x y:set, y :e {x} -> y = x. 

(* Parameter binunion "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "5e1ac4ac93257583d0e9e17d6d048ff7c0d6ccc1a69875b2a505a2d4da305784" *)
Parameter binunion : set -> set -> set.

(* Unicode :\/: "222a" *)
Infix :\/: 345 left := binunion.

Axiom binunionI1 : forall X Y z:set, z :e X -> z :e X :\/: Y.

Axiom binunionI2 : forall X Y z:set, z :e Y -> z :e X :\/: Y.

Axiom binunionE : forall X Y z:set, z :e X :\/: Y -> z :e X \/ z :e Y.
Axiom binunionE' : forall X Y z, forall p:prop, (z :e X -> p) -> (z :e Y -> p) -> (z :e X :\/: Y -> p).
Axiom binunion_Repl_E' : forall X Y, forall f g:set -> set, forall p:set -> prop,
    (forall x :e X, p (f x))
 -> (forall y :e Y, p (g y))
 -> (forall w :e {f x|x :e X} :\/: {g y|y :e Y}, p w).

Definition SetAdjoin : set->set->set := fun X y => X :\/: {y}.

Notation SetEnum Empty Sing UPair SetAdjoin.

Axiom Power_0_Sing_0 : Power Empty = {Empty}.

Axiom Repl_UPair : forall F:set->set, forall x y:set, {F z|z :e {x,y}} = {F x,F y}.

Axiom Repl_Sing : forall F:set->set, forall x:set, {F z|z :e {x}} = {F x}.

Axiom Repl_restr : forall X:set, forall F G:set -> set, (forall x:set, x :e X -> F x = G x) -> {F x|x :e X} = {G x|x :e X}.

(* Parameter famunion "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792" "b3e3bf86a58af5d468d398d3acad61ccc50261f43c856a68f8594967a06ec07a" *)
Parameter famunion:set->(set->set)->set.

(* Unicode \/_ "22C3" *)
(* Subscript \/_ *)
Binder \/_ , := famunion.

Axiom famunionI:forall X:set, forall F:(set->set), forall x y:set, x :e X -> y :e F x -> y :e \/_ x :e X, F x.

Axiom famunionE:forall X:set, forall F:(set->set), forall y:set, y :e (\/_ x :e X, F x) -> exists x :e X, y :e F x.

Axiom famunionE_impred : forall X : set , forall F : (set -> set) , forall y : set , y :e (\/_ x :e X , F x) -> forall p:prop, (forall x, x :e X -> y :e F x -> p) -> p.

Axiom UnionEq_famunionId:forall X:set, Union X = \/_ x :e X, x.

Axiom ReplEq_famunion_Sing:forall X:set, forall F:(set->set), {F x|x :e X} = \/_ x :e X, {F x}.

Axiom Power_Sing : forall x:set, Power {x} = {Empty,{x}}.
Axiom Power_Sing_0 : Power {Empty} = {Empty,{Empty}}.

(* Parameter Sep "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f336a4ec8d55185095e45a638507748bac5384e04e0c48d008e4f6a9653e9c44" *)
Parameter Sep: set -> (set -> prop) -> set.

Notation Sep Sep.

Axiom SepI:forall X:set, forall P:(set->prop), forall x:set, x :e X -> P x -> x :e {x :e X|P x}.
Axiom SepE:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X /\ P x.
Axiom SepE1:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> x :e X.
Axiom SepE2:forall X:set, forall P:(set->prop), forall x:set, x :e {x :e X|P x} -> P x.

Axiom Sep_Subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.

Axiom Sep_In_Power : forall X:set, forall P:set->prop, {x :e X|P x} :e Power X.

(* Parameter ReplSep "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" "ec807b205da3293041239ff9552e2912636525180ddecb3a2b285b91b53f70d8" *)
Parameter ReplSep : set->(set->prop)->(set->set)->set.
Notation ReplSep ReplSep.

Axiom ReplSepI: forall X:set, forall P:set->prop, forall F:set->set, forall x:set, x :e X -> P x -> F x :e {F x|x :e X, P x}.

Axiom ReplSepE:forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> exists x:set, x :e X /\ P x /\ y = F x.

Axiom ReplSepE_impred: forall X:set, forall P:set->prop, forall F:set->set, forall y:set, y :e {F x|x :e X, P x} -> forall p:prop, (forall x :e X, P x -> y = F x -> p) -> p.

(* Parameter ReplSep2 "816cc62796568c2de8e31e57b826d72c2e70ee3394c00fbc921f2e41e996e83a" "da098a2dd3a59275101fdd49b6d2258642997171eac15c6b60570c638743e785" *)
Parameter ReplSep2 : set -> (set -> set) -> (set -> set -> prop) -> (set -> set -> set) -> set.

Axiom ReplSep2I : forall A, forall B:set -> set, forall P:set -> set -> prop, forall F:set -> set -> set, forall x :e A, forall y :e B x, P x y -> F x y :e ReplSep2 A B P F.

Axiom ReplSep2E_impred : forall A, forall B:set -> set, forall P:set -> set -> prop, forall F:set -> set -> set, forall r :e ReplSep2 A B P F, forall p:prop, (forall x :e A, forall y :e B x, P x y -> r = F x y -> p) -> p.

Axiom ReplSep2E : forall A, forall B:set -> set, forall P:set -> set -> prop, forall F:set -> set -> set, forall r :e ReplSep2 A B P F, exists x :e A, exists y :e B x, P x y /\ r = F x y.

Axiom binunion_asso: forall X Y Z:set, X :\/: (Y :\/: Z) = (X :\/: Y) :\/: Z.
Axiom binunion_com: forall X Y:set, X :\/: Y = Y :\/: X.
Axiom binunion_idl: forall X:set, Empty :\/: X = X.
Axiom binunion_idr: forall X:set, X :\/: Empty = X.
Axiom binunion_idem: forall X:set, X :\/: X = X.
Axiom binunion_Subq_1: forall X Y:set, X c= X :\/: Y.
Axiom binunion_Subq_2: forall X Y:set, Y c= X :\/: Y.
Axiom binunion_Subq_min: forall X Y Z:set, X c= Z -> Y c= Z -> X :\/: Y c= Z.
Axiom Subq_binunion_eq:forall X Y, (X c= Y) = (X :\/: Y = Y).
Axiom binunion_nIn_I : forall X Y z:set, z /:e X -> z /:e Y -> z /:e X :\/: Y.
Axiom binunion_nIn_E : forall X Y z:set, z /:e X :\/: Y -> z /:e X /\ z /:e Y.

(* Parameter binintersect "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" "b2abd2e5215c0170efe42d2fa0fb8a62cdafe2c8fbd0d37ca14e3497e54ba729" *)
Parameter binintersect:set->set->set.

(* Unicode :/\: "2229" *)
Infix :/\: 340 left := binintersect.

Axiom binintersectI:forall X Y z, z :e X -> z :e Y -> z :e X :/\: Y.
Axiom binintersectE:forall X Y z, z :e X :/\: Y -> z :e X /\ z :e Y.
Axiom binintersectE1:forall X Y z, z :e X :/\: Y -> z :e X.
Axiom binintersectE2:forall X Y z, z :e X :/\: Y -> z :e Y.
Axiom binintersect_Subq_1:forall X Y:set, X :/\: Y c= X.
Axiom binintersect_Subq_2:forall X Y:set, X :/\: Y c= Y.
Axiom binintersect_Subq_eq_1 : forall X Y, X c= Y -> X :/\: Y = X.
Axiom binintersect_Subq_max:forall X Y Z:set, Z c= X -> Z c= Y -> Z c= X :/\: Y.
Axiom binintersect_asso:forall X Y Z:set, X :/\: (Y :/\: Z) = (X :/\: Y) :/\: Z.
Axiom binintersect_com: forall X Y:set, X :/\: Y = Y :/\: X.
Axiom binintersect_annil:forall X:set, Empty :/\: X = Empty.
Axiom binintersect_annir:forall X:set, X :/\: Empty = Empty.
Axiom binintersect_idem:forall X:set, X :/\: X = X.
Axiom binintersect_binunion_distr:forall X Y Z:set, X :/\: (Y :\/: Z) = X :/\: Y :\/: X :/\: Z.
Axiom binunion_binintersect_distr:forall X Y Z:set, X :\/: Y :/\: Z = (X :\/: Y) :/\: (X :\/: Z).
Axiom Subq_binintersection_eq:forall X Y:set, (X c= Y) = (X :/\: Y = X).
Axiom binintersect_nIn_I1 : forall X Y z:set, z /:e X -> z /:e X :/\: Y.
Axiom binintersect_nIn_I2 : forall X Y z:set, z /:e Y -> z /:e X :/\: Y.
Axiom binintersect_nIn_E : forall X Y z:set, z /:e X :/\: Y -> z /:e X \/ z /:e Y.

(* Parameter setminus "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060" "c68e5a1f5f57bc5b6e12b423f8c24b51b48bcc32149a86fc2c30a969a15d8881" *)
Parameter setminus:set->set->set.

(* Unicode :\: "2216" *)
Infix :\: 350 := setminus.

Axiom setminusI:forall X Y z, (z :e X) -> (z /:e Y) -> z :e X :\: Y.
Axiom setminusE:forall X Y z, (z :e X :\: Y) -> z :e X /\ z /:e Y.
Axiom setminusE1:forall X Y z, (z :e X :\: Y) -> z :e X.
Axiom setminusE2:forall X Y z, (z :e X :\: Y) -> z /:e Y.
Axiom setminus_Subq:forall X Y:set, X :\: Y c= X.
Axiom setminus_Subq_contra:forall X Y Z:set, Z c= Y -> X :\: Y c= X :\: Z.
Axiom setminus_nIn_I1: forall X Y z, z /:e X -> z /:e X :\: Y.
Axiom setminus_nIn_I2: forall X Y z, z :e Y -> z /:e X :\: Y.
Axiom setminus_nIn_E: forall X Y z, z /:e X :\: Y -> z /:e X \/ z :e Y.
Axiom setminus_selfannih:forall X:set, (X :\: X) = Empty.
Axiom setminus_binintersect:forall X Y Z:set, X :\: Y :/\: Z = (X :\: Y) :\/: (X :\: Z).
Axiom setminus_binunion:forall X Y Z:set, X :\: Y :\/: Z = (X :\: Y) :\: Z.
Axiom binintersect_setminus:forall X Y Z:set, (X :/\: Y) :\: Z = X :/\: (Y :\: Z).
Axiom binunion_setminus:forall X Y Z:set, X :\/: Y :\: Z = (X :\: Z) :\/: (Y :\: Z).
Axiom setminus_setminus:forall X Y Z:set, X :\: (Y :\: Z) = (X :\: Y) :\/: (X :/\: Z).
Axiom setminus_annil:forall X:set, Empty :\: X = Empty.
Axiom setminus_idr:forall X:set, X :\: Empty = X.

Axiom In_irref : forall x, x /:e x.
Axiom In_no2cycle : forall x y, x :e y -> y :e x -> False.
Axiom In_no3cycle : forall x y z, x :e y -> y :e z -> z :e x -> False.
Axiom In_no4cycle : forall x y z w, x :e y -> y :e z -> z :e w -> w :e x -> False.

(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "65d8837d7b0172ae830bed36c8407fcd41b7d875033d2284eb2df245b42295a6" *)
Parameter ordsucc : set->set.

Axiom ordsuccI1 : forall x:set, x c= ordsucc x.
Axiom ordsuccI2 : forall x:set, x :e ordsucc x.
Axiom ordsuccE : forall x y:set, y :e ordsucc x -> y :e x \/ y = x.

Notation Nat Empty ordsucc.

Axiom neq_0_ordsucc : forall a:set, 0 <> ordsucc a.
Axiom neq_ordsucc_0 : forall a:set, ordsucc a <> 0.

Axiom ordsucc_inj : forall a b:set, ordsucc a = ordsucc b -> a = b.
Axiom ordsucc_inj_contra : forall a b:set, a <> b -> ordsucc a <> ordsucc b.

Axiom In_0_1 : 0 :e 1.
Axiom In_0_2 : 0 :e 2.
Axiom In_1_2 : 1 :e 2.

Definition nat_p : set->prop := fun n:set => forall p:set->prop, p 0 -> (forall x:set, p x -> p (ordsucc x)) -> p n.

Axiom nat_0 : nat_p 0.
Axiom nat_ordsucc : forall n:set, nat_p n -> nat_p (ordsucc n).
Axiom nat_1 : nat_p 1.
Axiom nat_2 : nat_p 2.
Axiom nat_3: nat_p 3.
Axiom nat_4: nat_p 4.
Axiom nat_5: nat_p 5.
Axiom nat_6: nat_p 6.
Axiom nat_0_in_ordsucc : forall n, nat_p n -> 0 :e ordsucc n.
Axiom nat_ordsucc_in_ordsucc : forall n, nat_p n -> forall m :e n, ordsucc m :e ordsucc n.
Axiom nat_ind : forall p:set->prop, p 0 -> (forall n, nat_p n -> p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
Axiom nat_inv : forall n, nat_p n -> n = 0 \/ exists x, nat_p x /\ n = ordsucc x.
Axiom nat_complete_ind : forall p:set->prop, (forall n, nat_p n -> (forall m :e n, p m) -> p n) -> forall n, nat_p n -> p n.
Axiom nat_p_trans : forall n, nat_p n -> forall m :e n, nat_p m.
Axiom nat_trans : forall n, nat_p n -> forall m :e n, m c= n.
Axiom nat_ordsucc_trans : forall n, nat_p n -> forall m :e ordsucc n, m c= n.

Axiom Union_ordsucc_eq : forall n, nat_p n -> Union (ordsucc n) = n.

Axiom In_0_3: 0 :e 3.
Axiom In_1_3: 1 :e 3.
Axiom In_2_3: 2 :e 3.
Axiom In_0_4: 0 :e 4.
Axiom In_1_4: 1 :e 4.
Axiom In_2_4: 2 :e 4.
Axiom In_3_4: 3 :e 4.
Axiom In_0_5: 0 :e 5.
Axiom In_1_5: 1 :e 5.
Axiom In_2_5: 2 :e 5.
Axiom In_3_5: 3 :e 5.
Axiom In_4_5: 4 :e 5.
Axiom In_0_6: 0 :e 6.
Axiom In_1_6: 1 :e 6.
Axiom In_2_6: 2 :e 6.
Axiom In_3_6: 3 :e 6.
Axiom In_4_6: 4 :e 6.
Axiom In_5_6: 5 :e 6.

Axiom cases_1: forall i :e 1, forall p:set->prop, p 0 -> p i.
Axiom cases_2: forall i :e 2, forall p:set->prop, p 0 -> p 1 -> p i.
Axiom cases_3: forall i :e 3, forall p:set->prop, p 0 -> p 1 -> p 2 -> p i.
Axiom cases_4: forall i :e 4, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p i.
Axiom cases_5: forall i :e 5, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p i.
Axiom cases_6: forall i :e 6, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p i.

Axiom neq_0_1 : 0 <> 1.
Axiom neq_0_2 : 0 <> 2.
Axiom neq_1_2 : 1 <> 2.
Axiom neq_1_0 : 1 <> 0.
Axiom neq_2_0 : 2 <> 0.
Axiom neq_2_1 : 2 <> 1.
Axiom neq_3_0: 3 <> 0.
Axiom neq_3_1: 3 <> 1.
Axiom neq_3_2: 3 <> 2.
Axiom neq_4_0: 4 <> 0.
Axiom neq_4_1: 4 <> 1.
Axiom neq_4_2: 4 <> 2.
Axiom neq_4_3: 4 <> 3.
Axiom neq_5_0: 5 <> 0.
Axiom neq_5_1: 5 <> 1.
Axiom neq_5_2: 5 <> 2.
Axiom neq_5_3: 5 <> 3.
Axiom neq_5_4: 5 <> 4.

Axiom ZF_closed_I : forall U,
 Union_closed U ->
 Power_closed U ->
 Repl_closed U ->
 ZF_closed U.

Axiom ZF_closed_E : forall U, ZF_closed U ->
 forall p:prop,
 (Union_closed U ->
  Power_closed U ->
  Repl_closed U -> p)
 -> p.

Axiom ZF_Union_closed : forall U, ZF_closed U ->
  forall X :e U, Union X :e U.

Axiom ZF_Power_closed : forall U, ZF_closed U ->
  forall X :e U, Power X :e U.

Axiom ZF_Repl_closed : forall U, ZF_closed U ->
  forall X :e U, forall F:set->set, (forall x :e X, F x :e U) -> {F x|x:eX} :e U.

Axiom ZF_UPair_closed : forall U, ZF_closed U ->
  forall x y :e U, {x,y} :e U.

Axiom ZF_Sing_closed : forall U, ZF_closed U ->
  forall x :e U, {x} :e U.

Axiom ZF_binunion_closed : forall U, ZF_closed U ->
  forall X Y :e U, (X :\/: Y) :e U.

Axiom ZF_ordsucc_closed : forall U, ZF_closed U ->
  forall x :e U, ordsucc x :e U.

Axiom nat_p_UnivOf_Empty : forall n:set, nat_p n -> n :e UnivOf Empty.

(* Unicode omega "3c9" *)
(* Parameter omega "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "6fc30ac8f2153537e397b9ff2d9c981f80c151a73f96cf9d56ae2ee27dfd1eb2" *)
Parameter omega : set.

Axiom omega_nat_p : forall n :e omega, nat_p n.

Axiom nat_p_omega : forall n:set, nat_p n -> n :e omega.

Axiom omega_ordsucc : forall n :e omega, ordsucc n :e omega.

Definition ordinal : set->prop := fun (alpha:set) => TransSet alpha /\ forall beta :e alpha, TransSet beta.

Axiom ordinal_TransSet : forall alpha:set, ordinal alpha -> TransSet alpha.

Axiom ordinal_In_TransSet : forall alpha:set, ordinal alpha -> forall beta :e alpha, TransSet beta.

Axiom ordinal_Empty : ordinal Empty.

Axiom ordinal_Hered : forall alpha:set, ordinal alpha -> forall beta :e alpha, ordinal beta.

Axiom TransSet_ordsucc : forall X:set, TransSet X -> TransSet (ordsucc X).

Axiom ordinal_ordsucc : forall alpha:set, ordinal alpha -> ordinal (ordsucc alpha).

Axiom nat_p_ordinal : forall n:set, nat_p n -> ordinal n.

Axiom ordinal_1 : ordinal 1.

Axiom ordinal_2 : ordinal 2.

Axiom omega_TransSet : TransSet omega.

Axiom omega_ordinal : ordinal omega.

Axiom ordsucc_omega_ordinal: ordinal (ordsucc omega).

Axiom TransSet_ordsucc_In_Subq : forall X:set, TransSet X -> forall x :e X, ordsucc x c= X.

Axiom ordinal_ordsucc_In_Subq : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta c= alpha.

Axiom ordinal_trichotomy_or : forall alpha beta:set, ordinal alpha -> ordinal beta -> alpha :e beta \/ alpha = beta \/ beta :e alpha.

Axiom ordinal_In_Or_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha :e beta \/ beta c= alpha.

Axiom ordinal_linear : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta \/ beta c= alpha.

Axiom ordinal_ordsucc_In_eq : forall alpha beta, ordinal alpha -> beta :e alpha -> ordsucc beta :e alpha \/ alpha = ordsucc beta.

Axiom ordinal_lim_or_succ : forall alpha, ordinal alpha -> (forall beta :e alpha, ordsucc beta :e alpha) \/ (exists beta :e alpha, alpha = ordsucc beta).

Axiom ordinal_ordsucc_In : forall alpha, ordinal alpha -> forall beta :e alpha, ordsucc beta :e ordsucc alpha.

Axiom ordinal_Union : forall X, (forall x :e X, ordinal x) -> ordinal (Union X).

Axiom ordinal_famunion : forall X, forall F:set -> set, (forall x :e X, ordinal (F x)) -> ordinal (\/_ x :e X, F x).

Axiom ordinal_binintersect : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :/\: beta).

Axiom ordinal_binunion : forall alpha beta, ordinal alpha -> ordinal beta -> ordinal (alpha :\/: beta).

Axiom ordinal_Sep : forall alpha, ordinal alpha -> forall p:set -> prop, (forall beta :e alpha, forall gamma :e beta, p beta -> p gamma) -> ordinal {beta :e alpha|p beta}.

Definition inj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v).

Definition surj : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Definition bij : set->set->(set->set)->prop :=
  fun X Y f =>
  (forall u :e X, f u :e Y)
  /\
  (forall u v :e X, f u = f v -> u = v)
  /\
  (forall w :e Y, exists u :e X, f u = w).

Axiom bijI : forall X Y, forall f:set -> set,
    (forall u :e X, f u :e Y)
 -> (forall u v :e X, f u = f v -> u = v)
 -> (forall w :e Y, exists u :e X, f u = w)
 -> bij X Y f.

Axiom bijE : forall X Y, forall f:set -> set,
    bij X Y f
 -> forall p:prop,
      ((forall u :e X, f u :e Y)
    -> (forall u v :e X, f u = f v -> u = v)
    -> (forall w :e Y, exists u :e X, f u = w)
    -> p)
   -> p.
  
(* Parameter inv "e1e47685e70397861382a17f4ecc47d07cdab63beca11b1d0c6d2985d3e2d38b" "896fa967e973688effc566a01c68f328848acd8b37e857ad23e133fdd4a50463" *)
Parameter inv : set -> (set -> set) -> set -> set.

Axiom surj_rinv : forall X Y, forall f:set->set, (forall w :e Y, exists u :e X, f u = w) -> forall y :e Y, inv X f y :e X /\ f (inv X f y) = y.

Axiom inj_linv : forall X, forall f:set->set, (forall u v :e X, f u = f v -> u = v) -> forall x :e X, inv X f (f x) = x.

Axiom bij_inv : forall X Y, forall f:set->set, bij X Y f -> bij Y X (inv X f).

Axiom bij_comp : forall X Y Z:set, forall f g:set->set, bij X Y f -> bij Y Z g -> bij X Z (fun x => g (f x)).

Axiom bij_id : forall X, bij X X (fun x => x).

Axiom bij_inj : forall X Y, forall f:set -> set, bij X Y f -> inj X Y f.

Axiom bij_surj : forall X Y, forall f:set -> set, bij X Y f -> surj X Y f.

Axiom inj_surj_bij : forall X Y, forall f:set -> set, inj X Y f -> surj X Y f -> bij X Y f.

Axiom surj_inv_inj : forall X Y, forall f:set -> set, (forall y :e Y, exists x :e X, f x = y) -> inj Y X (inv X f).

Definition atleastp : set -> set -> prop
 := fun X Y : set => exists f : set -> set, inj X Y f.

Definition equip : set -> set -> prop
 := fun X Y : set => exists f : set -> set, bij X Y f.

Axiom equip_ref : forall X, equip X X.
Axiom equip_sym : forall X Y, equip X Y -> equip Y X.
Axiom equip_tra : forall X Y Z, equip X Y -> equip Y Z -> equip X Z.

Definition finite : set -> prop := fun X => exists n :e omega, equip X n.
Definition infinite : set -> prop := fun X => ~finite X.

Axiom KnasterTarski_set: forall A, forall F:set->set,
    (forall U :e Power A, F U :e Power A)
 -> (forall U V :e Power A, U c= V -> F U c= F V)
 -> exists Y :e Power A, F Y = Y.
Axiom image_In_Power : forall A B, forall f:set -> set, (forall x :e A, f x :e B) -> forall U :e Power A, {f x|x :e U} :e Power B.
Axiom image_monotone : forall f:set -> set, forall U V, U c= V -> {f x|x :e U} c= {f x|x :e V}.
Axiom setminus_In_Power : forall A U, A :\: U :e Power A.
Axiom setminus_antimonotone : forall A U V, U c= V -> A :\: V c= A :\: U.
Axiom SchroederBernstein: forall A B, forall f g:set -> set, inj A B f -> inj B A g -> equip A B.

Axiom f_eq_i : forall f:set -> set, forall x y, x = y -> f x = f y.
Axiom f_eq_i_i : forall f:set -> set -> set, forall x y z w, x = y -> z = w -> f x z = f y w.
Axiom eq_i_tra : forall x y z, x = y -> y = z -> x = z.

Definition nSubq : set->set->prop :=
fun X Y => ~Subq X Y.

(* Unicode /c= "2288" *)
Infix /c= 502 := nSubq.

Axiom Sing_inv : forall x Y, {x} = Y -> x :e Y /\ forall y :e Y, y = x.

Axiom TransSet_In_ordsucc_Subq : forall x y, TransSet y -> x :e ordsucc y -> x c= y.
Axiom inv_Repl_eq : forall X, forall f g:set -> set, (forall x :e X, f (g x) = x) -> {f y|y :e {g x|x :e X}} = X.
Axiom invol_Repl_eq : forall X, forall f:set -> set, (forall x :e X, f (f x) = x) -> {f y|y :e {f x|x :e X}} = X.

Axiom Eps_i_set_R : forall X:set, forall P:set->prop, forall x :e X, P x -> Eps_i (fun x => x :e X /\ P x) :e X /\ P (Eps_i (fun x => x :e X /\ P x)).

Axiom exandE_i : forall P Q:set -> prop, (exists x, P x /\ Q x) -> forall r:prop, (forall x, P x -> Q x -> r) -> r.

Axiom exandE_ii : forall P Q:(set -> set) -> prop, (exists x:set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set, P x -> Q x -> p) -> p.

Axiom exandE_iii : forall P Q:(set -> set -> set) -> prop, (exists x:set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set, P x -> Q x -> p) -> p.

Axiom exandE_iiii : forall P Q:(set -> set -> set -> set) -> prop, (exists x:set -> set -> set -> set, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set -> set, P x -> Q x -> p) -> p.

Axiom exandE_iio : forall P Q:(set -> set -> prop) -> prop, (exists x:set -> set -> prop, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> prop, P x -> Q x -> p) -> p.

Axiom exandE_iiio : forall P Q:(set -> set -> set -> prop) -> prop, (exists x:set -> set -> set -> prop, P x /\ Q x) -> forall p:prop, (forall x:set -> set -> set -> prop, P x -> Q x -> p) -> p.

Section Descr_ii.

Variable P : (set -> set) -> prop.

(* Parameter Descr_ii "a6e81668bfd1db6e6eb6a13bf66094509af176d9d0daccda274aa6582f6dcd7c" "3bae39e9880bbf5d70538d82bbb05caf44c2c11484d80d06dee0589d6f75178c" *)
Parameter Descr_ii : set -> set.

Hypothesis Pex: exists f:set -> set, P f.
Hypothesis Puniq: forall f g:set -> set, P f -> P g -> f = g.

Axiom Descr_ii_prop : P Descr_ii.

End Descr_ii.

Section Descr_iii.

Variable P : (set -> set -> set) -> prop.

(* Parameter Descr_iii "dc42f3fe5d0c55512ef81fe5d2ad0ff27c1052a6814b1b27f5a5dcb6d86240bf" "ca5fc17a582fdd4350456951ccbb37275637ba6c06694213083ed9434fe3d545" *)
Parameter Descr_iii : set -> set -> set.

Hypothesis Pex: exists f:set -> set -> set, P f.
Hypothesis Puniq: forall f g:set -> set -> set, P f -> P g -> f = g.

Axiom Descr_iii_prop : P Descr_iii.

End Descr_iii.

Section Descr_iio.

Variable P : (set -> set -> prop) -> prop.

(* Parameter Descr_iio "9909a953d666fea995cf1ccfe3d98dba3b95210581af4af82ae04f546c4c34a5" "e8e5113bb5208434f24bf352985586094222b59a435d2d632e542c768fb9c029" *)
Parameter Descr_iio : set -> set -> prop.

Hypothesis Pex: exists f:set -> set -> prop, P f.
Hypothesis Puniq: forall f g:set -> set -> prop, P f -> P g -> f = g.

Axiom Descr_iio_prop : P Descr_iio.

End Descr_iio.

Section Descr_Vo1.

Variable P : Vo 1 -> prop.

(* Parameter Descr_Vo1 "322bf09a1711d51a4512e112e1767cb2616a7708dc89d7312c8064cfee6e3315" "615c0ac7fca2b62596ed34285f29a77b39225d1deed75d43b7ae87c33ba37083" *)
Parameter Descr_Vo1 : Vo 1.

Hypothesis Pex: exists f:Vo 1, P f.
Hypothesis Puniq: forall f g:Vo 1, P f -> P g -> f = g.

Axiom Descr_Vo1_prop : P Descr_Vo1.

End Descr_Vo1.

Section Descr_Vo2.

Variable P : Vo 2 -> prop.

(* Parameter Descr_Vo2 "cc8f114cf9f75d4b7c382c62411d262d2241962151177e3b0506480d69962acc" "a64b5b4306387d52672cb5cdbc1cb423709703e6c04fdd94fa6ffca008f7e1ab" *)
Parameter Descr_Vo2 : Vo 2.

Hypothesis Pex: exists f:Vo 2, P f.
Hypothesis Puniq: forall f g:Vo 2, P f -> P g -> f = g.

Axiom Descr_Vo2_prop : P Descr_Vo2.

End Descr_Vo2.

Section If_ii.

Variable p:prop.
Variable f g:set -> set.

(* Parameter If_ii "e76df3235104afd8b513a92c00d3cc56d71dd961510bf955a508d9c2713c3f29" "17057f3db7be61b4e6bd237e7b37125096af29c45cb784bb9cc29b1d52333779" *)
Parameter If_ii : set -> set.

Axiom If_ii_1 : p -> If_ii = f.

Axiom If_ii_0 : ~p -> If_ii = g.

End If_ii.

Section If_iii.

Variable p:prop.
Variable f g:set -> set -> set.

(* Parameter If_iii "53034f33cbed012c3c6db42812d3964f65a258627a765f5bede719198af1d1ca" "3314762dce5a2e94b7e9e468173b047dd4a9fac6ee2c5f553c6ea15e9c8b7542" *)
Parameter If_iii : set -> set -> set.

Axiom If_iii_1 : p -> If_iii = f.

Axiom If_iii_0 : ~p -> If_iii = g.

End If_iii.

Section If_Vo1.

Variable p:prop.
Variable f g:Vo 1.

(* Parameter If_Vo1 "33be70138f61ae5ce327b6b29a949448c54f06c2da932a4fcf7d7a0cfc29f72e" "2bb1d80de996e76ceb61fc1636c53ea4dc6f7ce534bd5caee16a3ba4c8794a58" *)
Parameter If_Vo1 : Vo 1.

Axiom If_Vo1_1 : p -> If_Vo1 = f.

Axiom If_Vo1_0 : ~p -> If_Vo1 = g.

End If_Vo1.

Section If_iio.

Variable p:prop.
Variable f g:set -> set -> prop.

(* Parameter If_iio "216c935441f8678edc47540d419667fe9e5ab01fda1f1afbc64eacaea6a9cbfc" "bf2fb7b3431387bbd1ede0aa0b590233207130df523e71e36aaebd675479e880" *)
Parameter If_iio : set -> set -> prop.

Axiom If_iio_1 : p -> If_iio = f.

Axiom If_iio_0 : ~p -> If_iio = g.

End If_iio.

Section If_Vo2.

Variable p:prop.
Variable f g:Vo 2.

(* Parameter If_Vo2 "8117f6db2fb9c820e5905451e109f8ef633101b911baa48945806dc5bf927693" "6cf28b2480e4fa77008de59ed21788efe58b7d6926c3a8b72ec889b0c27b2f2e" *)
Parameter If_Vo2 : Vo 2.

Axiom If_Vo2_1 : p -> If_Vo2 = f.

Axiom If_Vo2_0 : ~p -> If_Vo2 = g.

End If_Vo2.

Section EpsilonRec_i.

Variable F:set -> (set -> set) -> set.

(* Parameter In_rec_i "f97da687c51f5a332ff57562bd465232bc70c9165b0afe0a54e6440fc4962a9f" "fac413e747a57408ad38b3855d3cde8673f86206e95ccdadff2b5babaf0c219e" *)
Parameter In_rec_i : set -> set.

Hypothesis Fr:forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_i_eq : forall X:set, In_rec_i X = F X In_rec_i.

End EpsilonRec_i.

Section EpsilonRec_ii.

Variable F:set -> (set -> (set -> set)) -> (set -> set).

(* Parameter In_rec_ii "4d137cad40b107eb0fc2c707372525f1279575e6cadb4ebc129108161af3cedb" "f3c9abbc5074c0d68e744893a170de526469426a5e95400ae7fc81f74f412f7e" *)
Parameter In_rec_ii : set -> (set -> set).

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_ii_eq : forall X:set, In_rec_ii X = F X In_rec_ii.

End EpsilonRec_ii.

Section EpsilonRec_iii.

Variable F:set -> (set -> (set -> set -> set)) -> (set -> set -> set).

(* Parameter In_rec_iii "222f1b8dcfb0d2e33cc4b232e87cbcdfe5c4a2bdc5326011eb70c6c9aeefa556" "9b3a85b85e8269209d0ca8bf18ef658e56f967161bf5b7da5e193d24d345dd06" *)
Parameter In_rec_iii : set -> (set -> set -> set).

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set -> set), (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_iii_eq : forall X:set, In_rec_iii X = F X In_rec_iii.

End EpsilonRec_iii.

Section EpsilonRec_iio.

Variable F:set -> (set -> (set -> set -> prop)) -> (set -> set -> prop).

(* Parameter In_rec_iio "2cb990eb7cf33a7bea142678f254baf1970aa17b7016039b89df7652eff72aba" "8465061e06db87ff5ec9bf4bd2245a29d557f6b265478036bee39419282a5e28" *)
Parameter In_rec_iio : set -> (set -> set -> prop).

Hypothesis Fr:forall X:set, forall g h:set -> (set -> set -> prop), (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_iio_eq : forall X:set, In_rec_iio X = F X In_rec_iio.

End EpsilonRec_iio.

Section EpsilonRec_Vo1.

Variable F:set -> (set -> Vo 1) -> Vo 1.

(* Parameter In_rec_Vo1 "45519cf90ff63f7cea32c7ebbbae0922cfc609d577dc157e25e68e131cddf2df" "e9c5f22f769cd18d0d29090a943f66f6006f0d132fafe90f542ee2ee8a3f7b59" *)
Parameter In_rec_Vo1 : set -> Vo 1.

Hypothesis Fr:forall X:set, forall g h:set -> Vo 1, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_Vo1_eq : forall X:set, In_rec_Vo1 X = F X In_rec_Vo1.

End EpsilonRec_Vo1.

Section EpsilonRec_Vo2.

Variable F:set -> (set -> Vo 2) -> Vo 2.

(* Parameter In_rec_Vo2 "e249fde27e212bc28b301523be2eee37636e29fc084bd9b775cb02f921e2ad7f" "8bc8d37461c7653ced731399d140c0d164fb9231e77b2824088e534889c31596" *)
Parameter In_rec_Vo2 : set -> Vo 2.

Hypothesis Fr:forall X:set, forall g h:set -> Vo 2, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_Vo2_eq : forall X:set, In_rec_Vo2 X = F X In_rec_Vo2.

End EpsilonRec_Vo2.

Section If_Vo3.

Variable p:prop.
Variable f g:Vo 3.

(* Parameter If_Vo3 "5b91106169bd98c177a0ff2754005f1488a83383fc6fc918d8c61f613843cf0f" "73dd2d0fb9a3283dfd7b1d719404da0bf605e7b4c7b714a2b4e2cb1a38d98c6f" *)
Parameter If_Vo3 : Vo 3.

Axiom If_Vo3_1 : p -> If_Vo3 = f.

Axiom If_Vo3_0 : ~p -> If_Vo3 = g.

End If_Vo3.

Section Descr_Vo3.

Variable P : Vo 3 -> prop.

(* Parameter Descr_Vo3 "2e63292920e9c098907a70c431c7555afc9d4d26c8920d41192c83c02196acbe" "f25ee4a03f8810e3e5a11b184db6c8f282acaa7ef4bfd93c4b2de131431b977c" *)
Parameter Descr_Vo3 : Vo 3.

Hypothesis Pex: exists f:Vo 3, P f.
Hypothesis Puniq: forall f g:Vo 3, P f -> P g -> f = g.

Axiom Descr_Vo3_prop : P Descr_Vo3.

End Descr_Vo3.

Section EpsilonRec_Vo3.

Variable F:set -> (set -> Vo 3) -> Vo 3.

(* Parameter In_rec_Vo3 "058168fdbe0aa41756ceb986449745cd561e65bf2dd594384cd039169aa7ec90" "80f7da89cc801b8279f42f9e1ed519f72d50d76e88aba5efdb67c4ae1e59aee0" *)
Parameter In_rec_Vo3 : set -> Vo 3.

Hypothesis Fr:forall X:set, forall g h:set -> Vo 3, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_Vo3_eq : forall X:set, In_rec_Vo3 X = F X In_rec_Vo3.

End EpsilonRec_Vo3.

Section If_Vo4.

Variable p:prop.
Variable f g:Vo 4.

(* Parameter If_Vo4 "6dc2e406a4ee93aabecb0252fd45bdf4b390d29b477ecdf9f4656d42c47ed098" "1a8f92ceed76bef818d85515ce73c347dd0e2c0bcfd3fdfc1fcaf4ec26faed04" *)
Parameter If_Vo4 : Vo 4.

Axiom If_Vo4_1 : p -> If_Vo4 = f.
Axiom If_Vo4_0 : ~p -> If_Vo4 = g.

End If_Vo4.

Section Descr_Vo4.

Variable P : Vo 4 -> prop.

(* Parameter Descr_Vo4 "28ea4ee0409fe1fc4b4516175b2254cb311b9609fd2a4015768b4a520fe69214" "8b81abb8b64cec9ea874d5c4dd619a9733a734933a713ef54ed7e7273510b0c3" *)
Parameter Descr_Vo4 : Vo 4.

Hypothesis Pex: exists f:Vo 4, P f.
Hypothesis Puniq: forall f g:Vo 4, P f -> P g -> f = g.

Axiom Descr_Vo4_prop : P Descr_Vo4.

End Descr_Vo4.

Section EpsilonRec_Vo4.

Variable F:set -> (set -> Vo 4) -> Vo 4.

(* Parameter In_rec_Vo4 "65bb4bac5d306fd1707029e38ff3088a6d8ed5aab414f1faf79ba5294ee2d01e" "d82c5791815ca8155da516354e8f8024d8b9d43a14ce62e2526e4563ff64e67f" *)
Parameter In_rec_Vo4 : set -> Vo 4.

Hypothesis Fr:forall X:set, forall g h:set -> Vo 4, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom In_rec_Vo4_eq : forall X:set, In_rec_Vo4 X = F X In_rec_Vo4.

End EpsilonRec_Vo4.

Definition bigintersect := fun (D:(set->prop)->prop) (x:set) => forall P:set->prop, D P -> P x.

Definition reflexive : (set->set->prop)->prop := fun R => forall x:set, R x x.
Definition irreflexive : (set->set->prop)->prop := fun R => forall x:set, ~R x x.
Definition symmetric : (set->set->prop)->prop := fun R => forall x y:set, R x y -> R y x.
Definition antisymmetric : (set->set->prop)->prop := fun R => forall x y:set, R x y -> R y x -> x = y.
Definition transitive : (set->set->prop)->prop := fun R => forall x y z:set, R x y -> R y z -> R x z.
Definition eqreln : (set->set->prop)->prop := fun R => reflexive R /\ symmetric R /\ transitive R.
Definition per : (set->set->prop)->prop := fun R => symmetric R /\ transitive R.
Definition linear : (set->set->prop)->prop := fun R => forall x y:set, R x y \/ R y x.
Definition trichotomous_or : (set->set->prop)->prop := fun R => forall x y:set, R x y \/ x = y \/ R y x.
Definition partialorder : (set->set->prop)->prop := fun R => reflexive R /\ antisymmetric R /\ transitive R.
Definition totalorder : (set->set->prop)->prop := fun R => partialorder R /\ linear R.
Definition strictpartialorder : (set->set->prop)->prop := fun R => irreflexive R /\ transitive R.
Definition stricttotalorder : (set->set->prop)->prop := fun R => strictpartialorder R /\ trichotomous_or R.

Axiom per_sym : forall R:set->set->prop, per R -> symmetric R.

Axiom per_tra : forall R:set->set->prop, per R -> transitive R.

Axiom per_stra1 : forall R:set->set->prop, per R -> forall x y z:set, R y x -> R y z -> R x z.

Axiom per_stra2 : forall R:set->set->prop, per R -> forall x y z:set, R x y -> R z y -> R x z.

Axiom per_stra3 : forall R:set->set->prop, per R -> forall x y z:set, R y x -> R z y -> R x z.

Axiom per_ref1 : forall R:set->set->prop, per R -> forall x y:set, R x y -> R x x.

Axiom per_ref2 : forall R:set->set->prop, per R -> forall x y:set, R x y -> R y y.

Axiom partialorder_strictpartialorder : forall R:set->set->prop,
  partialorder R -> strictpartialorder (fun x y => R x y /\ x <> y).

Definition reflclos : (set->set->prop)->(set->set->prop) := fun R x y => R x y \/ x = y.

Axiom reflclos_refl : forall R:set->set->prop, reflexive (reflclos R).

Axiom reflclos_min : forall R S:set->set->prop, R c= S -> reflexive S -> reflclos R c= S.

Axiom strictpartialorder_partialorder_reflclos : forall R:set->set->prop, strictpartialorder R -> partialorder (reflclos R).

Axiom stricttotalorder_totalorder_reflclos : forall R:set->set->prop,
  stricttotalorder R -> totalorder (reflclos R).

Section Zermelo1908.

(* Parameter ZermeloWO "dc4124cb3e699eb9154ce37eaa547c4d08adc8fd41c311d706024418f4f1c8d6" "36a362f5d7e56550e98a38468fb4fc4d70ea17f4707cfdd2f69fc2cce37a9643" *)
Parameter ZermeloWO : set -> set -> prop.

Axiom ZermeloWO_Eps : forall a:set, (Eps_i (ZermeloWO a)) = a.
Axiom ZermeloWO_ref : reflexive ZermeloWO.
Axiom ZermeloWO_lin : linear ZermeloWO.
Axiom ZermeloWO_tra : transitive ZermeloWO.
Axiom ZermeloWO_antisym : antisymmetric ZermeloWO.
Axiom ZermeloWO_partialorder : partialorder ZermeloWO.
Axiom ZermeloWO_totalorder : totalorder ZermeloWO.
Axiom ZermeloWO_wo : forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y -> ZermeloWO x y.

Definition ZermeloWOstrict := fun (a b:set) => ZermeloWO a b /\ a <> b.

Axiom ZermeloWOstrict_trich : trichotomous_or ZermeloWOstrict.
Axiom ZermeloWOstrict_stricttotalorder : stricttotalorder ZermeloWOstrict.
Axiom ZermeloWOstrict_wo : forall (p:set -> prop), (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y /\ y <> x -> ZermeloWOstrict x y.

Axiom Zermelo_WO : exists r : set -> set -> prop,
    totalorder r
 /\ (forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y -> r x y).

Axiom Zermelo_WO_strict : exists r : set -> set -> prop,
    stricttotalorder r
 /\ (forall p:set->prop, (exists x:set, p x) -> exists x:set, p x /\ forall y:set, p y /\ y <> x -> r x y).

End Zermelo1908.

Axiom eq_imp_or : (fun (x y:prop) => (x -> y)) = (fun (x y:prop) => (~x \/ y)).

Axiom famunion_Empty: forall F:set -> set, (\/_ x :e 0, F x) = 0.

Axiom Empty_or_ex : forall X:set, X = Empty \/ exists x:set, x :e X.

Axiom nIn_0_0 : 0 /:e 0.
Axiom nIn_1_0 : 1 /:e 0.
Axiom nIn_2_0 : 2 /:e 0.
Axiom nIn_1_1 : 1 /:e 1.
Axiom nIn_2_2 : 2 /:e 2.
Axiom Subq_0_0 : 0 c= 0.
Axiom Subq_0_1 : 0 c= 1.
Axiom Subq_0_2 : 0 c= 2.
Axiom nSubq_1_0 : 1 /c= 0.
Axiom Subq_1_1 : 1 c= 1.
Axiom Subq_1_2 : 1 c= 2.
Axiom nSubq_2_0 : 2 /c= 0.
Axiom nSubq_2_1 : 2 /c= 1.
Axiom Subq_2_2 : 2 c= 2.
Axiom In_0_7: 0 :e 7.
Axiom In_1_7: 1 :e 7.
Axiom In_2_7: 2 :e 7.
Axiom In_3_7: 3 :e 7.
Axiom In_4_7: 4 :e 7.
Axiom In_5_7: 5 :e 7.
Axiom In_6_7: 6 :e 7.
Axiom In_0_8: 0 :e 8.
Axiom In_1_8: 1 :e 8.
Axiom In_2_8: 2 :e 8.
Axiom In_3_8: 3 :e 8.
Axiom In_4_8: 4 :e 8.
Axiom In_5_8: 5 :e 8.
Axiom In_6_8: 6 :e 8.
Axiom In_7_8: 7 :e 8.
Axiom In_0_9: 0 :e 9.
Axiom In_1_9: 1 :e 9.
Axiom In_2_9: 2 :e 9.
Axiom In_3_9: 3 :e 9.
Axiom In_4_9: 4 :e 9.
Axiom In_5_9: 5 :e 9.
Axiom In_6_9: 6 :e 9.
Axiom In_7_9: 7 :e 9.
Axiom In_8_9: 8 :e 9.

Section NatRec.

Variable z:set.
Variable f:set->set->set.
Let F : set->(set->set)->set := fun n g => if Union n :e n then f (Union n) (g (Union n)) else z.

Definition nat_primrec : set->set := In_rec_i F.

Axiom nat_primrec_r : forall X:set, forall g h:set -> set, (forall x :e X, g x = h x) -> F X g = F X h.

Axiom nat_primrec_0 : nat_primrec 0 = z.

Axiom nat_primrec_S : forall n:set, nat_p n -> nat_primrec (ordsucc n) = f n (nat_primrec n).

End NatRec.

Section NatArith.

Definition add_nat : set->set->set := fun n m:set => nat_primrec n (fun _ r => ordsucc r) m.

Infix + 360 right := add_nat.

Axiom add_nat_0R : forall n:set, n + 0 = n.

Axiom add_nat_SR : forall n m:set, nat_p m -> n + ordsucc m = ordsucc (n + m).

Axiom add_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n + m).

Axiom add_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n+m)+k = n+(m+k).

Axiom add_nat_0L : forall m:set, nat_p m -> 0+m = m.

Axiom add_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n + m = ordsucc (n+m).

Axiom add_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n + m = m + n.

Definition mul_nat : set->set->set := fun n m:set => nat_primrec 0 (fun _ r => n + r) m.

Infix * 355 right := mul_nat.

Axiom mul_nat_0R : forall n:set, n * 0 = 0.

Axiom mul_nat_SR : forall n m:set, nat_p m -> n * ordsucc m = n + n * m.

Axiom mul_nat_p : forall n:set, nat_p n -> forall m:set, nat_p m -> nat_p (n * m).

Axiom mul_nat_0L : forall m:set, nat_p m -> 0 * m = 0.

Axiom mul_nat_SL : forall n:set, nat_p n -> forall m:set, nat_p m -> ordsucc n * m = n * m + m.

Axiom mul_nat_com : forall n:set, nat_p n -> forall m:set, nat_p m -> n * m = m * n.

Axiom mul_add_nat_distrL : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> n * (m + k) = n * m + n * k.

Axiom mul_add_nat_distrR : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n + m) * k = n * k + m * k.

Axiom mul_nat_asso : forall n:set, nat_p n -> forall m:set, nat_p m -> forall k:set, nat_p k -> (n*m)*k = n*(m*k).

Axiom add_nat_1_1_2 : 1 + 1 = 2.

Definition divides_nat : set -> set -> prop :=
  fun m n => m :e omega /\ n :e omega /\ exists k :e omega, m * k = n.

Definition prime_nat : set -> prop :=
  fun n => n :e omega /\ 1 :e n /\ forall k :e omega, divides_nat k n -> k = 1 \/ k = n.

Definition coprime_nat : set->set->prop := fun a b => a :e omega /\ b :e omega /\ forall x :e omega :\: 1, divides_nat x a -> divides_nat x b -> x = 1.

Definition exp_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.

Infix ^ 342 right := exp_nat.

Definition even_nat : set -> prop := fun n => n :e omega /\ exists m :e omega, n = 2 * m.
Definition odd_nat : set -> prop := fun n => n :e omega /\ forall m :e omega, n <> 2 * m.

Definition nat_factorial : set -> set := fun n => nat_primrec 1 (fun k r => ordsucc k * r) n.

End NatArith.

Axiom PigeonHole_nat : forall n, nat_p n -> forall f:set -> set, (forall i :e ordsucc n, f i :e n) -> ~(forall i j :e ordsucc n, f i = f j -> i = j).

Axiom PigeonHole_nat_bij : forall n, nat_p n -> forall f:set -> set, (forall i :e n, f i :e n) -> (forall i j :e n, f i = f j -> i = j) -> bij n n f.

Axiom cases_7: forall i :e 7, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p i.
Axiom cases_8: forall i :e 8, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p i.
Axiom cases_9: forall i :e 9, forall p:set->prop, p 0 -> p 1 -> p 2 -> p 3 -> p 4 -> p 5 -> p 6 -> p 7 -> p 8 -> p i.

Axiom nIn_2_1 : 2 /:e 1.
Axiom neq_6_0: 6 <> 0.
Axiom neq_6_1: 6 <> 1.
Axiom neq_6_2: 6 <> 2.
Axiom neq_6_3: 6 <> 3.
Axiom neq_6_4: 6 <> 4.
Axiom neq_6_5: 6 <> 5.
Axiom neq_7_0: 7 <> 0.
Axiom neq_7_1: 7 <> 1.
Axiom neq_7_2: 7 <> 2.
Axiom neq_7_3: 7 <> 3.
Axiom neq_7_4: 7 <> 4.
Axiom neq_7_5: 7 <> 5.
Axiom neq_7_6: 7 <> 6.
Axiom neq_8_0: 8 <> 0.
Axiom neq_8_1: 8 <> 1.
Axiom neq_8_2: 8 <> 2.
Axiom neq_8_3: 8 <> 3.
Axiom neq_8_4: 8 <> 4.
Axiom neq_8_5: 8 <> 5.
Axiom neq_8_6: 8 <> 6.
Axiom neq_8_7: 8 <> 7.
Axiom neq_9_0: 9 <> 0.
Axiom neq_9_1: 9 <> 1.
Axiom neq_9_2: 9 <> 2.
Axiom neq_9_3: 9 <> 3.
Axiom neq_9_4: 9 <> 4.
Axiom neq_9_5: 9 <> 5.
Axiom neq_9_6: 9 <> 6.
Axiom neq_9_7: 9 <> 7.
Axiom neq_9_8: 9 <> 8.
Axiom Subq_1_Sing0 : 1 c= {0}.
Axiom Subq_Sing0_1 : {0} c= 1.
Axiom eq_1_Sing0 : 1 = {0}.
Axiom Subq_2_UPair01 : 2 c= {0,1}.
Axiom Subq_UPair01_2 : {0,1} c= 2.
Axiom eq_2_UPair01 : 2 = {0,1}.
Axiom ordinal_ind : forall p:set->prop, 
(forall alpha, ordinal alpha -> (forall beta :e alpha, p beta) -> p alpha)
->
forall alpha, ordinal alpha -> p alpha.

Axiom least_ordinal_ex : forall p:set -> prop, (exists alpha, ordinal alpha /\ p alpha) -> exists alpha, ordinal alpha /\ p alpha /\ forall beta :e alpha, ~p beta.

Axiom ordinal_trichotomy_or_impred : forall alpha beta, ordinal alpha -> ordinal beta -> forall p:prop, (alpha :e beta -> p) -> (alpha = beta -> p) -> (beta :e alpha -> p) -> p.

Axiom ordinal_trichotomy : forall alpha beta:set,
 ordinal alpha -> ordinal beta -> exactly1of3 (alpha :e beta) (alpha = beta) (beta :e alpha).

(*** Injection of set into itself that will correspond to x |-> (1,x) after pairing is defined. ***)
Definition Inj1 : set -> set := In_rec_i (fun X f => {0} :\/: {f x|x :e X}).

Axiom Inj1_eq : forall X:set, Inj1 X = {0} :\/: {Inj1 x|x :e X}.
Axiom Inj1I1 : forall X:set, 0 :e Inj1 X.
Axiom Inj1I2 : forall X x:set, x :e X -> Inj1 x :e Inj1 X.
Axiom Inj1E : forall X y:set, y :e Inj1 X -> y = 0 \/ exists x :e X, y = Inj1 x.
Axiom Inj1NE1 : forall x:set, Inj1 x <> 0.
Axiom Inj1NE2 : forall x:set, Inj1 x /:e {0}.

(*** Injection of set into itself that will correspond to x |-> (0,x) after pairing is defined. ***)
Definition Inj0 : set -> set := fun X => {Inj1 x|x :e X}.

Axiom Inj0I : forall X x:set, x :e X -> Inj1 x :e Inj0 X.
Axiom Inj0E : forall X y:set, y :e Inj0 X -> exists x:set, x :e X /\ y = Inj1 x.

(*** Unj : Left inverse of Inj1 and Inj0 ***)
Definition Unj : set -> set := In_rec_i (fun X f => {f x|x :e X :\: {0}}).

Axiom Unj_eq : forall X:set, Unj X = {Unj x|x :e X :\: {0}}.
Axiom Unj_Inj1_eq : forall X:set, Unj (Inj1 X) = X.
Axiom Inj1_inj : forall X Y:set, Inj1 X = Inj1 Y -> X = Y.
Axiom Unj_Inj0_eq : forall X:set, Unj (Inj0 X) = X.
Axiom Inj0_inj : forall X Y:set, Inj0 X = Inj0 Y -> X = Y.
Axiom Inj0_0 : Inj0 0 = 0.
Axiom Inj0_Inj1_neq : forall X Y:set, Inj0 X <> Inj1 Y.

(*** setsum ***)
Definition setsum : set -> set -> set := fun X Y => {Inj0 x|x :e X} :\/: {Inj1 y|y :e Y}.

(* Unicode :+: "002b" *)
Infix :+: 450 left := setsum.

Axiom Inj0_setsum : forall X Y x:set, x :e X -> Inj0 x :e X :+: Y.
Axiom Inj1_setsum : forall X Y y:set, y :e Y -> Inj1 y :e X :+: Y.
Axiom setsum_Inj_inv : forall X Y z:set, z :e X :+: Y -> (exists x :e X, z = Inj0 x) \/ (exists y :e Y, z = Inj1 y).

Axiom Inj0_setsum_0L : forall X:set, 0 :+: X = Inj0 X.
Axiom Inj1_setsum_1L : forall X:set, 1 :+: X = Inj1 X.
Axiom nat_setsum1_ordsucc : forall n:set, nat_p n -> 1 :+: n = ordsucc n.
Axiom setsum_0_0 : 0 :+: 0 = 0.
Axiom setsum_1_0_1 : 1 :+: 0 = 1.
Axiom setsum_1_1_2 : 1 :+: 1 = 2.
Axiom setsum_mon : forall X Y W Z, X c= W -> Y c= Z -> X :+: Y c= W :+: Z.

Definition combine_funcs : set -> set -> (set -> set) -> (set -> set) -> set -> set :=
  fun X Y f g z =>
   if z = Inj0 (Unj z) then f (Unj z) else g (Unj z).

Axiom combine_funcs_eq1 : forall X Y, forall f g:set -> set,
  forall x, combine_funcs X Y f g (Inj0 x) = f x.

Axiom combine_funcs_eq2 : forall X Y, forall f g:set -> set,
  forall y, combine_funcs X Y f g (Inj1 y) = g y.

Section pair_setsum.

Let pair := setsum.

Axiom pair_0_0 : pair 0 0 = 0.
Axiom pair_1_0_1 : pair 1 0 = 1.
Axiom pair_1_1_2 : pair 1 1 = 2.
Axiom nat_pair1_ordsucc : forall n:set, nat_p n -> pair 1 n = ordsucc n.

Definition proj0 : set -> set := fun Z => {Unj z|z :e Z, exists x:set, Inj0 x = z}.
Definition proj1 : set -> set := fun Z => {Unj z|z :e Z, exists y:set, Inj1 y = z}.

Axiom Inj0_pair_0_eq : Inj0 = pair 0.
Axiom Inj1_pair_1_eq : Inj1 = pair 1.
Axiom pairI0 : forall X Y x, x :e X -> pair 0 x :e pair X Y.
Axiom pairI1 : forall X Y y, y :e Y -> pair 1 y :e pair X Y.
Axiom pairE : forall X Y z, z :e pair X Y -> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Axiom pairE0 : forall X Y x, pair 0 x :e pair X Y -> x :e X.
Axiom pairE1 : forall X Y y, pair 1 y :e pair X Y -> y :e Y.
Axiom pairEq : forall X Y z, z :e pair X Y <-> (exists x :e X, z = pair 0 x) \/ (exists y :e Y, z = pair 1 y).
Axiom pairSubq : forall X Y W Z, X c= W -> Y c= Z -> pair X Y c= pair W Z.
Axiom proj0I : forall w u:set, pair 0 u :e w -> u :e proj0 w.
Axiom proj0E : forall w u:set, u :e proj0 w -> pair 0 u :e w.
Axiom proj1I : forall w u:set, pair 1 u :e w -> u :e proj1 w.
Axiom proj1E : forall w u:set, u :e proj1 w -> pair 1 u :e w.
Axiom proj0_pair_eq : forall X Y:set, proj0 (pair X Y) = X.
Axiom proj1_pair_eq : forall X Y:set, proj1 (pair X Y) = Y.
Axiom pair_inj : forall x y w z:set, pair x y = pair w z -> x = w /\ y = z.
Axiom pair_eta_Subq_proj : forall w, pair (proj0 w) (proj1 w) c= w.

(*** Sigma X Y = {(x,y) | x in X, y in Y x} ***)
Definition Sigma : set -> (set -> set) -> set :=
fun X Y => \/_ x :e X, {pair x y|y :e Y x}.

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

Axiom pair_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, pair x y :e Sigma_ x :e X, Y x.

Axiom Sigma_eta_proj0_proj1 : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z /\ proj0 z :e X /\ proj1 z :e Y (proj0 z).

Axiom proj_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (proj0 z) (proj1 z) = z.

Axiom proj0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj0 z :e X.

Axiom proj1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> proj1 z :e Y (proj0 z).

Axiom pair_Sigma_E0 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> x :e X.

Axiom pair_Sigma_E1 : forall X:set, forall Y:set->set, forall x y:set, pair x y :e (Sigma_ x :e X, Y x) -> y :e Y x.

Axiom Sigma_E : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) -> exists x :e X, exists y :e Y x, z = pair x y.

Axiom Sigma_Eq : forall X:set, forall Y:set->set, forall z:set, z :e (Sigma_ x :e X, Y x) <-> exists x :e X, exists y :e Y x, z = pair x y.

(*** Covariance of subsets of Sigmas ***)
Axiom Sigma_mon : forall X Y:set, X c= Y -> forall Z W:set->set, (forall x :e X, Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, W y.

Axiom Sigma_mon0 : forall X Y:set, X c= Y -> forall Z:set->set, (Sigma_ x :e X, Z x) c= Sigma_ y :e Y, Z y.

Axiom Sigma_mon1 : forall X:set, forall Z W:set->set, (forall x, x :e X -> Z x c= W x) -> (Sigma_ x :e X, Z x) c= Sigma_ x :e X, W x.

Axiom Sigma_Power_1 : forall X:set, X :e Power 1 -> forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Sigma_ x :e X, Y x) :e Power 1.

Definition setprod : set->set->set := fun X Y:set => Sigma_ x :e X, Y.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

Axiom pair_setprod : forall X Y:set, forall (x :e X) (y :e Y), pair x y :e X :*: Y.

Axiom proj0_setprod : forall X Y:set, forall z :e X :*: Y, proj0 z :e X.

Axiom proj1_setprod : forall X Y:set, forall z :e X :*: Y, proj1 z :e Y.

Axiom pair_setprod_E0 : forall X Y x y:set, pair x y :e X :*: Y -> x :e X.

Axiom pair_setprod_E1 : forall X Y x y:set, pair x y :e X :*: Y -> y :e Y.

(*** lam X F = {(x,y) | x :e X, y :e F x} = \/_{x :e X} {(x,y) | y :e (F x)} = Sigma X F ***)
Let lam : set -> (set -> set) -> set := Sigma.

(***  ap f x = {proj1 z | z :e f,  exists y, z = pair x y}} ***)
Definition ap : set -> set -> set := fun f x => {proj1 z|z :e f, exists y:set, z = pair x y}.

Notation SetImplicitOp ap.
Notation SetLam Sigma.

Axiom lamI : forall X:set, forall F:set->set, forall x :e X, forall y :e F x, pair x y :e fun x :e X => F x.

Axiom lamE : forall X:set, forall F:set->set, forall z:set, z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = pair x y.

Axiom lamEq : forall X:set, forall F:set->set, forall z, z :e (fun x :e X => F x) <-> exists x :e X, exists y :e F x, z = pair x y.

Axiom apI : forall f x y, pair x y :e f -> y :e f x.

Axiom apE : forall f x y, y :e f x -> pair x y :e f.

Axiom apEq : forall f x y, y :e f x <-> pair x y :e f.

Axiom beta : forall X:set, forall F:set -> set, forall x:set, x :e X -> (fun x :e X => F x) x = F x.

Axiom beta0 : forall X:set, forall F:set -> set, forall x:set, x /:e X -> (fun x :e X => F x) x = 0.

Axiom proj0_ap_0 : forall u, proj0 u = u 0.

Axiom proj1_ap_1 : forall u, proj1 u = u 1.

Axiom pair_ap_0 : forall x y:set, (pair x y) 0 = x.

Axiom pair_ap_1 : forall x y:set, (pair x y) 1 = y.

Axiom pair_ap_n2 : forall x y i:set, i /:e 2 -> (pair x y) i = 0.

Axiom ap0_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 0) :e X.

Axiom ap1_Sigma : forall X:set, forall Y:set -> set, forall z:set, z :e (Sigma_ x :e X, Y x) -> (z 1) :e (Y (z 0)).

Definition pair_p:set->prop
:= fun u:set => pair (u 0) (u 1) = u.

Axiom pair_p_I : forall x y, pair_p (pair x y).

Axiom pair_p_I2 : forall w, (forall u :e w, pair_p u /\ u 0 :e 2) -> pair_p w.

Axiom pair_p_In_ap : forall w f, pair_p w -> w :e f -> w 1 :e ap f (w 0).

Definition tuple_p : set->set->prop :=
fun n u => forall z :e u, exists i :e n, exists x:set, z = pair i x.

Axiom pair_p_tuple2 : pair_p = tuple_p 2.

Axiom tuple_p_2_tuple : forall x y:set, tuple_p 2 (x,y).

Axiom tuple_pair : forall x y:set, pair x y = (x,y).

Definition Pi : set -> (set -> set) -> set := fun X Y => {f :e Power (Sigma_ x :e X, Union (Y x)) | forall x :e X, f x :e Y x}.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

Axiom PiI : forall X:set, forall Y:set->set, forall f:set,
    (forall u :e f, pair_p u /\ u 0 :e X) -> (forall x :e X, f x :e Y x) -> f :e Pi_ x :e X, Y x.

Axiom PiE : forall X:set, forall Y:set->set, forall f:set,
  f :e (Pi_ x :e X, Y x) -> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).

Axiom PiEq : forall X:set, forall Y:set->set, forall f:set,
    f :e Pi X Y <-> (forall u :e f, pair_p u /\ u 0 :e X) /\ (forall x :e X, f x :e Y x).

Axiom lam_Pi : forall X:set, forall Y:set -> set, forall F:set -> set,
 (forall x :e X, F x :e Y x) -> (fun x :e X => F x) :e (Pi_ x :e X, Y x).

Axiom ap_Pi : forall X:set, forall Y:set -> set, forall f:set, forall x:set, f :e (Pi_ x :e X, Y x) -> x :e X -> f x :e Y x.

Axiom Pi_ext_Subq : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x c= g x) -> f c= g.

Axiom Pi_ext : forall X:set, forall Y:set -> set, forall f g :e (Pi_ x :e X, Y x), (forall x :e X, f x = g x) -> f = g.

Axiom Pi_eta : forall X:set, forall Y:set -> set, forall f:set, f :e (Pi_ x :e X, Y x) -> (fun x :e X => f x) = f.

Definition setexp : set->set->set := fun X Y:set => Pi_ y :e Y, X.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Axiom pair_tuple_fun : pair = (fun x y => (x,y)).

Axiom lamI2 : forall X, forall F:set->set, forall x :e X, forall y :e F x, (x,y) :e fun x :e X => F x.

Axiom lamE2 : forall X, forall F : set -> set , forall z : set , z :e (fun x :e X => F x) -> exists x :e X, exists y :e F x, z = (x,y).

Axiom tuple_2_inj : forall x y w z:set, (x,y) = (w,z) -> x = w /\ y = z.

Section Tuples.

Variable x0 x1: set.
Axiom tuple_2_0_eq: (x0,x1) 0 = x0.

Axiom tuple_2_1_eq: (x0,x1) 1 = x1.

End Tuples.

Definition Sep2 : set -> (set -> set) -> (set -> set -> prop) -> set
 := fun X Y R => {u :e Sigma_ x :e X, Y x | R (u 0) (u 1)}.

Axiom Sep2I: forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall x :e X, forall y :e Y x, R x y -> (x,y) :e Sep2 X Y R.

Axiom Sep2E: forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall u :e Sep2 X Y R, exists x :e X, exists y :e Y x, u = (x,y) /\ R x y.

Axiom Sep2E': forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall x y, (x,y) :e Sep2 X Y R -> x :e X /\ y :e Y x /\ R x y.

Axiom Sep2E'1: forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall x y, (x,y) :e Sep2 X Y R -> x :e X.

Axiom Sep2E'2: forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall x y, (x,y) :e Sep2 X Y R -> y :e Y x.

Axiom Sep2E'3: forall X, forall Y:set -> set, forall R:set -> set -> prop,
   forall x y, (x,y) :e Sep2 X Y R -> R x y.

Definition set_of_pairs : set -> prop := fun X => forall x :e X, exists y z, x = (y,z).

Axiom set_of_pairs_ext : forall X Y,
     set_of_pairs X -> set_of_pairs Y
  -> (forall v w, (v,w) :e X <-> (v,w) :e Y)
  -> X = Y.

Axiom Sep2_set_of_pairs : forall X, forall Y:set -> set, forall R:set -> set -> prop,
   set_of_pairs (Sep2 X Y R).

Axiom Sep2_ext : forall X, forall Y:set -> set, forall R R':set -> set -> prop,
     (forall x :e X, forall y :e Y x, R x y <-> R' x y)
  -> Sep2 X Y R = Sep2 X Y R'.

Axiom lam_ext_sub: forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> (fun x :e X => F x) c= (fun x :e X => G x).

Axiom lam_ext: forall X, forall F G:set -> set, (forall x :e X, F x = G x) -> (fun x :e X => F x) = (fun x :e X => G x).

Axiom lam_eta: forall X, forall F:set -> set, (fun x :e X => (fun x :e X => F x) x) = (fun x :e X => F x).

Axiom tuple_2_eta : forall x y, (fun i :e 2 => (x,y) i) = (x,y).

Definition lam2 : set -> (set -> set) -> (set -> set -> set) -> set
 := fun X Y F => fun x :e X => fun y :e Y x => F x y.

Axiom beta2 : forall X, forall Y:set -> set, forall F:set->set->set, forall x :e X, forall y :e Y x, lam2 X Y F x y = F x y.

Axiom lam2_ext: forall X, forall Y:set -> set, forall F G:set -> set -> set,
     (forall x :e X, forall y :e Y x, F x y = G x y)
  -> lam2 X Y F = lam2 X Y G.

Definition encode_u : set -> (set -> set) -> set := lam.
Definition decode_u : set -> set -> set := ap.

Definition encode_b : set -> (set -> set -> set) -> set := fun X F => lam2 X (fun _ => X) F.
Definition decode_b : set -> set -> set -> set := fun F x y => F x y.

Definition encode_p : set -> (set -> prop) -> set := fun X P => Sep X P.
Definition decode_p : set -> set -> prop := fun P x => x :e P.

Definition encode_r : set -> (set -> set -> prop) -> set := fun X R => Sep2 X (fun _ => X) R.
Definition decode_r : set -> set -> set -> prop := fun R x y => (x,y) :e R.

Definition encode_c : set -> ((set -> prop) -> prop) -> set := fun X C => Sep (Power X) (fun U => (C (fun x => x :e U))).
Definition decode_c : set -> (set -> prop) -> prop := fun C U => exists V, (forall x, U x <-> x :e V) /\ V :e C.

Axiom decode_encode_u : forall X, forall F:set -> set, forall x :e X, decode_u (encode_u X F) x = F x.

Axiom encode_u_ext : forall X, forall F F':set -> set, (forall x :e X, F x = F' x) -> encode_u X F = encode_u X F'.

Axiom decode_encode_b : forall X, forall F:set -> set -> set, forall x y :e X, decode_b (encode_b X F) x y = F x y.

Axiom encode_b_ext : forall X, forall F F':set -> set -> set, (forall x y :e X, F x y = F' x y) -> encode_b X F = encode_b X F'.

Axiom decode_encode_p : forall X, forall P:set -> prop, forall x :e X, (decode_p (encode_p X P) x) = (P x).

Axiom encode_p_ext : forall X, forall P P':set -> prop, (forall x :e X, P x <-> P' x) -> encode_p X P = encode_p X P'.

Axiom decode_encode_r : forall X, forall R:set -> set -> prop, forall x y :e X, (decode_r (encode_r X R) x y) = (R x y).

Axiom encode_r_ext : forall X, forall R R':set -> set -> prop, (forall x y :e X, R x y <-> R' x y) -> encode_r X R = encode_r X R'.

Axiom decode_encode_c : forall X, forall C:(set -> prop) -> prop, forall U:set -> prop, (forall x, U x -> x :e X) -> (decode_c (encode_c X C) U) = (C U).

Axiom encode_c_ext : forall X, forall C C':(set -> prop) -> prop, (forall U:set -> prop, (forall x, U x -> x :e X) -> (C U <-> C' U)) -> encode_c X C = encode_c X C'.

Axiom setprod_mon : forall X Y:set, X c= Y -> forall Z W:set, Z c= W -> X :*: Z c= Y :*: W.

Axiom setprod_mon0 : forall X Y:set, X c= Y -> forall Z:set, X :*: Z c= Y :*: Z.

Axiom setprod_mon1 : forall X:set, forall Z W:set, Z c= W -> X :*: Z c= X :*: W.

Axiom pair_eta_Subq : forall w, pair (w 0) (w 1) c= w.

Axiom Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), pair (z 0) (z 1) = z.

Axiom ReplEq_setprod_ext : forall X Y, forall F G:set -> set -> set, (forall x :e X, forall y :e Y, F x y = G x y) -> {F (w 0) (w 1)|w :e X :*: Y} = {G (w 0) (w 1)|w :e X :*: Y}.

Axiom tuple_p_3_tuple : forall x y z:set, tuple_p 3 (x,y,z).

Axiom tuple_p_4_tuple : forall x y z w:set, tuple_p 4 (x,y,z,w).

Axiom Pi_Power_1 : forall X:set, forall Y:set->set, (forall x :e X, Y x :e Power 1) -> (Pi_ x :e X, Y x) :e Power 1.

Axiom Pi_0_dom_mon : forall X Y:set, forall A:set->set, X c= Y -> (forall y :e Y, y /:e X -> 0 :e A y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, A y.

Axiom Pi_cod_mon : forall X:set, forall A B:set->set, (forall x :e X, A x c= B x) -> (Pi_ x :e X, A x) c= Pi_ x :e X, B x.

Axiom Pi_0_mon : forall X Y:set, forall A B:set->set,
 (forall x :e X, A x c= B x) -> X c= Y -> (forall y :e Y, y /:e X -> 0 :e B y)
 -> (Pi_ x :e X, A x) c= Pi_ y :e Y, B y.

Axiom setexp_2_eq : forall X:set, X :*: X = X :^: 2.

Axiom setexp_0_dom_mon : forall A:set, 0 :e A -> forall X Y:set, X c= Y -> A :^: X c= A :^: Y.

Axiom setexp_0_mon : forall X Y A B:set, 0 :e B -> A c= B -> X c= Y -> A :^: X c= B :^: Y.

Axiom nat_in_setexp_mon : forall A:set, 0 :e A -> forall n, nat_p n -> forall m :e n, A :^: m c= A :^: n.

Axiom tupleI0 : forall X Y x, x :e X -> (0,x) :e (X,Y).

Axiom tupleI1 : forall X Y y, y :e Y -> (1,y) :e (X,Y).

Axiom tupleE : forall X Y z, z :e (X,Y) -> (exists x :e X, z = (0,x)) \/ (exists y :e Y, z = (1,y)).

Axiom tuple_2_Sigma : forall X:set, forall Y:set -> set, forall x :e X, forall y :e Y x, (x,y) :e Sigma_ x :e X, Y x.

Axiom tuple_2_setprod : forall X:set, forall Y:set, forall x :e X, forall y :e Y, (x,y) :e X :*: Y.

Axiom tuple_Sigma_eta : forall X:set, forall Y:set -> set, forall z :e (Sigma_ x :e X, Y x), (z 0,z 1) = z.

Axiom apI2 : forall f x y, (x,y) :e f -> y :e f x.

Axiom apE2 : forall f x y, y :e f x -> (x,y) :e f.

Axiom ap_const_0 : forall x, 0 x = 0.

Axiom tuple_2_in_A_2 : forall x y A, x :e A -> y :e A -> (x,y) :e A :^: 2.

Axiom tuple_2_bij_2 : forall x y, x :e 2 -> y :e 2 -> x <> y -> bij 2 2 (fun i => (x,y) i).

Axiom tuple_3_eta : forall x y z, (fun i :e 3 => (x,y,z) i) = (x,y,z).

Axiom tuple_4_eta : forall x y z w, (fun i :e 4 => (x,y,z,w) i) = (x,y,z,w).

Section Tuples.

Variable x0 x1 x2: set.

Axiom tuple_3_0_eq: (x0,x1,x2) 0 = x0.

Axiom tuple_3_1_eq: (x0,x1,x2) 1 = x1.

Axiom tuple_3_2_eq: (x0,x1,x2) 2 = x2.

Variable x3: set.
Axiom tuple_4_0_eq: (x0,x1,x2,x3) 0 = x0.

Axiom tuple_4_1_eq: (x0,x1,x2,x3) 1 = x1.

Axiom tuple_4_2_eq: (x0,x1,x2,x3) 2 = x2.

Axiom tuple_4_3_eq: (x0,x1,x2,x3) 3 = x3.

Variable x4: set.

Axiom tuple_5_0_eq: (x0,x1,x2,x3,x4) 0 = x0.

Axiom tuple_5_1_eq: (x0,x1,x2,x3,x4) 1 = x1.

Axiom tuple_5_2_eq: (x0,x1,x2,x3,x4) 2 = x2.

Axiom tuple_5_3_eq: (x0,x1,x2,x3,x4) 3 = x3.

Axiom tuple_5_4_eq: (x0,x1,x2,x3,x4) 4 = x4.

Variable x5: set.
Axiom tuple_6_0_eq: (x0,x1,x2,x3,x4,x5) 0 = x0.

Axiom tuple_6_1_eq: (x0,x1,x2,x3,x4,x5) 1 = x1.

Axiom tuple_6_2_eq: (x0,x1,x2,x3,x4,x5) 2 = x2.

Axiom tuple_6_3_eq: (x0,x1,x2,x3,x4,x5) 3 = x3.

Axiom tuple_6_4_eq: (x0,x1,x2,x3,x4,x5) 4 = x4.

Axiom tuple_6_5_eq: (x0,x1,x2,x3,x4,x5) 5 = x5.

Variable x6: set.
Axiom tuple_7_0_eq: (x0,x1,x2,x3,x4,x5,x6) 0 = x0.

Axiom tuple_7_1_eq: (x0,x1,x2,x3,x4,x5,x6) 1 = x1.

Axiom tuple_7_2_eq: (x0,x1,x2,x3,x4,x5,x6) 2 = x2.

Axiom tuple_7_3_eq: (x0,x1,x2,x3,x4,x5,x6) 3 = x3.

Axiom tuple_7_4_eq: (x0,x1,x2,x3,x4,x5,x6) 4 = x4.

Axiom tuple_7_5_eq: (x0,x1,x2,x3,x4,x5,x6) 5 = x5.

Axiom tuple_7_6_eq: (x0,x1,x2,x3,x4,x5,x6) 6 = x6.

Variable x7: set.

Axiom tuple_8_0_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 0 = x0.

Axiom tuple_8_1_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 1 = x1.

Axiom tuple_8_2_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 2 = x2.

Axiom tuple_8_3_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 3 = x3.

Axiom tuple_8_4_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 4 = x4.

Axiom tuple_8_5_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 5 = x5.

Axiom tuple_8_6_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 6 = x6.

Axiom tuple_8_7_eq: (x0,x1,x2,x3,x4,x5,x6,x7) 7 = x7.

Variable x8: set.
Axiom tuple_9_0_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 0 = x0.

Axiom tuple_9_1_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 1 = x1.

Axiom tuple_9_2_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 2 = x2.

Axiom tuple_9_3_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 3 = x3.

Axiom tuple_9_4_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 4 = x4.

Axiom tuple_9_5_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 5 = x5.

Axiom tuple_9_6_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 6 = x6.

Axiom tuple_9_7_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 7 = x7.

Axiom tuple_9_8_eq: (x0,x1,x2,x3,x4,x5,x6,x7,x8) 8 = x8.

End Tuples.

End pair_setsum.

(* Unicode Sigma_ "2211" *)
Binder+ Sigma_ , := Sigma.

(* Unicode :*: "2a2f" *)
Infix :*: 440 left := setprod.

(* Unicode Pi_ "220f" *)
Binder+ Pi_ , := Pi.

(* Superscript :^: *)
Infix :^: 430 left := setexp.

Axiom tuple_3_in_A_3 : forall x y z A, x :e A -> y :e A -> z :e A -> (x,y,z) :e A :^: 3.

Axiom tuple_3_bij_3 : forall x y z, x :e 3 -> y :e 3 -> z :e 3 -> x <> y -> x <> z -> y <> z -> bij 3 3 (fun i => (x,y,z) i).

Axiom tuple_4_in_A_4 : forall x y z w A, x :e A -> y :e A -> z :e A -> w :e A -> (x,y,z,w) :e A :^: 4.

Axiom tuple_4_bij_4 : forall x y z w, x :e 4 -> y :e 4 -> z :e 4 -> w :e 4 -> x <> y -> x <> z -> x <> w -> y <> z -> y <> w -> z <> w -> bij 4 4 (fun i => (x,y,z,w) i).

Axiom iff_refl : forall A:prop, A <-> A.

Axiom iff_sym : forall A B:prop, (A <-> B) -> (B <-> A).

Axiom iff_trans : forall A B C: prop, (A <-> B) -> (B <-> C) -> (A <-> C).

Axiom not_or_and_demorgan : forall A B:prop, ~(A \/ B) -> ~A /\ ~B.

Axiom and_not_or_demorgan : forall A B:prop, ~A /\ ~B -> ~(A \/ B).

Axiom not_ex_all_demorgan_i : forall P:set->prop, (~exists x, P x) -> forall x, ~P x.

Axiom not_all_ex_demorgan_i : forall P:set->prop, ~(forall x, P x) -> exists x, ~P x.

Axiom eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).

(* Parameter EpsR_i_i_1 "ddf851fd1854df71be5ab088768ea86709a9288535efee95c3e876766b3c9195" "20c61c861cf1a0ec40aa6c975b43cd41a1479be2503a10765e97a8492374fbb0" *)
Parameter EpsR_i_i_1 : (set->set->prop) -> set.

(* Parameter EpsR_i_i_2 "73402bd7c3bf0477017bc48f6f236eef4ba9c1b3cffe34afb0a7b991fea12054" "eced574473e7bc0629a71e0b88779fd6c752d24e0ef24f1e40d37c12fedf400a" *)
Parameter EpsR_i_i_2 : (set->set->prop) -> set.

Axiom EpsR_i_i_12 : forall R:set->set->prop, (exists x y, R x y) -> R (EpsR_i_i_1 R) (EpsR_i_i_2 R).

(* Parameter DescrR_i_io_1 "1f005fdad5c6f98763a15a5e5539088f5d43b7d1be866b0b204fda1ce9ed9248" "1d3fd4a14ef05bd43f5c147d7966cf05fd2fed808eea94f56380454b9a6044b2" *)
Parameter DescrR_i_io_1 : (set->(set->prop)->prop) -> set.

(* Parameter DescrR_i_io_2 "28d8599686476258c12dcc5fc5f5974335febd7d5259e1a8e5918b7f9b91ca03" "768eb2ad186988375e6055394e36e90c81323954b8a44eb08816fb7a84db2272" *)
Parameter DescrR_i_io_2 : (set->(set->prop)->prop) -> set->prop.

Axiom DescrR_i_io_12 : forall R:set->(set->prop)->prop, (exists x, (exists y:set->prop, R x y) /\ (forall y z:set -> prop, R x y -> R x z -> y = z)) -> R (DescrR_i_io_1 R) (DescrR_i_io_2 R).

(** Conway describes this way of formalizing in ZF in an appendix to Part Zero of his book,
    but rejects formalization in favor of "Mathematician's Liberation."
 **)

Definition PNoEq_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => forall beta :e alpha, p beta <-> q beta.

Axiom PNoEq_ref_ : forall alpha, forall p:set -> prop, PNoEq_ alpha p p.

Axiom PNoEq_sym_ : forall alpha, forall p q:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q p.

Axiom PNoEq_tra_ : forall alpha, forall p q r:set -> prop, PNoEq_ alpha p q -> PNoEq_ alpha q r -> PNoEq_ alpha p r.

Axiom PNoEq_antimon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoEq_ alpha p q -> PNoEq_ beta p q.

Definition PNoLt_ : set -> (set -> prop) -> (set -> prop) -> prop
 := fun alpha p q => exists beta :e alpha, PNoEq_ beta p q /\ ~p beta /\ q beta.

Axiom PNoLt_E_ : forall alpha, forall p q:set -> prop, PNoLt_ alpha p q ->
  forall R:prop, (forall beta, beta :e alpha -> PNoEq_ beta p q -> ~p beta -> q beta -> R) -> R.

Axiom PNoLt_irref_ : forall alpha, forall p:set -> prop, ~PNoLt_ alpha p p.

Axiom PNoLt_mon_ : forall p q:set -> prop, forall alpha, ordinal alpha -> forall beta :e alpha, PNoLt_ beta p q -> PNoLt_ alpha p q.

Axiom PNoLt_trichotomy_or_ : forall p q:set -> prop, forall alpha, ordinal alpha
  -> PNoLt_ alpha p q \/ PNoEq_ alpha p q \/ PNoLt_ alpha q p.

Axiom PNoLt_tra_ : forall alpha, ordinal alpha -> forall p q r:set -> prop, PNoLt_ alpha p q -> PNoLt_ alpha q r -> PNoLt_ alpha p r.

(* Parameter PNoLt "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "8f57a05ce4764eff8bc94b278352b6755f1a46566cd7220a5488a4a595a47189" *)
Parameter PNoLt : set -> (set -> prop) -> set -> (set -> prop) -> prop.

Axiom PNoLtI1 : forall alpha beta, forall p q:set -> prop,
  PNoLt_ (alpha :/\: beta) p q -> PNoLt alpha p beta q.

Axiom PNoLtI2 : forall alpha beta, forall p q:set -> prop,
  alpha :e beta -> PNoEq_ alpha p q -> q alpha -> PNoLt alpha p beta q.

Axiom PNoLtI3 : forall alpha beta, forall p q:set -> prop,
  beta :e alpha -> PNoEq_ beta p q -> ~p beta -> PNoLt alpha p beta q.

Axiom PNoLtE : forall alpha beta, forall p q:set -> prop,
  PNoLt alpha p beta q ->
  forall R:prop,
      (PNoLt_ (alpha :/\: beta) p q -> R)
   -> (alpha :e beta -> PNoEq_ alpha p q -> q alpha -> R)
   -> (beta :e alpha -> PNoEq_ beta p q -> ~p beta -> R)
   -> R.

Axiom PNoLtE2 : forall alpha, forall p q:set -> prop,
  PNoLt alpha p alpha q -> PNoLt_ alpha p q.

Axiom PNoLt_irref : forall alpha, forall p:set -> prop, ~PNoLt alpha p alpha p.

Axiom PNoLt_trichotomy_or : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q \/ PNoLt beta q alpha p.

Axiom PNoLtEq_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoEq_ beta q r -> PNoLt alpha p beta r.

Axiom PNoEqLt_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLt alpha q beta r -> PNoLt alpha p beta r.

Axiom PNoLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.

Definition PNoLe : set -> (set -> prop) -> set -> (set -> prop) -> prop
   := fun alpha p beta q => PNoLt alpha p beta q \/ alpha = beta /\ PNoEq_ alpha p q.

Axiom PNoLeI1 : forall alpha beta, forall p q:set -> prop,
   PNoLt alpha p beta q -> PNoLe alpha p beta q.

Axiom PNoLeI2 : forall alpha, forall p q:set -> prop,
   PNoEq_ alpha p q -> PNoLe alpha p alpha q.

Axiom PNoLe_ref : forall alpha, forall p:set -> prop, PNoLe alpha p alpha p.

Axiom PNoLe_antisym : forall alpha beta, ordinal alpha -> ordinal beta ->
 forall p q:set -> prop,
 PNoLe alpha p beta q -> PNoLe beta q alpha p -> alpha = beta /\ PNoEq_ alpha p q.

Axiom PNoLtLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLt alpha p beta q -> PNoLe beta q gamma r -> PNoLt alpha p gamma r.

Axiom PNoLeLt_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLt beta q gamma r -> PNoLt alpha p gamma r.

Axiom PNoEqLe_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoEq_ alpha p q -> PNoLe alpha q beta r -> PNoLe alpha p beta r.

Axiom PNoLeEq_tra : forall alpha beta, ordinal alpha -> ordinal beta -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoEq_ beta q r -> PNoLe alpha p beta r.

Axiom PNoLe_tra : forall alpha beta gamma, ordinal alpha -> ordinal beta -> ordinal gamma -> forall p q r:set -> prop, PNoLe alpha p beta q -> PNoLe beta q gamma r -> PNoLe alpha p gamma r.

Definition PNo_downc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun L alpha p => exists beta, ordinal beta /\ exists q:set -> prop, L beta q /\ PNoLe alpha p beta q.

Definition PNo_upc : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
 := fun R alpha p => exists beta, ordinal beta /\ exists q:set -> prop, R beta q /\ PNoLe beta q alpha p.

Axiom PNoLe_downc : forall L:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_downc L alpha p -> PNoLe beta q alpha p -> PNo_downc L beta q.

Axiom PNo_downc_ref : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, L alpha p -> PNo_downc L alpha p.

Axiom PNo_upc_ref : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, R alpha p -> PNo_upc R alpha p.

Axiom PNoLe_upc : forall R:set -> (set -> prop) -> prop, forall alpha beta, forall p q:set -> prop,
  ordinal alpha -> ordinal beta ->
  PNo_upc R alpha p -> PNoLe alpha p beta q -> PNo_upc R beta q.

Definition PNoLt_pwise : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> prop
  := fun L R => forall gamma, ordinal gamma -> forall p:set -> prop, L gamma p -> forall delta, ordinal delta -> forall q:set -> prop, R delta q -> PNoLt gamma p delta q.

Axiom PNoLt_pwise_downc_upc : forall L R:set -> (set -> prop) -> prop,
    PNoLt_pwise L R -> PNoLt_pwise (PNo_downc L) (PNo_upc R).

Definition PNo_rel_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_downc L beta q -> PNoLt beta q alpha p.

Definition PNo_rel_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta :e alpha, forall q:set -> prop, PNo_upc R beta q -> PNoLt alpha p beta q.

Definition PNo_rel_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_upperbd L alpha p /\ PNo_rel_strict_lowerbd R alpha p.

Axiom PNoEq_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L alpha q.

Axiom PNo_rel_strict_upperbd_antimon : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.

Axiom PNoEq_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R alpha q.

Axiom PNo_rel_strict_lowerbd_antimon : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.

Axiom PNoEq_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R alpha q.

Axiom PNo_rel_strict_imv_antimon : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p:set -> prop, forall beta :e alpha,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.

Definition PNo_rel_strict_uniq_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_rel_strict_imv L R alpha p /\ forall q:set -> prop, PNo_rel_strict_imv L R alpha q -> PNoEq_ alpha p q.

Definition PNo_rel_strict_split_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p =>
         PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha)
      /\ PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).

Axiom PNo_extend0_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta /\ delta <> alpha).

Axiom PNo_extend1_eq : forall alpha, forall p:set -> prop, PNoEq_ alpha p (fun delta => p delta \/ delta = alpha).

Axiom PNo_rel_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha ->
      (exists p:set -> prop, PNo_rel_strict_uniq_imv L R alpha p)
   \/ (exists tau :e alpha, exists p:set -> prop, PNo_rel_strict_split_imv L R tau p).

Definition PNo_lenbdd : set -> (set -> (set -> prop) -> prop) -> prop
  := fun alpha L => forall beta, forall p:set -> prop, L beta p -> beta :e alpha.

Axiom PNo_lenbdd_strict_imv_extend0 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta /\ delta <> alpha).

Axiom PNo_lenbdd_strict_imv_extend1 : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_imv L R (ordsucc alpha) (fun delta => p delta \/ delta = alpha).

Axiom PNo_lenbdd_strict_imv_split : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> PNo_lenbdd alpha L -> PNo_lenbdd alpha R ->
  forall p:set -> prop,
  PNo_rel_strict_imv L R alpha p -> PNo_rel_strict_split_imv L R alpha p.

Axiom PNo_rel_imv_bdd_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_rel_strict_split_imv L R beta p.

Definition PNo_strict_upperbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, L beta q -> PNoLt beta q alpha p.

Definition PNo_strict_lowerbd : (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun R alpha p =>
       forall beta, ordinal beta -> forall q:set -> prop, R beta q -> PNoLt alpha p beta q.

Definition PNo_strict_imv : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R alpha p => PNo_strict_upperbd L alpha p /\ PNo_strict_lowerbd R alpha p.

Axiom PNoEq_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_upperbd L alpha p -> PNo_strict_upperbd L alpha q.

Axiom PNoEq_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_lowerbd R alpha p -> PNo_strict_lowerbd R alpha q.

Axiom PNoEq_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha -> forall p q:set -> prop,
  PNoEq_ alpha p q -> PNo_strict_imv L R alpha p -> PNo_strict_imv L R alpha q.

Axiom PNo_strict_upperbd_imp_rel_strict_upperbd : forall L:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_upperbd L alpha p -> PNo_rel_strict_upperbd L beta p.

Axiom PNo_strict_lowerbd_imp_rel_strict_lowerbd : forall R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_lowerbd R alpha p -> PNo_rel_strict_lowerbd R beta p.

Axiom PNo_strict_imv_imp_rel_strict_imv : forall L R:set -> (set -> prop) -> prop, forall alpha, ordinal alpha ->
  forall beta :e ordsucc alpha, forall p:set -> prop,
   PNo_strict_imv L R alpha p -> PNo_rel_strict_imv L R beta p.

Axiom PNo_rel_split_imv_imp_strict_imv : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha -> forall p:set -> prop,
       PNo_rel_strict_split_imv L R alpha p
    -> PNo_strict_imv L R alpha p.

Axiom ordinal_PNo_strict_imv : forall L R:set -> (set -> prop) -> prop,
  forall alpha, ordinal alpha ->
  forall p:set -> prop, (forall beta :e alpha, p beta) -> 
  (forall beta, ordinal beta -> forall q:set -> prop, L beta q -> beta :e alpha) ->
  (forall beta :e alpha, L beta p) ->
  (forall beta, ordinal beta -> forall q:set -> prop, ~R beta q) ->
  PNo_strict_imv L R alpha p.

Axiom PNo_lenbdd_strict_imv_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta :e ordsucc alpha,
      exists p:set -> prop, PNo_strict_imv L R beta p.

Definition PNo_least_rep : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => ordinal beta
       /\ PNo_strict_imv L R beta p
       /\ forall gamma :e beta,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.

Axiom PNo_lenbdd_least_rep_ex : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta, exists p:set -> prop, PNo_least_rep L R beta p.

Definition PNo_least_rep2 : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> (set -> prop) -> prop
  := fun L R beta p => PNo_least_rep L R beta p /\ forall x, x /:e beta -> ~p x.

Axiom PNo_strict_imv_pred_eq : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha -> forall p q:set -> prop,
     PNo_least_rep L R alpha p
  -> PNo_strict_imv L R alpha q
  -> forall beta :e alpha, p beta <-> q beta.

Axiom PNo_lenbdd_least_rep2_exuniq2 : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> exists beta,
        (exists p:set -> prop, PNo_least_rep2 L R beta p)
     /\ (forall p q:set -> prop, PNo_least_rep2 L R beta p -> PNo_least_rep2 L R beta q -> p = q).

(* Parameter PNo_bd "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" "ed76e76de9b58e621daa601cca73b4159a437ba0e73114924cb92ec8044f2aa2" *)
Parameter PNo_bd : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set.

(* Parameter PNo_pred "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" "b2d51dcfccb9527e9551b0d0c47d891c9031a1d4ee87bba5a9ae5215025d107a" *)
Parameter PNo_pred : (set -> (set -> prop) -> prop) -> (set -> (set -> prop) -> prop) -> set -> prop.

Axiom PNo_bd_pred_lem : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep2 L R (PNo_bd L R) (PNo_pred L R).

Axiom PNo_bd_pred : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_least_rep L R (PNo_bd L R) (PNo_pred L R).

Axiom PNo_bd_ord : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> ordinal (PNo_bd L R).

Axiom PNo_bd_pred_strict_imv : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_strict_imv L R (PNo_bd L R) (PNo_pred L R).

Axiom PNo_bd_least_imv : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> forall gamma :e PNo_bd L R,
           forall q:set -> prop, ~PNo_strict_imv L R gamma q.

Axiom PNo_bd_In : forall L R:set -> (set -> prop) -> prop,
  PNoLt_pwise L R ->
  forall alpha, ordinal alpha
   -> PNo_lenbdd alpha L
   -> PNo_lenbdd alpha R
   -> PNo_bd L R :e ordsucc alpha.

Definition PNoCutL : set -> (set -> prop) -> set -> (set -> prop) -> prop
  := fun alpha p beta q => beta :e alpha /\ PNoLt beta q alpha p.
Definition PNoCutR : set -> (set -> prop) -> set -> (set -> prop) -> prop
  := fun alpha p beta q => beta :e alpha /\ PNoLt alpha p beta q.

Axiom PNoCutL_lenbdd : forall alpha, forall p:set -> prop, PNo_lenbdd alpha (PNoCutL alpha p).

Axiom PNoCutR_lenbdd : forall alpha, forall p:set -> prop, PNo_lenbdd alpha (PNoCutR alpha p).

Axiom PNoCut_pwise : forall alpha, ordinal alpha -> forall p:set -> prop, PNoLt_pwise (PNoCutL alpha p) (PNoCutR alpha p).

Axiom PNoCut_strict_imv : forall alpha, ordinal alpha -> forall p:set -> prop, PNo_strict_imv (PNoCutL alpha p) (PNoCutR alpha p) alpha p.

Axiom PNoCut_bd_eq : forall alpha, ordinal alpha -> forall p:set -> prop, PNo_bd (PNoCutL alpha p) (PNoCutR alpha p) = alpha.

Axiom PNoCut_pred_eq : forall alpha, ordinal alpha -> forall p:set -> prop, PNoEq_ alpha p (PNo_pred (PNoCutL alpha p) (PNoCutR alpha p)).

Section TaggedSets.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Axiom not_TransSet_Sing1 : ~TransSet {1}.

Axiom not_ordinal_Sing1 : ~ordinal {1}.

Axiom tagged_not_ordinal : forall y, ~ordinal (y ').

Axiom tagged_notin_ordinal : forall alpha y, ordinal alpha -> (y ') /:e alpha.

Axiom tagged_eqE_Subq : forall alpha beta, ordinal alpha -> alpha ' = beta ' -> alpha c= beta.

Axiom tagged_eqE_eq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha ' = beta ' -> alpha = beta.

Axiom tagged_ReplE : forall alpha beta, ordinal alpha -> ordinal beta -> beta ' :e {gamma '|gamma :e alpha} -> beta :e alpha.

Axiom ordinal_notin_tagged_Repl : forall alpha Y, ordinal alpha -> alpha /:e {y '|y :e Y}.

Definition SNoElts_ : set -> set := fun alpha => alpha :\/: {beta '|beta :e alpha}.

Axiom SNoElts_mon : forall alpha beta, alpha c= beta -> SNoElts_ alpha c= SNoElts_ beta.

Definition SNo_ : set -> set -> prop := fun alpha x =>
    x c= SNoElts_ alpha
 /\ forall beta :e alpha, exactly1of2 (beta ' :e x) (beta :e x).

Definition PSNo : set -> (set -> prop) -> set :=
  fun alpha p => {beta :e alpha|p beta} :\/: {beta '|beta :e alpha, ~p beta}.

Axiom PNoEq_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, PNoEq_ alpha (fun beta => beta :e PSNo alpha p) p.

Axiom SNo_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNo_ alpha (PSNo alpha p).

Axiom SNo_PSNo_eta_ : forall alpha x, ordinal alpha -> SNo_ alpha x -> x = PSNo alpha (fun beta => beta :e x).

(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "11faa7a742daf8e4f9aaf08e90b175467e22d0e6ad3ed089af1be90cfc17314b" *)
Parameter SNo : set -> prop.

Axiom SNo_SNo : forall alpha, ordinal alpha -> forall z, SNo_ alpha z -> SNo z.

(* Parameter SNoLev "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" "293b77d05dab711767d698fb4484aab2a884304256765be0733e6bd5348119e8" *)
Parameter SNoLev : set -> set.

Axiom SNoLev_uniq_Subq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha c= beta.

Axiom SNoLev_uniq : forall x alpha beta, ordinal alpha -> ordinal beta -> SNo_ alpha x -> SNo_ beta x -> alpha = beta.

Axiom SNoLev_prop : forall x, SNo x -> ordinal (SNoLev x) /\ SNo_ (SNoLev x) x.

Axiom SNoLev_ordinal : forall x, SNo x -> ordinal (SNoLev x).

Axiom SNoLev_ : forall x, SNo x -> SNo_ (SNoLev x) x.

Axiom SNo_PSNo_eta : forall x, SNo x -> x = PSNo (SNoLev x) (fun beta => beta :e x).

Axiom SNoLev_PSNo : forall alpha, ordinal alpha -> forall p:set -> prop, SNoLev (PSNo alpha p) = alpha.

Axiom SNo_Subq : forall x y, SNo x -> SNo y -> SNoLev x c= SNoLev y -> (forall alpha :e SNoLev x, alpha :e x <-> alpha :e y) -> x c= y.

Definition SNoEq_ : set -> set -> set -> prop
 := fun alpha x y => PNoEq_ alpha (fun beta => beta :e x) (fun beta => beta :e y).

Axiom SNoEq_I : forall alpha x y, (forall beta :e alpha, beta :e x <-> beta :e y) -> SNoEq_ alpha x y.

Axiom SNoEq_E : forall alpha x y, SNoEq_ alpha x y -> forall beta :e alpha, beta :e x <-> beta :e y.

Axiom SNoEq_E1 : forall alpha x y, SNoEq_ alpha x y -> forall beta :e alpha, beta :e x -> beta :e y.

Axiom SNoEq_E2 : forall alpha x y, SNoEq_ alpha x y -> forall beta :e alpha, beta :e y -> beta :e x.

Axiom SNoEq_antimon_ : forall alpha, ordinal alpha -> forall beta :e alpha, forall x y, SNoEq_ alpha x y -> SNoEq_ beta x y.

Axiom SNo_eq : forall x y, SNo x -> SNo y -> SNoLev x = SNoLev y -> SNoEq_ (SNoLev x) x y -> x = y.

Let ctag : set -> set := fun alpha => SetAdjoin alpha {2}.

Postfix '' 100 := ctag.

Axiom ctagged_not_ordinal : forall y, ~ordinal (y '').
Axiom ctagged_notin_ordinal : forall alpha y, ordinal alpha -> (y '') /:e alpha.
Axiom Sing2_notin_SingSing1 : {2} /:e {{1}}.

Axiom ctagged_notin_SNo : forall x y, SNo x -> (y '') /:e x.
Axiom ctagged_eqE_eq : forall x y, SNo x -> SNo y -> forall u :e x, forall v :e y, u '' = v '' -> u = v.

Definition SNo_pair : set -> set -> set := fun x y => x :\/: {u ''| u :e y}.

Axiom SNo_pair_prop_1 : forall x1 y1 x2 y2, SNo x1 -> SNo x2 -> SNo_pair x1 y1 = SNo_pair x2 y2 -> x1 = x2.
Axiom SNo_pair_prop_2 : forall x1 y1 x2 y2, SNo x1 -> SNo y1 -> SNo x2 -> SNo y2 -> SNo_pair x1 y1 = SNo_pair x2 y2 -> y1 = y2.
Axiom SNo_pair_prop : forall x1 y1 x2 y2, SNo x1 -> SNo y1 -> SNo x2 -> SNo y2 -> SNo_pair x1 y1 = SNo_pair x2 y2 -> x1 = x2 /\ y1 = y2.
Axiom SNo_pair_0 : forall x, SNo_pair x 0 = x.

End TaggedSets.

Definition SNoLt : set -> set -> prop :=
  fun x y => PNoLt (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).

Infix < 490 := SNoLt.

Definition SNoLe : set -> set -> prop :=
  fun x y => PNoLe (SNoLev x) (fun beta => beta :e x) (SNoLev y) (fun beta => beta :e y).

(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Axiom SNoLtLe : forall x y, x < y -> x <= y.

Axiom SNoLeE : forall x y, SNo x -> SNo y -> x <= y -> x < y \/ x = y.

Axiom SNoEq_ref_ : forall alpha x, SNoEq_ alpha x x.

Axiom SNoEq_sym_ : forall alpha x y, SNoEq_ alpha x y -> SNoEq_ alpha y x.

Axiom SNoEq_tra_ : forall alpha x y z, SNoEq_ alpha x y -> SNoEq_ alpha y z -> SNoEq_ alpha x z.

Axiom SNoLtE : forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z, SNo z -> SNoLev z :e SNoLev x :/\: SNoLev y -> SNoEq_ (SNoLev z) z x -> SNoEq_ (SNoLev z) z y -> x < z -> z < y -> SNoLev z /:e x -> SNoLev z :e y -> p)
 -> (SNoLev x :e SNoLev y -> SNoEq_ (SNoLev x) x y -> SNoLev x :e y -> p)
 -> (SNoLev y :e SNoLev x -> SNoEq_ (SNoLev y) x y -> SNoLev y /:e x -> p)
 -> p.

(** The analogous theorem to PNoLtI1 can be recovered by SNoLt_tra (transitivity) and SNoLtI2 and SNoLtI3. **)

Axiom SNoLtI2 : forall x y,
     SNoLev x :e SNoLev y
  -> SNoEq_ (SNoLev x) x y
  -> SNoLev x :e y
  -> x < y.

Axiom SNoLtI3 : forall x y,
     SNoLev y :e SNoLev x
  -> SNoEq_ (SNoLev y) x y
  -> SNoLev y /:e x
  -> x < y.

Axiom SNoLt_irref : forall x, ~SNoLt x x.

Axiom SNoLt_trichotomy_or : forall x y, SNo x -> SNo y -> x < y \/ x = y \/ y < x.
Axiom SNoLt_trichotomy_or_impred : forall x y, SNo x -> SNo y ->
  forall p:prop,
      (x < y -> p)
   -> (x = y -> p)
   -> (y < x -> p)
   -> p.

Axiom SNoLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y < z -> x < z.

Axiom SNoLe_ref : forall x, SNoLe x x.

Axiom SNoLe_antisym : forall x y, SNo x -> SNo y -> x <= y -> y <= x -> x = y.

Axiom SNoLtLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x < y -> y <= z -> x < z.

Axiom SNoLeLt_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y < z -> x < z.

Axiom SNoLe_tra : forall x y z, SNo x -> SNo y -> SNo z -> x <= y -> y <= z -> x <= z.

Axiom SNoLtLe_or : forall x y, SNo x -> SNo y -> x < y \/ y <= x.

Axiom SNoLt_PSNo_PNoLt : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PSNo alpha p < PSNo beta q -> PNoLt alpha p beta q.

Axiom PNoLt_SNoLt_PSNo : forall alpha beta, forall p q:set -> prop,
 ordinal alpha -> ordinal beta ->
 PNoLt alpha p beta q -> PSNo alpha p < PSNo beta q.

Definition SNoCut : set -> set -> set :=
  fun L R => PSNo (PNo_bd (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)) (PNo_pred (fun alpha p => ordinal alpha /\ PSNo alpha p :e L) (fun alpha p => ordinal alpha /\ PSNo alpha p :e R)).

Definition SNoCutP : set -> set -> prop :=
 fun L R =>
      (forall x :e L, SNo x)
   /\ (forall y :e R, SNo y)
   /\ (forall x :e L, forall y :e R, x < y).

Axiom SNoCutP_SNoCut : forall L R, SNoCutP L R
 -> SNo (SNoCut L R)
 /\ SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
 /\ (forall x :e L, x < SNoCut L R)
 /\ (forall y :e R, SNoCut L R < y)
 /\ (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z).

Axiom SNoCutP_SNoCut_impred : forall L R, SNoCutP L R
 -> forall p:prop,
      (SNo (SNoCut L R)
    -> SNoLev (SNoCut L R) :e ordsucc ((\/_ x :e L, ordsucc (SNoLev x)) :\/: (\/_ y :e R, ordsucc (SNoLev y)))
    -> (forall x :e L, x < SNoCut L R)
    -> (forall y :e R, SNoCut L R < y)
    -> (forall z, SNo z -> (forall x :e L, x < z) -> (forall y :e R, z < y) -> SNoLev (SNoCut L R) c= SNoLev z /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z)
    -> p)
   -> p.

Axiom SNoCutP_L_0: forall L, (forall x :e L, SNo x) -> SNoCutP L 0.
Axiom SNoCutP_0_R: forall R, (forall x :e R, SNo x) -> SNoCutP 0 R.
Axiom SNoCutP_0_0: SNoCutP 0 0.
Axiom SNoCut_0_0: SNoCut 0 0 = 0.

Axiom ordinal_SNoLt_In : forall alpha beta, ordinal alpha -> ordinal beta -> alpha < beta -> alpha :e beta.

Axiom ordinal_SNoLe_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha <= beta -> alpha c= beta.

Definition SNoS_ : set -> set := fun alpha => {x :e Power (SNoElts_ alpha)|exists beta :e alpha, SNo_ beta x}.

Axiom SNoS_E : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, exists beta :e alpha, SNo_ beta x.

Section TaggedSets2.

Let tag : set -> set := fun alpha => SetAdjoin alpha {1}.
Postfix ' 100 := tag.

Axiom SNoS_I : forall alpha, ordinal alpha -> forall x, forall beta :e alpha, SNo_ beta x -> x :e SNoS_ alpha.

Axiom SNoS_I2 : forall x y, SNo x -> SNo y -> SNoLev x :e SNoLev y -> x :e SNoS_ (SNoLev y).
 
Axiom SNoS_Subq : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> SNoS_ alpha c= SNoS_ beta.

Axiom SNoLev_uniq2 : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNoLev x = alpha.

Axiom SNoS_E2 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha,
 forall p:prop,
     (SNoLev x :e alpha -> ordinal (SNoLev x) -> SNo x -> SNo_ (SNoLev x) x -> p)
  -> p.

Axiom SNoS_In_neq : forall w, SNo w -> forall x :e SNoS_ (SNoLev w), x <> w.

Axiom SNoS_SNoLev : forall z, SNo z -> z :e SNoS_ (ordsucc (SNoLev z)).

Definition SNoL : set -> set := fun z => {x :e SNoS_ (SNoLev z) | x < z}.
Definition SNoR : set -> set := fun z => {y :e SNoS_ (SNoLev z) | z < y}.

Axiom SNoCutP_SNoL_SNoR: forall z, SNo z -> SNoCutP (SNoL z) (SNoR z).

Axiom SNoL_E : forall x, SNo x -> forall w :e SNoL x,
  forall p:prop,
       (SNo w -> SNoLev w :e SNoLev x -> w < x -> p)
    -> p.

Axiom SNoR_E : forall x, SNo x -> forall z :e SNoR x,
  forall p:prop,
       (SNo z -> SNoLev z :e SNoLev x -> x < z -> p)
    -> p.

Axiom SNoL_SNoS : forall x, SNo x -> forall w :e SNoL x, w :e SNoS_ (SNoLev x).
Axiom SNoR_SNoS : forall x, SNo x -> forall z :e SNoR x, z :e SNoS_ (SNoLev x).
Axiom SNoL_SNoS_ : forall z, SNoL z c= SNoS_ (SNoLev z).
Axiom SNoR_SNoS_ : forall z, SNoR z c= SNoS_ (SNoLev z).

Axiom SNoL_I : forall z, SNo z -> forall x, SNo x -> SNoLev x :e SNoLev z -> x < z -> x :e SNoL z.

Axiom SNoR_I : forall z, SNo z -> forall y, SNo y -> SNoLev y :e SNoLev z -> z < y -> y :e SNoR z.

Axiom SNo_eta : forall z, SNo z -> z = SNoCut (SNoL z) (SNoR z).

Axiom SNoCutP_SNo_SNoCut : forall L R, SNoCutP L R -> SNo (SNoCut L R).

Axiom SNoCutP_SNoCut_L : forall L R, SNoCutP L R -> forall x :e L, x < SNoCut L R.

Axiom SNoCutP_SNoCut_R : forall L R, SNoCutP L R -> forall y :e R, SNoCut L R < y.

Axiom SNoCutP_SNoCut_fst : forall L R, SNoCutP L R ->
 forall z, SNo z
   -> (forall x :e L, x < z)
   -> (forall y :e R, z < y)
   -> SNoLev (SNoCut L R) c= SNoLev z
   /\ SNoEq_ (SNoLev (SNoCut L R)) (SNoCut L R) z.

Axiom SNoCut_Le : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 <= SNoCut L2 R2.

Axiom SNoCut_ext : forall L1 R1 L2 R2, SNoCutP L1 R1 -> SNoCutP L2 R2
  -> (forall w :e L1, w < SNoCut L2 R2)
  -> (forall z :e R1, SNoCut L2 R2 < z)
  -> (forall w :e L2, w < SNoCut L1 R1)
  -> (forall z :e R2, SNoCut L1 R1 < z)
  -> SNoCut L1 R1 = SNoCut L2 R2.

Axiom SNoLt_SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y -> x < y ->
 forall p:prop,
    (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> p.

Axiom SNoL_or_SNoR_impred: forall x y, SNo x -> SNo y ->
 forall p:prop,
    (x = y -> p)
 -> (forall z :e SNoL y, z :e SNoR x -> p)
 -> (x :e SNoL y -> p)
 -> (y :e SNoR x -> p)
 -> (forall z :e SNoR y, z :e SNoL x -> p)
 -> (x :e SNoR y -> p)
 -> (y :e SNoL x -> p)
 -> p.

Axiom ordinal_SNo_ : forall alpha, ordinal alpha -> SNo_ alpha alpha.

Axiom ordinal_SNoL : forall alpha, ordinal alpha -> SNoL alpha = SNoS_ alpha.
Axiom ordinal_SNoR : forall alpha, ordinal alpha -> SNoR alpha = Empty.
Axiom ordinal_SNoCutP : forall alpha, ordinal alpha -> SNoCutP (SNoS_ alpha) Empty.
Axiom ordinal_SNoCut_eta : forall alpha, ordinal alpha -> alpha = SNoCut (SNoS_ alpha) Empty.

Axiom SNo_0 : SNo 0.
Axiom SNoLev_0 : SNoLev 0 = 0.
Axiom SNoL_0 : SNoL 0 = 0.
Axiom SNoR_0 : SNoR 0 = 0.
Axiom SNoL_1 : SNoL 1 = 1.
Axiom SNoR_1 : SNoR 1 = 0.
Axiom SNo_max_SNoLev : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> SNoLev x = x.
Axiom SNo_max_ordinal : forall x, SNo x -> (forall y :e SNoS_ (SNoLev x), y < x) -> ordinal x.

Definition SNo_extend0 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x /\ delta <> SNoLev x).

Definition SNo_extend1 : set -> set := fun x => PSNo (ordsucc (SNoLev x)) (fun delta => delta :e x \/ delta = SNoLev x).

Axiom SNo_extend0_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend0 x).

Axiom SNo_extend1_SNo_ : forall x, SNo x -> SNo_ (ordsucc (SNoLev x)) (SNo_extend1 x).

Axiom SNo_extend0_SNo : forall x, SNo x -> SNo (SNo_extend0 x).

Axiom SNo_extend1_SNo : forall x, SNo x -> SNo (SNo_extend1 x).

Axiom SNo_extend0_SNoLev : forall x, SNo x -> SNoLev (SNo_extend0 x) = ordsucc (SNoLev x).

Axiom SNo_extend1_SNoLev : forall x, SNo x -> SNoLev (SNo_extend1 x) = ordsucc (SNoLev x).

Axiom SNo_extend0_nIn : forall x, SNo x -> SNoLev x /:e SNo_extend0 x.

Axiom SNo_extend1_In : forall x, SNo x -> SNoLev x :e SNo_extend1 x.

Axiom SNo_extend0_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend0 x) x.

Axiom SNo_extend1_SNoEq : forall x, SNo x -> SNoEq_ (SNoLev x) (SNo_extend1 x) x.

Axiom SNo_extend0_Lt: forall x, SNo x -> SNo_extend0 x < x.
Axiom SNo_extend1_Gt: forall x, SNo x -> x < SNo_extend1 x.

Axiom nat_p_SNo: forall n, nat_p n -> SNo n.
Axiom omega_SNo: forall n :e omega, SNo n.

(** eps_ n is the Surreal Number 1/2^n, without needing to define division or exponents first **)
Definition eps_ : set -> set := fun n => {0} :\/: {(ordsucc m) ' | m :e n}.

Axiom eps_ordinal_In_eq_0 : forall n alpha, ordinal alpha -> alpha :e eps_ n -> alpha = 0.
Axiom eps_0_1 : eps_ 0 = 1.
Axiom SNo__eps_ : forall n :e omega, SNo_ (ordsucc n) (eps_ n).
Axiom SNo_eps_ : forall n :e omega, SNo (eps_ n).
Axiom SNoLev_eps_ : forall n :e omega, SNoLev (eps_ n) = ordsucc n.
Axiom SNo_eps_SNoS_omega : forall n :e omega, eps_ n :e SNoS_ omega.
Axiom SNo_eps_decr : forall n :e omega, forall m :e n, eps_ n < eps_ m.
Axiom SNo_eps_pos : forall n :e omega, 0 < eps_ n.
Axiom SNo_pos_eps_Lt : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> eps_ n < x.
Axiom SNo_pos_eps_Le : forall n, nat_p n -> forall x :e SNoS_ (ordsucc (ordsucc n)), 0 < x -> eps_ n <= x.

End TaggedSets2.

Axiom ordinal_SNo : forall alpha, ordinal alpha -> SNo alpha.

Axiom ordinal_SNoLev : forall alpha, ordinal alpha -> SNoLev alpha = alpha.

Axiom ordinal_SNoLev_max : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e alpha -> z < alpha.

Axiom ordinal_In_SNoLt : forall alpha, ordinal alpha -> forall beta :e alpha, beta < alpha.

Axiom ordinal_SNoLev_max_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> z <= alpha.

Axiom ordinal_Subq_SNoLe : forall alpha beta, ordinal alpha -> ordinal beta -> alpha c= beta -> alpha <= beta.

Axiom SNo_etaE : forall z, SNo z ->
  forall p:prop,
     (forall L R, SNoCutP L R
       -> (forall x :e L, SNoLev x :e SNoLev z)
       -> (forall y :e R, SNoLev y :e SNoLev z)
       -> z = SNoCut L R
       -> p)
   -> p.

(*** surreal induction ***)
Axiom SNo_ind : forall P:set -> prop,
  (forall L R, SNoCutP L R
   -> (forall x :e L, P x)
   -> (forall y :e R, P y)
   -> P (SNoCut L R))
 -> forall z, SNo z -> P z.

(*** surreal recursion ***)
Section SurrealRecI.

Variable F:set -> (set -> set) -> set.

(* Parameter SNo_rec_i "352082c509ab97c1757375f37a2ac62ed806c7b39944c98161720a584364bfaf" "be45dfaed6c479503a967f3834400c4fd18a8a567c8887787251ed89579f7be3" *)
Parameter SNo_rec_i : set -> set.

Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> set, (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Axiom SNo_rec_i_eq : forall z, SNo z -> SNo_rec_i z = F z SNo_rec_i.

End SurrealRecI.

Section SurrealRecII.

Variable F:set -> (set -> (set -> set)) -> (set -> set).

(* Parameter SNo_rec_ii "030b1b3db48f720b8db18b1192717cad8f204fff5fff81201b9a2414f5036417" "e148e62186e718374accb69cda703e3440725cca8832aed55c0b32731f7401ab" *)
Parameter SNo_rec_ii : set -> (set -> set).

Hypothesis Fr: forall z, SNo z ->
   forall g h:set -> (set -> set), (forall w :e SNoS_ (SNoLev z), g w = h w)
     -> F z g = F z h.

Axiom SNo_rec_ii_eq : forall z, SNo z -> SNo_rec_ii z = F z SNo_rec_ii.

End SurrealRecII.

Section SurrealRec2.

Variable F:set -> set -> (set -> set -> set) -> set.

(* Parameter SNo_rec2 "9c6267051fa817eed39b404ea37e7913b3571fe071763da2ebc1baa56b4b77f5" "7d10ab58310ebefb7f8bf63883310aa10fc2535f53bb48db513a868bc02ec028" *)
Parameter SNo_rec2 : set -> set -> set.

Hypothesis Fr: forall w, SNo w -> forall z, SNo z ->
   forall g h:set -> set -> set,
        (forall x :e SNoS_ (SNoLev w), forall y, SNo y -> g x y = h x y)
     -> (forall y :e SNoS_ (SNoLev z), g w y = h w y)
     -> F w z g = F w z h.

Axiom SNo_rec2_eq : forall w, SNo w -> forall z, SNo z ->
   SNo_rec2 w z = F w z SNo_rec2.

End SurrealRec2.

Axiom SNo_ordinal_ind : forall P:set -> prop,
  (forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, P x)
  ->
  (forall x, SNo x -> P x).

Axiom SNo_ordinal_ind2 : forall P:set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, P x y)
  ->
  (forall x y, SNo x -> SNo y -> P x y).

Axiom SNo_ordinal_ind3 : forall P:set -> set -> set -> prop,
  (forall alpha, ordinal alpha ->
   forall beta, ordinal beta ->
   forall gamma, ordinal gamma ->
   forall x :e SNoS_ alpha, forall y :e SNoS_ beta, forall z :e SNoS_ gamma, P x y z)
  ->
  (forall x y z, SNo x -> SNo y -> SNo z -> P x y z).

Axiom SNoLev_ind : forall P:set -> prop,
  (forall x, SNo x -> (forall w :e SNoS_ (SNoLev x), P w) -> P x)
  ->
  (forall x, SNo x -> P x).

Axiom SNoLev_ind2 : forall P:set -> set -> prop,
  (forall x y, SNo x -> SNo y
    -> (forall w :e SNoS_ (SNoLev x), P w y)
    -> (forall z :e SNoS_ (SNoLev y), P x z)
    -> (forall w :e SNoS_ (SNoLev x), forall z :e SNoS_ (SNoLev y), P w z)
    -> P x y)
-> forall x y, SNo x -> SNo y -> P x y.

Axiom SNoLev_ind3 : forall P:set -> set -> set -> prop,
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

Axiom SNo_1 : SNo 1.
Axiom SNo_2 : SNo 2.
Axiom SNo_omega : SNo omega.
Axiom SNoLt_0_1 : 0 < 1.
Axiom SNoLt_0_2 : 0 < 2.
Axiom SNoLt_1_2 : 1 < 2.

Axiom SNoLev_0_eq_0 : forall x, SNo x -> SNoLev x = 0 -> x = 0.
Axiom restr_SNo_ : forall x, SNo x -> forall alpha :e SNoLev x, SNo_ alpha (x :/\: SNoElts_ alpha).
Axiom restr_SNo : forall x, SNo x -> forall alpha :e SNoLev x, SNo (x :/\: SNoElts_ alpha).
Axiom restr_SNoLev : forall x, SNo x -> forall alpha :e SNoLev x, SNoLev (x :/\: SNoElts_ alpha) = alpha.
Axiom restr_SNoEq : forall x, SNo x -> forall alpha :e SNoLev x, SNoEq_ alpha (x :/\: SNoElts_ alpha) x.
Axiom restr_SNo_SNoCut : forall x, SNo x -> forall alpha :e SNoLev x, forall p:prop,
    (SNoCutP {w :e SNoL x|SNoLev w :e alpha} {z :e SNoR x|SNoLev z :e alpha}
  -> x :/\: SNoElts_ alpha = SNoCut {w :e SNoL x|SNoLev w :e alpha} {z :e SNoR x|SNoLev z :e alpha}
  -> p)
 -> p.

(* Parameter pack_e "faab5f334ba3328f24def7e6fcb974000058847411a2eb0618014eca864e537f" "dd8f2d332fef3b4d27898ab88fa5ddad0462180c8d64536ce201f5a9394f40dd" *)
Parameter pack_e : set -> set -> set.

Axiom pack_e_0_eq : forall S X, forall c:set, S = pack_e X c -> X = S 0.

Axiom pack_e_0_eq2 : forall X, forall c:set, X = pack_e X c 0.

Axiom pack_e_1_eq : forall S X, forall c:set, S = pack_e X c -> c = S 1.

Axiom pack_e_1_eq2 : forall X, forall c:set, c = pack_e X c 1.

Axiom pack_e_inj: forall X X', forall c c', pack_e X c = pack_e X' c' -> X = X' /\ c = c'.

Definition struct_e : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall c:set, c :e X -> q (pack_e X c)) -> q S.

Axiom pack_struct_e_I: forall X, forall c:set, c :e X -> struct_e (pack_e X c).

Axiom pack_struct_e_E1: forall X, forall c:set, struct_e (pack_e X c) -> c :e X.

Axiom struct_e_eta: forall S, struct_e S -> S = pack_e (S 0) (S 1).

(* Parameter unpack_e_i "933a1383079fba002694718ec8040dc85a8cca2bd54c5066c99fff135594ad7c" "91fff70be2f95d6e5e3fe9071cbd57d006bdee7d805b0049eefb19947909cc4e" *)
Parameter unpack_e_i : set -> (set -> set -> set) -> set.

Axiom unpack_e_i_eq : forall Phi:set -> set -> set,
  forall X, forall c:set, unpack_e_i (pack_e X c) Phi = Phi X c.

(* Parameter unpack_e_o "f3affb534ca9027c56d1a15dee5adcbb277a5c372d01209261fee22c6dd6eab2" "8e748578991012f665a61609fe4f951aa5e3791f69c71f5a551e29e39855416c" *)
Parameter unpack_e_o : set -> (set -> set -> prop) -> prop.

Axiom unpack_e_o_eq : forall Phi:set -> set -> prop,
  forall X, forall c:set, unpack_e_o (pack_e X c) Phi = Phi X c.

(* Parameter pack_u "9575c80a2655d3953184d74d13bd5860d4f415acbfc25d279378b4036579af65" "119d13725af3373dd508f147836c2eff5ff5acf92a1074ad6c114b181ea8a933" *)
Parameter pack_u : set -> (set -> set) -> set.

Axiom pack_u_0_eq : forall S X, forall F:set -> set, S = pack_u X F -> X = S 0.

Axiom pack_u_0_eq2 : forall X, forall F:set -> set, X = pack_u X F 0.

Axiom pack_u_1_eq : forall S X, forall F:set -> set, S = pack_u X F -> forall x :e X, F x = decode_u (S 1) x.

Axiom pack_u_1_eq2 : forall X, forall F:set -> set, forall x :e X, F x = decode_u (pack_u X F 1) x.

Axiom pack_u_inj: forall X X', forall F F':set -> set, pack_u X F = pack_u X' F' -> X = X' /\ forall x :e X, F x = F' x.

Axiom pack_u_ext : forall X, forall F F':set -> set,
     (forall x :e X, F x = F' x)
  -> pack_u X F = pack_u X F'.

Definition struct_u : set -> prop := fun S => forall q:set -> prop, (forall X, forall F:set -> set, (forall x :e X, F x :e X) -> q (pack_u X F)) -> q S.

Axiom pack_struct_u_I: forall X, forall F:set -> set, (forall x :e X, F x :e X) -> struct_u (pack_u X F).

Axiom pack_struct_u_E1: forall X, forall F:set -> set, struct_u (pack_u X F) -> forall x :e X, F x :e X.

Axiom struct_u_eta: forall S, struct_u S -> S = pack_u (S 0) (decode_u (S 1)).

(* Parameter unpack_u_i "4e62ce5c996f13a11eb05d8dbff98e7acceaca2d3b3a570bea862ad74b79f4df" "111dc52d4fe7026b5a4da1edbfb7867d219362a0e5da0682d7a644a362d95997" *)
Parameter unpack_u_i : set -> (set -> (set -> set) -> set) -> set.

Axiom unpack_u_i_eq : forall Phi:set -> (set -> set) -> set,
  forall X, forall F:set -> set,
  (forall F':set -> set, (forall x :e X, F x = F' x) -> Phi X F' = Phi X F)
  ->
  unpack_u_i (pack_u X F) Phi = Phi X F.

(* Parameter unpack_u_o "22baf0455fa7619b6958e5bd762f4085bae580997860844329722650209d24bf" "eb32c2161bb5020efad8203cd45aa4738a4908823619b55963cc2fd1f9830098" *)
Parameter unpack_u_o : set -> (set -> (set -> set) -> prop) -> prop.

Axiom unpack_u_o_eq : forall Phi:set -> (set -> set) -> prop,
  forall X, forall F:set -> set,
  (forall F':set -> set, (forall x :e X, F x = F' x) -> Phi X F' = Phi X F)
  ->
  unpack_u_o (pack_u X F) Phi = Phi X F.

(* Parameter pack_b "e007d96601771e291e9083ce21b5e97703bce4ff5257fec59b7ed3dbb05b5319" "855387af88aad68b5f942a3a97029fcd79fe0a4e781cdf546d058297f8a483ce" *)
Parameter pack_b : set -> (set -> set -> set) -> set.

Axiom pack_b_0_eq : forall S X, forall F:set -> set -> set, S = pack_b X F -> X = S 0.

Axiom pack_b_0_eq2 : forall X, forall F:set -> set -> set, X = pack_b X F 0.

Axiom pack_b_1_eq : forall S X, forall F:set -> set -> set, S = pack_b X F -> forall x y :e X, F x y = decode_b (S 1) x y.

Axiom pack_b_1_eq2 : forall X, forall F:set -> set -> set, forall x y :e X, F x y = decode_b (pack_b X F 1) x y.

Axiom pack_b_inj: forall X X', forall F F':set -> set -> set, pack_b X F = pack_b X' F' -> X = X' /\ forall x y :e X, F x y = F' x y.

Axiom pack_b_ext : forall X, forall F F':set -> set -> set,
     (forall x y :e X, F x y = F' x y)
  -> pack_b X F = pack_b X F'.

Definition struct_b : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall F:set -> set -> set, (forall x y :e X, F x y :e X) -> q (pack_b X F)) -> q S.

Axiom pack_struct_b_I: forall X, forall F:set -> set -> set, (forall x y :e X, F x y :e X) -> struct_b (pack_b X F).

Axiom pack_struct_b_E1: forall X, forall F:set -> set -> set, struct_b (pack_b X F) -> forall x y :e X, F x y :e X.

Axiom struct_b_eta: forall S, struct_b S -> S = pack_b (S 0) (decode_b (S 1)).

(* Parameter unpack_b_i "2890e728fd41ee56580615f32603326f19352dda5a1deea69ef696e560d62300" "b3bb92bcc166500c6f6465bf41e67a407d3435b2ce2ac6763fb02fac8e30640e" *)
Parameter unpack_b_i : set -> (set -> (set -> set -> set) -> set) -> set.

Axiom unpack_b_i_eq : forall Phi:set -> (set -> set -> set) -> set,
  forall X, forall F:set -> set -> set,
  (forall F':set -> set -> set, (forall x y :e X, F x y = F' x y) -> Phi X F' = Phi X F)
  ->
  unpack_b_i (pack_b X F) Phi = Phi X F.

(* Parameter unpack_b_o "0fa2c67750f22ef718feacbb3375b43caa7129d02200572180f9cfe7abf54cec" "0601c1c35ff2c84ae36acdecfae98d553546d98a227f007481baf6b962cc1dc8" *)
Parameter unpack_b_o : set -> (set -> (set -> set -> set) -> prop) -> prop.

Axiom unpack_b_o_eq : forall Phi:set -> (set -> set -> set) -> prop,
  forall X, forall F:set -> set -> set,
  (forall F':set -> set -> set, (forall x y :e X, F x y = F' x y) -> Phi X F' = Phi X F)
  ->
  unpack_b_o (pack_b X F) Phi = Phi X F.

(* Parameter pack_p "3c539dbbee9d5ff440b9024180e52e9c2adde77bbaa8264d8f67d724d8c8cb25" "d5afae717eff5e7035dc846b590d96bd5a7727284f8ff94e161398c148ab897f" *)
Parameter pack_p : set -> (set -> prop) -> set.

Axiom pack_p_0_eq : forall S X, forall P:set -> prop, S = pack_p X P -> X = S 0.

Axiom pack_p_0_eq2 : forall X, forall P:set -> prop, X = pack_p X P 0.

Axiom pack_p_1_eq : forall S X, forall P:set -> prop, S = pack_p X P -> forall x :e X, P x = decode_p (S 1) x.

Axiom pack_p_1_eq2 : forall X, forall P:set -> prop, forall x :e X, P x = decode_p (pack_p X P 1) x.

Axiom pack_p_inj: forall X X', forall P P':set -> prop, pack_p X P = pack_p X' P' -> X = X' /\ forall x :e X, P x = P' x.

Axiom pack_p_ext : forall X, forall P P':set -> prop,
     (forall x :e X, P x <-> P' x)
  -> pack_p X P = pack_p X P'.

Definition struct_p : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall P:set -> prop, q (pack_p X P)) -> q S.

Axiom pack_struct_p_I: forall X, forall P:set -> prop, struct_p (pack_p X P).

Axiom struct_p_eta: forall S, struct_p S -> S = pack_p (S 0) (decode_p (S 1)).

(* Parameter unpack_p_i "e24c519b20075049733185165766605b441fbcc5ee0900c9bd48c0c792ba5859" "dda44134499f98b412d13481678ca2262d520390676ab6b40e0cb0e0768412f6" *)
Parameter unpack_p_i : set -> (set -> (set -> prop) -> set) -> set.

Axiom unpack_p_i_eq : forall Phi:set -> (set -> prop) -> set,
  forall X, forall P:set -> prop,
  (forall P':set -> prop, (forall x :e X, P x <-> P' x) -> Phi X P' = Phi X P)
  ->
  unpack_p_i (pack_p X P) Phi = Phi X P.

(* Parameter unpack_p_o "4b92ca0383b3989d01ddc4ec8bdf940b54163f9a29e460dfd502939eb880162f" "30f11fc88aca72af37fd2a4235aa22f28a552bbc44f1fb01f4edf7f2b7e376ac" *)
Parameter unpack_p_o : set -> (set -> (set -> prop) -> prop) -> prop.

Axiom unpack_p_o_eq : forall Phi:set -> (set -> prop) -> prop,
  forall X, forall P:set -> prop,
  (forall P':set -> prop, (forall x :e X, P x <-> P' x) -> Phi X P' = Phi X P)
  ->
  unpack_p_o (pack_p X P) Phi = Phi X P.

(* Parameter pack_r "39d80099e1b48aed4548f424ae4f1ff25b2d595828aff4b3a5abe232ca0348b5" "217a7f92acc207b15961c90039aa929f0bd5d9212f66ce5595c3af1dd8b9737e" *)
Parameter pack_r : set -> (set -> set -> prop) -> set.

Axiom pack_r_0_eq : forall S X, forall R:set -> set -> prop, S = pack_r X R -> X = S 0.

Axiom pack_r_0_eq2 : forall X, forall R:set -> set -> prop, X = pack_r X R 0.

Axiom pack_r_1_eq : forall S X, forall R:set -> set -> prop, S = pack_r X R -> forall x y :e X, R x y = decode_r (S 1) x y.

Axiom pack_r_1_eq2 : forall X, forall R:set -> set -> prop, forall x y :e X, R x y = decode_r (pack_r X R 1) x y.

Axiom pack_r_inj: forall X X', forall R R':set -> set -> prop, pack_r X R = pack_r X' R' -> X = X' /\ forall x y :e X, R x y = R' x y.

Axiom pack_r_ext : forall X, forall R R':set -> set -> prop,
     (forall x y :e X, R x y <-> R' x y)
  -> pack_r X R = pack_r X R'.

Definition struct_r : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall R:set -> set -> prop, q (pack_r X R)) -> q S.

Axiom pack_struct_r_I: forall X, forall R:set -> set -> prop, struct_r (pack_r X R).

Axiom struct_r_eta: forall S, struct_r S -> S = pack_r (S 0) (decode_r (S 1)).

(* Parameter unpack_r_i "8e3580f89907c6b36f6b57ad7234db3561b008aa45f8fa86d5e51a7a85cd74b6" "3ace9e6e064ec2b6e839b94e81788f9c63b22e51ec9dec8ee535d50649401cf4" *)
Parameter unpack_r_i : set -> (set -> (set -> set -> prop) -> set) -> set.

Axiom unpack_r_i_eq : forall Phi:set -> (set -> set -> prop) -> set,
  forall X, forall R:set -> set -> prop,
  (forall R':set -> set -> prop, (forall x y :e X, R x y <-> R' x y) -> Phi X R' = Phi X R)
  ->
  unpack_r_i (pack_r X R) Phi = Phi X R.

(* Parameter unpack_r_o "8d2ef9c9e522891d1fe605a62dffeab8aefb6325650e4eab14135e7eee8002c5" "e3e6af0984cda0a02912e4f3e09614b67fc0167c625954f0ead4110f52ede086" *)
Parameter unpack_r_o : set -> (set -> (set -> set -> prop) -> prop) -> prop.

Axiom unpack_r_o_eq : forall Phi:set -> (set -> set -> prop) -> prop,
  forall X, forall R:set -> set -> prop,
  (forall R':set -> set -> prop, (forall x y :e X, R x y <-> R' x y) -> Phi X R' = Phi X R)
  ->
  unpack_r_o (pack_r X R) Phi = Phi X R.

(* Parameter pack_c "545700730c93ce350b761ead914d98adf2edbd5c9f253d9a6df972641fee3aed" "cd75b74e4a07d881da0b0eda458a004806ed5c24b08fd3fef0f43e91f64c4633" *)
Parameter pack_c : set -> ((set -> prop) -> prop) -> set.

Axiom pack_c_0_eq : forall S X, forall C:(set -> prop) -> prop, S = pack_c X C -> X = S 0.

Axiom pack_c_0_eq2 : forall X, forall C:(set -> prop) -> prop, X = pack_c X C 0.

Axiom pack_c_1_eq : forall S X, forall C:(set -> prop) -> prop, S = pack_c X C -> forall U:set -> prop, (forall x, U x -> x :e X) -> C U = decode_c (S 1) U.

Axiom pack_c_1_eq2 : forall X, forall C:(set -> prop) -> prop, forall U:set -> prop, (forall x, U x -> x :e X) -> C U = decode_c (pack_c X C 1) U.

Axiom pack_c_inj: forall X X', forall C C':(set -> prop) -> prop, pack_c X C = pack_c X' C' -> X = X' /\ forall U:set -> prop, (forall x, U x -> x :e X) -> C U = C' U.

Axiom pack_c_ext : forall X, forall C C':(set -> prop) -> prop,
     (forall U:set -> prop, (forall x, U x -> x :e X) -> (C U <-> C' U))
  -> pack_c X C = pack_c X C'.

Definition struct_c : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall C:(set -> prop) -> prop, q (pack_c X C)) -> q S.

Axiom pack_struct_c_I: forall X, forall C:(set -> prop) -> prop, struct_c (pack_c X C).

Axiom struct_c_eta: forall S, struct_c S -> S = pack_c (S 0) (decode_c (S 1)).

(* Parameter unpack_c_i "61506fb3d41686d186b4403e49371053ce82103f40b14367780a74e0d62e06bf" "a01360cac9e6ba0460797b632a50d83b7fadb5eadb897964c7102639062b23ba" *)
Parameter unpack_c_i : set -> (set -> ((set -> prop) -> prop) -> set) -> set.

Axiom unpack_c_i_eq : forall Phi:set -> ((set -> prop) -> prop) -> set,
  forall X, forall C:(set -> prop) -> prop,
  (forall C':(set -> prop) -> prop, (forall U:set -> prop, (forall x, U x -> x :e X) -> (C U <-> C' U)) -> Phi X C' = Phi X C)
  ->
  unpack_c_i (pack_c X C) Phi = Phi X C.

(* Parameter unpack_c_o "de068dc4f75465842d1d600bf2bf3a79223eb41ba14d4767bbaf047938e706ec" "939baef108d0de16a824c79fc4e61d99b3a9047993a202a0f47c60d551b65834" *)
Parameter unpack_c_o : set -> (set -> ((set -> prop) -> prop) -> prop) -> prop.

Axiom unpack_c_o_eq : forall Phi:set -> ((set -> prop) -> prop) -> prop,
  forall X, forall C:(set -> prop) -> prop,
  (forall C':(set -> prop) -> prop, (forall U:set -> prop, (forall x, U x -> x :e X) -> (C U <-> C' U)) -> Phi X C' = Phi X C)
  ->
  unpack_c_o (pack_c X C) Phi = Phi X C.

(* Parameter canonical_elt "7830817b065e5068a5d904d993bb45fa4ddb7b1157b85006099fa8b2d1698319" "24615c6078840ea77a483098ef7fecf7d2e10585bf1f31bd0c61fbaeced3ecb8" *)
Parameter canonical_elt : (set->set->prop)->set->set.
Axiom canonical_elt_rel : forall R:set->set->prop, forall x:set, R x x -> R x (canonical_elt R x).
Axiom canonical_elt_eq : forall R:set->set->prop, per R -> forall x y:set, R x y -> canonical_elt R x = canonical_elt R y.
Axiom canonical_elt_idem : forall R:set->set->prop, per R -> forall x:set, R x x -> canonical_elt R x = canonical_elt R (canonical_elt R x).

(* Parameter quotient "aa0da3fb21dcb8f9e118c9149aed409bb70d0408a316f1cce303813bf2428859" "185d8f16b44939deb8995cbb9be7d1b78b78d5fc4049043a3b6ccc9ec7b33b41" *)
Parameter quotient : (set->set->prop)->set->prop.
Axiom quotient_prop1 : forall R:set->set->prop,
 forall x:set, quotient R x -> R x x.
Axiom quotient_prop2 : forall R:set->set->prop, per R ->
 forall x y:set, quotient R x -> quotient R y -> R x y -> x = y.

(* Parameter canonical_elt_def "3727e8cd9a7e7bc56ef00eafdefe3e298cfb2bd8340a0f164b9611ce2f2e3b2a" "cd4f601256fbe0285d49ded42c4f554df32a64182e0242462437212fe90b44cd" *)
Parameter canonical_elt_def : (set->set->prop)->(set->set)->set->set.
Axiom canonical_elt_def_rel : forall R:set->set->prop, forall d:set->set, forall x:set, R x x -> R x (canonical_elt_def R d x).
Axiom canonical_elt_def_eq :
 forall R:set->set->prop, per R ->
 forall d:set->set, (forall x y:set, R x y -> d x = d y) ->
 forall x y:set, R x y -> canonical_elt_def R d x = canonical_elt_def R d y.
Axiom canonical_elt_def_idem :
 forall R:set->set->prop, per R ->
 forall d:set->set, (forall x y:set, R x y -> d x = d y) ->
 forall x:set, R x x -> canonical_elt_def R d x = canonical_elt_def R d (canonical_elt_def R d x).

(* Parameter quotient_def "f61cccfd432116f3443aff9f776423c64eaa3691d3634bf423d5ddd89caaa136" "612d4b4fd0d22dd5985c10cf0fed7eda4e18dce70710ebd2cd5e91acf3995937" *)
Parameter quotient_def : (set->set->prop)->(set->set)->set->prop.
Axiom quotient_def_prop0 :
 forall R:set->set->prop, per R ->
 forall d:set->set,
 forall x:set, R x (d x) -> x = d x -> quotient_def R d x.
Axiom quotient_def_prop1 :
 forall R:set->set->prop,
 forall d:set->set,
 forall x:set, quotient_def R d x -> R x x.
Axiom quotient_def_prop2 :
 forall R:set->set->prop, per R ->
 forall d:set->set, (forall x y:set, R x y -> d x = d y) ->
 forall x y:set, quotient_def R d x -> quotient_def R d y -> R x y -> x = y.

(**
 Abstract Version of Natural Numbers using Peano axioms.
 Note that base can be thought of as 0 or 1, with the difference
 only showing up if one defines addition and multiplication.
 **)
Section explicit_Nats.

Variable N : set.
Variable base : set.
Variable S : set -> set.

(* Parameter explicit_Nats "4a59caa11140eabb1b7db2d3493fe76a92b002b3b27e3dfdd313708c6c6ca78f" "3fb62f75e778736947d086a36d35ebe45a5d60bf0a340a0761ba08a396d4123a" *)
Parameter explicit_Nats : prop.

Axiom explicit_Nats_I:
    (base :e N)
 -> (forall m :e N, S m :e N)
 -> (forall m :e N, S m <> base)
 -> (forall m n :e N, S m = S n -> m = n)
 -> (forall p:set -> prop, p base -> (forall m, p m -> p (S m)) -> (forall m :e N, p m))
 -> explicit_Nats.

Axiom explicit_Nats_E : forall q:prop, 
    (explicit_Nats
  -> (base :e N)
  -> (forall m :e N, S m :e N)
  -> (forall m :e N, S m <> base)
  -> (forall m n :e N, S m = S n -> m = n)
  -> (forall p:set -> prop, p base -> (forall m, p m -> p (S m)) -> (forall m :e N, p m))
  -> q)
 -> explicit_Nats -> q.

Axiom explicit_Nats_ind : explicit_Nats ->
  forall p:set -> prop,
      p base
   -> (forall m :e N, p m -> p (S m))
   -> forall m :e N, p m.

(* Parameter explicit_Nats_primrec "5ec40a637f9843917a81733636ffe333120e9a78db0c1236764d271d8704674a" "a61e60c0704e01255992ecc776a771ad4ef672b2ed0f4edea9713442d02c0ba9" *)
Parameter explicit_Nats_primrec : set -> (set -> set -> set) -> set -> set.

Axiom explicit_Nats_primrec_base : forall a, forall f:set -> set -> set,
  explicit_Nats -> explicit_Nats_primrec a f base = a.

Axiom explicit_Nats_primrec_S : forall a, forall f:set -> set -> set,
  explicit_Nats ->
  forall n :e N, explicit_Nats_primrec a f (S n) = f n (explicit_Nats_primrec a f n).

Axiom explicit_Nats_primrec_P : explicit_Nats ->
   forall P:set -> prop,
   forall a, P a -> forall f:set -> set -> set, (forall n :e N, forall b, P b -> P (f n b))
 -> forall n :e N, P (explicit_Nats_primrec a f n).

End explicit_Nats.

Axiom explicit_Nats_omega : explicit_Nats omega 0 ordsucc.

Section explicit_Nats_zero.

Variable N : set.
Variable zero : set.
Variable S : set -> set.

(* Parameter explicit_Nats_zero_plus "8bf54ee811b0677aba3d56bc61913a6d81475e1022faa43989b56bfa7aed2021" "9683ebbbd2610b6b9f8f9bb32a63d9d3cf8c376a919e6989444d6d995da2aceb" *)
Parameter explicit_Nats_zero_plus : set -> set -> set.

Infix + 360 right := explicit_Nats_zero_plus.

(* Parameter explicit_Nats_zero_mult "a5462d7cd964ae608154fbea57766c59c7e8a63f8b6d7224fdacf7819d6543b7" "7cf43a3b8ce0af790f9fc86020fd06ab45e597b29a7ff1dbbe8921910d68638b" *)
Parameter explicit_Nats_zero_mult : set -> set -> set.

Infix * 355 right := explicit_Nats_zero_mult.

Hypothesis HN: explicit_Nats N zero S.

Axiom explicit_Nats_zero_plus_N : forall n m :e N, n + m :e N.
Axiom explicit_Nats_zero_plus_0L : forall m :e N, zero + m = m.
Axiom explicit_Nats_zero_plus_SL : forall n m :e N, S n + m = S (n + m).
Axiom explicit_Nats_zero_mult_N : forall n m :e N, n * m :e N.
Axiom explicit_Nats_zero_mult_0L : forall m :e N, zero * m = zero.
Axiom explicit_Nats_zero_mult_SL : forall n m :e N, S n * m = m + n * m.

End explicit_Nats_zero.

Section explicit_Nats_one.

Variable N : set.
Variable one : set.
Variable S : set -> set.

(* Parameter explicit_Nats_one_plus "96a3e501560225fd48b85405b64d8f27956fb33c35c2ef330600bc21c1ef0f6b" "c14dd5291f7204df5484a3c38ca94107f29d636a3cdfbd67faf1196b3bf192d6" *)
Parameter explicit_Nats_one_plus : set -> set -> set.

Infix + 360 right := explicit_Nats_one_plus.

(* Parameter explicit_Nats_one_mult "55e8bac8e9f8532e25fccb59d629f4f95d54a534cc861e1a106d746d54383308" "ec4f9ffffa60d2015503172b35532a59cebea3390c398d0157fd3159e693eb97" *)
Parameter explicit_Nats_one_mult : set -> set -> set.

Infix * 355 right := explicit_Nats_one_mult.

(* Parameter explicit_Nats_one_exp "37d77be7592c2812416b2592340280e577cddf5b5ea328b2cb4ded30e0361515" "cbcee236e6cb4bea1cf64f58905668aa36807a85032ea58e6bb539f5721ff4c4" *)
Parameter explicit_Nats_one_exp : set -> set -> set.

Infix ^ 342 right := explicit_Nats_one_exp.

Hypothesis HN: explicit_Nats N one S.

Axiom explicit_Nats_one_plus_N : forall n m :e N, n + m :e N.
Axiom explicit_Nats_one_plus_1L : forall m :e N, one + m = S m.
Axiom explicit_Nats_one_plus_SL : forall n m :e N, S n + m = S (n + m).
Axiom explicit_Nats_one_mult_N : forall n m :e N, n * m :e N.
Axiom explicit_Nats_one_mult_1L : forall m :e N, one * m = m.
Axiom explicit_Nats_one_mult_SL : forall n m :e N, S n * m = m + n * m.
Axiom explicit_Nats_one_exp_N : forall n m :e N, n ^ m :e N.
Axiom explicit_Nats_one_exp_1L : forall n :e N, n ^ one = n.
Axiom explicit_Nats_one_exp_SL : forall n m :e N, n ^ (S m) = n * n ^ m.

Definition explicit_Nats_one_lt : set -> set -> prop := fun m n => m :e N /\ n :e N /\ exists k :e N, m + k = n.
Definition explicit_Nats_one_le : set -> set -> prop := fun m n => m :e N /\ n :e N /\ (m = n \/ exists k :e N, m + k = n).

Infix < 490 := explicit_Nats_one_lt.

(* Unicode <= "2264" *)
Infix <= 490 := explicit_Nats_one_le.

End explicit_Nats_one.

Section explicit_Nats_transfer.

Variable N : set.
Variable base : set.
Variable S : set -> set.
Variable N' : set.
Variable base' : set.
Variable S' : set -> set.

Variable f:set -> set.

Axiom explicit_Nats_transfer: explicit_Nats N base S -> bij N N' f -> f base = base' -> (forall n :e N, f (S n) = S' (f n)) -> explicit_Nats N' base' S'.

End explicit_Nats_transfer.

Section AssocComm.

Variable R : set.
Variable plus : set -> set -> set.

Infix + 360 right := plus.

Axiom AssocComm_identities :
    (forall x y :e R, x + y :e R)
 -> (forall x y z :e R, x + (y + z) = (x + y) + z)
 -> (forall x y :e R, x + y = y + x)
 -> forall p:prop,
     ((forall x y z :e R, x + y + z = y + x + z)
   -> (forall x y z :e R, x + y + z = z + x + y)
   -> (forall x y z w :e R, (x + y) + (z + w) = (x + z) + (y + w))
   -> (forall x y z w :e R, x + y + z + w = w + x + y + z)
   -> (forall x y z w :e R, x + y + z + w = z + w + x + y)
   -> p)
  -> p.

End AssocComm.

Section Group1.

Variable G:set.

Section Group1Explicit.

Variable op:set -> set -> set.
Infix * 355 right := op.

Definition explicit_Group : prop :=
      (forall a b :e G, a * b :e G)
   /\ (forall a b c :e G, a * (b * c) = (a * b) * c)
   /\ exists e :e G,
           (forall a :e G, e * a = a /\ a * e = a)
        /\ (forall a :e G, exists b :e G, a * b = e /\ b * a = e).

Axiom explicit_Group_identity_unique : forall e e' :e G, (forall a :e G, e * a = a) -> (forall a :e G, a * e' = a) -> e = e'.

Hypothesis HG: explicit_Group.

Definition explicit_Group_identity : set := Eps_i (fun e => e :e G /\ ((forall a :e G, e * a = a /\ a * e = a) /\ forall a :e G, exists b :e G, a * b = e /\ b * a = e)).

Let e := explicit_Group_identity.

Definition explicit_Group_inverse : set -> set := fun a => Eps_i (fun b => b :e G /\ (a * b = e /\ b * a = e)).

Postfix - 340 := explicit_Group_inverse.

Axiom explicit_Group_identity_prop : e :e G /\ ((forall a :e G, e * a = a /\ a * e = a) /\ forall a :e G, exists b :e G, a * b = e /\ b * a = e).

Axiom explicit_Group_identity_in : e :e G.

Axiom explicit_Group_identity_lid : forall a :e G, e * a = a.

Axiom explicit_Group_identity_rid : forall a :e G, a * e = a.

Axiom explicit_Group_identity_invex : forall a :e G, exists b :e G, a * b = e /\ b * a = e.

Axiom explicit_Group_inverse_prop : forall a :e G, a- :e G /\ (a * a- = e /\ a- * a = e).

Axiom explicit_Group_inverse_in : forall a :e G, a- :e G.

Axiom explicit_Group_inverse_rinv : forall a :e G, a * a- = e.

Axiom explicit_Group_inverse_linv : forall a :e G, a- * a = e.

Axiom explicit_Group_lcancel : forall a b c :e G, a * b = a * c -> b = c.

Axiom explicit_Group_rcancel : forall a b c :e G, a * c = b * c -> a = b.

Axiom explicit_Group_rinv_rev : forall a b :e G, a * b = e -> b = a -.

Axiom explicit_Group_inv_com : forall a b :e G, a * b = e -> b * a = e.

Axiom explicit_Group_inv_rev2 : forall a b :e G, (a * b) * (a * b) = e -> (b * a) * (b * a) = e.

Definition explicit_abelian : prop := forall a b :e G, a * b = b * a.

End Group1Explicit.

Section Group1Explicit2.

Variable op:set -> set -> set.
Infix * 355 right := op.

Section Group1Explicit2RepIndep.

Variable op':set -> set -> set.
Infix :*: 355 right := op'.

Hypothesis Hopop': forall a b :e G, a * b = a :*: b.

Axiom explicit_Group_repindep_imp : explicit_Group op -> explicit_Group op'.

Let e := explicit_Group_identity op.
Let e' := explicit_Group_identity op'.

(** This could be proven in a way that would work more generally:
    the property of e stated with op and op' are provably equivalent.
    Here instead I use the usual way of proving identities are unique.
  **)
Axiom explicit_Group_identity_repindep: explicit_Group op -> e = e'.

Let inv := explicit_Group_inverse op.
Let inv' := explicit_Group_inverse op'.

Axiom explicit_Group_inverse_repindep: explicit_Group op -> forall a :e G, inv a = inv' a.

Axiom explicit_abelian_repindep_imp : explicit_abelian op -> explicit_abelian op'.

End Group1Explicit2RepIndep.

End Group1Explicit2.

Section Group1Explicit3RepIndep.

Variable op:set -> set -> set.
Infix * 355 right := op.

Variable op':set -> set -> set.
Infix :*: 355 right := op'.

Hypothesis Hopop': forall a b :e G, a * b = a :*: b.

Axiom explicit_Group_repindep : explicit_Group op <-> explicit_Group op'.

Axiom explicit_abelian_repindep : explicit_abelian op <-> explicit_abelian op'.

End Group1Explicit3RepIndep.

End Group1.

(** Group as a structure (with just the binary operation) **)
Definition Group : set -> prop :=
  fun G => struct_b G /\ unpack_b_o G explicit_Group.

Definition abelian_Group : set -> prop :=
  fun G => Group G /\ unpack_b_o G explicit_abelian.

Axiom Group_unpack_eq : forall G, forall op:set -> set -> set, unpack_b_o (pack_b G op) explicit_Group = explicit_Group G op.

Axiom GroupI: forall G, forall op:set -> set -> set, explicit_Group G op -> Group (pack_b G op).

Axiom GroupE: forall G, forall op:set -> set -> set, Group (pack_b G op) -> explicit_Group G op.

Axiom abelian_Group_unpack_eq: forall G, forall op:set -> set -> set, unpack_b_o (pack_b G op) explicit_abelian = explicit_abelian G op.

Axiom abelian_Group_E: forall G, forall op:set -> set -> set, abelian_Group (pack_b G op) -> Group (pack_b G op) /\ explicit_abelian G op.

(** https://proofwiki.org/wiki/Definition:Subgroup **)
Section Group2.

Variable G:set.
Variable op:set -> set -> set.
Infix * 355 right := op.
Postfix - 340 := explicit_Group_inverse G op.

Variable H:set.

Definition explicit_subgroup : prop := Group (pack_b H op) /\ H c= G.

Definition explicit_normal : prop := forall x :e G, {x * a * x - | a :e H} c= H.

Hypothesis HG: Group (pack_b G op).

Let e := explicit_Group_identity G op.

Axiom explicit_subgroup_test : H c= G -> e :e H -> (forall a :e H, a - :e H) -> (forall a b :e H, a * b :e H) -> explicit_subgroup.

Hypothesis HSG: explicit_subgroup.
Let e' := explicit_Group_identity H op.

Axiom explicit_subgroup_identity_eq : e = e'.

Axiom explicit_subgroup_inv_eq : forall a :e H, explicit_Group_inverse G op a = explicit_Group_inverse H op a.

Axiom explicit_abelian_normal : explicit_abelian G op -> explicit_normal.

End Group2.

Section Group3.

Variable H G:set.
Variable op op':set -> set -> set.
Infix * 355 right := op.
Postfix - 340 := explicit_Group_inverse G op.
Infix :*: 355 right := op'.
Postfix :-: 340 := explicit_Group_inverse G op'.

Hypothesis HG: explicit_Group G op.
Hypothesis HHG: H c= G.
Hypothesis Hopop': forall a b :e G, a * b = a :*: b.

Axiom explicit_normal_repindep_imp : explicit_normal G op H -> explicit_normal G op' H.

End Group3.

Definition subgroup : set -> set -> prop :=
  fun H G =>
     struct_b G /\ struct_b H /\
     unpack_b_o G
        (fun G' op =>
	  unpack_b_o H
	   (fun H' _ => H = pack_b H' op /\ Group (pack_b H' op) /\ H' c= G')).

Infix <= 400 := subgroup.

Definition subgroup_index : set -> set -> set
 := fun H G =>
     unpack_b_i G
        (fun G' op =>
           {n :e omega | exists f :e G' :^: ordsucc n,
                          forall i j :e ordsucc n, i <> j
                             -> forall a b :e H 0,
			           op (f i) a <> op (f j) b}).

Definition normal_subgroup : set -> set -> prop :=
  fun H G => H <= G /\
     unpack_b_o G
        (fun G' op =>
	  unpack_b_o H
	   (fun H' _ => explicit_normal G' op H')).

Axiom pack_b_subgroup_E : forall H G:set, forall opH op:set -> set -> set,
   pack_b H opH <= pack_b G op
   ->
   pack_b H opH = pack_b H op /\ explicit_subgroup G op H.

Axiom subgroup_E : forall H G, H <= G -> forall q:set -> set -> prop,
  (forall H G, forall op:set -> set -> set,
     (forall a b :e G, op a b :e G) ->
     Group (pack_b H op) ->
     H c= G ->
     q (pack_b H op) (pack_b G op))
  -> q H G.

Axiom abelian_group_normal_subgroup: forall G, abelian_Group G -> forall H, H <= G -> normal_subgroup H G.

Axiom subgroup_transitive: forall K H G, K <= H -> H <= G -> K <= G.

Section Group4.

Variable A:set.

Let G := {f :e A :^: A | bij A A (fun x => f x)}.
Let op := fun f g:set => fun x :e A => g (f x).
Infix * 355 right := op.

Let id := fun x :e A => x.

Axiom explicit_Group_symgroup: explicit_Group G op.

Axiom explicit_Group_symgroup_id_eq : explicit_Group_identity G op = id.

Axiom explicit_Group_symgroup_inv_eq : forall f :e G, explicit_Group_inverse G op f = (fun x :e A => inv A (fun x => f x) x).

Variable B:set.

Let H := {f :e A :^: A | bij A A (fun x => f x) /\ forall x :e B, f x = x}.

Axiom explicit_subgroup_symgroup_fixing : B c= A -> explicit_subgroup G op H.

End Group4.

Definition symgroup : set -> set := fun A => pack_b {f :e A :^: A | bij A A (fun x => f x)} (fun f g => fun x :e A => g (f x)).
Definition symgroup_fixing : set -> set -> set := fun A B => pack_b {f :e A :^: A | bij A A (fun x => f x) /\ forall x :e B, f x = x} (fun f g => fun x :e A => g (f x)).

Axiom Group_symgroup : forall A, Group (symgroup A).

Axiom Group_symgroup_fixing : forall A B, B c= A -> Group (symgroup_fixing A B).

Axiom subgroup_symgroup_fixing : forall A B, B c= A -> symgroup_fixing A B <= symgroup A.

Axiom subgroup_symgroup_fixing2 : forall A B C, C c= B -> B c= A -> symgroup_fixing A B <= symgroup_fixing A C.

Axiom nonnormal_subgroup: exists H G, Group G /\ H <= G /\ ~normal_subgroup H G.

Definition normal_subgroup_equiv : set -> set -> set -> set -> prop
 := fun G N a b =>
     unpack_b_o G
      (fun G op =>
        a :e G /\ b :e G /\ op a (explicit_Group_inverse G op b) :e N 0).

Definition quotient_Group : set -> set -> set
 := fun G N =>
     unpack_b_i G
      (fun G' op =>
        pack_b
          {a :e G' | quotient (normal_subgroup_equiv G N) a}
          (fun a b => canonical_elt (normal_subgroup_equiv G N) (op a b))).

Definition trivial_Group_p : set -> prop
  := fun G => Group G /\ forall x y :e G 0, x = y.

Definition solvable_Group_p : set -> prop
  := fun G =>
      exists n :e omega, exists Gseq,
          (forall i :e ordsucc n, Group (Gseq i))
       /\ (forall i :e n, normal_subgroup (Gseq (ordsucc i)) (Gseq i))
       /\ (forall i :e n, abelian_Group (quotient_Group (Gseq i) (Gseq (ordsucc i))))
       /\ G = Gseq 0
       /\ trivial_Group_p (Gseq n).

Definition Group_carrier : set -> set := fun Gs => Gs 0.
Definition Group_op : set -> set -> set -> set := fun Gs => decode_b (Gs 1).

Section Group2.

Variable Gs:set.
Variable Gs':set.

Let G : set := Group_carrier Gs.
Infix * 355 right := Group_op Gs.
Let G' : set := Group_carrier Gs'.
Infix :*: 355 right := Group_op Gs'.

Definition Group_Hom : set -> prop
 := fun g => Group Gs /\ Group Gs'
          /\ g :e G' :^: G
          /\ forall a b :e G, g (a * b) = g a :*: g b.

Definition Group_Iso : set -> prop
 := fun g => Group_Hom g /\ bij G G' (fun x => g x).

Definition Group_Isomorphic : prop
 := exists g, Group_Iso g.

End Group2.

Section explicit_Ring.

Variable R : set.

Variable zero : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

(* Parameter explicit_Ring "d4477da9be2011c148b7904162d5432e65ca0aa4565b8bb2822c6fa0a63f4fea" "aa9e02604aeaede16041c30137af87a14a6dd9733da1e227cc7d6b966907c706" *)
Parameter explicit_Ring : prop.

Axiom explicit_Ring_I : (forall x y :e R, x + y :e R)
 -> (forall x y z :e R, x + (y + z) = (x + y) + z)
 -> (forall x y :e R, x + y = y + x)
 -> zero :e R 
 -> (forall x :e R, zero + x = x)
 -> (forall x :e R, exists y :e R, x + y = zero)
 -> (forall x y :e R, x * y :e R)
 -> (forall x y z :e R, x * (y * z) = (x * y) * z)
 -> (forall x y z :e R, x * (y + z) = x * y + x * z)
 -> (forall x y z :e R, (x + y) * z = x * z + y * z)
 -> explicit_Ring.

Axiom explicit_Ring_E : forall q:prop,
    (explicit_Ring
  -> (forall x y :e R, x + y :e R)
  -> (forall x y z :e R, x + (y + z) = (x + y) + z)
  -> (forall x y :e R, x + y = y + x)
  -> (zero :e R)
  -> (forall x :e R, zero + x = x)
  -> (forall x :e R, exists y :e R, x + y = zero)
  -> (forall x y :e R, x * y :e R)
  -> (forall x y z :e R, x * (y * z) = (x * y) * z)
  -> (forall x y z :e R, x * (y + z) = x * y + x * z)
  -> (forall x y z :e R, (x + y) * z = x * z + y * z)
  -> q)
 -> explicit_Ring -> q.

(* Parameter explicit_Ring_minus "243cf5991540062f744d26d5acf1f57122889c3ec2939d5226591e58b27a1669" "2f43ee814823893eab4673fb76636de742c4d49e63bd645d79baa4d423489f20" *)
Parameter explicit_Ring_minus: set -> set.

Prefix - 358 := explicit_Ring_minus.

Axiom explicit_Ring_minus_prop : explicit_Ring -> forall x :e R, - x :e R /\ x + - x = zero.

Axiom explicit_Ring_minus_clos : explicit_Ring -> forall x :e R, - x :e R.

Axiom explicit_Ring_minus_R : explicit_Ring -> forall x :e R, x + - x = zero.

Axiom explicit_Ring_minus_L : explicit_Ring -> forall x :e R, - x + x = zero.

Axiom explicit_Ring_plus_cancelL : explicit_Ring -> forall x y z :e R, x + y = x + z -> y = z.

Axiom explicit_Ring_plus_cancelR : explicit_Ring -> forall x y z :e R, x + z = y + z -> x = y.

Axiom explicit_Ring_minus_invol : explicit_Ring -> forall x :e R, - - x = x.

End explicit_Ring.

Section explicit_Ring_with_id.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

(* Parameter explicit_Ring_with_id "119dceedb8bcb74f57da40dcfdf9ac97c6bea3532eab7e292bcfdd84f2505ae9" "51b1b6cf343b691168d1f26c39212233b95f9ae7efa3be71d53540eaa3c849ab" *)
Parameter explicit_Ring_with_id : prop.

Axiom explicit_Ring_with_id_I : (forall x y :e R, x + y :e R)
 -> (forall x y z :e R, x + (y + z) = (x + y) + z)
 -> (forall x y :e R, x + y = y + x)
 -> zero :e R 
 -> (forall x :e R, zero + x = x)
 -> (forall x :e R, exists y :e R, x + y = zero)
 -> (forall x y :e R, x * y :e R)
 -> (forall x y z :e R, x * (y * z) = (x * y) * z)
 -> (one :e R)
 -> (one <> zero)
 -> (forall x :e R, one * x = x)
 -> (forall x :e R, x * one = x)
 -> (forall x y z :e R, x * (y + z) = x * y + x * z)
 -> (forall x y z :e R, (x + y) * z = x * z + y * z)
 -> explicit_Ring_with_id.

Axiom explicit_Ring_with_id_E : forall q:prop,
    (explicit_Ring_with_id
  -> (forall x y :e R, x + y :e R)
  -> (forall x y z :e R, x + (y + z) = (x + y) + z)
  -> (forall x y :e R, x + y = y + x)
  -> (zero :e R)
  -> (forall x :e R, zero + x = x)
  -> (forall x :e R, exists y :e R, x + y = zero)
  -> (forall x y :e R, x * y :e R)
  -> (forall x y z :e R, x * (y * z) = (x * y) * z)
  -> (one :e R)
  -> (one <> zero)
  -> (forall x :e R, one * x = x)
  -> (forall x :e R, x * one = x)
  -> (forall x y z :e R, x * (y + z) = x * y + x * z)
  -> (forall x y z :e R, (x + y) * z = x * z + y * z)
  -> q)
 -> explicit_Ring_with_id -> q.

Axiom explicit_Ring_with_id_Ring : explicit_Ring_with_id -> explicit_Ring R zero plus mult.

Prefix - 358 := explicit_Ring_minus R zero plus mult.

Axiom explicit_Ring_with_id_minus_clos : explicit_Ring_with_id -> forall x :e R, - x :e R.

Axiom explicit_Ring_with_id_minus_R : explicit_Ring_with_id -> forall x :e R, x + - x = zero.

Axiom explicit_Ring_with_id_minus_L : explicit_Ring_with_id -> forall x :e R, - x + x = zero.

Axiom explicit_Ring_with_id_plus_cancelL : explicit_Ring_with_id -> forall x y z :e R, x + y = x + z -> y = z.

Axiom explicit_Ring_with_id_plus_cancelR : explicit_Ring_with_id -> forall x y z :e R, x + z = y + z -> x = y.

Axiom explicit_Ring_with_id_minus_invol : explicit_Ring_with_id -> forall x :e R, - - x = x.

Axiom explicit_Ring_with_id_minus_one_In : explicit_Ring_with_id -> - one :e R.

Axiom explicit_Ring_with_id_zero_multR : explicit_Ring_with_id -> forall x :e R, x * zero = zero.
Axiom explicit_Ring_with_id_zero_multL : explicit_Ring_with_id -> forall x :e R, zero * x = zero.

Axiom explicit_Ring_with_id_minus_mult : explicit_Ring_with_id -> forall x :e R, - x = (- one) * x.

Axiom explicit_Ring_with_id_mult_minus : explicit_Ring_with_id -> forall x :e R, - x = x * (- one).

Axiom explicit_Ring_with_id_minus_one_square : explicit_Ring_with_id -> (- one) * (- one) = one.

Axiom explicit_Ring_with_id_minus_square : explicit_Ring_with_id -> forall x :e R, (- x) * (- x) = x * x.

Definition explicit_Ring_with_id_exp_nat : set -> set -> set
  := fun x n => nat_primrec one (fun _ r => x * r) n.

Infix ^ 342 right := explicit_Ring_with_id_exp_nat.

(** explicit_Ring_with_id_eval_poly n cs x assumes cs is an n-tuple of coefficients from the carrier,
    specifiying an n-1 degree polynomial (with the zero polynomial for n=0) **)
Definition explicit_Ring_with_id_eval_poly : set -> set -> set -> set
  := fun n cs x => nat_primrec zero (fun m r => cs m * x ^ m + r) n.

End explicit_Ring_with_id.

Section explicit_Ring_with_id_RepIndep2.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable plus' mult':set -> set -> set.
Infix :+: 355 right := plus'.
Infix :*: 355 right := mult'.

Hypothesis Hpp': forall a b :e R, a + b = a :+: b.
Hypothesis Hmm': forall a b :e R, a * b = a :*: b.

Axiom explicit_Ring_with_id_repindep : explicit_Ring_with_id R zero one plus mult <-> explicit_Ring_with_id R zero one plus' mult'.

End explicit_Ring_with_id_RepIndep2.

Section explicit_CRing_with_id.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

(* Parameter explicit_CRing_with_id "e617a2c69bd7575dc6ebd47c67ca7c8b08c0c22a914504a403e3db24ee172987" "83e7eeb351d92427c0d3bb2bd24e83d0879191c3aa01e7be24fb68ffdbb9060c" *)
Parameter explicit_CRing_with_id : prop.

Axiom explicit_CRing_with_id_I : (forall x y :e R, x + y :e R)
 -> (forall x y z :e R, x + (y + z) = (x + y) + z)
 -> (forall x y :e R, x + y = y + x)
 -> zero :e R 
 -> (forall x :e R, zero + x = x)
 -> (forall x :e R, exists y :e R, x + y = zero)
 -> (forall x y :e R, x * y :e R)
 -> (forall x y z :e R, x * (y * z) = (x * y) * z)
 -> (forall x y :e R, x * y = y * x)
 -> (one :e R)
 -> (one <> zero)
 -> (forall x :e R, one * x = x)
 -> (forall x y z :e R, x * (y + z) = x * y + x * z)
 -> explicit_CRing_with_id.

Axiom explicit_CRing_with_id_E : forall q:prop,
    (explicit_CRing_with_id
  -> (forall x y :e R, x + y :e R)
  -> (forall x y z :e R, x + (y + z) = (x + y) + z)
  -> (forall x y :e R, x + y = y + x)
  -> (zero :e R)
  -> (forall x :e R, zero + x = x)
  -> (forall x :e R, exists y :e R, x + y = zero)
  -> (forall x y :e R, x * y :e R)
  -> (forall x y z :e R, x * (y * z) = (x * y) * z)
  -> (forall x y :e R, x * y = y * x)
  -> (one :e R)
  -> (one <> zero)
  -> (forall x :e R, one * x = x)
  -> (forall x y z :e R, x * (y + z) = x * y + x * z)
  -> q)
 -> explicit_CRing_with_id -> q.

Axiom explicit_CRing_with_id_Ring_with_id : explicit_CRing_with_id -> explicit_Ring_with_id R zero one plus mult.

Axiom explicit_CRing_with_id_Ring : explicit_CRing_with_id -> explicit_Ring R zero plus mult.

Prefix - 358 := explicit_Ring_minus R zero plus mult.

Axiom explicit_CRing_with_id_minus_clos : explicit_CRing_with_id -> forall x :e R, - x :e R.

Axiom explicit_CRing_with_id_minus_R : explicit_CRing_with_id -> forall x :e R, x + - x = zero.

Axiom explicit_CRing_with_id_minus_L : explicit_CRing_with_id -> forall x :e R, - x + x = zero.

Axiom explicit_CRing_with_id_plus_cancelL : explicit_CRing_with_id -> forall x y z :e R, x + y = x + z -> y = z.

Axiom explicit_CRing_with_id_plus_cancelR : explicit_CRing_with_id -> forall x y z :e R, x + z = y + z -> x = y.

Axiom explicit_CRing_with_id_minus_invol : explicit_CRing_with_id -> forall x :e R, - - x = x.

Axiom explicit_CRing_with_id_minus_one_In : explicit_CRing_with_id -> - one :e R.

Axiom explicit_CRing_with_id_zero_multR : explicit_CRing_with_id -> forall x :e R, x * zero = zero.
Axiom explicit_CRing_with_id_zero_multL : explicit_CRing_with_id -> forall x :e R, zero * x = zero.

Axiom explicit_CRing_with_id_minus_mult : explicit_CRing_with_id -> forall x :e R, - x = (- one) * x.

Axiom explicit_CRing_with_id_mult_minus : explicit_CRing_with_id -> forall x :e R, - x = x * (- one).

Axiom explicit_CRing_with_id_minus_one_square : explicit_CRing_with_id -> (- one) * (- one) = one.

Axiom explicit_CRing_with_id_minus_square : explicit_CRing_with_id -> forall x :e R, (- x) * (- x) = x * x.

End explicit_CRing_with_id.

Section explicit_CRing_with_id_RepIndep2.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable plus' mult':set -> set -> set.
Infix :+: 355 right := plus'.
Infix :*: 355 right := mult'.

Hypothesis Hpp': forall a b :e R, a + b = a :+: b.
Hypothesis Hmm': forall a b :e R, a * b = a :*: b.

Axiom explicit_CRing_with_id_repindep : explicit_CRing_with_id R zero one plus mult <-> explicit_CRing_with_id R zero one plus' mult'.

End explicit_CRing_with_id_RepIndep2.

(* Parameter pack_b_b_e "0c2f8a60f76952627b3e2c9597ef5771553931819c727dea75b98b59b548b5ec" "c9ca029e75ae9f47e0821539f84775cc07258db662e0b5ccf4a423c45a480766" *)
Parameter pack_b_b_e : set -> (set -> set -> set) -> (set -> set -> set) -> set -> set.

(* Parameter struct_b_b_e "0dcb26ac08141ff1637a69d653711c803f750140584a4da769aefebb168b9257" "755e4e2e4854b160b8c7e63bfc53bb4f4d968d82ce993ef8c5b5c176c4d14b33" *)
Parameter struct_b_b_e : set -> prop.

(* Parameter unpack_b_b_e_i "1c031505cc8bf49a0512a2238ae989977d9857fddee5960613267874496a28be" "7004278ccd490dc5f231c346523a94ad983051f8775b8942916378630dd40008" *)
Parameter unpack_b_b_e_i : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> set -> set) -> set.

(* Parameter unpack_b_b_e_o "81ac7e6231b8c316b5c2cb16fbb5f8038e2425b2efd9bd0fc382bc3d448a259d" "b94d6880c1961cc8323e2d6df4491604a11b5f2bf723511a06e0ab22f677364d" *)
Parameter unpack_b_b_e_o : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> set -> prop) -> prop.

Definition Ring : set -> prop
 := fun R => struct_b_b_e R
          /\ unpack_b_b_e_o R (fun R plus mult zero => explicit_Ring R zero plus mult).

Definition Ring_minus : set -> set -> set
 := fun R x => unpack_b_b_e_i R (fun R plus mult zero => explicit_Ring_minus R zero plus mult x).

(* Parameter pack_b_b_e_e "0ca5ba562d2ab04221b86aded545ed077bf3a2f06e21344f04ba0b43521b231e" "6859fb13a44929ca6d7c0e598ffc6a6f82969c8cfe5edda33f1c1d81187b9d31" *)
Parameter pack_b_b_e_e : set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> set.

(* Parameter struct_b_b_e_e "af2850387310cf676e35267e10a14affc439a209ad200b7edc42d8142611fcd4" "7685bdf4f6436a90f8002790ede7ec64e03b146138f7d85bc11be7d287d3652b" *)
Parameter struct_b_b_e_e : set -> prop.

(* Parameter unpack_b_b_e_e_i "78cabd5521b666604d7b8deee71a25d12741bbd39d84055b85d0a613ef13614c" "0708055ba3473c2f52dbd9ebd0f0042913b2ba689b64244d92acea4341472a1d" *)
Parameter unpack_b_b_e_e_i : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> set) -> set.

(* Parameter unpack_b_b_e_e_o "eb93435a79c01148fc12dd7779795d68cc2251130dc7633623f16664d25ed072" "1bcc21b2f13824c926a364c5b001d252d630f39a0ebe1f8af790facbe0f63a11" *)
Parameter unpack_b_b_e_e_o : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> set -> set -> prop) -> prop.

Definition Ring_with_id : set -> prop
 := fun R => struct_b_b_e_e R
          /\ unpack_b_b_e_e_o R (fun R plus mult zero one => explicit_Ring_with_id R zero one plus mult).

Axiom Ring_with_id_unpack_eq : forall R, forall plus mult:set -> set -> set, forall zero one, unpack_b_b_e_e_o (pack_b_b_e_e R plus mult zero one) (fun R plus mult zero one => explicit_Ring_with_id R zero one plus mult) = explicit_Ring_with_id R zero one plus mult.

Definition CRing_with_id : set -> prop
 := fun R => struct_b_b_e_e R
          /\ unpack_b_b_e_e_o R (fun R plus mult zero one => explicit_CRing_with_id R zero one plus mult).

Axiom CRing_with_id_unpack_eq : forall R, forall plus mult:set -> set -> set, forall zero one, unpack_b_b_e_e_o (pack_b_b_e_e R plus mult zero one) (fun R plus mult zero one => explicit_CRing_with_id R zero one plus mult) = explicit_CRing_with_id R zero one plus mult.

Definition Ring_of_Ring_with_id : set -> set
 := fun R => unpack_b_b_e_e_i R (fun R plus mult zero one => pack_b_b_e R plus mult zero).

Axiom CRing_with_id_is_Ring_with_id: forall R, CRing_with_id R -> Ring_with_id R.

(** Mostly Following Dieudonne's Foundations of Modern Analysis
    (first two pages of Chapter 2),
    except the zero and one elements are explicit to easily
    use them in multiple conditions.
 **)
Section explicit_Reals.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

(* Parameter explicit_Field "b2707c82b8b416a22264d2934d5221d1115ea55732f96cbb6663fbf7e945d3e3" "32dcc27d27b5003a86f8b13ba9ca16ffaec7168a11c5d9850940847c48148591" *)
Parameter explicit_Field : prop.

Axiom explicit_Field_I : (forall x y :e R, x + y :e R)
 -> (forall x y z :e R, x + (y + z) = (x + y) + z)
 -> (forall x y :e R, x + y = y + x)
 -> zero :e R 
 -> (forall x :e R, zero + x = x)
 -> (forall x :e R, exists y :e R, x + y = zero)
 -> (forall x y :e R, x * y :e R)
 -> (forall x y z :e R, x * (y * z) = (x * y) * z)
 -> (forall x y :e R, x * y = y * x)
 -> (one :e R)
 -> (one <> zero)
 -> (forall x :e R, one * x = x)
 -> (forall x :e R, x <> zero -> exists y :e R, x * y = one)
 -> (forall x y z :e R, x * (y + z) = x * y + x * z)
 -> explicit_Field.

Axiom explicit_Field_E : forall q:prop,
    (explicit_Field
  -> (forall x y :e R, x + y :e R)
  -> (forall x y z :e R, x + (y + z) = (x + y) + z)
  -> (forall x y :e R, x + y = y + x)
  -> (zero :e R)
  -> (forall x :e R, zero + x = x)
  -> (forall x :e R, exists y :e R, x + y = zero)
  -> (forall x y :e R, x * y :e R)
  -> (forall x y z :e R, x * (y * z) = (x * y) * z)
  -> (forall x y :e R, x * y = y * x)
  -> (one :e R)
  -> (one <> zero)
  -> (forall x :e R, one * x = x)
  -> (forall x :e R, x <> zero -> exists y :e R, x * y = one)
  -> (forall x y z :e R, x * (y + z) = x * y + x * z)
  -> q)
 -> explicit_Field -> q.

(* Parameter explicit_Field_minus "be660f6f1e37e7325ec2a39529b9c937b61a60f864e85f0dabdf2bddacb0986e" "5be570b4bcbe7fefd36c2057491ddcc7b11903d8d98ca54d9b37db60d1bf0f7e" *)
Parameter explicit_Field_minus : set -> set.

Prefix - 358 := explicit_Field_minus.

Axiom explicit_Field_minus_prop : explicit_Field -> forall x :e R, - x :e R /\ x + - x = zero.
Axiom explicit_Field_minus_clos : explicit_Field -> forall x :e R, - x :e R.
Axiom explicit_Field_minus_R : explicit_Field -> forall x :e R, x + - x = zero.
Axiom explicit_Field_minus_L : explicit_Field -> forall x :e R, - x + x = zero.
Axiom explicit_Field_plus_cancelL : explicit_Field -> forall x y z :e R, x + y = x + z -> y = z.
Axiom explicit_Field_plus_cancelR : explicit_Field -> forall x y z :e R, x + z = y + z -> x = y.
Axiom explicit_Field_minus_invol : explicit_Field -> forall x :e R, - - x = x.
Axiom explicit_Field_minus_one_In : explicit_Field -> - one :e R.
Axiom explicit_Field_zero_multR : explicit_Field -> forall x :e R, x * zero = zero.
Axiom explicit_Field_zero_multL : explicit_Field -> forall x :e R, zero * x = zero.
Axiom explicit_Field_minus_mult : explicit_Field -> forall x :e R, - x = (- one) * x.
Axiom explicit_Field_minus_one_square : explicit_Field -> (- one) * (- one) = one.
Axiom explicit_Field_minus_square : explicit_Field -> forall x :e R, (- x) * (- x) = x * x.

Axiom explicit_Field_minus_zero : explicit_Field -> - zero = zero.
Axiom explicit_Field_dist_R : explicit_Field -> forall x y z :e R, (x + y) * z = x * z + y * z.
Axiom explicit_Field_minus_plus_dist : explicit_Field -> forall x y :e R, - (x + y) = - x + - y.
Axiom explicit_Field_minus_mult_L : explicit_Field -> forall x y :e R, (- x) * y = - (x * y).
Axiom explicit_Field_minus_mult_R : explicit_Field -> forall x y :e R, x * (- y) = - (x * y).
Axiom explicit_Field_square_zero_inv : explicit_Field -> forall x :e R, x * x = zero -> x = zero.
Axiom explicit_Field_mult_zero_inv : explicit_Field -> forall x y :e R, x * y = zero -> x = zero \/ y = zero.

Variable leq : set -> set -> prop.

(* Unicode <= "2264" *)
Infix <= 490 := leq.

(* Parameter explicit_OrderedField "1195f96dcd143e4b896b4c1eb080d1fb877084debc58a8626d3dcf7a14ce8df7" "a18f7bca989a67fb7dc6df8e6c094372c26fa2c334578447d3314616155afb72" *)
Parameter explicit_OrderedField : prop.

Axiom explicit_OrderedField_I : explicit_Field
 -> (forall x y z :e R, x <= y -> y <= z -> x <= z)
 -> (forall x y :e R, x <= y /\ y <= x <-> x = y)
 -> (forall x y :e R, x <= y \/ y <= x)
 -> (forall x y z :e R, x <= y -> x + z <= y + z)
 -> (forall x y :e R, zero <= x -> zero <= y -> zero <= x * y)
 -> explicit_OrderedField.

Axiom explicit_OrderedField_E : forall q:prop,
    (explicit_OrderedField
  -> explicit_Field
  -> (forall x y z :e R, x <= y -> y <= z -> x <= z)
  -> (forall x y :e R, x <= y /\ y <= x <-> x = y)
  -> (forall x y :e R, x <= y \/ y <= x)
  -> (forall x y z :e R, x <= y -> x + z <= y + z)
  -> (forall x y :e R, zero <= x -> zero <= y -> zero <= x * y)
  -> q)
 -> explicit_OrderedField -> q.

Axiom explicit_OrderedField_minus_leq : explicit_OrderedField -> forall x y :e R, x <= y -> - y <= - x.
Axiom explicit_OrderedField_square_nonneg : explicit_OrderedField -> forall x :e R, zero <= x * x.
Axiom explicit_OrderedField_sum_squares_nonneg : explicit_OrderedField -> forall x y :e R, zero <= x * x + y * y.
Axiom explicit_OrderedField_sum_nonneg_zero_inv : explicit_OrderedField -> forall x y :e R, zero <= x -> zero <= y -> x + y = zero -> x = zero /\ y = zero.
Axiom explicit_OrderedField_sum_squares_zero_inv : explicit_OrderedField -> forall x y :e R, x * x + y * y = zero -> x = zero /\ y = zero.

Axiom explicit_OrderedField_leq_refl: explicit_OrderedField -> forall x :e R, x <= x.
Axiom explicit_OrderedField_leq_antisym: explicit_OrderedField -> forall x y :e R, x <= y -> y <= x -> x = y.
Axiom explicit_OrderedField_leq_tra: explicit_OrderedField -> forall x y z :e R, x <= y -> y <= z -> x <= z.
Axiom explicit_OrderedField_leq_zero_one: explicit_OrderedField -> zero <= one.

Definition lt : set -> set -> prop := fun x y => x <= y /\ x <> y.
Infix < 490 := lt.

(* Parameter natOfOrderedField_p "f97b150093ec13f84694e2b8f48becf45e4b6df2b43c1085ae7a99663116b9a6" "f1c45e0e9f9df75c62335865582f186c3ec3df1a94bc94b16d41e73bf27899f9" *)
Parameter natOfOrderedField_p : set -> prop.

Let N := {n :e R | natOfOrderedField_p n}.
Let Npos := {n :e N | n <> zero}.

Axiom explicit_Nats_natOfOrderedField: explicit_OrderedField -> explicit_Nats N zero (fun m => m + one).
Axiom explicit_PosNats_natOfOrderedField: explicit_OrderedField -> explicit_Nats Npos one (fun m => m + one).

Let Z := {n :e R | - n :e Npos \/ n = zero \/ n :e Npos}.

Definition explicit_OrderedField_rationalp : set -> prop
 := fun x => exists n :e Z, exists m :e Npos, m * x = n.

Let Q := {x :e R | explicit_OrderedField_rationalp x}.

Axiom explicit_OrderedField_Npos_props: explicit_OrderedField
 -> forall p:prop,
      (Npos c= R
    -> explicit_Nats Npos one (fun m => m + one)
    -> one :e Npos
    -> (forall m :e Npos, m + one <> one)
    -> (forall m :e Npos, forall q:set -> prop, q one -> (forall n :e Npos, q (n + one)) -> q m)
    -> (forall n m :e Npos, explicit_Nats_one_plus Npos one (fun m => m + one) n m = n + m)
    -> (forall n m :e Npos, explicit_Nats_one_mult Npos one (fun m => m + one) n m = n * m)
    -> (forall n m :e Npos, n + m :e Npos)
    -> (forall n m :e Npos, n * m :e Npos)
    -> p)
   -> p.

Axiom explicit_OrderedField_Z_props: explicit_OrderedField
 -> forall p:prop,
      ((forall n :e Npos, - n :e Z)
    -> zero :e Z
    -> Npos c= Z
    -> Z c= R
    -> (forall n :e Z, forall q:prop, (- n :e Npos -> q) -> (n = zero -> q) -> (n :e Npos -> q) -> q)
    -> one :e Z
    -> - one :e Z
    -> (forall m :e Z, - m :e Z)
    -> (forall n m :e Z, n + m :e Z)
    -> (forall n m :e Z, n * m :e Z)
    -> p)
   -> p.

Axiom explicit_OrderedField_Q_props: explicit_OrderedField
 -> forall p:prop,
      (Q c= R
    -> (forall x :e Q, forall q:prop,
           (x :e R -> forall n :e Z, forall m :e Npos, m * x = n -> q)
         -> q)
    -> (forall x :e R, forall n :e Z, forall m :e Npos, m * x = n -> x :e Q)
    -> p)
   -> p.

(* Parameter explicit_Reals "e5dee14fc7a24a63555de85859904de8dc1b462044060d68dbb06cc9a590bc38" "2c81615a11c9e3e301f3301ec7862ba122acea20bfe1c120f7bdaf5a2e18faf4" *)
Parameter explicit_Reals : prop.

Axiom explicit_Reals_I : explicit_OrderedField
 -> (forall x y :e R, zero < x -> zero <= y -> exists n :e N, y <= n * x)
 -> (forall a b :e R :^: N,
         (forall n :e N, a n <= b n /\ a n <= a (n + one) /\ b (n + one) <= b n)
      -> exists x :e R, forall n :e N, a n <= x /\ x <= b n)
 -> explicit_Reals.

Axiom explicit_Reals_E : forall q:prop,
    (explicit_Reals
  -> explicit_OrderedField
  -> (forall x y :e R, zero < x -> zero <= y -> exists n :e N, y <= n * x)
  -> (forall a b :e R :^: N,
        (forall n :e N, a n <= b n /\ a n <= a (n + one) /\ b (n + one) <= b n)
     -> exists x :e R, forall n :e N, a n <= x /\ x <= b n)
  -> q)
 -> explicit_Reals -> q.

Axiom explicit_Reals_characteristic_0 : explicit_Reals -> forall n :e omega, nat_primrec one (fun _ r => plus one r) n <> zero.

End explicit_Reals.

Definition CRing_with_id_carrier : set -> set := fun Rs => Rs 0.
Definition CRing_with_id_plus : set -> set -> set -> set := fun Rs => decode_b (Rs 1).
Definition CRing_with_id_mult : set -> set -> set -> set := fun Rs => decode_b (Rs 2).
Definition CRing_with_id_zero : set -> set := fun Rs => Rs 3.
Definition CRing_with_id_one : set -> set := fun Rs => Rs 4.

Section CRing_with_id.

Variable Rs:set.
Hypothesis HRs: CRing_with_id Rs.

Let R : set := CRing_with_id_carrier Rs.
Let zero : set := CRing_with_id_zero Rs.
Let one : set := CRing_with_id_one Rs.
Infix + 360 right := CRing_with_id_plus Rs.
Infix * 355 right := CRing_with_id_mult Rs.

Axiom CRing_with_id_eta: Rs = pack_b_b_e_e R (CRing_with_id_plus Rs) (CRing_with_id_mult Rs) zero one.
Axiom CRing_with_id_explicit_CRing_with_id: explicit_CRing_with_id R zero one (CRing_with_id_plus Rs) (CRing_with_id_mult Rs).
Axiom CRing_with_id_zero_In: zero :e R.
Axiom CRing_with_id_one_In: one :e R.
Axiom CRing_with_id_plus_clos: forall x y :e R, x + y :e R.
Axiom CRing_with_id_mult_clos: forall x y :e R, x * y :e R.
Axiom CRing_with_id_plus_assoc: forall x y z :e R, x + (y + z) = (x + y) + z.
Axiom CRing_with_id_plus_com: forall x y :e R, x + y = y + x.
Axiom CRing_with_id_zero_L: forall x :e R, zero + x = x.
Axiom CRing_with_id_plus_inv: forall x :e R, exists y :e R, x + y = zero.
Axiom CRing_with_id_mult_assoc: forall x y z :e R, x * (y * z) = (x * y) * z.
Axiom CRing_with_id_mult_com: forall x y :e R, x * y = y * x.
Axiom CRing_with_id_one_neq_zero: one <> zero.
Axiom CRing_with_id_one_L: forall x :e R, one * x = x.
Axiom CRing_with_id_distr_L: forall x y z :e R, x * (y + z) = x * y + x * z.

Definition CRing_with_id_omega_exp : set -> set -> set := fun x => nat_primrec one (fun k r => x * r).

Infix ^ 342 right := CRing_with_id_omega_exp.

Axiom CRing_with_id_omega_exp_0 : forall x, x ^ 0 = one.
Axiom CRing_with_id_omega_exp_S : forall x, forall n :e omega, x ^ (ordsucc n) = x * x ^ n.
Axiom CRing_with_id_omega_exp_1 : forall x :e R, x ^ 1 = x.
Axiom CRing_with_id_omega_exp_clos : forall x :e R, forall n :e omega, x ^ n :e R.

(** CRing_with_id_eval_poly n cs x assumes cs is an n-tuple of coefficients from the carrier,
    specifiying an n-1 degree polynomial (with the zero polynomial for n=0) **)
Definition CRing_with_id_eval_poly : set -> set -> set -> set
 := fun n cs x => nat_primrec zero (fun m r => cs m * x ^ m + r) n.

Axiom CRing_with_id_eval_poly_clos : forall n :e omega, forall cs :e R :^: n, forall x :e R, CRing_with_id_eval_poly n cs x :e R.

End CRing_with_id.

Section explicit_Reals.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Prefix - 358 := explicit_Field_minus R zero one plus mult.

Variable leq : set -> set -> prop.
(* Unicode <= "2264" *)
Infix <= 490 := leq.

Let N := {n :e R | natOfOrderedField_p R zero one plus mult leq n}.
Let Npos := {n :e N | n <> zero}.
Let Z := {n :e R | - n :e Npos \/ n = zero \/ n :e Npos}.
Let Q := {x :e R | explicit_OrderedField_rationalp R zero one plus mult leq x}.

Axiom explicit_OrderedField_explicit_Field_Q:
    explicit_OrderedField R zero one plus mult leq
 -> explicit_Field Q zero one plus mult.

Axiom explicit_OrderedField_sub:
    explicit_OrderedField R zero one plus mult leq
 -> forall R' c= R,
     zero :e R'
  -> one :e R'
  -> (forall x y :e R', x + y :e R')
  -> (forall x :e R', - x :e R')
  -> (forall x y :e R', x * y :e R')
  -> (forall x :e R', x <> zero -> exists y :e R', x * y = one)
  -> explicit_OrderedField R' zero one plus mult leq.

Axiom explicit_Reals_sub:
    explicit_OrderedField R zero one plus mult leq
 -> forall R' c= R,
     zero :e R'
  -> one :e R'
  -> (forall x y :e R', x + y :e R')
  -> (forall x :e R', - x :e R')
  -> (forall x y :e R', x * y :e R')
  -> (forall x :e R', x <> zero -> exists y :e R', x * y = one)
  -> explicit_OrderedField R' zero one plus mult leq.

Section explicit_Reals_Q_min_props.

Variable R':set.
Let N' := {n :e R' | natOfOrderedField_p R' zero one plus mult leq n}.
Let Npos' := {n :e N' | n <> zero}.
Let Z' := {n :e R' | explicit_Field_minus R' zero one plus mult n :e Npos' \/ n = zero \/ n :e Npos'}.
Let Q' := {x :e R' | explicit_OrderedField_rationalp R' zero one plus mult leq x}.

Axiom explicit_Reals_Q_min_props:
    explicit_OrderedField R zero one plus mult leq
 -> R' c= R
 -> explicit_Field R' zero one plus mult
 -> forall p:prop,
        ((forall x :e R', explicit_Field_minus R' zero one plus mult x = - x)
      -> (forall x :e R', - x :e R')
      -> N = N' -> Npos = Npos' -> Z = Z' -> Q = Q' -> p)
     -> p.

End explicit_Reals_Q_min_props.

Axiom explicit_Reals_Q_min:
    explicit_OrderedField R zero one plus mult leq
 -> forall R' c= R,
     explicit_Field R' zero one plus mult
  -> Q c= R'.

End explicit_Reals.

Section explicit_Field_transfer.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable R' : set.

Variable zero' one' : set.
Variable plus' mult' : set -> set -> set.

Infix :+: 360 right := plus'.
Infix :*: 355 right := mult'.

Variable f:set -> set.

Axiom explicit_Field_transfer: explicit_Field R zero one plus mult
 -> bij R R' f
 -> f zero = zero'
 -> f one = one'
 -> (forall x y :e R, f (x + y) = f x :+: f y)
 -> (forall x y :e R, f (x * y) = f x :*: f y)
 -> explicit_Field R' zero' one' plus' mult'.

End explicit_Field_transfer.

Section explicit_Field_RepIndep2.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable plus' mult':set -> set -> set.
Infix :+: 355 right := plus'.
Infix :*: 355 right := mult'.

Hypothesis Hpp': forall a b :e R, a + b = a :+: b.
Hypothesis Hmm': forall a b :e R, a * b = a :*: b.

Axiom explicit_Field_repindep : explicit_Field R zero one plus mult <-> explicit_Field R zero one plus' mult'.

End explicit_Field_RepIndep2.

Definition Field : set -> prop
 := fun F => struct_b_b_e_e F
          /\ unpack_b_b_e_e_o F (fun Q plus mult zero one => explicit_Field Q zero one plus mult).

Axiom Field_unpack_eq : forall R, forall plus mult:set -> set -> set, forall zero one, unpack_b_b_e_e_o (pack_b_b_e_e R plus mult zero one) (fun R plus mult zero one => explicit_Field R zero one plus mult) = explicit_Field R zero one plus mult.

Axiom Field_is_CRing_with_id: forall F, Field F -> CRing_with_id F.

Section explicit_OrderedField_transfer.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable leq : set -> set -> prop.

(* Unicode <= "2264" *)
Infix <= 490 := leq.

Variable R' : set.

Variable zero' one' : set.
Variable plus' mult' : set -> set -> set.

Infix :+: 360 right := plus'.
Infix :*: 355 right := mult'.

Variable leq' : set -> set -> prop.

Variable f:set -> set.

Axiom explicit_OrderedField_transfer : explicit_OrderedField R zero one plus mult leq
 -> bij R R' f
 -> f zero = zero'
 -> f one = one'
 -> (forall x y :e R, f (x + y) = f x :+: f y)
 -> (forall x y :e R, f (x * y) = f x :*: f y)
 -> (forall x y :e R, x <= y <-> leq' (f x) (f y))
 -> explicit_OrderedField R' zero' one' plus' mult' leq'.

End explicit_OrderedField_transfer.

Definition Field_carrier : set -> set := fun Fs => Fs 0.
Definition Field_plus : set -> set -> set -> set := fun Fs => decode_b (Fs 1).
Definition Field_mult : set -> set -> set -> set := fun Fs => decode_b (Fs 2).
Definition Field_zero : set -> set := fun Fs => Fs 3.
Definition Field_one : set -> set := fun Fs => Fs 4.

(* Parameter Field_minus "cad943ad3351894d7ba6a26fa37c5f118d52cb5656335ca3b111d786455306e6" "9072a08b056e30edab702a9b7c29162af6170c517da489a9b3eab1a982fdb325" *)
Parameter Field_minus : set -> set -> set.

Section Field.

Variable Fs:set.
Hypothesis HFs: Field Fs.

Let F : set := Field_carrier Fs.
Let zero : set := Field_zero Fs.
Let one : set := Field_one Fs.
Infix + 360 right := Field_plus Fs.
Infix * 355 right := Field_mult Fs.
Prefix - 358 := Field_minus Fs.

Axiom Field_eta: Fs = pack_b_b_e_e F (Field_plus Fs) (Field_mult Fs) zero one.
Axiom Field_explicit_Field: explicit_Field F zero one (Field_plus Fs) (Field_mult Fs).
Axiom Field_zero_In: zero :e F.
Axiom Field_one_In: one :e F.
Axiom Field_plus_clos: forall x y :e F, x + y :e F.
Axiom Field_mult_clos: forall x y :e F, x * y :e F.
Axiom Field_plus_assoc: forall x y z :e F, x + (y + z) = (x + y) + z.
Axiom Field_plus_com: forall x y :e F, x + y = y + x.
Axiom Field_zero_L: forall x :e F, zero + x = x.
Axiom Field_plus_inv: forall x :e F, exists y :e F, x + y = zero.
Axiom Field_mult_assoc: forall x y z :e F, x * (y * z) = (x * y) * z.
Axiom Field_mult_com: forall x y :e F, x * y = y * x.
Axiom Field_one_neq_zero: one <> zero.
Axiom Field_one_L: forall x :e F, one * x = x.
Axiom Field_mult_inv_L: forall x :e F, x <> zero -> exists y :e F, x * y = one.
Axiom Field_distr_L: forall x y z :e F, x * (y + z) = x * y + x * z.

(* Parameter Field_div "721b554268a9a69ec4ddc429f9be98a164c8910b662e21de0b0a667d19ac127f" "33f36e749d7a3683affaed574c634802fe501ef213c5ca5e7c8dc0153464ea3e" *)
Parameter Field_div:set -> set -> set.

Infix :/: 353 := Field_div.

Axiom Field_div_prop: forall x :e F, forall y :e F :\: {zero}, x :/: y :e F /\ x = y * (x :/: y).
Axiom Field_div_clos: forall x :e F, forall y :e F :\: {zero}, x :/: y :e F.
Axiom Field_mult_div: forall x :e F, forall y :e F :\: {zero}, x = y * (x :/: y).
Axiom Field_div_undef1: forall x y, x /:e F -> x :/: y = 0.
Axiom Field_div_undef2: forall x y, y /:e F -> x :/: y = 0.
Axiom Field_div_undef3: forall x, x :/: zero = 0.

Infix ^ 342 right := CRing_with_id_omega_exp Fs.

Axiom Field_omega_exp_0 : forall x, x ^ 0 = one.
Axiom Field_omega_exp_S : forall x, forall n :e omega, x ^ (ordsucc n) = x * x ^ n.
Axiom Field_omega_exp_1 : forall x :e F, x ^ 1 = x.
Axiom Field_omega_exp_clos : forall x :e F, forall n :e omega, x ^ n :e F.
Axiom Field_eval_poly_clos : forall n :e omega, forall cs :e F :^: n, forall x :e F, CRing_with_id_eval_poly Fs n cs x :e F.

Axiom Field_plus_cancelL : forall x y z :e F, x + y = x + z -> y = z.
Axiom Field_plus_cancelR : forall x y z :e F, x + z = y + z -> x = y.
Axiom Field_minus_eq: forall x :e F, - x = explicit_Field_minus F zero one (Field_plus Fs) (Field_mult Fs) x.
Axiom Field_minus_undef: forall x, x /:e F -> - x = 0.
Axiom Field_minus_clos : forall x :e F, - x :e F.
Axiom Field_minus_R : forall x :e F, x + - x = zero.
Axiom Field_minus_L : forall x :e F, - x + x = zero.
Axiom Field_minus_invol : forall x :e F, - - x = x.
Axiom Field_minus_one_In : - one :e F.
Axiom Field_zero_multR : forall x :e F, x * zero = zero.
Axiom Field_zero_multL : forall x :e F, zero * x = zero.
Axiom Field_minus_mult : forall x :e F, - x = (- one) * x.
Axiom Field_minus_one_square : (- one) * (- one) = one.
Axiom Field_minus_square : forall x :e F, (- x) * (- x) = x * x.
Axiom Field_minus_zero : - zero = zero.
Axiom Field_dist_R : forall x y z :e F, (x + y) * z = x * z + y * z.
Axiom Field_minus_plus_dist : forall x y :e F, - (x + y) = - x + - y.
Axiom Field_minus_mult_L : forall x y :e F, (- x) * y = - (x * y).
Axiom Field_minus_mult_R : forall x y :e F, x * (- y) = - (x * y).
Axiom Field_square_zero_inv : forall x :e F, x * x = zero -> x = zero.
Axiom Field_mult_zero_inv : forall x y :e F, x * y = zero -> x = zero \/ y = zero.

End Field.

Section Field2.

Variable Fs:set.
Variable Fs':set.

Let F : set := Field_carrier Fs.
Let zero : set := Field_zero Fs.
Let one : set := Field_one Fs.
Infix + 360 right := Field_plus Fs.
Infix * 355 right := Field_mult Fs.
Let F' : set := Field_carrier Fs'.
Let zero' : set := Field_zero Fs'.
Let one' : set := Field_one Fs'.
Infix :+: 360 right := Field_plus Fs'.
Infix :*: 355 right := Field_mult Fs'.

Prefix - 358 := Field_minus Fs.
Prefix :-: 358 := Field_minus Fs'.

(* Parameter subfield "dd4f4556431118d331981429937597efc8bf48e610d5e8046b728dd65002585d" "9216abdc1fcc466f5af2b17824d279c6b333449b4f283df271151525ba7c9aca" *)
Parameter subfield : prop.

Axiom subfield_I : Field Fs -> Field Fs' -> F c= F'
  -> zero = zero' -> one = one'
  -> (forall a b :e F, a + b = a :+: b)
  -> (forall a b :e F, a * b = a :*: b)
  -> subfield.
Axiom subfield_E : subfield -> forall p:prop,
 (Field Fs -> Field Fs' -> F c= F'
  -> zero = zero' -> one = one'
  -> (forall a b :e F, a + b = a :+: b)
  -> (forall a b :e F, a * b = a :*: b)
  -> p)
 -> p.

(* Parameter Field_Hom "12676b0afcebdd531bf5a99c2866d8f7da6b16c994f66eb12f1405c9fd63e375" "597c2157fb6463f8c1c7affb6f14328b44b57967ce9dff5ef3c600772504b9de" *)
Parameter Field_Hom : set -> prop.

Axiom Field_Hom_I : forall g,
        Field Fs -> Field Fs'
     -> g :e F' :^: F
     -> g zero = zero'
     -> g one = one'
     -> (forall a b :e F, g (a + b) = g a :+: g b)
     -> (forall a b :e F, g (a * b) = g a :*: g b)
     -> Field_Hom g.
Axiom Field_Hom_E : forall g, Field_Hom g -> forall p:prop,
       (Field Fs -> Field Fs'
     -> g :e F' :^: F
     -> g zero = zero'
     -> g one = one'
     -> (forall a b :e F, g (a + b) = g a :+: g b)
     -> (forall a b :e F, g (a * b) = g a :*: g b)
     -> (forall a :e F, g (- a) = :-: g a)
     -> (forall a :e F, g a = zero' -> a = zero)
     -> (forall a b :e F, g a = g b -> a = b)
     -> (forall a :e F, forall n :e omega, g (CRing_with_id_omega_exp Fs a n) = CRing_with_id_omega_exp Fs' (g a) n)
     -> p)
 -> p.
Axiom Field_Hom_inj : forall g, Field_Hom g -> forall a b :e F, g a = g b -> a = b.

End Field2.

Axiom subfield_refl: forall Fs, Field Fs -> subfield Fs Fs.
Axiom subfield_tra: forall Fs Fs' Fs'', subfield Fs Fs' -> subfield Fs' Fs'' -> subfield Fs Fs''.

(* Parameter Field_extension_by_1 "c932a6d0f2ee29b573c0be25ba093beec021e0fc0b04c4e76b8d0c627a582f33" "15c0a3060fb3ec8e417c48ab46cf0b959c315076fe1dc011560870c5031255de" *)
Parameter Field_extension_by_1 : set -> set -> set -> prop.

Axiom Field_extension_by_1_I: forall Fs Fs' a,
    subfield Fs Fs'
 -> a :e Field_carrier Fs' :\: Field_carrier Fs
 -> (forall Fs'', subfield Fs Fs'' -> a :e Field_carrier Fs'' -> subfield Fs' Fs'')
 -> Field_extension_by_1 Fs Fs' a.
Axiom Field_extension_by_1_E: forall Fs Fs' a, Field_extension_by_1 Fs Fs' a -> forall p:prop,
    (subfield Fs Fs'
  -> a :e Field_carrier Fs' :\: Field_carrier Fs
  -> (forall Fs'', subfield Fs Fs'' -> a :e Field_carrier Fs'' -> subfield Fs' Fs'')
  -> p)
 -> p.

(* Parameter radical_field_extension "84039222ea9e2c64fdc0a7ed6ea36601e7a743d9f5d57a381275ce025b4ab636" "4b1aa61ecf07fd27a8a97a4f5ac5a6df80f2d3ad5f55fc4cc58e6d3e76548591" *)
Parameter radical_field_extension : set -> set -> prop.

Axiom radical_field_extension_I: forall Fs Fs', forall r :e omega, forall Fseq,
     Fseq 0 = Fs
  -> Fseq r = Fs'
  -> (forall i :e ordsucc r, Field (Fseq i))
  -> (forall i :e r, exists a :e Field_carrier (Fseq (ordsucc i)), exists n :e omega,
              CRing_with_id_omega_exp (Fseq (ordsucc i)) a n :e Field_carrier (Fseq i)
           /\ Field_extension_by_1 (Fseq i) (Fseq (ordsucc i)) a)
  -> radical_field_extension Fs Fs'.
Axiom radical_field_extension_E: forall Fs Fs', radical_field_extension Fs Fs' ->
 forall p:prop,
    (Field Fs -> Field Fs' -> subfield Fs Fs'
  -> forall r :e omega, forall Fseq,
     Fseq 0 = Fs -> Fseq r = Fs'
  -> (forall i :e ordsucc r, Field (Fseq i))
  -> (forall i :e ordsucc r, forall j :e ordsucc i, subfield (Fseq j) (Fseq i))
  -> (forall i :e r, exists a :e Field_carrier (Fseq (ordsucc i)), exists n :e omega,
              CRing_with_id_omega_exp (Fseq (ordsucc i)) a n :e Field_carrier (Fseq i)
           /\ Field_extension_by_1 (Fseq i) (Fseq (ordsucc i)) a)
  -> p)
 -> p.

(* Parameter Field_automorphism_fixing "76c3f5c92d9fb5491c366bf4406686f6bb2d99a486ebe880c2b1d491036f79c0" "55cacef892af061835859ed177e5442518c93eb7ee28697cde3deaec5eafbf01" *)
Parameter Field_automorphism_fixing : set -> set -> set -> prop.

Axiom Field_automorphism_fixing_I : forall K F f,
     subfield F K
  -> Field_Hom K K f
  -> (forall y :e K 0, exists x :e K 0, f x = y)
  -> (forall x :e F 0, f x = x)
  -> Field_automorphism_fixing K F f.
Axiom Field_automorphism_fixing_E : forall K F f, Field_automorphism_fixing K F f -> forall p:prop,
    (subfield F K
  -> Field_Hom K K f
  -> (forall y :e K 0, exists x :e K 0, f x = y)
  -> (forall x :e F 0, f x = x)
  -> p)
 -> p.

Definition lam_comp : set -> set -> set -> set := fun A f g => fun x :e A => f (g x).
Definition lam_id : set -> set := fun A => fun x :e A => x.

Axiom lam_comp_exp_In : forall A B C, forall f :e B :^: A, forall g :e C :^: B, lam_comp A g f :e C :^: A.
Axiom lam_id_exp_In : forall A, lam_id A :e A :^: A.
Axiom lam_comp_assoc : forall A B, forall f :e B :^: A, forall g h, lam_comp A h (lam_comp A g f) = lam_comp A (lam_comp B h g) f.
Axiom lam_comp_id_L : forall A B, forall f :e B :^: A, lam_comp A (lam_id B) f = f.
Axiom lam_comp_id_R : forall A B, forall f :e B :^: A, lam_comp A f (lam_id A) = f.
Axiom Field_Hom_id : forall F, Field F -> Field_Hom F F (lam_id (F 0)).
Axiom Field_Hom_comp : forall F F' F'' g h, Field_Hom F F' g -> Field_Hom F' F'' h -> Field_Hom F F'' (lam_comp (F 0) h g).

Definition Galois_Group : set -> set -> set
 := fun K F => pack_b {f :e K 0 :^: K 0|Field_automorphism_fixing K F f} (lam_comp (K 0)).

Axiom Galois_Group_0 : forall K F, Galois_Group K F 0 = {f :e K 0 :^: K 0|Field_automorphism_fixing K F f}.
Axiom Galois_Group_Group : forall F K, subfield F K -> Group (Galois_Group K F).

Section explicit_Reals_transfer.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable leq : set -> set -> prop.

(* Unicode <= "2264" *)
Infix <= 490 := leq.

Variable R' : set.

Variable zero' one' : set.
Variable plus' mult' : set -> set -> set.

Infix :+: 360 right := plus'.
Infix :*: 355 right := mult'.

Variable leq' : set -> set -> prop.

Variable f:set -> set.

Axiom explicit_Reals_transfer : explicit_Reals R zero one plus mult leq
 -> bij R R' f
 -> f zero = zero'
 -> f one = one'
 -> (forall x y :e R, f (x + y) = f x :+: f y)
 -> (forall x y :e R, f (x * y) = f x :*: f y)
 -> (forall x y :e R, x <= y <-> leq' (f x) (f y))
 -> explicit_Reals R' zero' one' plus' mult' leq'.

End explicit_Reals_transfer.

Section explicit_Complex.

Variable C : set.

Variable Re Im : set -> set.
Variable zero one i : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Let R := {z :e C | Re z = z}.

(* Parameter explicit_Complex "552d05a240b7958c210e990f72c4938aa612373e1d79a5d97fa37f80e3d844b3" "bacb8536bbb356aa59ba321fb8eade607d1654d8a7e0b33887be9afbcfa5c504" *)
Parameter explicit_Complex : prop.

Axiom explicit_Complex_I : explicit_Field C zero one plus mult
 -> (exists leq:set -> set -> prop, explicit_Reals R zero one plus mult leq)
 -> (forall z :e C, Im z :e R)
 -> (i :e C)
 -> (forall z :e C, Re z :e C)
 -> (forall z :e C, Im z :e C)
 -> (forall z :e C, z = Re z + i * Im z)
 -> (forall z w :e C, Re z = Re w -> Im z = Im w -> z = w)
 -> (i * i + one = zero)
 -> explicit_Complex.

End explicit_Complex.

Section RealsToComplex.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.

Infix + 360 right := plus.
Infix * 355 right := mult.

Prefix - 358 := explicit_Field_minus R zero one plus mult.

Variable leq : set -> set -> prop.

Variable pa: set -> set -> set.

Let C : set := ReplSep2 R (fun _ => R) (fun x y => True) pa.

Let Re : set -> set := fun z => Eps_i (fun x => x :e R /\ exists y :e R, z = pa x y).
Let Im : set -> set := fun z => Eps_i (fun y => y :e R /\ z = pa (Re z) y).
Let Re' : set -> set := fun z => pa (Re z) zero.
Let Im' : set -> set := fun z => pa (Im z) zero.

Let R' := {z :e C | Re' z = z}.

Let zero' : set := pa zero zero.
Let one' : set := pa one zero.
Let i' : set := pa zero one.
Let plus' : set -> set -> set := fun z w => pa (Re z + Re w) (Im z + Im w).
Let mult' : set -> set -> set := fun z w => pa (Re z * Re w + - (Im z * Im w)) (Re z * Im w + Im z * Re w).

Axiom explicit_RealsToComplex: explicit_Reals R zero one plus mult leq
  -> (forall x1 y1 x2 y2 :e R, pa x1 y1 = pa x2 y2 -> x1 = x2 /\ y1 = y2)
  -> explicit_Complex C Re' Im' zero' one' i' plus' mult'.

Axiom explicit_RealsToComplex_exact_Subq: explicit_Reals R zero one plus mult leq
  -> (forall x1 y1 x2 y2 :e R, pa x1 y1 = pa x2 y2 -> x1 = x2 /\ y1 = y2)
  -> (forall x :e R, pa x zero = x)
  -> explicit_Complex C Re' Im' zero' one' i' plus' mult'
  /\ R c= C
  /\ (forall x :e R, Re x = x)
  /\ zero' = zero
  /\ one' = one
  /\ (forall x y :e R, plus' x y = x + y)
  /\ (forall x y :e R, mult' x y = x * y).

End RealsToComplex.

Section SurrealArithmetic.

(* Parameter minus_SNo "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "268a6c1da15b8fe97d37be85147bc7767b27098cdae193faac127195e8824808" *)
Parameter minus_SNo : set -> set.

Prefix - 358 := minus_SNo.

(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Axiom minus_SNo_eq : forall x, SNo x -> - x = SNoCut {- z|z :e SNoR x} {- w|w :e SNoL x}.
Axiom minus_SNo_prop1 : forall x, SNo x -> SNo (- x) /\ (forall u :e SNoL x, - x < - u) /\ (forall u :e SNoR x, - u < - x) /\ SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
Axiom SNo_minus_SNo : forall x, SNo x -> SNo (- x).

Axiom minus_SNo_Lt_contra : forall x y, SNo x -> SNo y -> x < y -> - y < - x.
Axiom minus_SNo_Le_contra : forall x y, SNo x -> SNo y -> x <= y -> - y <= - x.
Axiom minus_SNo_SNoCutP : forall x, SNo x -> SNoCutP {- z|z :e SNoR x} {- w|w :e SNoL x}.
Axiom minus_SNo_SNoCutP_gen : forall L R, SNoCutP L R -> SNoCutP {- z|z :e R} {- w|w :e L}.
Axiom minus_SNo_Lev_lem1 : forall alpha, ordinal alpha -> forall x :e SNoS_ alpha, SNoLev (- x) c= SNoLev x.
Axiom minus_SNo_Lev_lem2 : forall x, SNo x -> SNoLev (- x) c= SNoLev x.
Axiom minus_SNo_invol : forall x, SNo x -> - - x = x.
Axiom minus_SNo_Lev : forall x, SNo x -> SNoLev (- x) = SNoLev x.
Axiom minus_SNo_SNo_ : forall alpha, ordinal alpha -> forall x, SNo_ alpha x -> SNo_ alpha (- x).
Axiom minus_SNo_SNoS_ : forall alpha, ordinal alpha -> forall x, x :e SNoS_ alpha -> - x :e SNoS_ alpha.
Axiom minus_SNoCut_eq_lem : forall v, SNo v -> forall L R, SNoCutP L R -> v = SNoCut L R -> - v = SNoCut {- z|z :e R} {- w|w :e L}.
Axiom minus_SNoCut_eq : forall L R, SNoCutP L R -> - SNoCut L R = SNoCut {- z|z :e R} {- w|w :e L}.
Axiom minus_SNo_Lt_contra1 : forall x y, SNo x -> SNo y -> -x < y -> - y < x.
Axiom minus_SNo_Lt_contra2 : forall x y, SNo x -> SNo y -> x < -y -> y < - x.
Axiom minus_SNo_Lt_contra3 : forall x y, SNo x -> SNo y -> -x < -y -> y < x.
Axiom minus_SNo_0 : - 0 = 0.
Axiom SNo_momega : SNo (- omega).
Axiom mordinal_SNo : forall alpha, ordinal alpha -> SNo (- alpha).
Axiom mordinal_SNoLev : forall alpha, ordinal alpha -> SNoLev (- alpha) = alpha.
Axiom mordinal_SNoLev_min : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e alpha -> - alpha < z.
Axiom mordinal_SNoLev_min_2 : forall alpha, ordinal alpha -> forall z, SNo z -> SNoLev z :e ordsucc alpha -> - alpha <= z.

Axiom minus_SNo_SNoS_omega : forall x :e SNoS_ omega, - x :e SNoS_ omega.

Axiom nonpos_nonneg_0 : forall m n :e omega, m = - n -> m = 0 /\ n = 0.

(* Parameter add_SNo "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" "127d043261bd13d57aaeb99e7d2c02cae2bd0698c0d689b03e69f1ac89b3c2c6" *)
Parameter add_SNo : set -> set -> set.

Infix + 360 right := add_SNo.

Axiom add_SNo_eq : forall x, SNo x -> forall y, SNo y ->
    x + y = SNoCut ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).

Axiom add_SNo_prop1 : forall x y, SNo x -> SNo y ->
    SNo (x + y)
 /\ (forall u :e SNoL x, u + y < x + y)
 /\ (forall u :e SNoR x, x + y < u + y)
 /\ (forall u :e SNoL y, x + u < x + y)
 /\ (forall u :e SNoR y, x + y < x + u)
 /\ SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).

Axiom SNo_add_SNo : forall x y, SNo x -> SNo y -> SNo (x + y).
Axiom SNo_add_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + z).
Axiom SNo_add_SNo_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> SNo (x + y + z + w).

Axiom add_SNo_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x < z -> x + y < z + y.

Axiom add_SNo_Le1 : forall x y z, SNo x -> SNo y -> SNo z -> x <= z -> x + y <= z + y.

Axiom add_SNo_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> y < z -> x + y < x + z.

Axiom add_SNo_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> y <= z -> x + y <= x + z.

Axiom add_SNo_Lt3a : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y <= w -> x + y < z + w.

Axiom add_SNo_Lt3b : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y < w -> x + y < z + w.

Axiom add_SNo_Lt3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x < z -> y < w -> x + y < z + w.

Axiom add_SNo_Le3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x <= z -> y <= w -> x + y <= z + w.

Axiom add_SNo_SNoCutP : forall x y, SNo x -> SNo y -> SNoCutP ({w + y|w :e SNoL x} :\/: {x + w|w :e SNoL y}) ({z + y|z :e SNoR x} :\/: {x + z|z :e SNoR y}).

Axiom add_SNo_SNoCutP_gen : forall Lx Rx Ly Ry, SNoCutP Lx Rx -> SNoCutP Ly Ry
 -> SNoCutP ({w + SNoCut Ly Ry|w :e Lx} :\/: {SNoCut Lx Rx + w|w :e Ly})
            ({z + SNoCut Ly Ry|z :e Rx} :\/: {SNoCut Lx Rx + z|z :e Ry}).

Axiom add_SNo_com : forall x y, SNo x -> SNo y -> x + y = y + x.

Axiom add_SNo_0L : forall x, SNo x -> 0 + x = x.

Axiom add_SNo_0R : forall x, SNo x -> x + 0 = x.

Axiom add_SNo_minus_SNo_linv : forall x, SNo x -> -x+x = 0.
Axiom SNo_add_SNo_3c : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x + y + - z).

Axiom add_SNo_minus_SNo_rinv : forall x, SNo x -> x + -x = 0.

Axiom add_SNo_ordinal_SNoCutP : forall alpha, ordinal alpha -> forall beta, ordinal beta -> SNoCutP ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.

Axiom add_SNo_ordinal_eq : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + beta = SNoCut ({x + beta | x :e SNoS_ alpha} :\/: {alpha + x | x :e SNoS_ beta}) Empty.

Axiom add_SNo_ordinal_ordinal : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordinal (alpha + beta).

Axiom add_SNo_ordinal_SL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordsucc alpha + beta = ordsucc (alpha + beta).

Axiom add_SNo_ordinal_SR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> alpha + ordsucc beta = ordsucc (alpha + beta).

Axiom add_SNo_ordinal_InL : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e alpha, gamma + beta :e alpha + beta.

Axiom add_SNo_ordinal_InR : forall alpha, ordinal alpha -> forall beta, ordinal beta -> forall gamma :e beta, alpha + gamma :e alpha + beta.

Axiom add_nat_add_SNo : forall n m :e omega, add_nat n m = n + m.

Axiom add_SNo_In_omega : forall n m :e omega, n + m :e omega.

Axiom add_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x + y), (exists v :e SNoL x, u <= v + y) \/ (exists v :e SNoL y, u <= x + v).

Axiom add_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x + y), (exists v :e SNoR x, v + y <= u) \/ (exists v :e SNoR y, x + v <= u).

Axiom add_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z -> x + (y + z) = (x + y) + z.

Axiom add_SNo_cancel_L : forall x y z, SNo x -> SNo y -> SNo z -> x + y = x + z -> y = z.

Axiom add_SNo_cancel_R : forall x y z, SNo x -> SNo y -> SNo z -> x + y = z + y -> x = z.

Axiom minus_add_SNo_distr : forall x y, SNo x -> SNo y -> -(x+y) = (-x) + (-y).
Axiom minus_add_SNo_distr_3 : forall x y z, SNo x -> SNo y -> SNo z -> -(x + y + z) = -x + - y + -z.

Axiom add_SNo_Lev_bd : forall x y, SNo x -> SNo y -> SNoLev (x + y) c= SNoLev x + SNoLev y.
Axiom add_SNo_SNoS_omega : forall x y :e SNoS_ omega, x + y :e SNoS_ omega.

Axiom add_SNo_minus_R2 : forall x y, SNo x -> SNo y -> (x + y) + - y = x.
Axiom add_SNo_minus_R2' : forall x y, SNo x -> SNo y -> (x + - y) + y = x.
Axiom add_SNo_minus_L2 : forall x y, SNo x -> SNo y -> - x + (x + y) = y.
Axiom add_SNo_minus_L2' : forall x y, SNo x -> SNo y -> x + (- x + y) = y.
Axiom add_SNo_Lt1_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < z + y -> x < z.
Axiom add_SNo_Lt2_cancel : forall x y z, SNo x -> SNo y -> SNo z -> x + y < x + z -> y < z.
Axiom add_SNo_assoc_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> x + y + z + w = (x + y + z) + w.
Axiom add_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x + y + z = y + x + z.
Axiom add_SNo_com_4_inner_flat : forall x y z w, SNo y -> SNo z -> SNo w
  -> x + y + z + w = x + z + y + w.
Axiom add_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x + y) + z = (x + z) + y.
Axiom add_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x + y) + (z + w) = (x + z) + (y + w).
Axiom add_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x + y + z = z + x + y.
Axiom add_SNo_rotate_4_1 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w ->
  x + y + z + w = w + x + y + z.
Axiom add_SNo_rotate_5_1 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = v + x + y + z + w.
Axiom add_SNo_rotate_5_2 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x + y + z + w + v = w + v + x + y + z.
Axiom add_SNo_minus_SNo_prop1 : forall x y, SNo x -> SNo y -> - x + x + y = y.
Axiom add_SNo_minus_SNo_prop2 : forall x y, SNo x -> SNo y -> x + - x + y = y.
Axiom add_SNo_minus_SNo_prop3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (- z + w) = x + y + w.
Axiom add_SNo_minus_SNo_prop4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + z) + (w + - z) = x + y + w.
Axiom add_SNo_minus_SNo_prop5 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y + - z) + (z + w) = x + y + w.
Axiom add_SNo_minus_Lt1 : forall x y z, SNo x -> SNo y -> SNo z -> x + - y < z -> x < z + y.
Axiom add_SNo_minus_Lt1b : forall x y z, SNo x -> SNo y -> SNo z -> x < z + y -> x + - y < z.
Axiom add_SNo_minus_Lt2 : forall x y z, SNo x -> SNo y -> SNo z -> z < x + - y -> z + y < x.
Axiom add_SNo_minus_Lt2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y < x -> z < x + - y.
Axiom add_SNo_minus_Lt1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y < w + z -> x + y + - z < w.
Axiom add_SNo_minus_Lt2b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> w + z < x + y -> w < x + y + - z.
Axiom add_SNo_Lt_subprop2 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v
  -> x + u < z + v
  -> y + v < w + u
  -> x + y < z + w.
Axiom add_SNo_Lt_subprop3a : forall x y z w u a, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a
  -> x + z < w + a
  -> y + a < u
  -> x + y + z < w + u.
Axiom add_SNo_Lt_subprop3b : forall x y w u v a, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a
  -> x + a < w + v
  -> y < a + u
  -> x + y < w + u + v.
Axiom add_SNo_Lt_subprop3c : forall x y z w u a b c, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo a -> SNo b -> SNo c
 -> x + a < b + c
 -> y + c < u
 -> b + z < w + a
 -> x + y + z < w + u.
Axiom add_SNo_Lt_subprop3d : forall x y w u v a b c, SNo x -> SNo y -> SNo w -> SNo u -> SNo v -> SNo a -> SNo b -> SNo c
 -> x + a < b + v
 -> y < c + u
 -> b + c < w + a
 -> x + y < w + u + v.

Axiom ordinal_ordsucc_SNo_eq : forall alpha, ordinal alpha -> ordsucc alpha = 1 + alpha.

Axiom add_SNo_omega_eps_Lt : forall x y :e SNoS_ omega, x < y -> exists n :e omega, x + eps_ n < y.

(* Parameter mul_SNo "f56bf39b8eea93d7f63da529dedb477ae1ab1255c645c47d8915623f364f2d6b" "48d05483e628cb37379dd5d279684d471d85c642fe63533c3ad520b84b18df9d" *)
Parameter mul_SNo : set -> set -> set.

Infix * 355 right := mul_SNo.

Axiom mul_SNo_eq : forall x, SNo x -> forall y, SNo y ->
   x * y
      = SNoCut ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoL y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoR y})
               ({(w 0) * y + x * (w 1) + - (w 0) * (w 1)|w :e SNoL x :*: SNoR y}
                  :\/:
                {(z 0) * y + x * (z 1) + - (z 0) * (z 1)|z :e SNoR x :*: SNoL y}).

Axiom mul_SNo_eq_2 : forall x y, SNo x -> SNo y ->
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

Axiom mul_SNo_prop_1 : forall x, SNo x -> forall y, SNo y ->
 forall p:prop,
    (SNo (x * y)
  -> (forall u :e SNoL x, forall v :e SNoL y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoR x, forall v :e SNoR y, u * y + x * v < x * y + u * v)
  -> (forall u :e SNoL x, forall v :e SNoR y, x * y + u * v < u * y + x * v)
  -> (forall u :e SNoR x, forall v :e SNoL y, x * y + u * v < u * y + x * v)
  -> p)
 -> p.

Axiom SNo_mul_SNo : forall x y, SNo x -> SNo y -> SNo (x * y).

Axiom mul_SNo_eq_3 : forall x y, SNo x -> SNo y ->
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

Axiom mul_SNo_Lt : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u < x -> v < y -> u * y + x * v < x * y + u * v.
Axiom mul_SNo_Le : forall x y u v, SNo x -> SNo y -> SNo u -> SNo v
 -> u <= x -> v <= y -> u * y + x * v <= x * y + u * v.

Axiom mul_SNo_SNoL_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 (exists v :e SNoL x, exists w :e SNoL y, u + v * w <= v * y + x * w)
 \/
 (exists v :e SNoR x, exists w :e SNoR y, u + v * w <= v * y + x * w).

Axiom mul_SNo_SNoL_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoL (x * y),
 forall p:prop,
      (forall v :e SNoL x, forall w :e SNoL y, u + v * w <= v * y + x * w -> p)
   -> (forall v :e SNoR x, forall w :e SNoR y, u + v * w <= v * y + x * w -> p)
   -> p.

Axiom mul_SNo_SNoR_interpolate : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 (exists v :e SNoL x, exists w :e SNoR y, v * y + x * w <= u + v * w)
 \/
 (exists v :e SNoR x, exists w :e SNoL y, v * y + x * w <= u + v * w).

Axiom mul_SNo_SNoR_interpolate_impred : forall x y, SNo x -> SNo y -> forall u :e SNoR (x * y),
 forall p:prop,
     (forall v :e SNoL x, forall w :e SNoR y, v * y + x * w <= u + v * w -> p)
  -> (forall v :e SNoR x, forall w :e SNoL y, v * y + x * w <= u + v * w -> p)
  -> p.

Axiom mul_SNo_zeroR : forall x, SNo x -> x * 0 = 0.
Axiom mul_SNo_oneR : forall x, SNo x -> x * 1 = x.
Axiom mul_SNo_com : forall x y, SNo x -> SNo y -> x * y = y * x.
Axiom mul_SNo_minus_distrL : forall x y, SNo x -> SNo y -> (- x) * y = - x * y.
Axiom mul_SNo_minus_distrR : forall x y, SNo x -> SNo y -> x * (- y) = - (x * y).
Axiom mul_SNo_distrR : forall x y z, SNo x -> SNo y -> SNo z -> (x + y) * z = x * z + y * z.
Axiom mul_SNo_distrL : forall x y z, SNo x -> SNo y -> SNo z -> x * (y + z) = x * y + x * z.
Axiom mul_SNo_assoc : forall x y z, SNo x -> SNo y -> SNo z -> x * (y * z) = (x * y) * z.

Axiom mul_nat_mul_SNo : forall n m :e omega, mul_nat n m = n * m.

Axiom mul_SNo_In_omega : forall n m :e omega, n * m :e omega.

Axiom mul_SNo_zeroL : forall x, SNo x -> 0 * x = 0.
Axiom mul_SNo_oneL : forall x, SNo x -> 1 * x = x.
Axiom pos_mul_SNo_Lt : forall x y z, SNo x -> 0 < x -> SNo y -> SNo z -> y < z -> x * y < x * z.
Axiom nonneg_mul_SNo_Le : forall x y z, SNo x -> 0 <= x -> SNo y -> SNo z -> y <= z -> x * y <= x * z.
Axiom neg_mul_SNo_Lt : forall x y z, SNo x -> x < 0 -> SNo y -> SNo z -> z < y -> x * y < x * z.
Axiom nonpos_mul_SNo_Le : forall x y z, SNo x -> x <= 0 -> SNo y -> SNo z -> z <= y -> x * y <= x * z.

(* Parameter abs_SNo "9f9389c36823b2e0124a7fe367eb786d080772b5171a5d059b10c47361cef0ef" "34f6dccfd6f62ca020248cdfbd473fcb15d8d9c5c55d1ec7c5ab6284006ff40f" *)
Parameter abs_SNo : set -> set.

Axiom nonneg_abs_SNo : forall x, 0 <= x -> abs_SNo x = x.
Axiom not_nonneg_abs_SNo : forall x, ~(0 <= x) -> abs_SNo x = - x.
Axiom abs_SNo_0 : abs_SNo 0 = 0.
Axiom pos_abs_SNo : forall x, 0 < x -> abs_SNo x = x.
Axiom neg_abs_SNo : forall x, SNo x -> x < 0 -> abs_SNo x = - x.
Axiom SNo_abs_SNo : forall x, SNo x -> SNo (abs_SNo x).
Axiom abs_SNo_Lev : forall x, SNo x -> SNoLev (abs_SNo x) = SNoLev x.
Axiom abs_SNo_minus: forall x, SNo x -> abs_SNo (- x) = abs_SNo x.
Axiom abs_SNo_dist_swap: forall x y, SNo x -> SNo y -> abs_SNo (x + - y) = abs_SNo (y + - x).
Axiom SNo_triangle: forall x y, SNo x -> SNo y -> abs_SNo (x + y) <= abs_SNo x + abs_SNo y.
Axiom SNo_triangle2: forall x y z, SNo x -> SNo y -> SNo z -> abs_SNo (x + - z) <= abs_SNo (x + - y) + abs_SNo (y + - z).
Axiom eps_SNo_eq : forall n, nat_p n -> forall x :e SNoS_ (ordsucc n), 0 < x -> SNoEq_ (SNoLev x) (eps_ n) x -> exists m :e n, x = eps_ m.
Axiom eps_SNoCutP : forall n :e omega, SNoCutP {0} {eps_ m|m :e n}.
Axiom eps_SNoCut : forall n :e omega, eps_ n = SNoCut {0} {eps_ m|m :e n}.
Axiom eps_ordsucc_half_add : forall n, nat_p n -> eps_ (ordsucc n) + eps_ (ordsucc n) = eps_ n.
Axiom SNo_eps_1 : SNo (eps_ 1).
Axiom eps_1_half_eq1 : eps_ 1 + eps_ 1 = 1.
Axiom add_SNo_1_1_2 : 1 + 1 = 2.
Axiom eps_1_half_eq2 : 2 * eps_ 1 = 1.
Axiom eps_1_half_eq3 : eps_ 1 * 2 = 1.
Axiom eps_1_split_eq : forall x, SNo x -> eps_ 1 * x + eps_ 1 * x = x.
Axiom eps_1_split_Le_bd : forall x y z, SNo x -> SNo y -> SNo z -> y <= eps_ 1 * x -> z <= eps_ 1 * x -> y + z <= x.
Axiom eps_1_split_LeLt_bd : forall x y z, SNo x -> SNo y -> SNo z -> y <= eps_ 1 * x -> z < eps_ 1 * x -> y + z < x.
Axiom eps_1_split_LtLe_bd : forall x y z, SNo x -> SNo y -> SNo z -> y < eps_ 1 * x -> z <= eps_ 1 * x -> y + z < x.
Axiom eps_1_split_Lt_bd : forall x y z, SNo x -> SNo y -> SNo z -> y < eps_ 1 * x -> z < eps_ 1 * x -> y + z < x.

Definition SNo_ord_seq : set -> (set -> set) -> prop
 := fun lambda s => forall alpha :e lambda, SNo (s alpha).

Axiom mul_SNo_pos_pos: forall x y, SNo x -> SNo y -> 0 < x -> 0 < y -> 0 < x * y.
Axiom mul_SNo_pos_neg: forall x y, SNo x -> SNo y -> 0 < x -> y < 0 -> x * y < 0.
Axiom mul_SNo_neg_pos: forall x y, SNo x -> SNo y -> x < 0 -> 0 < y -> x * y < 0.
Axiom mul_SNo_neg_neg: forall x y, SNo x -> SNo y -> x < 0 -> y < 0 -> 0 < x * y.
Axiom mul_SNo_nonzero: forall x y, SNo x -> SNo y -> x <> 0 -> y <> 0 -> x * y <> 0.
Axiom minus_SNo_restr_SNo : forall x, SNo x -> forall alpha :e SNoLev x,
 (- x) :/\: SNoElts_ alpha = - (x :/\: SNoElts_ alpha).
Axiom minus_SNo_exactly1of2 : forall x, SNo x -> forall alpha :e SNoLev x, exactly1of2 (alpha :e x) (alpha :e - x).
Axiom minus_SNo_In : forall x, SNo x -> forall alpha :e SNoLev x, alpha :e x -> alpha /:e - x.
Axiom minus_SNo_nIn : forall x, SNo x -> forall alpha :e SNoLev x, alpha /:e x -> alpha :e - x.

Definition exp_SNo_nat : set->set->set := fun n m:set => nat_primrec 1 (fun _ r => n * r) m.

Infix ^ 342 right := exp_SNo_nat.

End SurrealArithmetic.

Definition CSNo : set -> prop := fun z => exists x, SNo x /\ exists y, SNo y /\ z = SNo_pair x y.

Axiom CSNo_I : forall x y, SNo x -> SNo y -> CSNo (SNo_pair x y).
Axiom CSNo_E : forall z, CSNo z ->
  forall p:set -> prop,
      (forall x y, SNo x -> SNo y -> z = SNo_pair x y -> p (SNo_pair x y))
    -> p z.
Axiom SNo_CSNo : forall x, SNo x -> CSNo x.

Section Complex.

Definition Complex_i : set := SNo_pair 0 1.

Let i := Complex_i.

Axiom CSNo_Complex_i : CSNo i.

Definition CSNo_Re : set -> set := fun z => Eps_i (fun x => SNo x /\ exists y, SNo y /\ z = SNo_pair x y).
Definition CSNo_Im : set -> set := fun z => Eps_i (fun y => SNo y /\ z = SNo_pair (CSNo_Re z) y).

Let Re : set -> set := CSNo_Re.
Let Im : set -> set := CSNo_Im.
Let pa : set -> set -> set := SNo_pair.

Axiom CSNo_Re1: forall z, CSNo z -> SNo (Re z) /\ exists y, SNo y /\ z = pa (Re z) y.
Axiom CSNo_Re2: forall x y, SNo x -> SNo y -> Re (pa x y) = x.
Axiom CSNo_Im1: forall z, CSNo z -> SNo (Im z) /\ z = pa (Re z) (Im z).
Axiom CSNo_Im2: forall x y, SNo x -> SNo y -> Im (pa x y) = y.
Axiom CSNo_ReR: forall z, CSNo z -> SNo (Re z).
Axiom CSNo_ImR: forall z, CSNo z -> SNo (Im z).
Axiom CSNo_ReIm: forall z, CSNo z -> z = pa (Re z) (Im z).
Axiom CSNo_ReIm_split: forall z w, CSNo z -> CSNo w -> Re z = Re w -> Im z = Im w -> z = w.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

Definition minus_CSNo : set -> set := fun z => pa (- Re z) (- Im z).
Definition add_CSNo : set -> set -> set := fun z w => pa (Re z + Re w) (Im z + Im w).
Definition mul_CSNo : set -> set -> set := fun z w => pa (Re z * Re w + - (Im z * Im w)) (Re z * Im w + Im z * Re w).

Axiom CSNo_minus_CSNo : forall z, CSNo z -> CSNo (minus_CSNo z).

Axiom SNo_Re: forall x, SNo x -> Re x = x.

Axiom SNo_Im: forall x, SNo x -> Im x = 0.

Axiom Re_0 : Re 0 = 0.

Axiom Im_0 : Im 0 = 0.

Axiom Re_1 : Re 1 = 1.

Axiom Im_1 : Im 1 = 0.

Axiom Re_i : Re i = 0.

Axiom Im_i : Im i = 1.

Axiom add_SNo_add_CSNo : forall x y, SNo x -> SNo y -> x + y = add_CSNo x y.

Axiom CSNo_add_CSNo : forall z w, CSNo z -> CSNo w -> CSNo (add_CSNo z w).

Axiom add_CSNo_0L : forall z, CSNo z -> add_CSNo 0 z = z.

Axiom add_CSNo_0R : forall z, CSNo z -> add_CSNo z 0 = z.

Axiom add_CSNo_minus_CSNo_linv : forall z, CSNo z -> add_CSNo (minus_CSNo z) z = 0.

Axiom add_CSNo_minus_CSNo_rinv : forall z, CSNo z -> add_CSNo z (minus_CSNo z) = 0.

Axiom minus_SNo_minus_CSNo : forall x, SNo x -> - x = minus_CSNo x.

End Complex.

Section Complex.

Prefix - 358 := minus_CSNo.
Infix + 360 right := add_CSNo.
Infix * 355 right := mul_CSNo.

Definition int : set := omega :\/: {- n|n :e omega}.

Axiom int_SNo : forall x :e int, SNo x.

Definition Sum : set -> set -> (set -> set) -> set
 := fun m n f =>
      nat_primrec 0 (fun k r => if k :e m then 0 else f k + r) (ordsucc n).

Definition Prod : set -> set -> (set -> set) -> set
 := fun m n f =>
      nat_primrec 1 (fun k r => if k :e m then 1 else f k * r) (ordsucc n).

End Complex.

Section Int.

Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Prefix - 358 := minus_SNo.

Axiom int_SNo_cases : forall p:set -> prop,
    (forall n :e omega, p n)
 -> (forall n :e omega, p (- n))
 -> forall x :e int, p x.
Axiom Subq_omega_int : omega c= int.
Axiom int_minus_SNo_omega : forall n :e omega, - n :e int.
Axiom int_minus_SNo: forall x :e int, - x :e int.
Axiom int_add_SNo_lem: forall n :e omega, forall m, nat_p m -> - n + m :e int.
Axiom int_add_SNo: forall x y :e int, x + y :e int.
Axiom int_mul_SNo: forall x y :e int, x * y :e int.

Definition divides_int : set -> set -> prop :=
  fun m n => m :e int /\ n :e int /\ exists k :e int, m * k = n.

Definition coprime_int : set->set->prop := fun a b => a :e int /\ b :e int /\ forall x :e omega :\: 1, divides_int x a -> divides_int x b -> x = 1.

Definition equiv_nat_mod : set -> set -> set -> prop
  := fun m k n => m :e omega /\ k :e omega /\ n :e omega :\: 1
       /\ ((exists q :e omega, m + q * n = k)
        \/ (exists q :e omega, k + q * n = m)).

Definition equiv_int_mod : set -> set -> set -> prop
  := fun m k n => m :e int /\ k :e int /\ n :e omega :\: 1 /\ divides_int n (m + - k).

Axiom int_cases_3 : forall p:set -> prop,
    p 0
 -> (forall n :e omega :\: 1, p n)
 -> (forall n :e omega :\: 1, p (- n))
 -> forall x :e int, p x.

Axiom int_cases_3' : forall x :e int, forall p:prop,
    (x = 0 -> p)
 -> (x :e omega :\: 1 -> p)
 -> (forall n :e omega :\: 1, x = - n -> p)
 -> p.

Axiom divides_nat_int : forall m n, divides_nat m n -> divides_int m n.
Axiom divides_int_nat : forall m n :e omega, divides_int m n -> divides_nat m n.
Axiom coprime_nat_int : forall a b, coprime_nat a b -> coprime_int a b.
Axiom coprime_int_nat : forall a b :e omega, coprime_int a b -> coprime_nat a b.
Axiom equiv_nat_mod_int : forall m k n, equiv_nat_mod m k n -> equiv_int_mod m k n.
Axiom equiv_int_mod_nat : forall m k :e omega, forall n, equiv_int_mod m k n -> equiv_nat_mod m k n.

End Int.

(* Parameter pack_b_b_r_e_e "94ec6541b5d420bf167196743d54143ff9e46d4022e0ccecb059cf098af4663d" "8efb1973b4a9b292951aa9ca2922b7aa15d8db021bfada9c0f07fc9bb09b65fb" *)
Parameter pack_b_b_r_e_e : set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> set.

Axiom pack_b_b_r_e_e_0_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> X = S 0.

Axiom pack_b_b_r_e_e_0_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, X = pack_b_b_r_e_e X f g R c d 0.

Axiom pack_b_b_r_e_e_1_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> forall x y :e X, f x y = decode_b (S 1) x y.

Axiom pack_b_b_r_e_e_1_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, forall x y :e X, f x y = decode_b (pack_b_b_r_e_e X f g R c d 1) x y.

Axiom pack_b_b_r_e_e_2_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> forall x y :e X, g x y = decode_b (S 2) x y.

Axiom pack_b_b_r_e_e_2_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, forall x y :e X, g x y = decode_b (pack_b_b_r_e_e X f g R c d 2) x y.

Axiom pack_b_b_r_e_e_3_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> forall x y :e X, R x y = decode_r (S 3) x y.

Axiom pack_b_b_r_e_e_3_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, forall x y :e X, R x y = decode_r (pack_b_b_r_e_e X f g R c d 3) x y.

Axiom pack_b_b_r_e_e_4_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> c = S 4.

Axiom pack_b_b_r_e_e_4_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, c = pack_b_b_r_e_e X f g R c d 4.

Axiom pack_b_b_r_e_e_5_eq: forall S X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, S = pack_b_b_r_e_e X f g R c d -> d = S 5.

Axiom pack_b_b_r_e_e_5_eq2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, d = pack_b_b_r_e_e X f g R c d 5.

Axiom pack_b_b_r_e_e_inj : forall X X', forall f f':set -> set -> set, forall g g':set -> set -> set, forall R R':set -> set -> prop, forall c c':set, forall d d':set, pack_b_b_r_e_e X f g R c d = pack_b_b_r_e_e X' f' g' R' c' d' -> X = X' /\ (forall x y :e X, f x y = f' x y) /\ (forall x y :e X, g x y = g' x y) /\ (forall x y :e X, R x y = R' x y) /\ c = c' /\ d = d'.

Axiom pack_b_b_r_e_e_ext : forall X, forall f f':set -> set -> set, forall g g':set -> set -> set, forall R R':set -> set -> prop, forall c, forall d,
 (forall x y :e X, f x y = f' x y) ->
 (forall x y :e X, g x y = g' x y) ->
 (forall x y :e X, R x y <-> R' x y) ->
 pack_b_b_r_e_e X f g R c d = pack_b_b_r_e_e X f' g' R' c d.

Definition struct_b_b_r_e_e : set -> prop := fun S => forall q:set -> prop, (forall X:set, forall f:set -> set -> set, (forall x y :e X, f x y :e X) -> forall g:set -> set -> set, (forall x y :e X, g x y :e X) -> forall R:set -> set -> prop, forall c:set, c :e X -> forall d:set, d :e X -> q (pack_b_b_r_e_e X f g R c d)) -> q S.

Axiom pack_struct_b_b_r_e_e_I: forall X, forall f:set -> set -> set, (forall x y :e X, f x y :e X) -> forall g:set -> set -> set, (forall x y :e X, g x y :e X) -> forall R:set -> set -> prop, forall c:set, c :e X -> forall d:set, d :e X -> struct_b_b_r_e_e (pack_b_b_r_e_e X f g R c d).

Axiom pack_struct_b_b_r_e_e_E1: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, struct_b_b_r_e_e (pack_b_b_r_e_e X f g R c d) -> forall x y :e X, f x y :e X.

Axiom pack_struct_b_b_r_e_e_E2: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, struct_b_b_r_e_e (pack_b_b_r_e_e X f g R c d) -> forall x y :e X, g x y :e X.

Axiom pack_struct_b_b_r_e_e_E4: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, struct_b_b_r_e_e (pack_b_b_r_e_e X f g R c d) -> c :e X.

Axiom pack_struct_b_b_r_e_e_E5: forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set, struct_b_b_r_e_e (pack_b_b_r_e_e X f g R c d) -> d :e X.

Axiom struct_b_b_r_e_e_eta: forall S, struct_b_b_r_e_e S -> S = pack_b_b_r_e_e (S 0) (decode_b (S 1)) (decode_b (S 2)) (decode_r (S 3)) (S 4) (S 5).

(* Parameter unpack_b_b_r_e_e_i "9841164c05115cc07043487bccc48e1ce748fa3f4dfc7d109f8286f9a5bce324" "89fb5e380d96cc4a16ceba7825bfbc02dfd37f2e63dd703009885c4bf3794d07" *)
Parameter unpack_b_b_r_e_e_i : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> set) -> set.

Axiom unpack_b_b_r_e_e_i_eq : forall Phi:set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> set,
  forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set,
  ( forall f':set -> set -> set, (forall x y :e X, f x y = f' x y) ->  forall g':set -> set -> set, (forall x y :e X, g x y = g' x y) ->  forall R':set -> set -> prop, (forall x y :e X, R x y <-> R' x y) -> Phi X f' g' R' c d = Phi X f g R c d)
  ->
  unpack_b_b_r_e_e_i (pack_b_b_r_e_e X f g R c d) Phi = Phi X f g R c d.

(* Parameter unpack_b_b_r_e_e_o "3db063fdbe07c7344b83deebc95b091786045a06e01e2ce6e2eae1d885f574af" "b3a2fc60275daf51e6cbe3161abaeed96cb2fc4e1d5fe26b5e3e58d0eb93c477" *)
Parameter unpack_b_b_r_e_e_o : set -> (set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> prop) -> prop.

Axiom unpack_b_b_r_e_e_o_eq : forall Phi:set -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> prop) -> set -> set -> prop,
  forall X, forall f:set -> set -> set, forall g:set -> set -> set, forall R:set -> set -> prop, forall c:set, forall d:set,
  (forall f':set -> set -> set, (forall x y :e X, f x y = f' x y) ->  forall g':set -> set -> set, (forall x y :e X, g x y = g' x y) ->  forall R':set -> set -> prop, (forall x y :e X, R x y <-> R' x y) -> Phi X f' g' R' c d = Phi X f g R c d)
  ->
  unpack_b_b_r_e_e_o (pack_b_b_r_e_e X f g R c d) Phi = Phi X f g R c d.

(* Parameter OrderedFieldStruct "606d31b0ebadd0ba5b2644b171b831936b36964cb4ca899eebfac62651e1c270" "98aa98f64160bebd5622706908b639f9fdfe4056f2678ed69e5b099b8dd7b888" *)
Parameter OrderedFieldStruct : set -> prop.

Section explicit_OrderedField_RepIndep2.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.
Variable leq:set -> set -> prop.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable plus' mult':set -> set -> set.
Variable leq':set -> set -> prop.
Infix :+: 355 right := plus'.
Infix :*: 355 right := mult'.

Hypothesis Hpp': forall a b :e R, a + b = a :+: b.
Hypothesis Hmm': forall a b :e R, a * b = a :*: b.
Hypothesis Hll': forall a b :e R, leq a b <-> leq' a b.

Axiom explicit_OrderedField_repindep : explicit_OrderedField R zero one plus mult leq <-> explicit_OrderedField R zero one plus' mult' leq'.

End explicit_OrderedField_RepIndep2.

Axiom OrderedFieldStruct_unpack_eq : forall R, forall plus mult:set -> set -> set, forall leq:set -> set -> prop, forall zero one, unpack_b_b_r_e_e_o (pack_b_b_r_e_e R plus mult leq zero one) (fun R plus mult leq zero one => explicit_OrderedField R zero one plus mult leq) = explicit_OrderedField R zero one plus mult leq.

Definition RealsStruct : set -> prop
 := fun R => struct_b_b_r_e_e R
          /\ unpack_b_b_r_e_e_o R (fun R plus mult leq zero one => explicit_Reals R zero one plus mult leq).

Section explicit_Reals_RepIndep2.

Variable R : set.

Variable zero one : set.
Variable plus mult : set -> set -> set.
Variable leq:set -> set -> prop.

Infix + 360 right := plus.
Infix * 355 right := mult.

Variable plus' mult':set -> set -> set.
Variable leq':set -> set -> prop.
Infix :+: 355 right := plus'.
Infix :*: 355 right := mult'.

Hypothesis Hpp': forall a b :e R, a + b = a :+: b.
Hypothesis Hmm': forall a b :e R, a * b = a :*: b.
Hypothesis Hll': forall a b :e R, leq a b <-> leq' a b.

Axiom explicit_Reals_repindep : explicit_Reals R zero one plus mult leq <-> explicit_Reals R zero one plus' mult' leq'.

End explicit_Reals_RepIndep2.

Axiom RealsStruct_unpack_eq : forall R, forall plus mult:set -> set -> set, forall leq:set -> set -> prop, forall zero one, unpack_b_b_r_e_e_o (pack_b_b_r_e_e R plus mult leq zero one) (fun R plus mult leq zero one => explicit_Reals R zero one plus mult leq) = explicit_Reals R zero one plus mult leq.

Definition RealsStruct_carrier : set -> set := fun Rs => Rs 0.

Definition RealsStruct_plus : set -> set -> set -> set := fun Rs => decode_b (Rs 1).

Definition RealsStruct_mult : set -> set -> set -> set := fun Rs => decode_b (Rs 2).

Definition RealsStruct_leq : set -> set -> set -> prop := fun Rs => decode_r (Rs 3).

Definition RealsStruct_zero : set -> set := fun Rs => Rs 4.

Definition RealsStruct_one : set -> set := fun Rs => Rs 5.

(* Parameter Field_of_RealsStruct "ea953ac10b642a9da289025dff57d46f78a32954a0c94609646f8f83d8119728" "e1df2c6881a945043093f666186fa5159d4b31d68340b37bd2be81d10ba28060" *)
Parameter Field_of_RealsStruct : set -> set.

Axiom Field_of_RealsStruct_0: forall Rs, Field_of_RealsStruct Rs 0 = RealsStruct_carrier Rs.

Axiom Field_of_RealsStruct_1: forall Rs, forall x y :e RealsStruct_carrier Rs, Field_of_RealsStruct Rs 1 x y = RealsStruct_plus Rs x y.

Axiom Field_of_RealsStruct_2: forall Rs, forall x y :e RealsStruct_carrier Rs, Field_of_RealsStruct Rs 2 x y = RealsStruct_mult Rs x y.

Axiom Field_of_RealsStruct_3: forall Rs, Field_of_RealsStruct Rs 3 = RealsStruct_zero Rs.

Axiom Field_of_RealsStruct_4: forall Rs, Field_of_RealsStruct Rs 4 = RealsStruct_one Rs.

Section RealsStruct.

Variable Rs:set.
Hypothesis HRs: RealsStruct Rs.

Let R : set := RealsStruct_carrier Rs.
Let zero : set := RealsStruct_zero Rs.
Let one : set := RealsStruct_one Rs.
Infix + 360 right := RealsStruct_plus Rs.
Infix * 355 right := RealsStruct_mult Rs.
(* Unicode <= "2264" *)
Infix <= 490 := RealsStruct_leq Rs.

Axiom RealsStruct_eta: Rs = pack_b_b_r_e_e R (RealsStruct_plus Rs) (RealsStruct_mult Rs) (RealsStruct_leq Rs) zero one.
Axiom RealsStruct_explicit_Reals: explicit_Reals R zero one (RealsStruct_plus Rs) (RealsStruct_mult Rs) (RealsStruct_leq Rs).

Axiom Field_of_RealsStruct_is_CRing_with_id: CRing_with_id (Field_of_RealsStruct Rs).

Definition RealsStruct_lt : set -> set -> prop := fun x y => x <= y /\ x <> y.
Infix < 490 := RealsStruct_lt.

Axiom explicit_Field_of_RealsStruct: explicit_Field R zero one (RealsStruct_plus Rs) (RealsStruct_mult Rs).
Axiom explicit_OrderedField_of_RealsStruct: explicit_OrderedField R zero one (RealsStruct_plus Rs) (RealsStruct_mult Rs) (RealsStruct_leq Rs).
Axiom RealsStruct_OrderedField: OrderedFieldStruct Rs.

Axiom Field_of_RealsStruct_1f: (fun x y:set => Field_of_RealsStruct Rs 1 x y) = RealsStruct_plus Rs.
Axiom Field_of_RealsStruct_2f: (fun x y:set => Field_of_RealsStruct Rs 2 x y) = RealsStruct_mult Rs.
Axiom explicit_Field_of_RealsStruct_2: explicit_Field R (Field_of_RealsStruct Rs 3) (Field_of_RealsStruct Rs 4) (decode_b (Field_of_RealsStruct Rs 1)) (decode_b (Field_of_RealsStruct Rs 2)).
Axiom Field_Field_of_RealsStruct: Field (Field_of_RealsStruct Rs).

Axiom RealsStruct_zero_In: zero :e R.
Axiom RealsStruct_one_In: one :e R.
Axiom RealsStruct_plus_clos: forall x y :e R, x + y :e R.
Axiom RealsStruct_mult_clos: forall x y :e R, x * y :e R.
Axiom RealsStruct_plus_assoc: forall x y z :e R, x + (y + z) = (x + y) + z.
Axiom RealsStruct_plus_com: forall x y :e R, x + y = y + x.
Axiom RealsStruct_zero_L: forall x :e R, zero + x = x.
Axiom RealsStruct_mult_assoc: forall x y z :e R, x * (y * z) = (x * y) * z.
Axiom RealsStruct_mult_com: forall x y :e R, x * y = y * x.
Axiom RealsStruct_one_neq_zero: one <> zero.
Axiom RealsStruct_one_L: forall x :e R, one * x = x.
Axiom RealsStruct_distr_L: forall x y z :e R, x * (y + z) = x * y + x * z.
Axiom RealsStruct_leq_refl: forall x :e R, x <= x.
Axiom RealsStruct_leq_tra: forall x y z :e R, x <= y -> y <= z -> x <= z.
Axiom RealsStruct_leq_antisym: forall x y :e R, x <= y -> y <= x -> x = y.
Axiom RealsStruct_leq_linear: forall x y :e R, x <= y \/ y <= x.
Axiom RealsStruct_leq_plus: forall x y z :e R, x <= y -> x + z <= y + z.
Axiom RealsStruct_lt_leq: forall x y :e R, x < y -> x <= y.
Axiom RealsStruct_lt_irref: forall x :e R, ~(x < x).
Axiom RealsStruct_lt_leq_asym: forall x y :e R, x < y -> ~(y <= x).
Axiom RealsStruct_leq_lt_asym: forall x y :e R, x <= y -> ~(y < x).
Axiom RealsStruct_lt_asym: forall x y :e R, x < y -> ~(y < x).
Axiom RealsStruct_lt_leq_tra: forall x y z :e R, x < y -> y <= z -> x < z.
Axiom RealsStruct_leq_lt_tra: forall x y z :e R, x <= y -> y < z -> x < z.
Axiom RealsStruct_lt_tra: forall x y z :e R, x < y -> y < z -> x < z.
Axiom RealsStruct_lt_trich_impred: forall x y :e R, forall p:prop, (x < y -> p) -> (x = y -> p) -> (y < x -> p) -> p.
Axiom RealsStruct_lt_trich: forall x y :e R, x < y \/ x = y \/ y < x.
Axiom RealsStruct_leq_lt_linear: forall x y :e R, x <= y \/ y < x.

Prefix - 358 := Field_minus (Field_of_RealsStruct Rs).

Axiom RealsStruct_minus_eq: forall x :e R, - x = explicit_Field_minus R (Field_of_RealsStruct Rs 3) (Field_of_RealsStruct Rs 4) (decode_b (Field_of_RealsStruct Rs 1)) (decode_b (Field_of_RealsStruct Rs 2)) x.
Axiom RealsStruct_minus_clos : forall x :e R, - x :e R.
Axiom RealsStruct_minus_R: forall x :e R, x + - x = zero.
Axiom RealsStruct_minus_L: forall x :e R, - x + x = zero.
Axiom RealsStruct_plus_cancelL : forall x y z :e R, x + y = x + z -> y = z.
Axiom RealsStruct_minus_eq2: forall x :e R, - x = explicit_Field_minus R zero one (RealsStruct_plus Rs) (RealsStruct_mult Rs) x.
Axiom RealsStruct_plus_cancelR : forall x y z :e R, x + z = y + z -> x = y.
Axiom RealsStruct_minus_invol : forall x :e R, - - x = x.
Axiom RealsStruct_minus_one_In : - one :e R.
Axiom RealsStruct_zero_multR : forall x :e R, x * zero = zero.
Axiom RealsStruct_zero_multL : forall x :e R, zero * x = zero.
Axiom RealsStruct_minus_mult : forall x :e R, - x = (- one) * x.
Axiom RealsStruct_minus_one_square : (- one) * (- one) = one.
Axiom RealsStruct_minus_square : forall x :e R, (- x) * (- x) = x * x.
Axiom RealsStruct_minus_zero : - zero = zero.
Axiom RealsStruct_dist_R : forall x y z :e R, (x + y) * z = x * z + y * z.
Axiom RealsStruct_minus_plus_dist : forall x y :e R, - (x + y) = - x + - y.
Axiom RealsStruct_minus_mult_L : forall x y :e R, (- x) * y = - (x * y).
Axiom RealsStruct_minus_mult_R : forall x y :e R, x * (- y) = - (x * y).
Axiom RealsStruct_mult_zero_inv : forall x y :e R, x * y = zero -> x = zero \/ y = zero.
Axiom RealsStruct_square_zero_inv : forall x :e R, x * x = zero -> x = zero.
Axiom RealsStruct_minus_leq : forall x y :e R, x <= y -> - y <= - x.
Axiom RealsStruct_square_nonneg : forall x :e R, zero <= x * x.
Axiom RealsStruct_sum_squares_nonneg : forall x y :e R, zero <= x * x + y * y.
Axiom RealsStruct_sum_nonneg_zero_inv : forall x y :e R, zero <= x -> zero <= y -> x + y = zero -> x = zero /\ y = zero.
Axiom RealsStruct_sum_squares_zero_inv : forall x y :e R, x * x + y * y = zero -> x = zero /\ y = zero.
Axiom RealsStruct_leq_zero_one: zero <= one.

(* Parameter RealsStruct_N "c60ee42484639ad65bdabfeeb7220f90861c281a74898207df2b83c9dbe71ee3" "5e5ba235d9b0b40c084850811a514efd2e7f76df45b4ca1be43ba33c41356d3b" *)
Parameter RealsStruct_N: set.

Let N := RealsStruct_N.

Axiom RealsStruct_Arch: forall x y :e R, zero < x -> zero <= y -> exists n :e N, y <= n * x.
Axiom RealsStruct_Compl: forall a b :e R :^: N,
        (forall n :e N, a n <= b n /\ a n <= a (n + one) /\ b (n + one) <= b n)
     -> exists x :e R, forall n :e N, a n <= x /\ x <= b n.

Axiom RealsStruct_natOfOrderedField: explicit_Nats N zero (fun m => m + one).

Definition RealsStruct_Npos := {n :e N|n <> zero}.
Let Npos := RealsStruct_Npos.

Axiom RealsStruct_PosNats_natOfOrderedField: explicit_Nats Npos one (fun m => m + one).

(* Parameter RealsStruct_Z "c934b0a37a42002a6104de6f7753559507f7fc42144bbd2d672c37e984e3a441" "736c836746de74397a8fa69b6bbd46fc21a6b3f1430f6e4ae87857bf6f077989" *)
Parameter RealsStruct_Z:set.
Let Z := RealsStruct_Z.

(* Parameter RealsStruct_Q "9134ada3d735402039f76383770584fc0f331d09a6678c60511c4437b58c8986" "255c25547da742d6085a5308f204f5b90d6ba5991863cf0b3e4036ef74ee35a2" *)
Parameter RealsStruct_Q:set.
Let Q := RealsStruct_Q.

Axiom RealsStruct_Npos_props: forall p:prop,
      (Npos c= R
    -> explicit_Nats Npos one (fun m => m + one)
    -> one :e Npos
    -> (forall m :e Npos, m + one <> one)
    -> (forall m :e Npos, forall q:set -> prop, q one -> (forall n :e Npos, q (n + one)) -> q m)
    -> (forall n m :e Npos, explicit_Nats_one_plus Npos one (fun m => m + one) n m = n + m)
    -> (forall n m :e Npos, explicit_Nats_one_mult Npos one (fun m => m + one) n m = n * m)
    -> (forall n m :e Npos, n + m :e Npos)
    -> (forall n m :e Npos, n * m :e Npos)
    -> p)
   -> p.

Axiom RealsStruct_Npos_R: Npos c= R.

Axiom RealsStruct_one_Npos: one :e Npos.

Axiom RealsStruct_Z_props: forall p:prop,
      ((forall n :e Npos, - n :e Z)
    -> zero :e Z
    -> Npos c= Z
    -> Z c= R
    -> (forall n :e Z, forall q:prop, (- n :e Npos -> q) -> (n = zero -> q) -> (n :e Npos -> q) -> q)
    -> one :e Z
    -> - one :e Z
    -> (forall m :e Z, - m :e Z)
    -> (forall n m :e Z, n + m :e Z)
    -> (forall n m :e Z, n * m :e Z)
    -> p)
   -> p.

Axiom RealsStruct_neg_Z: forall n :e Npos, - n :e Z.
Axiom RealsStruct_zero_Z: zero :e Z.
Axiom RealsStruct_Npos_Z: Npos c= Z.
Axiom RealsStruct_Z_R: Z c= R.

Axiom RealsStruct_Q_props: forall p:prop,
      (Q c= R
    -> (forall x :e Q, forall q:prop,
           (x :e R -> forall n :e Z, forall m :e Npos, m * x = n -> q)
         -> q)
    -> (forall x :e R, forall n :e Z, forall m :e Npos, m * x = n -> x :e Q)
    -> p)
   -> p.

Axiom RealsStruct_Q_R: Q c= R.
Axiom RealsStruct_Z_Q: Z c= Q.

Infix :/: 353 := Field_div (Field_of_RealsStruct Rs).
Axiom RealsStruct_div_clos: forall x :e R, forall y :e R :\: {zero}, x :/: y :e R.
Axiom RealsStruct_mult_div: forall x :e R, forall y :e R :\: {zero}, x = y * (x :/: y).
Axiom RealsStruct_div_undef1: forall x y, x /:e R -> x :/: y = 0.
Axiom RealsStruct_div_undef2: forall x y, y /:e R -> x :/: y = 0.
Axiom RealsStruct_div_undef3: forall x, x :/: zero = 0.

Infix ^ 342 right := CRing_with_id_omega_exp (Field_of_RealsStruct Rs).

Axiom RealsStruct_omega_exp_0 : forall x, x ^ 0 = one.
Axiom RealsStruct_omega_exp_S : forall x, forall n :e omega, x ^ (ordsucc n) = x * x ^ n.
Axiom RealsStruct_omega_exp_1 : forall x :e R, x ^ 1 = x.
Axiom RealsStruct_omega_exp_clos : forall x :e R, forall n :e omega, x ^ n :e R.

(* Parameter RealsStruct_abs "ff30733afb56aca63687fac2b750743306c2142ffbfafc95a8ecc167da4fd5fa" "fcf3391eeb9d6b26a8b41a73f701da5e27e74021d7a3ec1b11a360045a5f13ca" *)
Parameter RealsStruct_abs : set -> set.

Axiom RealsStruct_abs_clos : forall x :e R, RealsStruct_abs x :e R.
Axiom RealsStruct_abs_nonneg_case : forall x :e R, zero <= x -> RealsStruct_abs x = x.
Axiom RealsStruct_abs_neg_case : forall x :e R, x < zero -> RealsStruct_abs x = - x.
Axiom RealsStruct_abs_nonneg : forall x :e R, zero <= RealsStruct_abs x.
Axiom RealsStruct_abs_zero_inv : forall x :e R, RealsStruct_abs x = zero -> x = zero.
Axiom RealsStruct_dist_zero_eq : forall x y :e R, RealsStruct_abs (x + - y) = zero -> x = y.

Definition RealsStruct_divides : set -> set -> prop := fun m n => exists k :e Npos, m * k = n.

Definition RealsStruct_Primes := {n :e N | one < n /\ forall m :e Npos, RealsStruct_divides m n -> m = one \/ m = n}.

Definition RealsStruct_coprime : set -> set -> prop := fun m n => forall k :e Npos, RealsStruct_divides k m -> RealsStruct_divides k n -> k = one.

Let Qs := pack_b_b_e_e Q (RealsStruct_plus Rs) (RealsStruct_mult Rs) zero one.
Axiom Field_RealsStruct_Q: Field Qs.

Definition RealsStruct_omega_embedding : set -> set := nat_primrec zero (fun _ r => r + one).

Let emb : set -> set := RealsStruct_omega_embedding.

Axiom RealsStruct_omega_embedding_N : forall n :e omega, emb n :e N.

End RealsStruct.

Section SurrealReals.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix < 490 := SNoLt.
(* Unicode <= "2264" *)
Infix <= 490 := SNoLe.

Infix ^ 342 right := exp_SNo_nat.

Axiom add_SNo_minus_Le1 : forall x y z, SNo x -> SNo y -> SNo z -> x + - y <= z -> x <= z + y.
Axiom add_SNo_minus_Le1b : forall x y z, SNo x -> SNo y -> SNo z -> x <= z + y -> x + - y <= z.
Axiom add_SNo_minus_Le2 : forall x y z, SNo x -> SNo y -> SNo z -> z <= x + - y -> z + y <= x.
Axiom add_SNo_minus_Le2b : forall x y z, SNo x -> SNo y -> SNo z -> z + y <= x -> z <= x + - y.
Axiom exp_SNo_nat_0 : forall x, SNo x -> x ^ 0 = 1.
Axiom exp_SNo_nat_S : forall x, SNo x -> forall n, nat_p n -> x ^ (ordsucc n) = x * x ^ n.
Axiom SNo_exp_SNo_nat : forall x, SNo x -> forall n, nat_p n -> SNo (x ^ n).
Axiom nat_exp_SNo_nat : forall x, nat_p x -> forall n, nat_p n -> nat_p (x ^ n).
Axiom mul_SNo_eps_power_2: forall n, nat_p n -> eps_ n * 2 ^ n = 1.
Axiom mul_SNo_eps_power_2': forall n, nat_p n -> 2 ^ n * eps_ n = 1.
Axiom exp_SNo_nat_mul_add : forall x, SNo x -> forall m, nat_p m -> forall n, nat_p n -> x ^ m * x ^ n = x ^ (m + n).
Axiom exp_SNo_nat_mul_add' : forall x, SNo x -> forall m n :e omega, x ^ m * x ^ n = x ^ (m + n).
Axiom exp_SNo_nat_pos : forall x, SNo x -> 0 < x -> forall n, nat_p n -> 0 < x ^ n.
Axiom mul_SNo_nonzero_cancel: forall x y z, SNo x -> x <> 0 -> SNo y -> SNo z -> x * y = x * z -> y = z.
Axiom mul_SNo_eps_eps_add_SNo: forall m n :e omega, eps_ m * eps_ n = eps_ (m + n).
Axiom omega_SNoS_omega : omega c= SNoS_ omega.
Axiom add_SNo_1_ordsucc : forall n :e omega, n + 1 = ordsucc n.
Axiom SNo_prereal_incr_lower_pos: forall x, SNo x -> 0 < x
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> forall k :e omega,
     forall p:prop,
         (forall q :e SNoS_ omega, 0 < q -> q < x -> x < q + eps_ k -> p)
      -> p.
Axiom pos_mul_SNo_Lt' : forall x y z, SNo x -> SNo y -> SNo z -> 0 < z -> x < y -> x * z < y * z.
Axiom pos_mul_SNo_Lt2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 < x -> 0 < y -> x < z -> y < w -> x * y < z * w.
Axiom nonneg_mul_SNo_Le' : forall x y z, SNo x -> SNo y -> SNo z -> 0 <= z -> x <= y -> x * z <= y * z.
Axiom nonneg_mul_SNo_Le2 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> 0 <= x -> 0 <= y -> x <= z -> y <= w -> x * y <= z * w.
Axiom exp_SNo_1_bd: forall x, SNo x -> 1 <= x -> forall n, nat_p n -> 1 <= x ^ n.
Axiom exp_SNo_2_bd: forall n, nat_p n -> n < 2 ^ n.
Axiom eps_bd_1 : forall n :e omega, eps_ n <= 1.
Axiom SNo_foil: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + y) * (z + w) = x * z + x * w + y * z + y * w.
Axiom mul_SNo_minus_minus: forall x y, SNo x -> SNo y -> (- x) * (- y) = x * y.
Axiom add_SNo_Lt4 : forall x y z w u v, SNo x -> SNo y -> SNo z -> SNo w -> SNo u -> SNo v -> x < w -> y < u -> z < v -> x + y + z < w + u + v.
Axiom mul_SNo_Lt1_pos_Lt : forall x y, SNo x -> SNo y -> x < 1 -> 0 < y -> x * y < y.
Axiom mul_SNo_Le1_nonneg_Le : forall x y, SNo x -> SNo y -> x <= 1 -> 0 <= y -> x * y <= y.
Axiom SNo_mul_SNo_3 : forall x y z, SNo x -> SNo y -> SNo z -> SNo (x * y * z).
Axiom SNo_mul_SNo_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> SNo (x * y * z * w).
Axiom mul_SNo_assoc_4 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> x * y * z * w = (x * y * z) * w.
Axiom mul_SNo_com_3_0_1 : forall x y z, SNo x -> SNo y -> SNo z
  -> x * y * z = y * x * z.
Axiom mul_SNo_com_4_inner_flat : forall x y z w, SNo y -> SNo z -> SNo w
  -> x * y * z * w = x * z * y * w.
Axiom mul_SNo_com_3b_1_2 : forall x y z, SNo x -> SNo y -> SNo z
  -> (x * y) * z = (x * z) * y.
Axiom mul_SNo_com_4_inner_mid : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w
  -> (x * y) * (z * w) = (x * z) * (y * w).
Axiom mul_SNo_rotate_3_1 : forall x y z, SNo x -> SNo y -> SNo z ->
  x * y * z = z * x * y.
Axiom mul_SNo_rotate_4_1 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w ->
  x * y * z * w = w * x * y * z.
Axiom mul_SNo_rotate_5_1 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x * y * z * w * v = v * x * y * z * w.
Axiom mul_SNo_rotate_5_2 : forall x y z w v, SNo x -> SNo y -> SNo z -> SNo w -> SNo v ->
  x * y * z * w * v = w * v * x * y * z.
Axiom SNoCutP_SNoCut_lim : forall lambda, ordinal lambda
 -> (forall alpha :e lambda, ordsucc alpha :e lambda)
 -> forall L R c= SNoS_ lambda, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc lambda.
Axiom SNoCutP_SNoCut_omega : forall L R c= SNoS_ omega, SNoCutP L R
 -> SNoLev (SNoCut L R) :e ordsucc omega.
Axiom add_SNo_eps_Lt : forall x, SNo x -> forall n :e omega, x < x + eps_ n.
Axiom add_SNo_eps_Lt' : forall x y, SNo x -> SNo y -> forall n :e omega, x < y -> x < y + eps_ n.
Axiom SNoLt_minus_pos : forall x y, SNo x -> SNo y -> x < y -> 0 < y + - x.
Axiom SNoS_ordsucc_omega_bdd_above : forall x :e SNoS_ (ordsucc omega), x < omega -> exists N :e omega, x < N.
Axiom SNoS_ordsucc_omega_bdd_below : forall x :e SNoS_ (ordsucc omega), - omega < x -> exists N :e omega, - N < x.
Axiom SNoS_omega_drat_intvl : forall x :e SNoS_ omega,
  forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
Axiom SNoS_ordsucc_omega_bdd_drat_intvl : forall x :e SNoS_ (ordsucc omega),
    - omega < x -> x < omega
 -> forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k.
Axiom SNo_prereal_incr_lower_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists f :e SNoS_ omega :^: omega,
       forall n :e omega, f n < x /\ x < f n + eps_ n
                       /\ forall i :e n, f i < f n.

(* Parameter real "0d955384652ad934e09a854e236e549b47a140bb15c1ad93b6b63a51593ab579" "e26ffa4403d3e38948f53ead677d97077fe74954ba92c8bb181aba8433e99682" *)
Parameter real:set.

Axiom real_I : forall x :e SNoS_ (ordsucc omega),
    x <> omega
 -> x <> - omega
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> x :e real.
Axiom real_E : forall x :e real,
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
Axiom real_SNo : forall x :e real, SNo x.
Axiom real_SNoS_omega_prop : forall x :e real, forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x.
Axiom SNoS_omega_real : SNoS_ omega c= real.
Axiom SNoLev_In_real_SNoS_omega : forall x :e real, forall w, SNo w -> SNoLev w :e SNoLev x -> w :e SNoS_ omega.
Axiom minus_SNo_prereal_1 : forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - - x) < eps_ k) -> q = - x).
Axiom minus_SNo_prereal_2 : forall x, SNo x ->
    (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < - x /\ - x < q + eps_ k).
Axiom SNo_prereal_decr_upper_approx: forall x, SNo x ->
    (forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - x) < eps_ k) -> q = x)
 -> (forall k :e omega, exists q :e SNoS_ omega, q < x /\ x < q + eps_ k)
 -> exists g :e SNoS_ omega :^: omega,
       forall n :e omega, g n + - eps_ n < x /\ x < g n
                       /\ forall i :e n, g n < g i.
Axiom SNo_real_incr_lower_approx: forall x :e real,
 forall p:prop,
     (forall f :e SNoS_ omega :^: omega,
          (forall n :e omega, f n < x)
       -> (forall n :e omega, x < f n + eps_ n)
       -> (forall n :e omega, forall i :e n, f i < f n)
       -> p)
  -> p.
Axiom SNo_real_decr_upper_approx: forall x :e real,
 forall p:prop,
     (forall g :e SNoS_ omega :^: omega,
          (forall n :e omega, g n + - eps_ n < x)
       -> (forall n :e omega, x < g n)
       -> (forall n :e omega, forall i :e n, g n < g i)
       -> p)
  -> p.

Axiom SNo_approx_real_lem:
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
Axiom SNo_approx_real: forall x, SNo x ->
 forall f g :e SNoS_ omega :^: omega,
     (forall n :e omega, f n < x)
  -> (forall n :e omega, x < f n + eps_ n)
  -> (forall n :e omega, forall i :e n, f i < f n)
  -> (forall n :e omega, x < g n)
  -> (forall n :e omega, forall i :e n, g n < g i)
  -> x = SNoCut {f n|n :e omega} {g n|n :e omega}
  -> x :e real.
Axiom SNo_approx_real_rep : forall x :e real,
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
Axiom real_minus_SNo : forall x :e real, - x :e real.
Axiom SNoS_ordsucc_omega_bdd_eps_pos : forall x :e SNoS_ (ordsucc omega), 0 < x -> x < omega -> exists N :e omega, eps_ N * x < 1.
Axiom SNoS_ordsucc_omega_bdd_eps : forall x :e SNoS_ (ordsucc omega), - omega < x -> x < omega -> exists N :e omega, abs_SNo (eps_ N * x) < 1.
Axiom real_Archimedean: forall x y :e real, 0 < x -> 0 <= y -> exists n :e omega, y <= n * x.
Axiom mul_SNo_ordinal_ordinal : forall alpha, ordinal alpha -> forall beta, ordinal beta -> ordinal (alpha * beta).
Axiom mul_SNo_ordinal_In : forall alpha, ordinal alpha -> forall beta, ordinal beta ->
  forall gamma :e alpha, forall delta :e beta,
    gamma * beta + alpha * delta :e alpha * beta + gamma * delta.
Axiom SNo_extend0_SNoCutP: forall x, SNo x -> SNoCutP (SNoL x) {x}.
Axiom SNo_extend0_SNoCut: forall x, SNo x -> SNo_extend0 x = SNoCut (SNoL x) {x}.
Axiom SNo_extend1_SNoCutP: forall x, SNo x -> SNoCutP {x} (SNoR x).
Axiom SNo_extend1_SNoCut: forall x, SNo x -> SNo_extend1 x = SNoCut {x} (SNoR x).

Axiom real_complete1: forall a b :e real :^: omega,
    (forall n :e omega, a n <= b n /\ a n <= a (ordsucc n) /\ b (ordsucc n) <= b n)
 -> exists x :e real, forall n :e omega, a n <= x /\ x <= b n.

Axiom real_complete2: forall a b :e real :^: omega,
    (forall n :e omega, a n <= b n /\ a n <= a (n + 1) /\ b (n + 1) <= b n)
 -> exists x :e real, forall n :e omega, a n <= x /\ x <= b n.

Axiom real_add_SNo : forall x y :e real, x + y :e real.

Axiom add_SNo_minus_eq1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y = w + z -> x + y + - z = w.

Axiom add_SNo_minus_Le1b3 : forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> x + y <= w + z -> x + y + - z <= w.

Axiom SNo_extend0_LtLe_1: forall x y, SNo x -> SNo y -> SNoLev y :e ordsucc (SNoLev x) -> SNo_extend0 x < y -> x <= y.
Axiom SNo_extend1_LtLe_1: forall x y, SNo x -> SNo y -> SNoLev y :e ordsucc (SNoLev x) -> y < SNo_extend1 x -> y <= x.

Definition SNo_max_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> y <= x.
Definition SNo_min_of : set -> set -> prop := fun X x => x :e X /\ SNo x /\ forall y :e X, SNo y -> x <= y.

Axiom SNo_max_of_uniq : forall X x x', SNo_max_of X x -> SNo_max_of X x' -> x = x'.

Axiom SNo_min_of_uniq : forall X x x', SNo_min_of X x -> SNo_min_of X x' -> x = x'.

Axiom eps_1_split_eq': forall x, SNo x -> x = eps_ 1 * (x + x).

Axiom Repl_inv_eq : forall P:set -> prop, forall f g:set -> set,
    (forall x, P x -> g (f x) = x)
 -> forall X, (forall x :e X, P x) -> {g y|y :e {f x|x :e X}} = X.

Axiom Repl_invol_eq : forall P:set -> prop, forall f:set -> set,
    (forall x, P x -> f (f x) = x)
 -> forall X, (forall x :e X, P x) -> {f y|y :e {f x|x :e X}} = X.

Axiom minus_SNo_max_min : forall X y, (forall x :e X, SNo x) -> SNo_max_of X y -> SNo_min_of {- x|x :e X} (- y).

Axiom minus_SNo_max_min' : forall X y, (forall x :e X, SNo x) -> SNo_max_of {- x|x :e X} y -> SNo_min_of X (- y).

Axiom minus_SNo_min_max : forall X y, (forall x :e X, SNo x) -> SNo_min_of X y -> SNo_max_of {- x|x :e X} (- y).

Axiom minus_SNo_min_max' : forall X y, (forall x :e X, SNo x) -> SNo_min_of {- x|x :e X} y -> SNo_max_of X (- y).

Axiom double_SNo_max_1 : forall x y, SNo x -> SNo_max_of (SNoL x) y -> forall z, SNo z -> x < z -> y + z < x + x -> exists w :e SNoR z, y + w = x + x.

Axiom SNoL_minus_SNoR: forall x, SNo x -> SNoL (- x) = {- w|w :e SNoR x}.

Axiom double_SNo_min_1 : forall x y, SNo x -> SNo_min_of (SNoR x) y -> forall z, SNo z -> z < x -> x + x < y + z -> exists w :e SNoL z, y + w = x + x.

Axiom nonneg_diadic_rational_p_SNoS_omega: forall k :e omega, forall n, nat_p n -> eps_ k * n :e SNoS_ omega.

Axiom omega_nonneg : forall m :e omega, 0 <= m.

Axiom double_eps_1 : forall x y z, SNo x -> SNo y -> SNo z -> x + x = y + z -> x = eps_ 1 * (y + z).

Axiom real_0 : 0 :e real.
Axiom real_1 : 1 :e real.

Definition diadic_rational_p : set -> prop := fun x => exists k :e omega, exists m :e int, x = eps_ k * m.

Axiom diadic_rational_p_SNoS_omega: forall x, diadic_rational_p x -> x :e SNoS_ omega.
Axiom diadic_rational_p_SNo: forall x, diadic_rational_p x -> SNo x.
Axiom int_diadic_rational_p : forall m :e int, diadic_rational_p m.
Axiom omega_diadic_rational_p : forall m :e omega, diadic_rational_p m.
Axiom eps_diadic_rational_p : forall k :e omega, diadic_rational_p (eps_ k).
Axiom minus_SNo_diadic_rational_p : forall x, diadic_rational_p x -> diadic_rational_p (- x).
Axiom mul_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x * y).
Axiom add_SNo_diadic_rational_p : forall x y, diadic_rational_p x -> diadic_rational_p y -> diadic_rational_p (x + y).

Axiom finite_max_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_max_of X x.
Axiom finite_min_exists : forall X, (forall x :e X, SNo x) -> finite X -> X <> 0 -> exists x, SNo_min_of X x.
Axiom SNoS_0 : SNoS_ 0 = 0.
Axiom add_SNo_omega_In_cases: forall m, forall n :e omega, forall k, nat_p k -> m :e n + k -> m :e n \/ m + - n :e k.
Axiom SNo_extend0_restr_eq : forall x, SNo x -> x = SNo_extend0 x :/\: SNoElts_ (SNoLev x).
Axiom SNo_extend1_restr_eq : forall x, SNo x -> x = SNo_extend1 x :/\: SNoElts_ (SNoLev x).
Axiom SNoS_omega_Lev_equip : forall n, nat_p n -> equip {x :e SNoS_ omega|SNoLev x = n} (2 ^ n).
Axiom equip_0_Empty : forall X, equip X 0 -> X = 0.
Axiom finite_ind : forall p:set -> prop,
    p Empty
 -> (forall X y, finite X -> y /:e X -> p X -> p (X :\/: {y}))
 -> forall X, finite X -> p X.
Axiom finite_Empty: finite 0.
Axiom nat_inv_impred : forall p:set->prop, p 0 -> (forall n, nat_p n -> p (ordsucc n)) -> forall n, nat_p n -> p n.
Axiom nat_inv_impred' : forall n, nat_p n -> forall p:set->prop, p 0 -> (forall n, nat_p n -> p (ordsucc n)) -> p n.
Axiom adjoin_finite: forall X y, finite X -> finite (X :\/: {y}).
Axiom binunion_finite: forall X, finite X -> forall Y, finite Y -> finite (X :\/: Y).
Axiom famunion_nat_finite : forall X:set -> set, forall n, nat_p n -> (forall i :e n, finite (X i)) -> finite (\/_ i :e n, X i).
Axiom SNoS_finite : forall n :e omega, finite (SNoS_ n).
Axiom Subq_finite : forall X, finite X -> forall Y, Y c= X -> finite Y.
Axiom SNoS_omega_SNoL_finite : forall x :e SNoS_ omega, finite (SNoL x).
Axiom SNoS_omega_SNoR_finite : forall x :e SNoS_ omega, finite (SNoR x).
Axiom SNoS_omega_SNoL_max_exists : forall x :e SNoS_ omega, SNoL x = 0 \/ exists y, SNo_max_of (SNoL x) y.
Axiom SNoS_omega_SNoR_min_exists : forall x :e SNoS_ omega, SNoR x = 0 \/ exists y, SNo_min_of (SNoR x) y.

Axiom SNoS_omega_diadic_rational_p_lem: forall n, nat_p n -> forall x, SNo x -> SNoLev x = n -> diadic_rational_p x.
Axiom SNoS_omega_diadic_rational_p: forall x :e SNoS_ omega, diadic_rational_p x.
Axiom mul_SNo_SNoS_omega : forall x y :e SNoS_ omega, x * y :e SNoS_ omega.
Axiom SNo_foil_mm: forall x y z w, SNo x -> SNo y -> SNo z -> SNo w -> (x + - y) * (z + - w) = x * z + - x * w + - y * z + y * w.
Axiom add_SNo_3a_2b: forall x y z w u, SNo x -> SNo y -> SNo z -> SNo w -> SNo u
 -> (x + y + z) + (w + u) = (u + y + z) + (w + x).
Axiom real_mul_SNo_pos : forall x y :e real, 0 < x -> 0 < y -> x * y :e real.
Axiom real_mul_SNo : forall x y :e real, x * y :e real.
Axiom abs_SNo_intvl_bd : forall x y z, SNo x -> SNo y -> SNo z
 -> x <= y -> y < x + z
 -> abs_SNo (y + - x) < z.
Axiom real_0_SNoS_omega_prop: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo q < eps_ k) -> q = 0.
Axiom real_1_SNoS_omega_prop: forall q :e SNoS_ omega, (forall k :e omega, abs_SNo (q + - 1) < eps_ k) -> q = 1.

Axiom nonneg_mul_SNo_Lt_conv : forall x y z, SNo x -> 0 <= x -> SNo y -> SNo z -> x * y < x * z -> y < z.
Axiom nonneg_mul_SNo_Lt'_conv : forall x y z, SNo x -> SNo y -> SNo z -> 0 <= z -> x * z < y * z -> x < y.
Axiom pos_small_real_recip_ex: forall x :e real, 0 < x -> x < 1 -> exists y :e real, x * y = 1.
Axiom pos_real_recip_ex: forall x :e real, 0 < x -> exists y :e real, x * y = 1.
Axiom nonzero_real_recip_ex: forall x :e real, x <> 0 -> exists y :e real, x * y = 1.
Axiom explicit_Field_SurrealReals: explicit_Field real 0 1 add_SNo mul_SNo.
Axiom explicit_OrderedField_SurrealReals: explicit_OrderedField real 0 1 add_SNo mul_SNo SNoLe.
Axiom explicit_Nats_E' : forall N base, forall S:set -> set, explicit_Nats N base S ->
 forall q:prop,
     (base :e N
   -> (forall m :e N, S m :e N)
   -> (forall m :e N, S m <> base)
   -> (forall m n :e N, S m = S n -> m = n)
   -> (forall p:set -> prop, p base -> (forall m, p m -> p (S m)) -> (forall m :e N, p m))
   -> q)
  -> q.
Axiom natOfOrderedField_SurrealReals_omega : {n :e real | natOfOrderedField_p real 0 1 add_SNo mul_SNo SNoLe n} = omega.
Axiom explicit_Reals_SurrealReals: explicit_Reals real 0 1 add_SNo mul_SNo SNoLe.

Definition SurrealRealsStruct : set := pack_b_b_r_e_e real add_SNo mul_SNo SNoLe 0 1.
Axiom RealsStruct_SurrealReals : RealsStruct SurrealRealsStruct.
  
End SurrealReals.

