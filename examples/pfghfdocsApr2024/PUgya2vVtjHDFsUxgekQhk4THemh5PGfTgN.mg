(* Parameter False "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" *)
(* Parameter True "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" *)
(* Parameter not "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" *)
(* Parameter and "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" *)
(* Parameter Subq "8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87" *)
(* Parameter TransSet "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3" *)
(* Parameter ordsucc "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
(* Parameter binintersect "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036" *)
(* Parameter binrep "d744bcd791713cf88021ce34168c3e2d109a8a6c45637d74541d94007e3139ca" *)
(* Parameter setprod "ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7" *)
(* Parameter exactly2 "c7df083c7cf25a97335c4c9d8dc333551ed272dcab0c9c75bdb57679962006f5" *)
(* Parameter SNo "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" *)

(* Unicode False "22A5" *)
Parameter False : prop.
Parameter True : prop.

Parameter not : prop -> prop.

(* Unicode ~ "00ac" *)
Prefix ~ 700 := not.

Parameter and : prop -> prop -> prop.

(* Unicode /\ "2227" *)
Infix /\ 780 left := and.

Section Eq.

Variable A:SType.

Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.

End Eq.

Infix = 502 := eq.

Parameter In:set->set->prop.
Parameter Subq : set->set->prop.
Parameter Empty : set.
(* Unicode Power "1D4AB" *)
Parameter Power : set->set.
Parameter TransSet : set->prop.
Parameter ordsucc : set -> set.
Parameter binintersect : set -> set -> set.
Parameter binrep : set -> set -> set.
Parameter setprod : set -> set -> set.
Parameter exactly2 : set -> prop.
Parameter SNo : set -> prop.

Notation Nat Empty ordsucc.

Axiom False_def: False = (forall P:prop, P).
Axiom True_def: True = (forall P : prop, P -> P).
Axiom not_def: not = (fun A:prop => A -> False).
Axiom and_def: and = (fun A B:prop => forall P:prop, (A -> B -> P) -> P).

Theorem FalseE: False -> forall p:prop, p.
exact False_def (fun u v:prop => u).
Qed.

Theorem TrueI : True.
rewrite True_def.
let P. assume H: P. exact H.
Qed.

Theorem notE: forall A:prop, ~A -> A -> False.
let A.
rewrite not_def.
assume H1: A -> False.
assume H2: A.
exact H1 H2.
Qed.

Theorem andE: forall A B:prop, A /\ B -> forall p:prop, (A -> B -> p) -> p.
let A B.
exact and_def (fun u v => u A B).
Qed.

Theorem and_notTrue: forall A:prop, A /\ ~True -> forall p:prop, p.
let A.
assume H1: A /\ ~True.
apply FalseE.
prove False.
apply andE A (~True) H1.
assume H2: A.
assume H3: ~True.
apply notE True.
- prove ~True. exact H3.
- prove True. exact TrueI.
Qed.

Theorem prop_fec13 : (forall P : set -> prop, forall f : set -> set, and ((P (f (binintersect (f (Power 0)) (f (binrep (Power (Power (Power 0))) 0)))) -> TransSet (f 0) -> forall x, In x 0 -> forall q : prop, (forall y, and (Subq y x) (exactly2 (ordsucc (f y))) -> q) -> q) -> forall x : prop, (forall y, and (forall q : prop, (forall z, and (Subq z y) (y = f y -> forall r : prop, (forall w, and (Subq w y) (not (P (setprod z (binrep (Power (binrep (Power (Power 0)) 0)) (Power (Power 0)))))) -> r) -> r) -> q) -> q) (not (SNo y)) -> x) -> x) (not (P (f (f (f (binrep (binrep (Power (binrep (Power (Power 0)) 0)) (Power 0)) 0))))))) -> forall p : prop, p.
assume H1: forall P : set -> prop, forall f : set -> set, and ((P (f (binintersect (f (Power 0)) (f (binrep (Power (Power (Power 0))) 0)))) -> TransSet (f 0) -> forall x, In x 0 -> forall q : prop, (forall y, and (Subq y x) (exactly2 (ordsucc (f y))) -> q) -> q) -> forall x : prop, (forall y, and (forall q : prop, (forall z, and (Subq z y) (y = f y -> forall r : prop, (forall w, and (Subq w y) (not (P (setprod z (binrep (Power (binrep (Power (Power 0)) 0)) (Power (Power 0)))))) -> r) -> r) -> q) -> q) (not (SNo y)) -> x) -> x) (not (P (f (f (f (binrep (binrep (Power (binrep (Power (Power 0)) 0)) (Power 0)) 0)))))).
exact and_notTrue ?A:o? (H1 (fun x => True) (fun x => x)).
Qed.


