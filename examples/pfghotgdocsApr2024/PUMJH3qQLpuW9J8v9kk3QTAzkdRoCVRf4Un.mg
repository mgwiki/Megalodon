Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.
Infix = 502 := eq.
Section Ex.
Variable A:SType.
Definition ex : (A->prop)->prop := fun Q:A->prop => forall P:prop, (forall x:A, Q x -> P) -> P.
End Ex.
(* Unicode exists "2203" *)
Binder+ exists , := ex.
(* Parameter Eps_i "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter Eps_i : (set->prop)->set.
Parameter In:set->set->prop.
Parameter Empty : set.
(* Unicode Union "22C3" *)
Parameter Union : set->set.
(* Unicode Power "1D4AB" *)
Parameter Power : set->set.
Parameter Repl : set -> (set -> set) -> set.
Notation Repl Repl.
Parameter UnivOf : set->set.
Definition ChurchNum2 : (set -> set) -> set -> set :=
 (fun x00 : set -> set => fun x01 : set => x00 (x00 x01)).
Definition ChurchNum4 : (set -> set) -> set -> set :=
 (fun x00 : set -> set => fun x01 : set => x00 (x00 (x00 (x00 x01)))).
Definition ChurchNum_plus : ((set -> set) -> set -> set) -> ((set -> set) -> set -> set) -> (set -> set) -> set -> set :=
 (fun x00 x01 : (set -> set) -> set -> set => fun x02 : set -> set => fun x03 : set => x00 x02 (x01 x02 x03)).
Definition ChurchNum_mult : ((set -> set) -> set -> set) -> ((set -> set) -> set -> set) -> (set -> set) -> set -> set :=
 (fun x00 x01 : (set -> set) -> set -> set => fun x02 : set -> set => x00 (x01 x02)).
Theorem ChurchNum_plus_2_2_4 : ChurchNum_plus ChurchNum2 ChurchNum2 = ChurchNum4.
let x00: ((set -> set) -> set -> set) -> ((set -> set) -> set -> set) -> prop.
assume H0: x00 (ChurchNum_plus ChurchNum2 ChurchNum2) ChurchNum4.
exact H0.
Qed.
Theorem ChurchNum_mult_2_2_4 : ChurchNum_mult ChurchNum2 ChurchNum2 = ChurchNum4.
let x00: ((set -> set) -> set -> set) -> ((set -> set) -> set -> set) -> prop.
assume H0: x00 (ChurchNum_mult ChurchNum2 ChurchNum2) ChurchNum4.
exact H0.
Qed.
