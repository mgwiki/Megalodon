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
Definition permargs_i_2_3_0_1_4_5 : (set -> set -> set -> set -> set -> set -> set) -> set -> set -> set -> set -> set -> set -> set :=
 (fun x0 : set -> set -> set -> set -> set -> set -> set => fun x1 x2 x3 x4 : set => x0 x3 x4 x1 x2).
Definition Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 : (set -> set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> set -> set -> set -> set -> set -> set -> set :=
 (fun x0 x1 : set -> set -> set -> set -> set -> set -> set => fun x2 x3 x4 x5 x6 x7 : set => x0 (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x7 x6) (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x6 x7) (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x6 x7) (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x7 x6) (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x6 x7) (permargs_i_2_3_0_1_4_5 x1 x2 x3 x4 x5 x6 x7)).
(* Parameter Church6_to_u6 "f4d68b947c391fb202fb8df5218ea17bcff67d9bbb507885bfc603a34fd5f054" "eb5db5f738ad7aa7a16e5fd9f1201ca51305373920f987771a6afffbc5cda3de" *)
Parameter Church6_to_u6 : (set -> set -> set -> set -> set -> set -> set) -> set.
(* Parameter nth_6_tuple "368935f3a5f424f35961c43f39985442e0a4fe403f656e92d8a87b20af68c0d7" "d45c1fe6a3dff7795ce0a3b891aea8946efc8dceebae3c8b8977b41878b0e841" *)
Parameter nth_6_tuple : set -> set -> set -> set -> set -> set -> set -> set.
Definition u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 : set -> set -> set :=
 (fun x0 x1 : set => Church6_to_u6 (Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 (nth_6_tuple x0) (nth_6_tuple x1))).
Definition Church6_p : (set -> set -> set -> set -> set -> set -> set) -> prop :=
 (fun x0 : set -> set -> set -> set -> set -> set -> set => forall x1 : (set -> set -> set -> set -> set -> set -> set) -> prop, x1 (fun x2 x3 x4 x5 x6 x7 : set => x2) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x3) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x4) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x5) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x6) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x7) -> x1 x0).
Definition Church6_lt4p : (set -> set -> set -> set -> set -> set -> set) -> prop :=
 (fun x0 : set -> set -> set -> set -> set -> set -> set => forall x1 : (set -> set -> set -> set -> set -> set -> set) -> prop, x1 (fun x2 x3 x4 x5 x6 x7 : set => x2) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x3) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x4) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x5) -> x1 x0).
Axiom missingprop_56ce56513a8af1327555b873c1c6ce07e295bb2d93a34f831bbfdb3328f2809b : Church6_lt4p (fun x0 x1 x2 x3 x4 x5 : set => x0).
Axiom missingprop_995579645b8886904e46af0dc0ac8e19ee3cd4af7d78809ff698344ead396f5a : Church6_lt4p (fun x0 x1 x2 x3 x4 x5 : set => x1).
Axiom missingprop_bd8f81a1227d0cc25cea7c364f7541293f70705efd4999ad0dba8cf8857226a9 : Church6_lt4p (fun x0 x1 x2 x3 x4 x5 : set => x2).
Axiom missingprop_9ab406e767d5138f84eceb89ae815ef2f93656cc034576ca18ab84af7a608607 : Church6_lt4p (fun x0 x1 x2 x3 x4 x5 : set => x3).
Theorem missingprop_b54b6027f17f74407872b79435a97bc6b80bb4e8d1a20c185f9858d492a97c96 : (forall x0 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> (forall x1 : (set -> set -> set -> set -> set -> set -> set) -> prop, (Church6_lt4p x0 -> x1 x0) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x6) -> x1 (fun x2 x3 x4 x5 x6 x7 : set => x7) -> x1 x0)).
admit.
Qed.
Theorem missingprop_0e22f978562dc11600b4a135ff8bf16b6b22cc758598e8948a6ed9acd3e10295 : (forall x0 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> (forall x1 : set -> set -> set -> set -> set -> set -> set, Church6_lt4p x1 -> Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1 = permargs_i_2_3_0_1_4_5 x1)).
admit.
Qed.
Axiom missingprop_616c991f45f4fe9d3efb0220d6bfc2b3a9576d02c827cfd1aa156159e180bc78 : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x2).
Axiom missingprop_829cc6bcf19535104e1ef14d3c37a121ee539b24777eaff2cd61aead27db443c : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x3).
Axiom missingprop_331adedb7edd49a25927b93fceb0218da7c5b54994dbd262dd5d161f43c67d7a : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x0).
Axiom missingprop_043e4b78a0654a6683c9234d3bf7766badd8de7fbbde08ad6810ddd8a4f5acef : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x1).
Axiom missingprop_4d8598615c468fd2c2438610c865b021fd567a1a56272aa5746a1a4686cd4fd4 : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x5).
Axiom missingprop_c2058c433a08cbd0a9de8592bbafc20a46c3ba8f1b81c7ac182023aff037fe72 : Church6_p (fun x0 x1 x2 x3 x4 x5 : set => x4).
Theorem missingprop_87b44ea852a703abaf8b1ee45427f8c0cbd069f7b68987ed3e5257508f1d4189 : (forall x0 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> (forall x1 : set -> set -> set -> set -> set -> set -> set, Church6_p x1 -> Church6_p (Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1))).
admit.
Qed.
(* Parameter u6 "fa055287e35da0dbdfea4eda00e6036e98d3ddf3a436e0535f56582c21372e8e" "a7eb4561b2cb31701ce7ec9226931f7d9eae8f8b49a5a52f5987c7cac14cdcb3" *)
Parameter u6 : set.
Axiom missingprop_1df6cb25245842ac80f846f984ad1ab224979cc48aebddb9e27917721a4b0bdb : (forall x0 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> nth_6_tuple (Church6_to_u6 x0) = x0).
Axiom missingprop_90460311f4fb47844a8dd0d64a1306416f6a25ac4d465fc1811061f42791aace : (forall x0, x0 :e u6 -> Church6_p (nth_6_tuple x0)).
Theorem missingprop_62e6bf486fecaeb09a02dcd16f1e532b4aade1130734120dfd4654be87ffd669 : (forall x0, x0 :e u6 -> (forall x1, x1 :e u6 -> Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 (nth_6_tuple x0) (nth_6_tuple x1) = nth_6_tuple (u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1))).
admit.
Qed.
Definition TwoRamseyGraph_4_6_Church6_squared_a : (set -> set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> set -> set -> set :=
 (fun x0 x1 x2 x3 : set -> set -> set -> set -> set -> set -> set => fun x4 x5 : set => x0 (x1 (x2 (x3 x4 x5 x4 x5 x4 x5) (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x5 x4 x4 x4 x5) (x3 x5 x4 x4 x5 x4 x5) (x3 x5 x5 x4 x4 x5 x5) (x3 x4 x5 x4 x4 x5 x4)) (x2 (x3 x5 x4 x5 x4 x5 x4) (x3 x4 x4 x5 x5 x5 x4) (x3 x5 x5 x4 x4 x5 x4) (x3 x4 x5 x5 x4 x5 x4) (x3 x5 x5 x4 x4 x5 x5) (x3 x5 x4 x4 x4 x5 x4)) (x2 (x3 x4 x5 x4 x5 x5 x4) (x3 x5 x5 x4 x4 x4 x5) (x3 x4 x4 x5 x5 x4 x5) (x3 x4 x5 x5 x4 x5 x4) (x3 x4 x4 x5 x5 x5 x5) (x3 x4 x4 x4 x5 x5 x4)) (x2 (x3 x5 x4 x5 x4 x4 x5) (x3 x5 x5 x4 x4 x5 x4) (x3 x4 x4 x5 x5 x5 x4) (x3 x5 x4 x4 x5 x4 x5) (x3 x4 x4 x5 x5 x5 x5) (x3 x4 x4 x5 x4 x5 x4)) (x2 (x3 x4 x5 x5 x4 x4 x5) (x3 x5 x4 x4 x5 x5 x5) (x3 x4 x5 x5 x4 x4 x4) (x3 x4 x5 x5 x4 x4 x4) (x3 x5 x4 x4 x5 x5 x5) (x3 x5 x5 x5 x5 x4 x4)) (x2 (x3 x5 x4 x4 x5 x5 x4) (x3 x4 x5 x5 x4 x5 x5) (x3 x5 x4 x4 x5 x4 x4) (x3 x5 x4 x4 x5 x4 x4) (x3 x4 x5 x5 x4 x5 x5) (x3 x5 x5 x5 x5 x4 x4))) (x1 (x2 (x3 x4 x4 x5 x5 x5 x4) (x3 x4 x5 x4 x5 x5 x4) (x3 x4 x5 x5 x5 x4 x5) (x3 x5 x4 x4 x4 x4 x5) (x3 x5 x4 x4 x5 x5 x4) (x3 x5 x4 x5 x5 x5 x4)) (x2 (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x4 x5 x4 x4 x5) (x3 x5 x4 x5 x5 x5 x4) (x3 x4 x5 x4 x4 x5 x4) (x3 x4 x5 x5 x4 x4 x5) (x3 x4 x5 x5 x5 x5 x4)) (x2 (x3 x5 x5 x4 x4 x4 x5) (x3 x4 x5 x4 x5 x5 x4) (x3 x5 x5 x4 x5 x4 x5) (x3 x4 x4 x5 x4 x5 x4) (x3 x4 x5 x5 x4 x5 x4) (x3 x5 x5 x5 x4 x5 x4)) (x2 (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x4 x5 x4 x4 x5) (x3 x5 x5 x5 x4 x5 x4) (x3 x4 x4 x4 x5 x4 x5) (x3 x5 x4 x4 x5 x4 x5) (x3 x5 x5 x4 x5 x5 x4)) (x2 (x3 x4 x5 x4 x5 x5 x5) (x3 x5 x4 x5 x4 x4 x4) (x3 x5 x4 x5 x4 x5 x5) (x3 x5 x5 x5 x5 x4 x4) (x3 x5 x5 x5 x5 x5 x4) (x3 x5 x4 x5 x4 x4 x4)) (x2 (x3 x5 x4 x5 x4 x5 x5) (x3 x4 x5 x4 x5 x4 x4) (x3 x4 x5 x4 x5 x5 x5) (x3 x5 x5 x5 x5 x4 x4) (x3 x5 x5 x5 x5 x4 x5) (x3 x4 x5 x4 x5 x4 x4))) (x1 (x2 (x3 x5 x5 x4 x4 x4 x5) (x3 x4 x5 x5 x5 x5 x4) (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x4 x4 x5 x5 x4) (x3 x5 x5 x4 x4 x5 x5) (x3 x5 x5 x4 x5 x4 x4)) (x2 (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x4 x5 x5 x4 x5) (x3 x4 x4 x5 x5 x5 x4) (x3 x4 x5 x5 x4 x4 x5) (x3 x5 x5 x4 x4 x5 x5) (x3 x5 x5 x5 x4 x4 x4)) (x2 (x3 x4 x4 x5 x5 x5 x4) (x3 x5 x5 x4 x5 x5 x4) (x3 x5 x5 x4 x4 x4 x5) (x3 x4 x5 x5 x4 x4 x5) (x3 x4 x4 x5 x5 x5 x5) (x3 x4 x5 x5 x5 x4 x4)) (x2 (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x5 x5 x4 x4 x5) (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x4 x4 x5 x5 x4) (x3 x4 x4 x5 x5 x5 x5) (x3 x5 x4 x5 x5 x4 x4)) (x2 (x3 x4 x5 x4 x5 x4 x4) (x3 x4 x5 x4 x5 x5 x5) (x3 x4 x5 x4 x5 x4 x4) (x3 x5 x5 x5 x5 x5 x5) (x3 x5 x4 x5 x4 x5 x5) (x3 x5 x5 x5 x5 x5 x4)) (x2 (x3 x5 x4 x5 x4 x4 x4) (x3 x5 x4 x5 x4 x5 x5) (x3 x5 x4 x5 x4 x4 x4) (x3 x5 x5 x5 x5 x5 x5) (x3 x4 x5 x4 x5 x5 x5) (x3 x5 x5 x5 x5 x5 x4))) (x1 (x2 (x3 x5 x4 x4 x5 x4 x5) (x3 x5 x4 x4 x4 x5 x5) (x3 x5 x4 x4 x5 x5 x5) (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x5 x4 x5 x5 x4) (x3 x4 x4 x5 x5 x4 x4)) (x2 (x3 x4 x5 x5 x4 x5 x4) (x3 x4 x5 x4 x4 x5 x5) (x3 x4 x5 x5 x4 x5 x5) (x3 x4 x4 x5 x5 x5 x4) (x3 x5 x5 x5 x4 x4 x5) (x3 x4 x4 x5 x5 x4 x4)) (x2 (x3 x4 x5 x5 x4 x5 x4) (x3 x4 x4 x5 x4 x5 x5) (x3 x4 x5 x5 x4 x5 x5) (x3 x5 x5 x4 x4 x5 x4) (x3 x4 x5 x5 x5 x5 x4) (x3 x5 x5 x4 x4 x4 x4)) (x2 (x3 x5 x4 x4 x5 x4 x5) (x3 x4 x4 x4 x5 x5 x5) (x3 x5 x4 x4 x5 x5 x5) (x3 x5 x5 x4 x4 x4 x5) (x3 x5 x4 x5 x5 x4 x5) (x3 x5 x5 x4 x4 x4 x4)) (x2 (x3 x4 x5 x5 x4 x4 x4) (x3 x4 x5 x5 x4 x4 x4) (x3 x5 x4 x4 x5 x5 x5) (x3 x4 x5 x5 x4 x4 x5) (x3 x5 x5 x5 x5 x5 x5) (x3 x5 x4 x4 x5 x5 x4)) (x2 (x3 x5 x4 x4 x5 x4 x4) (x3 x5 x4 x4 x5 x4 x4) (x3 x4 x5 x5 x4 x5 x5) (x3 x5 x4 x4 x5 x5 x4) (x3 x5 x5 x5 x5 x5 x5) (x3 x4 x5 x5 x4 x5 x4))) (x1 (x2 (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x4 x4 x5 x5 x5) (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x5 x4 x5 x5 x5) (x3 x4 x5 x4 x4 x5 x4) (x3 x4 x4 x5 x5 x5 x4)) (x2 (x3 x5 x5 x4 x4 x4 x5) (x3 x4 x5 x5 x4 x5 x5) (x3 x5 x5 x4 x4 x4 x5) (x3 x5 x5 x5 x4 x5 x5) (x3 x5 x4 x4 x4 x4 x5) (x3 x4 x4 x5 x5 x5 x4)) (x2 (x3 x4 x4 x5 x5 x4 x5) (x3 x4 x5 x5 x4 x5 x5) (x3 x4 x4 x5 x5 x5 x4) (x3 x4 x5 x5 x5 x5 x5) (x3 x4 x4 x4 x5 x5 x4) (x3 x5 x5 x4 x4 x5 x4)) (x2 (x3 x4 x4 x5 x5 x5 x4) (x3 x5 x4 x4 x5 x5 x5) (x3 x4 x4 x5 x5 x4 x5) (x3 x5 x4 x5 x5 x5 x5) (x3 x4 x4 x5 x4 x4 x5) (x3 x5 x5 x4 x4 x5 x4)) (x2 (x3 x5 x5 x5 x5 x5 x5) (x3 x5 x4 x5 x4 x5 x4) (x3 x5 x5 x5 x5 x5 x5) (x3 x5 x4 x5 x4 x5 x5) (x3 x5 x4 x5 x4 x4 x5) (x3 x4 x4 x4 x4 x4 x4)) (x2 (x3 x5 x5 x5 x5 x5 x5) (x3 x4 x5 x4 x5 x4 x5) (x3 x5 x5 x5 x5 x5 x5) (x3 x4 x5 x4 x5 x5 x5) (x3 x4 x5 x4 x5 x5 x4) (x3 x4 x4 x4 x4 x4 x4))) (x1 (x2 (x3 x4 x5 x4 x4 x5 x5) (x3 x5 x4 x5 x5 x5 x4) (x3 x5 x5 x4 x5 x5 x5) (x3 x4 x4 x5 x5 x5 x4) (x3 x4 x4 x5 x5 x4 x4) (x3 x4 x5 x5 x4 x5 x4)) (x2 (x3 x5 x4 x4 x4 x5 x5) (x3 x4 x5 x5 x5 x4 x5) (x3 x5 x5 x5 x4 x5 x5) (x3 x4 x4 x5 x5 x4 x5) (x3 x4 x4 x5 x5 x4 x4) (x3 x5 x4 x4 x5 x5 x4)) (x2 (x3 x4 x4 x4 x5 x5 x5) (x3 x5 x5 x5 x4 x5 x4) (x3 x4 x5 x5 x5 x5 x5) (x3 x5 x5 x4 x4 x4 x5) (x3 x5 x5 x4 x4 x4 x4) (x3 x5 x4 x4 x5 x5 x4)) (x2 (x3 x4 x4 x5 x4 x5 x5) (x3 x5 x5 x4 x5 x4 x5) (x3 x5 x4 x5 x5 x5 x5) (x3 x5 x5 x4 x4 x5 x4) (x3 x5 x5 x4 x4 x4 x4) (x3 x4 x5 x5 x4 x5 x4)) (x2 (x3 x5 x5 x5 x5 x4 x4) (x3 x5 x5 x5 x5 x4 x4) (x3 x4 x4 x4 x4 x5 x5) (x3 x4 x4 x4 x4 x5 x5) (x3 x5 x5 x5 x5 x4 x4) (x3 x5 x5 x5 x5 x4 x4)) (x2 (x3 x4 x4 x4 x4 x4 x4) (x3 x4 x4 x4 x4 x4 x4) (x3 x4 x4 x4 x4 x4 x4) (x3 x4 x4 x4 x4 x4 x4) (x3 x4 x4 x4 x4 x4 x4) (x3 x4 x4 x4 x4 x4 x4)))).
Axiom missingprop_34d0445a9eb4349bf533e02609a62eed06fba8535ef9778cc7a04d99c2765d4b : (forall x0 x1 x2 x3 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> Church6_lt4p x1 -> Church6_p x2 -> Church6_lt4p x3 -> TwoRamseyGraph_4_6_Church6_squared_a x0 x1 x2 x3 = (fun x5 x6 : set => x5) -> TwoRamseyGraph_4_6_Church6_squared_a x0 (permargs_i_2_3_0_1_4_5 x1) x2 (permargs_i_2_3_0_1_4_5 x3) = (fun x5 x6 : set => x5)).
Definition False : prop :=
 (forall x0 : prop, x0).
Axiom FalseE : False -> (forall x0 : prop, x0).
Axiom missingprop_1019f796b5519c5beeeef55b1daae2de48848a97e75d217687db0a2449fd5208 : (fun x1 x2 : set => x2) = (fun x1 x2 : set => x1) -> (forall x0 : prop, x0).
Theorem missingprop_b57248c4c97ce6f996d417fe9e374a31475e8680b8f7cc9874cbc90fa17ae8ad : (forall x0 x1 x2 x3 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> Church6_p x1 -> Church6_p x2 -> Church6_p x3 -> TwoRamseyGraph_4_6_Church6_squared_a x0 x1 x2 x3 = (fun x5 x6 : set => x5) -> TwoRamseyGraph_4_6_Church6_squared_a x0 (Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1) x2 (Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x2 x3) = (fun x5 x6 : set => x5)).
admit.
Qed.
Definition TwoRamseyGraph_4_6_35_a : set -> set -> set -> set -> prop :=
 (fun x0 x1 x2 x3 : set => forall x4 : (set -> set -> set) -> (set -> set -> set) -> prop, x4 (TwoRamseyGraph_4_6_Church6_squared_a (nth_6_tuple x0) (nth_6_tuple x1) (nth_6_tuple x2) (nth_6_tuple x3)) (fun x5 x6 : set => x5) -> x4 (fun x5 x6 : set => x5) (TwoRamseyGraph_4_6_Church6_squared_a (nth_6_tuple x0) (nth_6_tuple x1) (nth_6_tuple x2) (nth_6_tuple x3))).
Theorem missingprop_2ef1eb8cd624df8207a9f9a4386046f2fcdb45ce1d0aed9ec0def40feaacb489 : (forall x0, x0 :e u6 -> (forall x1, x1 :e u6 -> (forall x2, x2 :e u6 -> (forall x3, x3 :e u6 -> TwoRamseyGraph_4_6_35_a x0 x1 x2 x3 -> TwoRamseyGraph_4_6_35_a x0 (u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1) x2 (u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x2 x3))))).
admit.
Qed.
Theorem missingprop_4ed84cefbe6bafe072d498a530a8147003d97a2a39c53acf05021f089f9b7b32 : (forall x0 : set -> set -> set -> set -> set -> set -> set, Church6_p x0 -> (forall x1 : set -> set -> set -> set -> set -> set -> set, Church6_p x1 -> Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 (Church6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1) = x1)).
admit.
Qed.
Axiom missingprop_72649fc0d609625e17ac53e25cd57a51abe86f395cd11e949eac34127a9e2ea9 : (forall x0, x0 :e u6 -> Church6_to_u6 (nth_6_tuple x0) = x0).
Theorem missingprop_4d91bec054042bcdeefe33bb5a3d3611c13820c9f08314db2f8ef62923a83386 : (forall x0, x0 :e u6 -> (forall x1, x1 :e u6 -> u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 (u6_squared_permutation__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5__2_3_0_1_4_5 x0 x1) = x1)).
admit.
Qed.
