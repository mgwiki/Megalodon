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
(* Parameter lam_id "00e0580a8881b84ea1ef7f67247f59ec145448a850064052345ecd4ecb637071" "6271864c471837aeded4c4e7dc37b9735f9fc4828a34ac9c7979945da815a3c7" *)
Parameter lam_id : set -> set.
(* Parameter ap "58c1782da006f2fb2849c53d5d8425049fad551eb4f8025055d260f0c9e1fe40" "c7aaa670ef9b6f678b8cf10b13b2571e4dc1e6fde061d1f641a5fa6c30c09d46" *)
Parameter ap : set -> set -> set.
Definition struct_id : set -> set :=
 (fun x0 : set => lam_id (ap x0 Empty)).
(* Parameter lam_comp "fe600fee4888e854b519619f9d314569f986253bb2b5db02807f68aa12bf7c5a" "29d9e2fc6403a0149dee771fde6a2efc8a94f848a3566f3ccd60af2065396289" *)
Parameter lam_comp : set -> set -> set -> set.
Definition struct_comp : set -> set -> set -> set -> set -> set :=
 (fun x0 x1 x2 : set => lam_comp (ap x0 Empty)).
Definition and : prop -> prop -> prop :=
 (fun x0 x1 : prop => forall x2 : prop, (x0 -> x1 -> x2) -> x2).
(* Parameter struct_r "40bec47cb8d77d09a8db5316dde8cb26bd415be5a40f26f59f167843da58eb63" "2c39441e10ec56a1684beb291702e235e2a9e44db516e916d62ce426108cfd26" *)
Parameter struct_r : set -> prop.
(* Parameter unpack_r_o "8d2ef9c9e522891d1fe605a62dffeab8aefb6325650e4eab14135e7eee8002c5" "e3e6af0984cda0a02912e4f3e09614b67fc0167c625954f0ead4110f52ede086" *)
Parameter unpack_r_o : set -> (set -> (set -> set -> prop) -> prop) -> prop.
(* Parameter not "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" "f30435b6080d786f27e1adaca219d7927ddce994708aacaf4856c5b701fe9fa1" *)
Parameter not : prop -> prop.
(* Parameter or "cfe97741543f37f0262568fe55abbab5772999079ff734a49f37ed123e4363d7" "9577468199161470abc0815b6a25e03706a4e61d5e628c203bf1f793606b1153" *)
Parameter or : prop -> prop -> prop.
Definition missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb : set -> prop :=
 (fun x0 : set => and (struct_r x0) (unpack_r_o x0 (fun x1 : set => fun x2 : set -> set -> prop => and (and (and (forall x3, x3 :e x1 -> not (x2 x3 x3)) (forall x3, x3 :e x1 -> (forall x4, x4 :e x1 -> or (x2 x3 x4) (x2 x4 x3)))) (forall x3, x3 :e x1 -> (forall x4, x4 :e x1 -> (forall x5, x5 :e x1 -> x2 x3 x4 -> x2 x4 x5 -> x2 x3 x5)))) (forall x3 : set -> prop, (forall x4, x4 :e x1 -> (forall x5, x5 :e x1 -> x2 x5 x4 -> x3 x5) -> x3 x4) -> (forall x4, x4 :e x1 -> x3 x4))))).
(* Parameter MetaCat "9b2dee6442140d530f300f187f315d389cfa416a087e15c1677d3bf02f85f063" "fd9743c836fc84a35eca7120bf513d8be118e8eff433fbcc8ca5369662cda164" *)
Parameter MetaCat : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.
(* Parameter BinRelnHom "352304ebb6c77dbc4e2a952e767857a98538e43de1c35fb4bcd6c99fca02ae7e" "acf0f04c6a55a143e3ed8404c0fa6b09b323d938c83532f081b47091e31c4eb3" *)
Parameter BinRelnHom : set -> set -> set -> prop.
Axiom missingprop_cbfb7b0a858ebd43603219779360cb4b49636cdfaa135c2740cff97583aabee7 : (forall x0 : set -> prop, (forall x1, x0 x1 -> struct_r x1) -> MetaCat x0 BinRelnHom (fun x1 : set => lam_id (ap x1 Empty)) (fun x1 x2 x3 : set => lam_comp (ap x1 Empty))).
Theorem missingprop_376093b7cbd1c20ec232fe20c998ec27304d2132036a33ad980f47d30b9a1236 : MetaCat missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp.
admit.
Qed.
(* Parameter MetaFunctor "3f1821f85d08e8012e699b09efeb0773942fcc2adacfea48bc8f23b31eb6673d" "f35b679c6bab1e6cf0fdcf922094790594854b8da194ab1c6b10991183d51c1a" *)
Parameter MetaFunctor : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> prop.
(* Parameter True "5867641425602c707eaecd5be95229f6fd709c9b58d50af108dfe27cb49ac069" "f81b3934a73154a8595135f10d1564b0719278d3976cc83da7fda60151d770da" *)
Parameter True : prop.
(* Parameter HomSet "161e94d84ccfb9b03f97f8dd48da7489affeb461b5931fee82f582ce63054de8" "de8fdf3d1593629dc04bc929fc51714e9acdbd4d4b7e5ac4f6e31798f074955a" *)
Parameter HomSet : set -> set -> set -> prop.
Axiom missingprop_8faf0f6f6af4c6811dc2a9fddf49a6de91e15ce9a8949ea3d00ad9c7e8345ae0 : (forall x0 : set -> prop, (forall x1, x0 x1 -> struct_r x1) -> MetaFunctor x0 BinRelnHom (fun x1 : set => lam_id (ap x1 Empty)) (fun x1 x2 x3 : set => lam_comp (ap x1 Empty)) (fun x1 : set => True) HomSet lam_id (fun x1 x2 x3 : set => lam_comp x1) (fun x1 : set => ap x1 Empty) (fun x1 x2 x3 : set => x3)).
Theorem missingprop_7164083ef71b3c42dcf6555b02377dfbbfb24e5e618944fa19f342f51d96d9ab : MetaFunctor missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp (fun x0 : set => True) HomSet lam_id (fun x0 x1 x2 : set => lam_comp x0) (fun x0 : set => ap x0 Empty) (fun x0 x1 x2 : set => x2).
admit.
Qed.
(* Parameter MetaCat_initial_p "469fedb3c0890bbe6f1968a679e8940fd80553c3929ed17a6b7130c588aa8e13" "a7ed72144cefda0957baa33b821766b4dfe468731094cdca6edcf0a9613fc7c8" *)
Parameter MetaCat_initial_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> set -> (set -> set) -> prop.
Theorem missingprop_6b40b84e42c95a266c6d65f4a814833b54e6c056f016aac874ccb1bd8842f984 : (forall x0 : prop, (forall x1, (forall x2 : prop, (forall x3 : set -> set, MetaCat_initial_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_terminal_p "e188a394359450645dfdce85a0b30e951da4f945117188395c3ab12bb228e33d" "fdae77d1a5079ae1a09aaeb23343f4bd6081907e9fe81a573b7244a35af0d909" *)
Parameter MetaCat_terminal_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> set -> (set -> set) -> prop.
Theorem missingprop_7e884229d4b6222265af2823c7acd697bad4881db9c8f35b228689cbf2e70fce : (forall x0 : prop, (forall x1, (forall x2 : prop, (forall x3 : set -> set, MetaCat_terminal_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_coproduct_constr_p "8f2fbe77e432c151f468828696bc88cfbde14365208ec6d40c57d57f47201c42" "9283cafc90df46790d36399d9c4a27aec79cadc0fd1a9b2f654b0465ca1d1659" *)
Parameter MetaCat_coproduct_constr_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_70ffe18298cb5c5a81b8c9bb44dce739a1e2cd1b3deb740398358e0a837e1091 : (forall x0 : prop, (forall x1 : set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set, (forall x6 : prop, (forall x7 : set -> set -> set -> set -> set -> set, MetaCat_coproduct_constr_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_product_constr_p "174a19a576b89f1308ff59f6dd7de2117117f98e28682f4bbd15fbb1975ae6f0" "8627a945e60408d81c3094008f07f651db6b692c34fa1ffa9753e39b66d38044" *)
Parameter MetaCat_product_constr_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_088808a15920a0f23f54230a23f067deff84d0470d4d96799fc2a69c67edecfb : (forall x0 : prop, (forall x1 : set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set, (forall x6 : prop, (forall x7 : set -> set -> set -> set -> set -> set, MetaCat_product_constr_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_coequalizer_buggy_struct_p "b635bdf22563c31dfe7ebe5ef5db6659c84c46d4448fbd36c50ffb05669d7a72" "90c303e6b6cca396b2d8ddeff62cda2c0954a43d45ad666e7b8ea21c1d8fa73a" *)
Parameter MetaCat_coequalizer_buggy_struct_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_b8244e4864625b2ae56f8b4017450c227fb87a1ff51a3fe36a2856295c08582b : (forall x0 : prop, (forall x1 : set -> set -> set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set -> set -> set -> set -> set, MetaCat_coequalizer_buggy_struct_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_equalizer_buggy_struct_p "e67bc4d0a725995ed2ec3098468550e926fee1bce25684449381d154f0ee8440" "0cc8a8cbd38e8ba1ee07ccfd5533e5863ca3585fcd0f824fb201b116adadea99" *)
Parameter MetaCat_equalizer_buggy_struct_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_61b76646ff4741fd96ad63f630ead272c2661111c9de452904877b834ecb5add : (forall x0 : prop, (forall x1 : set -> set -> set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set -> set -> set -> set -> set, MetaCat_equalizer_buggy_struct_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_pushout_buggy_constr_p "a40e2bf43bfaedcb235fbe9cf70798d807af253c9fbdaca746d406eede069a95" "e4ed700f88c7356f166d3aaad35c3007fde4361ccaa00c752a1b65ddb538052e" *)
Parameter MetaCat_pushout_buggy_constr_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_0796df234b2516fc12a39de32b7564e9f4056b0abc2d05404c4501b9eef768dd : (forall x0 : prop, (forall x1 : set -> set -> set -> set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set -> set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set -> set -> set -> set, (forall x6 : prop, (forall x7 : set -> set -> set -> set -> set -> set -> set -> set -> set, MetaCat_pushout_buggy_constr_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_pullback_buggy_struct_p "d911abc76bc46c5334e7c773fdba8df1c33d0156234b37084c9e6526851c30b9" "944de6e799f202bde0a6c9ed7626d6a7b2530cb8ff1b9c9a979548e02c1a4b81" *)
Parameter MetaCat_pullback_buggy_struct_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_a9e37a242c1f25509bfe70c17d8cb129f59bdd140b2da27b026f04424753c0ee : (forall x0 : prop, (forall x1 : set -> set -> set -> set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set -> set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set -> set -> set -> set, (forall x6 : prop, (forall x7 : set -> set -> set -> set -> set -> set -> set -> set -> set, MetaCat_pullback_buggy_struct_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_exp_constr_p "9f6ce4075c92a59821f6cfbfc8f86cc2c3b8a00b532253e0c92520fca04ab97b" "b618dfe4a17334147263c506b2138f51d0d2c7b154efad7f4f29ccbe49e432f3" *)
Parameter MetaCat_exp_constr_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set -> set) -> (set -> set -> set) -> (set -> set -> set -> set -> set) -> prop.
Theorem missingprop_44f22525131436d3e36e1bb15724fb0a6a8b56cdca8dc007f45a0fcd1b12700c : (forall x0 : prop, (forall x1 : set -> set -> set, (forall x2 : prop, (forall x3 : set -> set -> set, (forall x4 : prop, (forall x5 : set -> set -> set, (forall x6 : prop, (forall x7 : set -> set -> set -> set -> set -> set, (forall x8 : prop, (forall x9 : set -> set -> set, (forall x10 : prop, (forall x11 : set -> set -> set, (forall x12 : prop, (forall x13 : set -> set -> set -> set -> set, MetaCat_exp_constr_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 x9 x11 x13 -> x12) -> x12) -> x10) -> x10) -> x8) -> x8) -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_subobject_classifier_buggy_p "b430b61db2900bb60168d91af644ce9e8886b53b9fc1d812f4f50f301fbaf2ad" "b25dda61a9e31c2b6c19744c16c5af120939ef77a89fe6bcea622a7b6ba6ce78" *)
Parameter MetaCat_subobject_classifier_buggy_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> set -> (set -> set) -> set -> set -> (set -> set -> set -> set) -> (set -> set -> set -> set -> set -> set -> set) -> prop.
Theorem missingprop_d07eb0b617a7dd28706d4f01b657032d408a69a66508c7398ad74d69f986c582 : (forall x0 : prop, (forall x1, (forall x2 : prop, (forall x3 : set -> set, (forall x4 : prop, (forall x5, (forall x6 : prop, (forall x7, (forall x8 : prop, (forall x9 : set -> set -> set -> set, (forall x10 : prop, (forall x11 : set -> set -> set -> set -> set -> set -> set, MetaCat_subobject_classifier_buggy_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 x9 x11 -> x10) -> x10) -> x8) -> x8) -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaCat_nno_p "5b8f1bcabb96c729d6120f7525c02179f8baf007a2bc04b7f8efb36fff497cf6" "037a74a15834f7850061137e15b24c1545b3cec27cea76d5a22e5f66ad2e9ff1" *)
Parameter MetaCat_nno_p : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> set -> (set -> set) -> set -> set -> set -> (set -> set -> set -> set) -> prop.
Theorem missingprop_75815b34747fc9944c3cb3261049a0fbdffd63b4cd7a5add8a26916944fba578 : (forall x0 : prop, (forall x1, (forall x2 : prop, (forall x3 : set -> set, (forall x4 : prop, (forall x5, (forall x6 : prop, (forall x7, (forall x8 : prop, (forall x9, (forall x10 : prop, (forall x11 : set -> set -> set -> set, MetaCat_nno_p missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 x5 x7 x9 x11 -> x10) -> x10) -> x8) -> x8) -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
(* Parameter MetaAdjunction_strict "be3dc11d683b255bfbd9127adb3c6087d074a17cb0e31c91d602b5ae49893e97" "c8ed7d3ad63a4a29ebc88ac0ccb02bfd5f4c0141eebc8a7a349ed7115a3a3eb9" *)
Parameter MetaAdjunction_strict : (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> prop) -> (set -> set -> set -> prop) -> (set -> set) -> (set -> set -> set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set -> set -> set) -> (set -> set) -> (set -> set) -> prop.
Theorem missingprop_7d926b4185179ce2d53078b70d9806b67334f6b432014cd3b31a1fb00e56df84 : (forall x0 : prop, (forall x1 : set -> set, (forall x2 : prop, (forall x3 : set -> set -> set -> set, (forall x4 : prop, (forall x5 : set -> set, (forall x6 : prop, (forall x7 : set -> set, MetaAdjunction_strict (fun x8 : set => True) HomSet lam_id (fun x8 x9 x10 : set => lam_comp x8) missingname_db327cd543066326bb45dc67bfcc985dc294b4385263e93b2af4265149541ffb BinRelnHom struct_id struct_comp x1 x3 (fun x8 : set => ap x8 Empty) (fun x8 x9 x10 : set => x10) x5 x7 -> x6) -> x6) -> x4) -> x4) -> x2) -> x2) -> x0) -> x0).
Admitted.
