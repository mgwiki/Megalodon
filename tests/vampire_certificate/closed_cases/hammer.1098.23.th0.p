% megalodon_origin ((file "examples/hammer/100thms_12_h.mg") (line "1098") (char "23") (kind "aby"))
% megalodon_source_map (type "c_Eps_5Fi" "Eps_i" "")
thf(c_Eps_5Fi,type,(c_Eps_5Fi : (($i > $o) > $i))). % 174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5
% megalodon_source_map (type "c_In" "In" "")
thf(c_In,type,(c_In : ($i > ($i > $o)))). % 73c9efe869770ab42f7cde0b33fe26bbc3e2bd157dad141c0c27d1e7348d60f5
% megalodon_source_map (type "c_Subq" "Subq" "")
thf(c_Subq,type,(c_Subq : ($i > ($i > $o)))).
% megalodon_source_map (def "c_Subq_def" "Subq" "8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87")
thf(c_Subq_def,definition,(c_Subq = (^ [X0:$i] : (^ [X1:$i] : (! [X2:$i] : (((c_In @ X2) @ X0) => ((c_In @ X2) @ X1))))))). % 8a8e36b858cd07fc5e5f164d8075dc68a88221ed1e4c9f28dac4a6fdb2172e87
% megalodon_source_map (type "c_Empty" "Empty" "")
thf(c_Empty,type,(c_Empty : $i)). % e2a83319facad3a3d8ff453f4ef821d9da495e56a623695546bb7d7ac333f3fe
% megalodon_source_map (type "c_Union" "Union" "")
thf(c_Union,type,(c_Union : ($i > $i))). % 844774016d959cff921a3292054b30b52f175032308aa11e418cb73f5fef3d54
% megalodon_source_map (type "c_Power" "Power" "")
thf(c_Power,type,(c_Power : ($i > $i))). % 2a38dbb37506341b157c11dddf8eb7d8404ce97eb50d5e940b23d5094ae39d70
% megalodon_source_map (type "c_Repl" "Repl" "")
thf(c_Repl,type,(c_Repl : ($i > (($i > $i) > $i)))). % b1b8f6f9d4d6136be8375ed2faddb54df84cdb3018ec6bd2ac07b2c25d3d8af8
% megalodon_source_map (type "c_TransSet" "TransSet" "")
thf(c_TransSet,type,(c_TransSet : ($i > $o))).
% megalodon_source_map (def "c_TransSet_def" "TransSet" "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3")
thf(c_TransSet_def,definition,(c_TransSet = (^ [X0:$i] : (! [X1:$i] : (((c_In @ X1) @ X0) => ((c_Subq @ X1) @ X0)))))). % e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3
% megalodon_source_map (type "c_Union_5Fclosed" "Union_closed" "")
thf(c_Union_5Fclosed,type,(c_Union_5Fclosed : ($i > $o))).
% megalodon_source_map (def "c_Union_5Fclosed_def" "Union_closed" "54850182033d0575e98bc2b12aa8b9baaa7a541e9d5abc7fddeb74fc5d0a19ac")
thf(c_Union_5Fclosed_def,definition,(c_Union_5Fclosed = (^ [X0:$i] : (! [X1:$i] : (((c_In @ X1) @ X0) => ((c_In @ (c_Union @ X1)) @ X0)))))). % 54850182033d0575e98bc2b12aa8b9baaa7a541e9d5abc7fddeb74fc5d0a19ac
% megalodon_source_map (type "c_Power_5Fclosed" "Power_closed" "")
thf(c_Power_5Fclosed,type,(c_Power_5Fclosed : ($i > $o))).
% megalodon_source_map (def "c_Power_5Fclosed_def" "Power_closed" "5a811b601343da9ff9d05d188d672be567de94b980bbbe0e04e628d817f4c7ac")
thf(c_Power_5Fclosed_def,definition,(c_Power_5Fclosed = (^ [X0:$i] : (! [X1:$i] : (((c_In @ X1) @ X0) => ((c_In @ (c_Power @ X1)) @ X0)))))). % 5a811b601343da9ff9d05d188d672be567de94b980bbbe0e04e628d817f4c7ac
% megalodon_source_map (type "c_Repl_5Fclosed" "Repl_closed" "")
thf(c_Repl_5Fclosed,type,(c_Repl_5Fclosed : ($i > $o))).
% megalodon_source_map (def "c_Repl_5Fclosed_def" "Repl_closed" "962d14a92fc8c61bb8319f6fe1508fa2dfbe404fd3a3766ebce0c6db17eeeaa1")
thf(c_Repl_5Fclosed_def,definition,(c_Repl_5Fclosed = (^ [X0:$i] : (! [X1:$i] : (((c_In @ X1) @ X0) => (! [X2:($i > $i)] : ((! [X3:$i] : (((c_In @ X3) @ X1) => ((c_In @ (X2 @ X3)) @ X0))) => ((c_In @ ((c_Repl @ X1) @ (^ [X3:$i] : (X2 @ X3)))) @ X0)))))))). % 962d14a92fc8c61bb8319f6fe1508fa2dfbe404fd3a3766ebce0c6db17eeeaa1
% megalodon_source_map (type "c_ZF_5Fclosed" "ZF_closed" "")
thf(c_ZF_5Fclosed,type,(c_ZF_5Fclosed : ($i > $o))).
% megalodon_source_map (def "c_ZF_5Fclosed_def" "ZF_closed" "43f34d6a2314b56cb12bf5cf84f271f3f02a3e68417b09404cc73152523dbfa0")
thf(c_ZF_5Fclosed_def,definition,(c_ZF_5Fclosed = (^ [X0:$i] : (((c_Union_5Fclosed @ X0) & (c_Power_5Fclosed @ X0)) & (c_Repl_5Fclosed @ X0))))). % 43f34d6a2314b56cb12bf5cf84f271f3f02a3e68417b09404cc73152523dbfa0
% megalodon_source_map (type "c_UnivOf" "UnivOf" "")
thf(c_UnivOf,type,(c_UnivOf : ($i > $i))). % 5a50bfe3a33a99c34615616f54f10cc2df28717bcf140147a4c61b78529a8e94
% megalodon_source_map (type "nIn" "nIn" "")
thf(nIn,type,(nIn : ($i > ($i > $o)))).
% megalodon_source_map (def "nIn_def" "nIn" "2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359")
thf(nIn_def,definition,(nIn = (^ [X0:$i] : (^ [X1:$i] : (~ ((c_In @ X0) @ X1)))))). % 2f8b7f287504f141b0f821928ac62823a377717763a224067702eee02fc1f359
% megalodon_source_map (known "c_UnionI" "UnionI" "681f08928f47fe62e4803e6fa2b70b4ea7a5d093a6d00273519a068fea82736f")
thf(c_UnionI,axiom,(! [X0:$i] : (! [X1:$i] : (! [X2:$i] : (((c_In @ X1) @ X2) => (((c_In @ X2) @ X0) => ((c_In @ X1) @ (c_Union @ X0)))))))). % 681f08928f47fe62e4803e6fa2b70b4ea7a5d093a6d00273519a068fea82736f
% megalodon_source_map (type "exactly1of2" "exactly1of2" "")
thf(exactly1of2,type,(exactly1of2 : ($o > ($o > $o)))).
% megalodon_source_map (def "exactly1of2_def" "exactly1of2" "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b")
thf(exactly1of2_def,definition,(exactly1of2 = (^ [X0:$o] : (^ [X1:$o] : ((X0 & (~ (X1))) | ((~ (X0)) & X1)))))). % 3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b
% megalodon_source_map (type "c_If_5Fi" "If_i" "")
thf(c_If_5Fi,type,(c_If_5Fi : ($o > ($i > ($i > $i))))).
% megalodon_source_map (def "c_If_5Fi_def" "If_i" "8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf")
thf(c_If_5Fi_def,definition,(c_If_5Fi = (^ [X0:$o] : (^ [X1:$i] : (^ [X2:$i] : (c_Eps_5Fi @ (^ [X3:$i] : ((X0 & (X3 = X1)) | ((~ (X0)) & (X3 = X2)))))))))). % 8c8f550868df4fdc93407b979afa60092db4b1bb96087bc3c2f17fadf3f35cbf
% megalodon_source_map (type "c_UPair" "UPair" "")
thf(c_UPair,type,(c_UPair : ($i > ($i > $i)))).
% megalodon_source_map (def "c_UPair_def" "UPair" "80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d")
thf(c_UPair_def,definition,(c_UPair = (^ [X0:$i] : (^ [X1:$i] : ((c_Repl @ (c_Power @ (c_Power @ c_Empty))) @ (^ [X2:$i] : (((c_If_5Fi @ ((c_In @ c_Empty) @ X2)) @ X0) @ X1))))))). % 80aea0a41bb8a47c7340fe8af33487887119c29240a470e920d3f6642b91990d
% megalodon_source_map (type "c_Sing" "Sing" "")
thf(c_Sing,type,(c_Sing : ($i > $i))).
% megalodon_source_map (def "c_Sing_def" "Sing" "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7")
thf(c_Sing_def,definition,(c_Sing = (^ [X0:$i] : ((c_UPair @ X0) @ X0)))). % 158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7
% megalodon_source_map (type "binunion" "binunion" "")
thf(binunion,type,(binunion : ($i > ($i > $i)))).
% megalodon_source_map (def "binunion_def" "binunion" "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e")
thf(binunion_def,definition,(binunion = (^ [X0:$i] : (^ [X1:$i] : (c_Union @ ((c_UPair @ X0) @ X1)))))). % 0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e
% megalodon_source_map (type "c_SetAdjoin" "SetAdjoin" "")
thf(c_SetAdjoin,type,(c_SetAdjoin : ($i > ($i > $i)))).
% megalodon_source_map (def "c_SetAdjoin_def" "SetAdjoin" "153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8")
thf(c_SetAdjoin_def,definition,(c_SetAdjoin = (^ [X0:$i] : (^ [X1:$i] : ((binunion @ X0) @ (c_Sing @ X1)))))). % 153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8
% megalodon_source_map (type "famunion" "famunion" "")
thf(famunion,type,(famunion : ($i > (($i > $i) > $i)))).
% megalodon_source_map (def "famunion_def" "famunion" "d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792")
thf(famunion_def,definition,(famunion = (^ [X0:$i] : (^ [X1:($i > $i)] : (c_Union @ ((c_Repl @ X0) @ (^ [X2:$i] : (X1 @ X2)))))))). % d772b0f5d472e1ef525c5f8bd11cf6a4faed2e76d4eacfa455f4d65cc24ec792
% megalodon_source_map (type "c_Sep" "Sep" "")
thf(c_Sep,type,(c_Sep : ($i > (($i > $o) > $i)))).
% megalodon_source_map (def "c_Sep_def" "Sep" "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079")
thf(c_Sep_def,definition,(c_Sep = (^ [X0:$i] : (^ [X1:($i > $o)] : (((c_If_5Fi @ (? [X2:$i] : (((c_In @ X2) @ X0) & (X1 @ X2)))) @ ((c_Repl @ X0) @ (^ [X2:$i] : ((^ [X3:$i] : (((c_If_5Fi @ (X1 @ X3)) @ X3) @ (c_Eps_5Fi @ (^ [X4:$i] : (((c_In @ X4) @ X0) & (X1 @ X4)))))) @ X2)))) @ c_Empty))))). % f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079
% megalodon_source_map (type "c_ReplSep" "ReplSep" "")
thf(c_ReplSep,type,(c_ReplSep : ($i > (($i > $o) > (($i > $i) > $i))))).
% megalodon_source_map (def "c_ReplSep_def" "ReplSep" "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd")
thf(c_ReplSep_def,definition,(c_ReplSep = (^ [X0:$i] : (^ [X1:($i > $o)] : (^ [X2:($i > $i)] : ((c_Repl @ ((c_Sep @ X0) @ (^ [X3:$i] : (X1 @ X3)))) @ (^ [X3:$i] : (X2 @ X3)))))))). % f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd
% megalodon_source_map (type "binintersect" "binintersect" "")
thf(binintersect,type,(binintersect : ($i > ($i > $i)))).
% megalodon_source_map (def "binintersect_def" "binintersect" "8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036")
thf(binintersect_def,definition,(binintersect = (^ [X0:$i] : (^ [X1:$i] : ((c_Sep @ X0) @ (^ [X2:$i] : ((c_In @ X2) @ X1))))))). % 8cf6b1f490ef8eb37db39c526ab9d7c756e98b0eb12143156198f1956deb5036
% megalodon_source_map (type "setminus" "setminus" "")
thf(setminus,type,(setminus : ($i > ($i > $i)))).
% megalodon_source_map (def "setminus_def" "setminus" "cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060")
thf(setminus_def,definition,(setminus = (^ [X0:$i] : (^ [X1:$i] : ((c_Sep @ X0) @ (^ [X2:$i] : ((nIn @ X2) @ X1))))))). % cc569397a7e47880ecd75c888fb7c5512aee4bcb1e7f6bd2c5f80cccd368c060
% megalodon_source_map (type "ordsucc" "ordsucc" "")
thf(ordsucc,type,(ordsucc : ($i > $i))).
% megalodon_source_map (def "ordsucc_def" "ordsucc" "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec")
thf(ordsucc_def,definition,(ordsucc = (^ [X0:$i] : ((binunion @ X0) @ (c_Sing @ X0))))). % 9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec
% megalodon_source_map (known "ordsuccI2" "ordsuccI2" "0bce99a2a196c1d6c6e5f195bcbe470674eab0f020f5c6768ba374f8363f164a")
thf(ordsuccI2,axiom,(! [X0:$i] : ((c_In @ X0) @ (ordsucc @ X0)))). % 0bce99a2a196c1d6c6e5f195bcbe470674eab0f020f5c6768ba374f8363f164a
% megalodon_source_map (type "nat_5Fp" "nat_p" "")
thf(nat_5Fp,type,(nat_5Fp : ($i > $o))).
% megalodon_source_map (def "nat_5Fp_def" "nat_p" "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab")
thf(nat_5Fp_def,definition,(nat_5Fp = (^ [X0:$i] : (! [X1:($i > $o)] : ((X1 @ c_Empty) => ((! [X2:$i] : ((X1 @ X2) => (X1 @ (ordsucc @ X2)))) => (X1 @ X0))))))). % 25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab
% megalodon_source_map (type "surj" "surj" "")
thf(surj,type,(surj : ($i > ($i > (($i > $i) > $o))))).
% megalodon_source_map (def "surj_def" "surj" "2be3caddae434ec70b82fad7b2b6379b3dfb1775433420e56919db4d17507425")
thf(surj_def,definition,(surj = (^ [X0:$i] : (^ [X1:$i] : (^ [X2:($i > $i)] : ((! [X3:$i] : (((c_In @ X3) @ X0) => ((c_In @ (X2 @ X3)) @ X1))) & (! [X3:$i] : (((c_In @ X3) @ X1) => (? [X4:$i] : (((c_In @ X4) @ X0) & ((X2 @ X4) = X3))))))))))). % 2be3caddae434ec70b82fad7b2b6379b3dfb1775433420e56919db4d17507425
% megalodon_source_map (type "inj" "inj" "")
thf(inj,type,(inj : ($i > ($i > (($i > $i) > $o))))).
% megalodon_source_map (def "inj_def" "inj" "2ce94583b11dd10923fde2a0e16d5b0b24ef079ca98253fdbce2d78acdd63e6e")
thf(inj_def,definition,(inj = (^ [X0:$i] : (^ [X1:$i] : (^ [X2:($i > $i)] : ((! [X3:$i] : (((c_In @ X3) @ X0) => ((c_In @ (X2 @ X3)) @ X1))) & (! [X3:$i] : (((c_In @ X3) @ X0) => (! [X4:$i] : (((c_In @ X4) @ X0) => (((X2 @ X3) = (X2 @ X4)) => (X3 = X4)))))))))))). % 2ce94583b11dd10923fde2a0e16d5b0b24ef079ca98253fdbce2d78acdd63e6e
% megalodon_source_map (type "bij" "bij" "")
thf(bij,type,(bij : ($i > ($i > (($i > $i) > $o))))).
% megalodon_source_map (def "bij_def" "bij" "b2487cac08f5762d6b201f12df6bd1872b979a4baefc5f637987e633ae46675d")
thf(bij_def,definition,(bij = (^ [X0:$i] : (^ [X1:$i] : (^ [X2:($i > $i)] : (((! [X3:$i] : (((c_In @ X3) @ X0) => ((c_In @ (X2 @ X3)) @ X1))) & (! [X3:$i] : (((c_In @ X3) @ X0) => (! [X4:$i] : (((c_In @ X4) @ X0) => (((X2 @ X3) = (X2 @ X4)) => (X3 = X4))))))) & (! [X3:$i] : (((c_In @ X3) @ X1) => (? [X4:$i] : (((c_In @ X4) @ X0) & ((X2 @ X4) = X3))))))))))). % b2487cac08f5762d6b201f12df6bd1872b979a4baefc5f637987e633ae46675d
% megalodon_source_map (type "inv" "inv" "")
thf(inv,type,(inv : ($i > (($i > $i) > ($i > $i))))).
% megalodon_source_map (def "inv_def" "inv" "e1e47685e70397861382a17f4ecc47d07cdab63beca11b1d0c6d2985d3e2d38b")
thf(inv_def,definition,(inv = (^ [X0:$i] : (^ [X1:($i > $i)] : (^ [X2:$i] : (c_Eps_5Fi @ (^ [X3:$i] : (((c_In @ X3) @ X0) & ((X1 @ X3) = X2))))))))). % e1e47685e70397861382a17f4ecc47d07cdab63beca11b1d0c6d2985d3e2d38b
% megalodon_source_map (type "atleastp" "atleastp" "")
thf(atleastp,type,(atleastp : ($i > ($i > $o)))).
% megalodon_source_map (def "atleastp_def" "atleastp" "6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d")
thf(atleastp_def,definition,(atleastp = (^ [X0:$i] : (^ [X1:$i] : (? [X2:($i > $i)] : (((inj @ X0) @ X1) @ X2)))))). % 6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d
% megalodon_source_map (type "equip" "equip" "")
thf(equip,type,(equip : ($i > ($i > $o)))).
% megalodon_source_map (def "equip_def" "equip" "5719b3150f582144388b11e7da6c992f73c9f410c816893fdc1019f1b12097e0")
thf(equip_def,definition,(equip = (^ [X0:$i] : (^ [X1:$i] : (? [X2:($i > $i)] : (((bij @ X0) @ X1) @ X2)))))). % 5719b3150f582144388b11e7da6c992f73c9f410c816893fdc1019f1b12097e0
% megalodon_source_map (local_type "n_tp" "n" "")
thf(n_tp,type,(n : $i)).
% megalodon_source_map (conjecture "conj_c__2Fproject_2Ftmp_2Fsource_5Flinked_5Fstrict_5F100_5Fcorpus_5Ffresh_5F041947_2Fhammer_5F1098_5F23" "/project/tmp/source_linked_strict_100_corpus_fresh_041947/hammer_1098_23" "")
thf(conj_c__2Fproject_2Ftmp_2Fsource_5Flinked_5Fstrict_5F100_5Fcorpus_5Ffresh_5F041947_2Fhammer_5F1098_5F23,conjecture,(! [X1:$i] : (((c_In @ X1) @ n) => ((c_In @ X1) @ (c_Union @ (ordsucc @ n)))))).
