% megalodon_origin ((file "/project/Megalodon/examples/hammer/100thms_12_h.mg") (line "10789") (char "22") (kind "aby"))
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
% megalodon_source_map (type "exactly1of2" "exactly1of2" "")
thf(exactly1of2,type,(exactly1of2 : ($o > ($o > $o)))).
% megalodon_source_map (type "c_If_5Fi" "If_i" "")
thf(c_If_5Fi,type,(c_If_5Fi : ($o > ($i > ($i > $i))))).
% megalodon_source_map (type "c_UPair" "UPair" "")
thf(c_UPair,type,(c_UPair : ($i > ($i > $i)))).
% megalodon_source_map (type "c_Sing" "Sing" "")
thf(c_Sing,type,(c_Sing : ($i > $i))).
% megalodon_source_map (type "binunion" "binunion" "")
thf(binunion,type,(binunion : ($i > ($i > $i)))).
% megalodon_source_map (type "c_SetAdjoin" "SetAdjoin" "")
thf(c_SetAdjoin,type,(c_SetAdjoin : ($i > ($i > $i)))).
% megalodon_source_map (def "c_SetAdjoin_def" "SetAdjoin" "153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8")
thf(c_SetAdjoin_def,definition,(c_SetAdjoin = (^ [X0:$i] : (^ [X1:$i] : ((binunion @ X0) @ (c_Sing @ X1)))))). % 153bff87325a9c7569e721334015eeaf79acf75a785b960eb1b46ee9a5f023f8
% megalodon_source_map (type "famunion" "famunion" "")
thf(famunion,type,(famunion : ($i > (($i > $i) > $i)))).
% megalodon_source_map (type "c_Sep" "Sep" "")
thf(c_Sep,type,(c_Sep : ($i > (($i > $o) > $i)))).
% megalodon_source_map (type "c_ReplSep" "ReplSep" "")
thf(c_ReplSep,type,(c_ReplSep : ($i > (($i > $o) > (($i > $i) > $i))))).
% megalodon_source_map (type "binintersect" "binintersect" "")
thf(binintersect,type,(binintersect : ($i > ($i > $i)))).
% megalodon_source_map (type "setminus" "setminus" "")
thf(setminus,type,(setminus : ($i > ($i > $i)))).
% megalodon_source_map (type "ordsucc" "ordsucc" "")
thf(ordsucc,type,(ordsucc : ($i > $i))).
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
% megalodon_source_map (type "atleastp" "atleastp" "")
thf(atleastp,type,(atleastp : ($i > ($i > $o)))).
% megalodon_source_map (def "atleastp_def" "atleastp" "6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d")
thf(atleastp_def,definition,(atleastp = (^ [X0:$i] : (^ [X1:$i] : (? [X2:($i > $i)] : (((inj @ X0) @ X1) @ X2)))))). % 6f4d9bb1b2eaccdca0b575e1c5e5a35eca5ce1511aa156bebf7a824f08d1d69d
% megalodon_source_map (type "equip" "equip" "")
thf(equip,type,(equip : ($i > ($i > $o)))).
% megalodon_source_map (def "equip_def" "equip" "5719b3150f582144388b11e7da6c992f73c9f410c816893fdc1019f1b12097e0")
thf(equip_def,definition,(equip = (^ [X0:$i] : (^ [X1:$i] : (? [X2:($i > $i)] : (((bij @ X0) @ X1) @ X2)))))). % 5719b3150f582144388b11e7da6c992f73c9f410c816893fdc1019f1b12097e0
% megalodon_source_map (type "ordinal" "ordinal" "")
thf(ordinal,type,(ordinal : ($i > $o))).
% megalodon_source_map (def "ordinal_def" "ordinal" "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f")
thf(ordinal_def,definition,(ordinal = (^ [X0:$i] : ((c_TransSet @ X0) & (! [X1:$i] : (((c_In @ X1) @ X0) => (c_TransSet @ X1))))))). % dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f
% megalodon_source_map (type "c_Descr_5Fii" "Descr_ii" "")
thf(c_Descr_5Fii,type,(c_Descr_5Fii : ((($i > $i) > $o) > ($i > $i)))).
% megalodon_source_map (type "c_Descr_5Fiii" "Descr_iii" "")
thf(c_Descr_5Fiii,type,(c_Descr_5Fiii : ((($i > ($i > $i)) > $o) > ($i > ($i > $i))))).
% megalodon_source_map (type "c_Descr_5FVo1" "Descr_Vo1" "")
thf(c_Descr_5FVo1,type,(c_Descr_5FVo1 : ((($i > $o) > $o) > ($i > $o)))).
% megalodon_source_map (type "c_If_5Fii" "If_ii" "")
thf(c_If_5Fii,type,(c_If_5Fii : ($o > (($i > $i) > (($i > $i) > ($i > $i)))))).
% megalodon_source_map (type "c_If_5Fiii" "If_iii" "")
thf(c_If_5Fiii,type,(c_If_5Fiii : ($o > (($i > ($i > $i)) > (($i > ($i > $i)) > ($i > ($i > $i))))))).
% megalodon_source_map (type "c_In_5Frec_5Fi_5FG" "In_rec_i_G" "")
thf(c_In_5Frec_5Fi_5FG,type,(c_In_5Frec_5Fi_5FG : (($i > (($i > $i) > $i)) > ($i > ($i > $o))))).
% megalodon_source_map (def "c_In_5Frec_5Fi_5FG_def" "In_rec_i_G" "ee2e1f36ccc047af9077fcfe6de79d6c9574876b02cae0b4b919e11461760f0d")
thf(c_In_5Frec_5Fi_5FG_def,definition,(c_In_5Frec_5Fi_5FG = (^ [X0:($i > (($i > $i) > $i))] : (^ [X1:$i] : (^ [X2:$i] : (! [X3:($i > ($i > $o))] : ((! [X4:$i] : (! [X5:($i > $i)] : ((! [X6:$i] : (((c_In @ X6) @ X4) => ((X3 @ X6) @ (X5 @ X6)))) => ((X3 @ X4) @ ((X0 @ X4) @ X5))))) => ((X3 @ X1) @ X2)))))))). % ee2e1f36ccc047af9077fcfe6de79d6c9574876b02cae0b4b919e11461760f0d
% megalodon_source_map (type "c_In_5Frec_5Fi" "In_rec_i" "")
thf(c_In_5Frec_5Fi,type,(c_In_5Frec_5Fi : (($i > (($i > $i) > $i)) > ($i > $i)))).
% megalodon_source_map (type "c_In_5Frec_5FG_5Fii" "In_rec_G_ii" "")
thf(c_In_5Frec_5FG_5Fii,type,(c_In_5Frec_5FG_5Fii : (($i > (($i > ($i > $i)) > ($i > $i))) > ($i > (($i > $i) > $o))))).
% megalodon_source_map (def "c_In_5Frec_5FG_5Fii_def" "In_rec_G_ii" "a1d647a0d4604c00a9299eeb35a7aec5e9e7640c5ed0e0cfe0fcf2e0cbdd918c")
thf(c_In_5Frec_5FG_5Fii_def,definition,(c_In_5Frec_5FG_5Fii = (^ [X0:($i > (($i > ($i > $i)) > ($i > $i)))] : (^ [X1:$i] : (^ [X2:($i > $i)] : (! [X3:($i > (($i > $i) > $o))] : ((! [X4:$i] : (! [X5:($i > ($i > $i))] : ((! [X6:$i] : (((c_In @ X6) @ X4) => ((X3 @ X6) @ (X5 @ X6)))) => ((X3 @ X4) @ ((X0 @ X4) @ X5))))) => ((X3 @ X1) @ X2)))))))). % a1d647a0d4604c00a9299eeb35a7aec5e9e7640c5ed0e0cfe0fcf2e0cbdd918c
% megalodon_source_map (type "c_In_5Frec_5Fii" "In_rec_ii" "")
thf(c_In_5Frec_5Fii,type,(c_In_5Frec_5Fii : (($i > (($i > ($i > $i)) > ($i > $i))) > ($i > ($i > $i))))).
% megalodon_source_map (type "c_In_5Frec_5FG_5Fiii" "In_rec_G_iii" "")
thf(c_In_5Frec_5FG_5Fiii,type,(c_In_5Frec_5FG_5Fiii : (($i > (($i > ($i > ($i > $i))) > ($i > ($i > $i)))) > ($i > (($i > ($i > $i)) > $o))))).
% megalodon_source_map (def "c_In_5Frec_5FG_5Fiii_def" "In_rec_G_iii" "6f1ed1ab5306302aa43faafa35c3f0dae0c1345ff560e0c25ae730cb72fb50e5")
thf(c_In_5Frec_5FG_5Fiii_def,definition,(c_In_5Frec_5FG_5Fiii = (^ [X0:($i > (($i > ($i > ($i > $i))) > ($i > ($i > $i))))] : (^ [X1:$i] : (^ [X2:($i > ($i > $i))] : (! [X3:($i > (($i > ($i > $i)) > $o))] : ((! [X4:$i] : (! [X5:($i > ($i > ($i > $i)))] : ((! [X6:$i] : (((c_In @ X6) @ X4) => ((X3 @ X6) @ (X5 @ X6)))) => ((X3 @ X4) @ ((X0 @ X4) @ X5))))) => ((X3 @ X1) @ X2)))))))). % 6f1ed1ab5306302aa43faafa35c3f0dae0c1345ff560e0c25ae730cb72fb50e5
% megalodon_source_map (type "c_In_5Frec_5Fiii" "In_rec_iii" "")
thf(c_In_5Frec_5Fiii,type,(c_In_5Frec_5Fiii : (($i > (($i > ($i > ($i > $i))) > ($i > ($i > $i)))) > ($i > ($i > ($i > $i)))))).
% megalodon_source_map (type "nat_5Fprimrec" "nat_primrec" "")
thf(nat_5Fprimrec,type,(nat_5Fprimrec : ($i > (($i > ($i > $i)) > ($i > $i))))).
% megalodon_source_map (def "nat_5Fprimrec_def" "nat_primrec" "9161ec45669e68b6f032fc9d4d59e7cf0b3f5f860baeb243e29e767a69d600b1")
thf(nat_5Fprimrec_def,definition,(nat_5Fprimrec = (^ [X0:$i] : (^ [X1:($i > ($i > $i))] : (c_In_5Frec_5Fi @ (^ [X2:$i] : (^ [X3:($i > $i)] : (((c_If_5Fi @ ((c_In @ (c_Union @ X2)) @ X2)) @ ((X1 @ (c_Union @ X2)) @ (X3 @ (c_Union @ X2)))) @ X0)))))))). % 9161ec45669e68b6f032fc9d4d59e7cf0b3f5f860baeb243e29e767a69d600b1
% megalodon_source_map (type "add_5Fnat" "add_nat" "")
thf(add_5Fnat,type,(add_5Fnat : ($i > ($i > $i)))).
% megalodon_source_map (type "mul_5Fnat" "mul_nat" "")
thf(mul_5Fnat,type,(mul_5Fnat : ($i > ($i > $i)))).
% megalodon_source_map (type "c_Pi_5Fnat" "Pi_nat" "")
thf(c_Pi_5Fnat,type,(c_Pi_5Fnat : (($i > $i) > ($i > $i)))).
% megalodon_source_map (def "c_Pi_5Fnat_def" "Pi_nat" "943d76f17a0e477678ed13ccab3bd20db13c2b882292f78f171c50fa1e70cfae")
thf(c_Pi_5Fnat_def,definition,(c_Pi_5Fnat = (^ [X0:($i > $i)] : (^ [X1:$i] : (((nat_5Fprimrec @ (ordsucc @ c_Empty)) @ (^ [X2:$i] : (^ [X3:$i] : ((mul_5Fnat @ X3) @ (X0 @ X2))))) @ X1))))). % 943d76f17a0e477678ed13ccab3bd20db13c2b882292f78f171c50fa1e70cfae
% megalodon_source_map (type "exp_5Fnat" "exp_nat" "")
thf(exp_5Fnat,type,(exp_5Fnat : ($i > ($i > $i)))).
% megalodon_source_map (def "exp_5Fnat_def" "exp_nat" "4ce015b98f266293ef85ef9898e1d8f66f4d9664bd9601197410d96354105016")
thf(exp_5Fnat_def,definition,(exp_5Fnat = (^ [X0:$i] : (^ [X1:$i] : (((nat_5Fprimrec @ (ordsucc @ c_Empty)) @ (^ [X2:$i] : (^ [X3:$i] : ((mul_5Fnat @ X0) @ X3)))) @ X1))))). % 4ce015b98f266293ef85ef9898e1d8f66f4d9664bd9601197410d96354105016
% megalodon_source_map (type "omega" "omega" "")
thf(omega,type,(omega : $i)).
% megalodon_source_map (type "finite" "finite" "")
thf(finite,type,(finite : ($i > $o))).
% megalodon_source_map (def "finite_def" "finite" "0498e68493e445a8fce3569ba778f96fe83f914d7905473f18fe1fee01869f5f")
thf(finite_def,definition,(finite = (^ [X0:$i] : (? [X1:$i] : (((c_In @ X1) @ omega) & ((equip @ X0) @ X1)))))). % 0498e68493e445a8fce3569ba778f96fe83f914d7905473f18fe1fee01869f5f
% megalodon_source_map (type "infinite" "infinite" "")
thf(infinite,type,(infinite : ($i > $o))).
% megalodon_source_map (def "infinite_def" "infinite" "7b21e4abd94d496fba9bd902c949754d45c46d1896ef4a724d6867561c7055ed")
thf(infinite_def,definition,(infinite = (^ [X0:$i] : (~ (finite @ X0))))). % 7b21e4abd94d496fba9bd902c949754d45c46d1896ef4a724d6867561c7055ed
% megalodon_source_map (type "divides_5Fnat" "divides_nat" "")
thf(divides_5Fnat,type,(divides_5Fnat : ($i > ($i > $o)))).
% megalodon_source_map (def "divides_5Fnat_def" "divides_nat" "d4edc81b103a7f8386389b4214215e09786f1c39c399dd0cc78b51305ee606ce")
thf(divides_5Fnat_def,definition,(divides_5Fnat = (^ [X0:$i] : (^ [X1:$i] : ((((c_In @ X0) @ omega) & ((c_In @ X1) @ omega)) & (? [X2:$i] : (((c_In @ X2) @ omega) & (((mul_5Fnat @ X0) @ X2) = X1)))))))). % d4edc81b103a7f8386389b4214215e09786f1c39c399dd0cc78b51305ee606ce
% megalodon_source_map (type "prime_5Fnat" "prime_nat" "")
thf(prime_5Fnat,type,(prime_5Fnat : ($i > $o))).
% megalodon_source_map (def "prime_5Fnat_def" "prime_nat" "894d319b8678a53d5ba0debfa7c31b2615043dbd1e2916815fe1b2e94b3bb6c4")
thf(prime_5Fnat_def,definition,(prime_5Fnat = (^ [X0:$i] : ((((c_In @ X0) @ omega) & ((c_In @ (ordsucc @ c_Empty)) @ X0)) & (! [X1:$i] : (((c_In @ X1) @ omega) => (((divides_5Fnat @ X1) @ X0) => ((X1 = (ordsucc @ c_Empty)) | (X1 = X0))))))))). % 894d319b8678a53d5ba0debfa7c31b2615043dbd1e2916815fe1b2e94b3bb6c4
% megalodon_source_map (type "composite_5Fnat" "composite_nat" "")
thf(composite_5Fnat,type,(composite_5Fnat : ($i > $o))).
% megalodon_source_map (def "composite_5Fnat_def" "composite_nat" "139cb816cd2cc78d77099c5118e6cc48108521f2e7f1338351b7c6c10db4341e")
thf(composite_5Fnat_def,definition,(composite_5Fnat = (^ [X0:$i] : (((c_In @ X0) @ omega) & (? [X1:$i] : (((c_In @ X1) @ omega) & (? [X2:$i] : (((c_In @ X2) @ omega) & ((((c_In @ (ordsucc @ c_Empty)) @ X1) & ((c_In @ (ordsucc @ c_Empty)) @ X2)) & (((mul_5Fnat @ X1) @ X2) = X0)))))))))). % 139cb816cd2cc78d77099c5118e6cc48108521f2e7f1338351b7c6c10db4341e
% megalodon_source_map (type "primes" "primes" "")
thf(primes,type,(primes : $i)).
% megalodon_source_map (def "primes_def" "primes" "858cf7940eb54ced0b57f814a4cc36689f68ab5dc2d94eed51d50c6c58acd3f0")
thf(primes_def,definition,(primes = ((c_Sep @ omega) @ (^ [X0:$i] : (prime_5Fnat @ X0))))). % 858cf7940eb54ced0b57f814a4cc36689f68ab5dc2d94eed51d50c6c58acd3f0
% megalodon_source_map (type "c_Inj1" "Inj1" "")
thf(c_Inj1,type,(c_Inj1 : ($i > $i))).
% megalodon_source_map (def "c_Inj1_def" "Inj1" "fb5286197ee583bb87a6f052d00fee2b461d328cc4202e5fb40ec0a927da5d7e")
thf(c_Inj1_def,definition,(c_Inj1 = (c_In_5Frec_5Fi @ (^ [X0:$i] : (^ [X1:($i > $i)] : ((binunion @ (c_Sing @ c_Empty)) @ ((c_Repl @ X0) @ (^ [X2:$i] : (X1 @ X2))))))))). % fb5286197ee583bb87a6f052d00fee2b461d328cc4202e5fb40ec0a927da5d7e
% megalodon_source_map (type "c_Inj0" "Inj0" "")
thf(c_Inj0,type,(c_Inj0 : ($i > $i))).
% megalodon_source_map (def "c_Inj0_def" "Inj0" "3585d194ae078f7450f400b4043a7820330f482343edc5773d1d72492da8d168")
thf(c_Inj0_def,definition,(c_Inj0 = (^ [X0:$i] : ((c_Repl @ X0) @ (^ [X1:$i] : (c_Inj1 @ X1)))))). % 3585d194ae078f7450f400b4043a7820330f482343edc5773d1d72492da8d168
% megalodon_source_map (type "c_Unj" "Unj" "")
thf(c_Unj,type,(c_Unj : ($i > $i))).
% megalodon_source_map (def "c_Unj_def" "Unj" "d3f7df13cbeb228811efe8a7c7fce2918025a8321cdfe4521523dc066cca9376")
thf(c_Unj_def,definition,(c_Unj = (c_In_5Frec_5Fi @ (^ [X0:$i] : (^ [X1:($i > $i)] : ((c_Repl @ ((setminus @ X0) @ (c_Sing @ c_Empty))) @ (^ [X2:$i] : (X1 @ X2)))))))). % d3f7df13cbeb228811efe8a7c7fce2918025a8321cdfe4521523dc066cca9376
% megalodon_source_map (type "setsum" "setsum" "")
thf(setsum,type,(setsum : ($i > ($i > $i)))).
% megalodon_source_map (def "setsum_def" "setsum" "b260cb5327df5c1f762d4d3068ddb3c7cc96a9cccf7c89cee6abe113920d16f1")
thf(setsum_def,definition,(setsum = (^ [X0:$i] : (^ [X1:$i] : ((binunion @ ((c_Repl @ X0) @ (^ [X2:$i] : (c_Inj0 @ X2)))) @ ((c_Repl @ X1) @ (^ [X2:$i] : (c_Inj1 @ X2)))))))). % b260cb5327df5c1f762d4d3068ddb3c7cc96a9cccf7c89cee6abe113920d16f1
% megalodon_source_map (type "proj0" "proj0" "")
thf(proj0,type,(proj0 : ($i > $i))).
% megalodon_source_map (def "proj0_def" "proj0" "877ee30615a1a7b24a60726a1cf1bff24d7049b80efb464ad22a6a9c9c4f6738")
thf(proj0_def,definition,(proj0 = (^ [X0:$i] : (((c_ReplSep @ X0) @ (^ [X1:$i] : (? [X2:$i] : ((c_Inj0 @ X2) = X1)))) @ (^ [X1:$i] : (c_Unj @ X1)))))). % 877ee30615a1a7b24a60726a1cf1bff24d7049b80efb464ad22a6a9c9c4f6738
% megalodon_source_map (type "proj1" "proj1" "")
thf(proj1,type,(proj1 : ($i > $i))).
% megalodon_source_map (def "proj1_def" "proj1" "dc75c4d622b258b96498f307f3988491e6ba09fbf1db56d36317e5c18aa5cac6")
thf(proj1_def,definition,(proj1 = (^ [X0:$i] : (((c_ReplSep @ X0) @ (^ [X1:$i] : (? [X2:$i] : ((c_Inj1 @ X2) = X1)))) @ (^ [X1:$i] : (c_Unj @ X1)))))). % dc75c4d622b258b96498f307f3988491e6ba09fbf1db56d36317e5c18aa5cac6
% megalodon_source_map (type "c_Sigma" "Sigma" "")
thf(c_Sigma,type,(c_Sigma : ($i > (($i > $i) > $i)))).
% megalodon_source_map (type "setprod" "setprod" "")
thf(setprod,type,(setprod : ($i > ($i > $i)))).
% megalodon_source_map (def "setprod_def" "setprod" "ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7")
thf(setprod_def,definition,(setprod = (^ [X0:$i] : (^ [X1:$i] : ((c_Sigma @ X0) @ (^ [X2:$i] : X1)))))). % ecef5cea93b11859a42b1ea5e8a89184202761217017f3a5cdce1b91d10b34a7
% megalodon_source_map (type "ap" "ap" "")
thf(ap,type,(ap : ($i > ($i > $i)))).
% megalodon_source_map (type "pair_5Fp" "pair_p" "")
thf(pair_5Fp,type,(pair_5Fp : ($i > $o))).
% megalodon_source_map (def "pair_5Fp_def" "pair_p" "dac986a57e8eb6cc7f35dc0ecc031b9ba0403416fabe2dbe130edd287a499231")
thf(pair_5Fp_def,definition,(pair_5Fp = (^ [X0:$i] : (((setsum @ ((ap @ X0) @ c_Empty)) @ ((ap @ X0) @ (ordsucc @ c_Empty))) = X0)))). % dac986a57e8eb6cc7f35dc0ecc031b9ba0403416fabe2dbe130edd287a499231
% megalodon_source_map (type "c_Pi" "Pi" "")
thf(c_Pi,type,(c_Pi : ($i > (($i > $i) > $i)))).
% megalodon_source_map (type "setexp" "setexp" "")
thf(setexp,type,(setexp : ($i > ($i > $i)))).
% megalodon_source_map (def "setexp_def" "setexp" "fcd77a77362d494f90954f299ee3eb7d4273ae93d2d776186c885fc95baa40dc")
thf(setexp_def,definition,(setexp = (^ [X0:$i] : (^ [X1:$i] : ((c_Pi @ X1) @ (^ [X2:$i] : X0)))))). % fcd77a77362d494f90954f299ee3eb7d4273ae93d2d776186c885fc95baa40dc
% megalodon_source_map (type "c_DescrR_5Fi_5Fio_5F1" "DescrR_i_io_1" "")
thf(c_DescrR_5Fi_5Fio_5F1,type,(c_DescrR_5Fi_5Fio_5F1 : (($i > (($i > $o) > $o)) > $i))).
% megalodon_source_map (type "c_DescrR_5Fi_5Fio_5F2" "DescrR_i_io_2" "")
thf(c_DescrR_5Fi_5Fio_5F2,type,(c_DescrR_5Fi_5Fio_5F2 : (($i > (($i > $o) > $o)) > ($i > $o)))).
% megalodon_source_map (type "c_PNoEq_5F" "PNoEq_" "")
thf(c_PNoEq_5F,type,(c_PNoEq_5F : ($i > (($i > $o) > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNoEq_5F_def" "PNoEq_" "ac96e86902ef72d5c44622f4a1ba3aaf673377d32cc26993c04167cc9f22067f")
thf(c_PNoEq_5F_def,definition,(c_PNoEq_5F = (^ [X0:$i] : (^ [X1:($i > $o)] : (^ [X2:($i > $o)] : (! [X3:$i] : (((c_In @ X3) @ X0) => ((X1 @ X3) <=> (X2 @ X3))))))))). % ac96e86902ef72d5c44622f4a1ba3aaf673377d32cc26993c04167cc9f22067f
% megalodon_source_map (type "c_PNoLt_5F" "PNoLt_" "")
thf(c_PNoLt_5F,type,(c_PNoLt_5F : ($i > (($i > $o) > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNoLt_5F_def" "PNoLt_" "f36b5131fd375930d531d698d26ac2fc4552d148f386caa7d27dbce902085320")
thf(c_PNoLt_5F_def,definition,(c_PNoLt_5F = (^ [X0:$i] : (^ [X1:($i > $o)] : (^ [X2:($i > $o)] : (? [X3:$i] : (((c_In @ X3) @ X0) & (((((c_PNoEq_5F @ X3) @ X1) @ X2) & (~ (X1 @ X3))) & (X2 @ X3))))))))). % f36b5131fd375930d531d698d26ac2fc4552d148f386caa7d27dbce902085320
% megalodon_source_map (type "c_PNoLt" "PNoLt" "")
thf(c_PNoLt,type,(c_PNoLt : ($i > (($i > $o) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (type "c_PNoLe" "PNoLe" "")
thf(c_PNoLe,type,(c_PNoLe : ($i > (($i > $o) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNoLe_def" "PNoLe" "f91c31af54bc4bb4f184b6de34d1e557a26e2d1c9f3c78c2b12be5ff6d66df66")
thf(c_PNoLe_def,definition,(c_PNoLe = (^ [X0:$i] : (^ [X1:($i > $o)] : (^ [X2:$i] : (^ [X3:($i > $o)] : (((((c_PNoLt @ X0) @ X1) @ X2) @ X3) | ((X0 = X2) & (((c_PNoEq_5F @ X0) @ X1) @ X3))))))))). % f91c31af54bc4bb4f184b6de34d1e557a26e2d1c9f3c78c2b12be5ff6d66df66
% megalodon_source_map (type "c_PNo_5Fdownc" "PNo_downc" "")
thf(c_PNo_5Fdownc,type,(c_PNo_5Fdownc : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Fdownc_def" "PNo_downc" "e59af381b17c6d7665103fc55f99405c91c5565fece1832a6697045a1714a27a")
thf(c_PNo_5Fdownc_def,definition,(c_PNo_5Fdownc = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (? [X3:$i] : ((ordinal @ X3) & (? [X4:($i > $o)] : (((X0 @ X3) @ X4) & ((((c_PNoLe @ X1) @ X2) @ X3) @ X4)))))))))). % e59af381b17c6d7665103fc55f99405c91c5565fece1832a6697045a1714a27a
% megalodon_source_map (type "c_PNo_5Fupc" "PNo_upc" "")
thf(c_PNo_5Fupc,type,(c_PNo_5Fupc : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Fupc_def" "PNo_upc" "eb5699f1770673cc0c3bfaa04e50f2b8554934a9cbd6ee4e9510f57bd9e88b67")
thf(c_PNo_5Fupc_def,definition,(c_PNo_5Fupc = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (? [X3:$i] : ((ordinal @ X3) & (? [X4:($i > $o)] : (((X0 @ X3) @ X4) & ((((c_PNoLe @ X3) @ X4) @ X1) @ X2)))))))))). % eb5699f1770673cc0c3bfaa04e50f2b8554934a9cbd6ee4e9510f57bd9e88b67
% megalodon_source_map (type "c_PNoLt_5Fpwise" "PNoLt_pwise" "")
thf(c_PNoLt_5Fpwise,type,(c_PNoLt_5Fpwise : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > $o)))).
% megalodon_source_map (def "c_PNoLt_5Fpwise_def" "PNoLt_pwise" "8b40c8c4336d982e6282a1024322e7d9333f9d2c5cf49044df61ef6c36e6b13d")
thf(c_PNoLt_5Fpwise_def,definition,(c_PNoLt_5Fpwise = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (! [X2:$i] : ((ordinal @ X2) => (! [X3:($i > $o)] : (((X0 @ X2) @ X3) => (! [X4:$i] : ((ordinal @ X4) => (! [X5:($i > $o)] : (((X1 @ X4) @ X5) => ((((c_PNoLt @ X2) @ X3) @ X4) @ X5))))))))))))). % 8b40c8c4336d982e6282a1024322e7d9333f9d2c5cf49044df61ef6c36e6b13d
% megalodon_source_map (type "c_PNo_5Frel_5Fstrict_5Fupperbd" "PNo_rel_strict_upperbd" "")
thf(c_PNo_5Frel_5Fstrict_5Fupperbd,type,(c_PNo_5Frel_5Fstrict_5Fupperbd : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Frel_5Fstrict_5Fupperbd_def" "PNo_rel_strict_upperbd" "e3c1352956e5bf2eaee279f30cd72331033b9bd8d92b7ea676e3690a9a8ff39a")
thf(c_PNo_5Frel_5Fstrict_5Fupperbd_def,definition,(c_PNo_5Frel_5Fstrict_5Fupperbd = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (! [X3:$i] : (((c_In @ X3) @ X1) => (! [X4:($i > $o)] : ((((c_PNo_5Fdownc @ X0) @ X3) @ X4) => ((((c_PNoLt @ X3) @ X4) @ X1) @ X2)))))))))). % e3c1352956e5bf2eaee279f30cd72331033b9bd8d92b7ea676e3690a9a8ff39a
% megalodon_source_map (type "c_PNo_5Frel_5Fstrict_5Flowerbd" "PNo_rel_strict_lowerbd" "")
thf(c_PNo_5Frel_5Fstrict_5Flowerbd,type,(c_PNo_5Frel_5Fstrict_5Flowerbd : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Frel_5Fstrict_5Flowerbd_def" "PNo_rel_strict_lowerbd" "bc8218c25b0a9da87c5c86b122421e1e9bb49d62b1a2ef19c972e04205dda286")
thf(c_PNo_5Frel_5Fstrict_5Flowerbd_def,definition,(c_PNo_5Frel_5Fstrict_5Flowerbd = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (! [X3:$i] : (((c_In @ X3) @ X1) => (! [X4:($i > $o)] : ((((c_PNo_5Fupc @ X0) @ X3) @ X4) => ((((c_PNoLt @ X1) @ X2) @ X3) @ X4)))))))))). % bc8218c25b0a9da87c5c86b122421e1e9bb49d62b1a2ef19c972e04205dda286
% megalodon_source_map (type "c_PNo_5Frel_5Fstrict_5Fimv" "PNo_rel_strict_imv" "")
thf(c_PNo_5Frel_5Fstrict_5Fimv,type,(c_PNo_5Frel_5Fstrict_5Fimv : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Frel_5Fstrict_5Fimv_def" "PNo_rel_strict_imv" "59afcfba9fdd03aeaf46e2c6e78357750119f49ceee909d654321be1842de7c6")
thf(c_PNo_5Frel_5Fstrict_5Fimv_def,definition,(c_PNo_5Frel_5Fstrict_5Fimv = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : ((((c_PNo_5Frel_5Fstrict_5Fupperbd @ X0) @ X2) @ X3) & (((c_PNo_5Frel_5Fstrict_5Flowerbd @ X1) @ X2) @ X3)))))))). % 59afcfba9fdd03aeaf46e2c6e78357750119f49ceee909d654321be1842de7c6
% megalodon_source_map (type "c_PNo_5Frel_5Fstrict_5Funiq_5Fimv" "PNo_rel_strict_uniq_imv" "")
thf(c_PNo_5Frel_5Fstrict_5Funiq_5Fimv,type,(c_PNo_5Frel_5Fstrict_5Funiq_5Fimv : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Frel_5Fstrict_5Funiq_5Fimv_def" "PNo_rel_strict_uniq_imv" "c12e8ab3e6933c137bb7f6da0ea861e26e38083cba3ed9d95d465030f8532067")
thf(c_PNo_5Frel_5Fstrict_5Funiq_5Fimv_def,definition,(c_PNo_5Frel_5Fstrict_5Funiq_5Fimv = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : (((((c_PNo_5Frel_5Fstrict_5Fimv @ X0) @ X1) @ X2) @ X3) & (! [X4:($i > $o)] : (((((c_PNo_5Frel_5Fstrict_5Fimv @ X0) @ X1) @ X2) @ X4) => (((c_PNoEq_5F @ X2) @ X3) @ X4)))))))))). % c12e8ab3e6933c137bb7f6da0ea861e26e38083cba3ed9d95d465030f8532067
% megalodon_source_map (type "c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv" "PNo_rel_strict_split_imv" "")
thf(c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv,type,(c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv_def" "PNo_rel_strict_split_imv" "78a3bf7ecddc538557453ade96e29b8ff44a970ec9a42fd661f64160ff971930")
thf(c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv_def,definition,(c_PNo_5Frel_5Fstrict_5Fsplit_5Fimv = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : (((((c_PNo_5Frel_5Fstrict_5Fimv @ X0) @ X1) @ (ordsucc @ X2)) @ (^ [X4:$i] : ((X3 @ X4) & (~ (X4 = X2))))) & ((((c_PNo_5Frel_5Fstrict_5Fimv @ X0) @ X1) @ (ordsucc @ X2)) @ (^ [X4:$i] : ((X3 @ X4) | (X4 = X2))))))))))). % 78a3bf7ecddc538557453ade96e29b8ff44a970ec9a42fd661f64160ff971930
% megalodon_source_map (type "c_PNo_5Flenbdd" "PNo_lenbdd" "")
thf(c_PNo_5Flenbdd,type,(c_PNo_5Flenbdd : ($i > (($i > (($i > $o) > $o)) > $o)))).
% megalodon_source_map (def "c_PNo_5Flenbdd_def" "PNo_lenbdd" "41a47127fd3674a251aaf14f866ade125c56dc72c68d082b8759d4c3e687b4fd")
thf(c_PNo_5Flenbdd_def,definition,(c_PNo_5Flenbdd = (^ [X0:$i] : (^ [X1:($i > (($i > $o) > $o))] : (! [X2:$i] : (! [X3:($i > $o)] : (((X1 @ X2) @ X3) => ((c_In @ X2) @ X0)))))))). % 41a47127fd3674a251aaf14f866ade125c56dc72c68d082b8759d4c3e687b4fd
% megalodon_source_map (type "c_PNo_5Fstrict_5Fupperbd" "PNo_strict_upperbd" "")
thf(c_PNo_5Fstrict_5Fupperbd,type,(c_PNo_5Fstrict_5Fupperbd : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Fstrict_5Fupperbd_def" "PNo_strict_upperbd" "23550cc9acffc87f322ad317d1c98641dca02e97c9cac67a1860a4c64d0825fe")
thf(c_PNo_5Fstrict_5Fupperbd_def,definition,(c_PNo_5Fstrict_5Fupperbd = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (! [X3:$i] : ((ordinal @ X3) => (! [X4:($i > $o)] : (((X0 @ X3) @ X4) => ((((c_PNoLt @ X3) @ X4) @ X1) @ X2)))))))))). % 23550cc9acffc87f322ad317d1c98641dca02e97c9cac67a1860a4c64d0825fe
% megalodon_source_map (type "c_PNo_5Fstrict_5Flowerbd" "PNo_strict_lowerbd" "")
thf(c_PNo_5Fstrict_5Flowerbd,type,(c_PNo_5Fstrict_5Flowerbd : (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o))))).
% megalodon_source_map (def "c_PNo_5Fstrict_5Flowerbd_def" "PNo_strict_lowerbd" "7401799183ed959352a65e49de9fe60e8cc9f883b777b9f6486f987bc305367b")
thf(c_PNo_5Fstrict_5Flowerbd_def,definition,(c_PNo_5Fstrict_5Flowerbd = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:$i] : (^ [X2:($i > $o)] : (! [X3:$i] : ((ordinal @ X3) => (! [X4:($i > $o)] : (((X0 @ X3) @ X4) => ((((c_PNoLt @ X1) @ X2) @ X3) @ X4)))))))))). % 7401799183ed959352a65e49de9fe60e8cc9f883b777b9f6486f987bc305367b
% megalodon_source_map (type "c_PNo_5Fstrict_5Fimv" "PNo_strict_imv" "")
thf(c_PNo_5Fstrict_5Fimv,type,(c_PNo_5Fstrict_5Fimv : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Fstrict_5Fimv_def" "PNo_strict_imv" "69ce10766e911ed54fa1fda563f82aefcfba7402ed6fd8d3b9c63c00157b1758")
thf(c_PNo_5Fstrict_5Fimv_def,definition,(c_PNo_5Fstrict_5Fimv = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : ((((c_PNo_5Fstrict_5Fupperbd @ X0) @ X2) @ X3) & (((c_PNo_5Fstrict_5Flowerbd @ X1) @ X2) @ X3)))))))). % 69ce10766e911ed54fa1fda563f82aefcfba7402ed6fd8d3b9c63c00157b1758
% megalodon_source_map (type "c_PNo_5Fleast_5Frep" "PNo_least_rep" "")
thf(c_PNo_5Fleast_5Frep,type,(c_PNo_5Fleast_5Frep : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Fleast_5Frep_def" "PNo_least_rep" "8050b18a682b443263cb27b578f9d8f089d2bc989740edf6ac729e91f5f46f64")
thf(c_PNo_5Fleast_5Frep_def,definition,(c_PNo_5Fleast_5Frep = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : (((ordinal @ X2) & ((((c_PNo_5Fstrict_5Fimv @ X0) @ X1) @ X2) @ X3)) & (! [X4:$i] : (((c_In @ X4) @ X2) => (! [X5:($i > $o)] : (~ ((((c_PNo_5Fstrict_5Fimv @ X0) @ X1) @ X4) @ X5)))))))))))). % 8050b18a682b443263cb27b578f9d8f089d2bc989740edf6ac729e91f5f46f64
% megalodon_source_map (type "c_PNo_5Fleast_5Frep2" "PNo_least_rep2" "")
thf(c_PNo_5Fleast_5Frep2,type,(c_PNo_5Fleast_5Frep2 : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > (($i > $o) > $o)))))).
% megalodon_source_map (def "c_PNo_5Fleast_5Frep2_def" "PNo_least_rep2" "d3592c771464826c60ca07f5375f571afb7698968b3356c8660f76cd4df7f9c6")
thf(c_PNo_5Fleast_5Frep2_def,definition,(c_PNo_5Fleast_5Frep2 = (^ [X0:($i > (($i > $o) > $o))] : (^ [X1:($i > (($i > $o) > $o))] : (^ [X2:$i] : (^ [X3:($i > $o)] : (((((c_PNo_5Fleast_5Frep @ X0) @ X1) @ X2) @ X3) & (! [X4:$i] : (((nIn @ X4) @ X2) => (~ (X3 @ X4))))))))))). % d3592c771464826c60ca07f5375f571afb7698968b3356c8660f76cd4df7f9c6
% megalodon_source_map (type "c_PNo_5Fbd" "PNo_bd" "")
thf(c_PNo_5Fbd,type,(c_PNo_5Fbd : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > $i)))).
% megalodon_source_map (type "c_PNo_5Fpred" "PNo_pred" "")
thf(c_PNo_5Fpred,type,(c_PNo_5Fpred : (($i > (($i > $o) > $o)) > (($i > (($i > $o) > $o)) > ($i > $o))))).
% megalodon_source_map (type "c_SNoElts_5F" "SNoElts_" "")
thf(c_SNoElts_5F,type,(c_SNoElts_5F : ($i > $i))).
% megalodon_source_map (def "c_SNoElts_5F_def" "SNoElts_" "1e55e667ef0bb79beeaf1a09548d003a4ce4f951cd8eb679eb1fed9bde85b91c")
thf(c_SNoElts_5F_def,definition,(c_SNoElts_5F = (^ [X0:$i] : ((binunion @ X0) @ ((c_Repl @ X0) @ (^ [X1:$i] : ((^ [X2:$i] : ((c_SetAdjoin @ X2) @ (c_Sing @ (ordsucc @ c_Empty)))) @ X1))))))). % 1e55e667ef0bb79beeaf1a09548d003a4ce4f951cd8eb679eb1fed9bde85b91c
% megalodon_source_map (type "c_SNo_5F" "SNo_" "")
thf(c_SNo_5F,type,(c_SNo_5F : ($i > ($i > $o)))).
% megalodon_source_map (def "c_SNo_5F_def" "SNo_" "3bbf071b189275f9b1ce422c67c30b34c127fdb067b3c9b4436b02cfbe125351")
thf(c_SNo_5F_def,definition,(c_SNo_5F = (^ [X0:$i] : (^ [X1:$i] : (((c_Subq @ X1) @ (c_SNoElts_5F @ X0)) & (! [X2:$i] : (((c_In @ X2) @ X0) => ((exactly1of2 @ ((c_In @ ((^ [X3:$i] : ((c_SetAdjoin @ X3) @ (c_Sing @ (ordsucc @ c_Empty)))) @ X2)) @ X1)) @ ((c_In @ X2) @ X1))))))))). % 3bbf071b189275f9b1ce422c67c30b34c127fdb067b3c9b4436b02cfbe125351
% megalodon_source_map (type "c_PSNo" "PSNo" "")
thf(c_PSNo,type,(c_PSNo : ($i > (($i > $o) > $i)))).
% megalodon_source_map (def "c_PSNo_def" "PSNo" "89e534b3d5ad303c952b3eac3b2b69eb72d95ba1d9552659f81c57725fc03350")
thf(c_PSNo_def,definition,(c_PSNo = (^ [X0:$i] : (^ [X1:($i > $o)] : ((binunion @ ((c_Sep @ X0) @ (^ [X2:$i] : (X1 @ X2)))) @ (((c_ReplSep @ X0) @ (^ [X2:$i] : (~ (X1 @ X2)))) @ (^ [X2:$i] : ((^ [X3:$i] : ((c_SetAdjoin @ X3) @ (c_Sing @ (ordsucc @ c_Empty)))) @ X2)))))))). % 89e534b3d5ad303c952b3eac3b2b69eb72d95ba1d9552659f81c57725fc03350
% megalodon_source_map (type "c_SNo" "SNo" "")
thf(c_SNo,type,(c_SNo : ($i > $o))).
% megalodon_source_map (type "c_SNoLev" "SNoLev" "")
thf(c_SNoLev,type,(c_SNoLev : ($i > $i))).
% megalodon_source_map (type "c_SNoEq_5F" "SNoEq_" "")
thf(c_SNoEq_5F,type,(c_SNoEq_5F : ($i > ($i > ($i > $o))))).
% megalodon_source_map (def "c_SNoEq_5F_def" "SNoEq_" "6f17daea88196a4c038cd716092bd8ddbb3eb8bddddfdc19e65574f30c97ab87")
thf(c_SNoEq_5F_def,definition,(c_SNoEq_5F = (^ [X0:$i] : (^ [X1:$i] : (^ [X2:$i] : (((c_PNoEq_5F @ X0) @ (^ [X3:$i] : ((c_In @ X3) @ X1))) @ (^ [X3:$i] : ((c_In @ X3) @ X2)))))))). % 6f17daea88196a4c038cd716092bd8ddbb3eb8bddddfdc19e65574f30c97ab87
% megalodon_source_map (type "c_SNoLt" "SNoLt" "")
thf(c_SNoLt,type,(c_SNoLt : ($i > ($i > $o)))).
% megalodon_source_map (def "c_SNoLt_def" "SNoLt" "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1")
thf(c_SNoLt_def,definition,(c_SNoLt = (^ [X0:$i] : (^ [X1:$i] : ((((c_PNoLt @ (c_SNoLev @ X0)) @ (^ [X2:$i] : ((c_In @ X2) @ X0))) @ (c_SNoLev @ X1)) @ (^ [X2:$i] : ((c_In @ X2) @ X1))))))). % 0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1
% megalodon_source_map (type "c_SNoLe" "SNoLe" "")
thf(c_SNoLe,type,(c_SNoLe : ($i > ($i > $o)))).
% megalodon_source_map (def "c_SNoLe_def" "SNoLe" "09cdd0b9af76352f6b30bf3c4bca346eaa03d280255f13afb2e73fe8329098b6")
thf(c_SNoLe_def,definition,(c_SNoLe = (^ [X0:$i] : (^ [X1:$i] : ((((c_PNoLe @ (c_SNoLev @ X0)) @ (^ [X2:$i] : ((c_In @ X2) @ X0))) @ (c_SNoLev @ X1)) @ (^ [X2:$i] : ((c_In @ X2) @ X1))))))). % 09cdd0b9af76352f6b30bf3c4bca346eaa03d280255f13afb2e73fe8329098b6
% megalodon_source_map (type "c_SNoCut" "SNoCut" "")
thf(c_SNoCut,type,(c_SNoCut : ($i > ($i > $i)))).
% megalodon_source_map (def "c_SNoCut_def" "SNoCut" "0e3071dce24dfee0112b8d48d9e9fc53f835e6a5b50de4c25d1dfd053ad33bf1")
thf(c_SNoCut_def,definition,(c_SNoCut = (^ [X0:$i] : (^ [X1:$i] : ((c_PSNo @ ((c_PNo_5Fbd @ (^ [X2:$i] : (^ [X3:($i > $o)] : ((ordinal @ X2) & ((c_In @ ((c_PSNo @ X2) @ X3)) @ X0))))) @ (^ [X2:$i] : (^ [X3:($i > $o)] : ((ordinal @ X2) & ((c_In @ ((c_PSNo @ X2) @ X3)) @ X1)))))) @ ((c_PNo_5Fpred @ (^ [X2:$i] : (^ [X3:($i > $o)] : ((ordinal @ X2) & ((c_In @ ((c_PSNo @ X2) @ X3)) @ X0))))) @ (^ [X2:$i] : (^ [X3:($i > $o)] : ((ordinal @ X2) & ((c_In @ ((c_PSNo @ X2) @ X3)) @ X1)))))))))). % 0e3071dce24dfee0112b8d48d9e9fc53f835e6a5b50de4c25d1dfd053ad33bf1
% megalodon_source_map (type "c_SNoCutP" "SNoCutP" "")
thf(c_SNoCutP,type,(c_SNoCutP : ($i > ($i > $o)))).
% megalodon_source_map (def "c_SNoCutP_def" "SNoCutP" "b102ccc5bf572aba76b2c5ff3851795ba59cb16151277dbee9ce5a1aad694334")
thf(c_SNoCutP_def,definition,(c_SNoCutP = (^ [X0:$i] : (^ [X1:$i] : (((! [X2:$i] : (((c_In @ X2) @ X0) => (c_SNo @ X2))) & (! [X2:$i] : (((c_In @ X2) @ X1) => (c_SNo @ X2)))) & (! [X2:$i] : (((c_In @ X2) @ X0) => (! [X3:$i] : (((c_In @ X3) @ X1) => ((c_SNoLt @ X2) @ X3)))))))))). % b102ccc5bf572aba76b2c5ff3851795ba59cb16151277dbee9ce5a1aad694334
% megalodon_source_map (type "c_SNoS_5F" "SNoS_" "")
thf(c_SNoS_5F,type,(c_SNoS_5F : ($i > $i))).
% megalodon_source_map (def "c_SNoS_5F_def" "SNoS_" "7df1da8a4be89c3e696aebe0cabd8b8f51f0c9e350e3396209ee4a31203ddcab")
thf(c_SNoS_5F_def,definition,(c_SNoS_5F = (^ [X0:$i] : ((c_Sep @ (c_Power @ (c_SNoElts_5F @ X0))) @ (^ [X1:$i] : (? [X2:$i] : (((c_In @ X2) @ X0) & ((c_SNo_5F @ X2) @ X1)))))))). % 7df1da8a4be89c3e696aebe0cabd8b8f51f0c9e350e3396209ee4a31203ddcab
% megalodon_source_map (type "c_SNoL" "SNoL" "")
thf(c_SNoL,type,(c_SNoL : ($i > $i))).
% megalodon_source_map (def "c_SNoL_def" "SNoL" "08c87b1a5ce6404b103275d893aba544e498d2abfb545b46ce0e00ad2bb85cd5")
thf(c_SNoL_def,definition,(c_SNoL = (^ [X0:$i] : ((c_Sep @ (c_SNoS_5F @ (c_SNoLev @ X0))) @ (^ [X1:$i] : ((c_SNoLt @ X1) @ X0)))))). % 08c87b1a5ce6404b103275d893aba544e498d2abfb545b46ce0e00ad2bb85cd5
% megalodon_source_map (type "c_SNoR" "SNoR" "")
thf(c_SNoR,type,(c_SNoR : ($i > $i))).
% megalodon_source_map (def "c_SNoR_def" "SNoR" "df0c7f1a5ed1eb8adafd81d6ecc1616d8afbec6fb8f400245c819ce49365279f")
thf(c_SNoR_def,definition,(c_SNoR = (^ [X0:$i] : ((c_Sep @ (c_SNoS_5F @ (c_SNoLev @ X0))) @ (^ [X1:$i] : ((c_SNoLt @ X0) @ X1)))))). % df0c7f1a5ed1eb8adafd81d6ecc1616d8afbec6fb8f400245c819ce49365279f
% megalodon_source_map (known "nat_5Fp_5FSNo" "nat_p_SNo" "2ac1aa136404b01e6a45a3a2fbc56f071a8ad744a5c5a75b81020960959f7bff")
thf(nat_5Fp_5FSNo,axiom,(! [X0:$i] : ((! [X1:($i > $o)] : ((X1 @ c_Empty) => ((! [X2:$i] : ((X1 @ X2) => (X1 @ (ordsucc @ X2)))) => (X1 @ X0)))) => (c_SNo @ X0)))). % 2ac1aa136404b01e6a45a3a2fbc56f071a8ad744a5c5a75b81020960959f7bff
% megalodon_source_map (type "c_SNo_5Fextend0" "SNo_extend0" "")
thf(c_SNo_5Fextend0,type,(c_SNo_5Fextend0 : ($i > $i))).
% megalodon_source_map (def "c_SNo_5Fextend0_def" "SNo_extend0" "e94a939c86c866ea378958089db656d350c86095197c9912d4e9d0f1ea317f09")
thf(c_SNo_5Fextend0_def,definition,(c_SNo_5Fextend0 = (^ [X0:$i] : ((c_PSNo @ (ordsucc @ (c_SNoLev @ X0))) @ (^ [X1:$i] : (((c_In @ X1) @ X0) & (~ (X1 = (c_SNoLev @ X0))))))))). % e94a939c86c866ea378958089db656d350c86095197c9912d4e9d0f1ea317f09
% megalodon_source_map (type "c_SNo_5Fextend1" "SNo_extend1" "")
thf(c_SNo_5Fextend1,type,(c_SNo_5Fextend1 : ($i > $i))).
% megalodon_source_map (def "c_SNo_5Fextend1_def" "SNo_extend1" "680d7652d15d54f0a766df3f997236fe6ea93db85d1c85bee2fa1d84b02d9c1d")
thf(c_SNo_5Fextend1_def,definition,(c_SNo_5Fextend1 = (^ [X0:$i] : ((c_PSNo @ (ordsucc @ (c_SNoLev @ X0))) @ (^ [X1:$i] : (((c_In @ X1) @ X0) | (X1 = (c_SNoLev @ X0)))))))). % 680d7652d15d54f0a766df3f997236fe6ea93db85d1c85bee2fa1d84b02d9c1d
% megalodon_source_map (type "eps_5F" "eps_" "")
thf(eps_5F,type,(eps_5F : ($i > $i))).
% megalodon_source_map (type "c_SNo_5Frec_5Fi" "SNo_rec_i" "")
thf(c_SNo_5Frec_5Fi,type,(c_SNo_5Frec_5Fi : (($i > (($i > $i) > $i)) > ($i > $i)))).
% megalodon_source_map (type "c_SNo_5Frec_5Fii" "SNo_rec_ii" "")
thf(c_SNo_5Frec_5Fii,type,(c_SNo_5Frec_5Fii : (($i > (($i > ($i > $i)) > ($i > $i))) > ($i > ($i > $i))))).
% megalodon_source_map (type "c_SNo_5Frec2" "SNo_rec2" "")
thf(c_SNo_5Frec2,type,(c_SNo_5Frec2 : (($i > ($i > (($i > ($i > $i)) > $i))) > ($i > ($i > $i))))).
% megalodon_source_map (type "minus_5FSNo" "minus_SNo" "")
thf(minus_5FSNo,type,(minus_5FSNo : ($i > $i))).
% megalodon_source_map (type "add_5FSNo" "add_SNo" "")
thf(add_5FSNo,type,(add_5FSNo : ($i > ($i > $i)))).
% megalodon_source_map (type "abs_5FSNo" "abs_SNo" "")
thf(abs_5FSNo,type,(abs_5FSNo : ($i > $i))).
% megalodon_source_map (type "mul_5FSNo" "mul_SNo" "")
thf(mul_5FSNo,type,(mul_5FSNo : ($i > ($i > $i)))).
% megalodon_source_map (type "int" "int" "")
thf(int,type,(int : $i)).
% megalodon_source_map (def "int_def" "int" "f7cd39d139f71b389f61d3cf639bf341d01dac1be60ad65b40ee3aa5218e0043")
thf(int_def,definition,(int = ((binunion @ omega) @ ((c_Repl @ omega) @ (^ [X0:$i] : (minus_5FSNo @ X0)))))). % f7cd39d139f71b389f61d3cf639bf341d01dac1be60ad65b40ee3aa5218e0043
% megalodon_source_map (local_type "n_tp" "n" "")
thf(n_tp,type,(n : $i)).
% megalodon_source_map (local_type "m_tp" "m" "")
thf(m_tp,type,(m : $i)).
% megalodon_source_map (local_type "q_tp" "q" "")
thf(q_tp,type,(q : $i)).
% megalodon_source_map (local_type "r_tp" "r" "")
thf(r_tp,type,(r : $i)).
% megalodon_source_map (local_fact "c_LnN" "LnN" "")
thf(c_LnN,axiom,(! [X4:($i > $o)] : ((X4 @ c_Empty) => ((! [X5:$i] : ((X4 @ X5) => (X4 @ (ordsucc @ X5)))) => (X4 @ n))))).
% megalodon_source_map (conjecture "conj_c__2Fproject_2Ftmp_2Fmegalodon3_5Fsource_5Flinked_5Fcorpus_5F250_2Fhammer_5F10789_5F22" "/project/tmp/megalodon3_source_linked_corpus_250/hammer_10789_22" "")
thf(conj_c__2Fproject_2Ftmp_2Fmegalodon3_5Fsource_5Flinked_5Fcorpus_5F250_2Fhammer_5F10789_5F22,conjecture,(c_SNo @ n)).
