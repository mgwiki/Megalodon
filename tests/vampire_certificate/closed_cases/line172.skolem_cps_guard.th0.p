% megalodon_origin ((file "/project/tmp/native_aby_smoke_after_source_target_transport/100thms_12_h_slice.mg") (line "172") (char "4") (kind "aby"))
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
% megalodon_source_map (conjecture "conj_c_100thms_5F12_5Fh_5Fslice_5Fline172_5Fchar4" "100thms_12_h_slice_line172_char4" "")
thf(conj_c_100thms_5F12_5Fh_5Fslice_5Fline172_5Fchar4,conjecture,(! [X0:$o] : (! [X1:$o] : ((! [X2:$o] : ((X0 => (X1 => X2)) => X2)) => X0)))).
