% megalodon_origin ((file "native_cert_v1_open_negative_paramod_valid.mg") (line "1") (char "1") (kind "synthetic_open_negative_paramod"))
% megalodon_source_map (known "a1" "original_a1" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
thf(a1,axiom,(f__true = (p @ a))). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "a2" "original_a2" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
thf(a2,axiom,(~((p @ a) = f__true) | (f__true = (p @ X0)))). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
% megalodon_source_map (known "a3" "original_a3" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
thf(a3,axiom,~(f__true = (p @ a))). % cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
