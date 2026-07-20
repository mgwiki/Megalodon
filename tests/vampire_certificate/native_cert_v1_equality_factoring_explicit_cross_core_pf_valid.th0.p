% megalodon_origin ((file "native_cert_v1_equality_factoring_explicit_cross_core_pf_valid.mg") (line "1") (char "1") (kind "synthetic_equality_factoring_explicit_cross_core_pf"))
thf(a_type,type,a:$i).
thf(b_type,type,b:$i).
thf(c_type,type,c:$i).
% megalodon_source_map (known "two_equalities" "two_equalities" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
cnf(two_equalities,axiom,(a = b) | (c = a)). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "not_c_a" "not_c_a" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
cnf(not_c_a,axiom,~(c = a)). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
% megalodon_source_map (known "b_c" "b_c" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
cnf(b_c,axiom,b = c). % cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
