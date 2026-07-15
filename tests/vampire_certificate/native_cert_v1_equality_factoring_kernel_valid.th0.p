% megalodon_origin ((file "native_cert_v1_equality_factoring_kernel_valid.mg") (line "1") (char "1") (kind "synthetic_equality_factoring_kernel"))
thf(a_type,type,a:$i).
thf(b_type,type,b:$i).
thf(c_type,type,c:$i).
% megalodon_source_map (known "two_equalities" "two_equalities" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
cnf(two_equalities,axiom,(a = b | a = c)). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "not_a_eq_c" "not_a_eq_c" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
cnf(not_a_eq_c,axiom,~(a = c)). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
% megalodon_source_map (known "b_eq_c" "b_eq_c" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
cnf(b_eq_c,axiom,b = c). % cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
