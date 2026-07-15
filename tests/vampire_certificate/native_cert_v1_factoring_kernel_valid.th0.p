% megalodon_origin ((file "native_cert_v1_factoring_kernel_valid.mg") (line "1") (char "1") (kind "synthetic_factoring_kernel"))
thf(p,type,p:$o).
% megalodon_source_map (known "dup_p" "dup_p" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
cnf(dup_p,axiom,(p | p)). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "not_p" "not_p" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
cnf(not_p,axiom,~p). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
