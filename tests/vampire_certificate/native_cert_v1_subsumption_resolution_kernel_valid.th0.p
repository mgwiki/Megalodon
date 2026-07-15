% megalodon_origin ((file "native_cert_v1_subsumption_resolution_kernel_valid.mg") (line "1") (char "1") (kind "synthetic_subsumption_resolution_kernel"))
thf(p,type,p:$o).
thf(q,type,q:$o).
% megalodon_source_map (known "pq" "pq" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
cnf(pq,axiom,(p | q)). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "not_p" "not_p" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
cnf(not_p,axiom,~p). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
% megalodon_source_map (known "not_q" "not_q" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
cnf(not_q,axiom,~q). % cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
