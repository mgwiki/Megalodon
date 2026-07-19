% megalodon_origin ((file "synthetic_avatar_split_multi_var_pf.mg") (line "1") (char "1") (kind "synthetic_avatar_split_multi_var_pf"))
thf(p_type,type,p:$i>$o).
thf(q_type,type,q:$o).
% megalodon_source_map (local_fact "xy_source" "xy_source" "")
cnf(xy_source,axiom,((p @ X) | (p @ Y))).
% megalodon_source_map (local_fact "not_split_1" "not_split_1" "")
thf(not_split_1,axiom,~split_1).
% megalodon_source_map (local_fact "not_split_2" "not_split_2" "")
thf(not_split_2,axiom,~split_2).
