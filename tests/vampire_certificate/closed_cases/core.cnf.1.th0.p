% megalodon_origin ((file "core_probe.mg") (line "1") (char "1") (kind "manual_core_probe"))
% megalodon_source_map (known "a1" "a1" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
cnf(a1,axiom,p | q). % aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
% megalodon_source_map (known "a2" "a2" "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")
cnf(a2,axiom,~p). % bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
% megalodon_source_map (known "a3" "a3" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
cnf(a3,axiom,~q). % cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
