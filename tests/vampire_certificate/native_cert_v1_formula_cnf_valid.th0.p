% megalodon_source_map (local_fact "imp" "imp" "")
thf(imp,axiom,(p => q)).
% megalodon_source_map (local_fact "p_true" "p_true" "")
thf(p_true,axiom,(f__true = p)).
% megalodon_source_map (local_fact "q_false" "q_false" "")
thf(q_false,axiom,~(f__true = q)).
