% megalodon_source_map (local_fact "exists_applied_head" "exists_applied_head" "")
thf(exists_applied_head,axiom,? [X0:$i>$i] : ! [X1:$i] : ((X0 @ X1) = $true)).
% megalodon_source_map (local_fact "neg_applied_head" "neg_applied_head" "")
thf(neg_applied_head,axiom,~((sk @ X1) = $true)).
