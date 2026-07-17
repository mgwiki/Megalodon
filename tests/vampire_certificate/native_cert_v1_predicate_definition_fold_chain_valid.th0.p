% megalodon_origin ((file "native_cert_v1_predicate_definition_fold_chain_valid.mg") (line "1") (char "1") (kind "synthetic_predicate_definition_fold_chain"))
thf(r_type,type,r:$o).
thf(q_type,type,q:$o).
thf(pdef_type,type,pdef:$o).
thf(qdef_type,type,qdef:$o).
% megalodon_source_map (local_fact "source_formula" "source_formula" "")
thf(source_formula,axiom,(r & q)).
% megalodon_source_map (local_fact "not_folded" "not_folded" "")
thf(not_folded,axiom,~($true = qdef)).
