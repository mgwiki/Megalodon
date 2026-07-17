(*** Shared vocabulary for the Vampire/Megalodon small-kernel certificate. ***)

type literal =
  | Pos of Syntax.tm
  | Neg of Syntax.tm

type clause = literal list

let schema = "prover9-small-kernel-v1"

let primitive_contracts = [
  ("fool_formula", ["fool_atom_lift"]);
  ("rectify_formula", ["rectify_formula"]);
  ("formula_normalize", ["ennf_formula"]);
  ("skolemize", ["skolem_formula"]);
  ("cnf_clause", ["cnf_literal"; "cnf_formula_clause"]);
  ("formula_copy", ["formula_copy"; "formula_term_copy"]);
  ("fool_exhaustiveness", ["fool_exhaustiveness"]);
  ("truth_conflict", ["truth_conflict"]);
  ("equality_resolution",
   ["equality_resolution"; "equality_resolution_constraints"]);
  ("equality_factoring",
   ["equality_factoring"; "equality_factoring_constraints"]);
  ("avatar_component", ["avatar_component"]);
  ("avatar_split", ["avatar_split"]);
  ("avatar_refutation", ["avatar_refutation"]);
  ("avatar_definition", ["avatar_definition"]);
  ("split_dependency", ["split_dependency"]);
  ("superposition", ["paramodulate"]);
  ("rewrite", ["paramodulate"]);
  ("subsumption_resolution", ["resolve"]);
  ("unit_resulting_resolution", ["resolve"]);
  ("resolution", ["resolve"]);
  ("factoring", ["factor"]);
  ("instantiation", ["substitute"]);
]

let structural_rules = [
  "predicate_definition";
  "predicate_definition_fold";
  "predicate_definition_fold_chain";
]

let supported_rules =
  List.sort_uniq String.compare
    (structural_rules @ List.map fst primitive_contracts)

let is_supported_rule rule =
  List.mem rule supported_rules

let required_primitives_for_rule rule =
  match List.assoc_opt rule primitive_contracts with
  | Some primitives -> primitives
  | None -> []
