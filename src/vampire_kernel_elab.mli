(*** Deterministic proof-term boundary for the Vampire/Megalodon small kernel. ***)

exception Error of string

type clause_formula_basis = {
  false_tm : Syntax.tm;
  or_tm : Syntax.tm -> Syntax.tm -> Syntax.tm;
  atom_tm : Syntax.tm -> Syntax.tm;
}

val identity_atom : Syntax.tm -> Syntax.tm

val literal_prop :
  clause_formula_basis ->
  Vampire_kernel_syntax.literal ->
  Syntax.tm

val clause_prop :
  clause_formula_basis ->
  Vampire_kernel_syntax.clause ->
  Syntax.tm

type proof_step = {
  step_id : string;
  step_clause : Vampire_kernel_syntax.clause;
  step_prop : Syntax.tm;
  step_proof : Syntax.pf;
}

val input_step :
  clause_formula_basis ->
  id:string ->
  clause:Vampire_kernel_syntax.clause ->
  Syntax.pf ->
  proof_step

val db_for_result_variable :
  result_step_variables:(string * Syntax.tp) list ->
  string ->
  Syntax.tp ->
  Syntax.tm option

val first_result_variable_of_type :
  result_step_variables:(string * Syntax.tp) list ->
  Syntax.tp ->
  Syntax.tm option

val result_variables_of_type :
  result_step_variables:(string * Syntax.tp) list ->
  Syntax.tp ->
  Syntax.tm list

val bind_result_step_variables :
  result_step_variables:(string * Syntax.tp) list ->
  close_body:(Syntax.pf -> Syntax.pf) ->
  Syntax.pf ->
  Syntax.pf

val apply_parent_step_variables :
  ?shift_parent_proof:bool ->
  parent_step_variables:(string * Syntax.tp) list ->
  result_step_variables:(string * Syntax.tp) list ->
  resolve_parent_variable:(string -> Syntax.tp -> Syntax.tm option) ->
  missing_parent_variable:(string -> string) ->
  Syntax.pf ->
  Syntax.pf

val open_step_theorem_body_in_result_context :
  ?shift_parent_proof:bool ->
  id:string ->
  parent_step_variables:(string * Syntax.tp) list ->
  result_step_variables:(string * Syntax.tp) list ->
  subst:(string * Syntax.tm) list ->
  close_witness:(Syntax.tm -> Syntax.tm) ->
  Syntax.pf ->
  Syntax.pf

val skolem_choice_witness_proof :
  choice_theorem:string ->
  eps_symbol:string ->
  witness_type:Syntax.tp ->
  predicate:Syntax.tm ->
  Syntax.pf ->
  Syntax.tm * Syntax.pf

val church_exists_map_proof :
  witness_type:Syntax.tp ->
  source_body:Syntax.tm ->
  target_body:Syntax.tm ->
  pointwise_proof:Syntax.pf ->
  Syntax.pf ->
  Syntax.pf

val church_exists_elim_proof :
  target_prop:Syntax.tm ->
  continuation:Syntax.pf ->
  Syntax.pf ->
  Syntax.pf

val replace_exact_terms_in_proof :
  normalize:(Syntax.tm -> Syntax.tm) ->
  (Syntax.tm * Syntax.tm) list ->
  Syntax.pf ->
  Syntax.pf

val close_named_term :
  ?depth:int ->
  canonical_name:(string -> string option) ->
  (string * Syntax.tp) list ->
  Syntax.tm ->
  Syntax.tm

val term_scoped_under :
  context_depth:int ->
  Syntax.tm ->
  bool

val dependent_witness_definition :
  canonical_name:(string -> string option) ->
  variables:(string * Syntax.tp) list ->
  dependencies:(string * Syntax.tp) list ->
  Syntax.tm ->
  Syntax.tm

type live_safe_delta_entry = {
  live_safe_delta_name : string;
  live_safe_delta_arity : int;
  live_safe_delta_body : Syntax.tm;
}

type live_safe_delta_skip = {
  live_safe_delta_skipped_entry : live_safe_delta_entry;
  live_safe_delta_unsafe_symbol : string option;
}

type live_safe_delta_result = {
  live_safe_delta_kept : live_safe_delta_entry list;
  live_safe_delta_skipped : live_safe_delta_skip list;
}

val live_safe_delta_entries :
  ?alias_name:(string -> string option) ->
  body_expander:(Syntax.tm -> Syntax.tm) ->
  is_live_symbol:(string -> bool) ->
  is_extra_symbol:(string -> bool) ->
  live_safe_delta_entry list ->
  live_safe_delta_result

val proof_contains_term_symbol :
  string list ->
  Syntax.pf ->
  bool

val term_contains_symbol :
  string list ->
  Syntax.tm ->
  bool

val proof_contains_exact_term :
  normalize:(Syntax.tm -> Syntax.tm) ->
  Syntax.tm ->
  Syntax.pf ->
  bool

val first_enclosing_term_with_symbol :
  string list ->
  Syntax.pf ->
  (string * Syntax.tm) option

val enclosing_terms_with_symbol :
  normalize:(Syntax.tm -> Syntax.tm) ->
  string list ->
  Syntax.pf ->
  Syntax.tm list

val enclosing_terms_with_symbol_depth :
  normalize:(Syntax.tm -> Syntax.tm) ->
  string list ->
  Syntax.pf ->
  (int * Syntax.tm) list

val registered_witness_term_replacements :
  normalize:(Syntax.tm -> Syntax.tm) ->
  witness_symbols:string list ->
  (string * Syntax.tm) list ->
  Syntax.pf ->
  (Syntax.tm * Syntax.tm) list

val contract_backed_branch_choice_term_replacements :
  normalize:(Syntax.tm -> Syntax.tm) ->
  choice_symbols:string list ->
  replacement_names:string list ->
  definition:Syntax.tm ->
  Syntax.pf ->
  (string * Syntax.tm * Syntax.tm * Syntax.tm) list

type skolem_witness_transport = {
  skolem_transport_name : string;
  skolem_transport_choice_occurrence : Syntax.tm;
  skolem_transport_definition : Syntax.tm;
  skolem_transport_local_template : Syntax.tm;
}

val contract_backed_skolem_witness_transports :
  normalize:(Syntax.tm -> Syntax.tm) ->
  choice_symbols:string list ->
  replacement_names:string list ->
  definition:Syntax.tm ->
  Syntax.pf ->
  skolem_witness_transport list

val skolem_witness_transport_symbol_replacements :
  skolem_witness_transport list ->
  (string * Syntax.tm * Syntax.tm * Syntax.tm) list

val skolem_witness_transport_term_replacements :
  skolem_witness_transport list ->
  (Syntax.tm * Syntax.tm) list

val skolem_witness_transport_proof_replacements :
  skolem_witness_transport list ->
  (Syntax.tm * Syntax.tm) list

val skolem_witness_transport_proof_replacements_with_aliases :
  alias_names:(string -> string list) ->
  skolem_witness_transport list ->
  (Syntax.tm * Syntax.tm) list

val prioritized_skolem_witness_transport_proof_replacements :
  normalize:(Syntax.tm -> Syntax.tm) ->
  alias_names:(string -> string list) ->
  witness_symbols:string list ->
  registered_witnesses:(string * Syntax.tm) list ->
  transports:skolem_witness_transport list ->
  Syntax.pf ->
  (Syntax.tm * Syntax.tm) list

type introduced_symbol_replacement_classification = {
  introduced_symbols_present : string list;
  introduced_symbols_with_direct_replacement : string list;
  introduced_symbols_without_direct_replacement : string list;
}

val classify_introduced_symbol_replacements :
  alias_names:(string -> string list) ->
  introduced_symbols:string list ->
  replacements:(Syntax.tm * Syntax.tm) list ->
  Syntax.pf ->
  introduced_symbol_replacement_classification

type skolem_witness_cleanup_plan = {
  skolem_cleanup_transports : skolem_witness_transport list;
  skolem_cleanup_ambiguous_choice_occurrences : Syntax.tm list;
  skolem_cleanup_replacements : (Syntax.tm * Syntax.tm) list;
  skolem_cleanup_introduced_classification :
    introduced_symbol_replacement_classification;
}

val disambiguate_skolem_witness_transports :
  skolem_witness_transport list ->
  skolem_witness_transport list * Syntax.tm list

val skolem_witness_cleanup_plan :
  normalize:(Syntax.tm -> Syntax.tm) ->
  alias_names:(string -> string list) ->
  witness_symbols:string list ->
  introduced_symbols:string list ->
  registered_witnesses:(string * Syntax.tm) list ->
  transports:skolem_witness_transport list ->
  Syntax.pf ->
  skolem_witness_cleanup_plan

type skolem_branch_choice_template_expansion_plan = {
  skolem_template_replacement_names : string list;
  skolem_template_local_templates : Syntax.tm list;
}

val skolem_branch_choice_template_expansion_plan :
  alias_names:(string -> string list) ->
  template_limit:int ->
  skolem_witness_transport list ->
  skolem_branch_choice_template_expansion_plan

val skolem_branch_choice_template_replacements :
  skolem_branch_choice_template_expansion_plan ->
  Syntax.tm ->
  (string * Syntax.tm) list

val canonical_witness_name :
  string ->
  string

type registered_choice_expansion = {
  registered_choice_expansion_name : string;
  registered_choice_expansion_terms : Syntax.tm list;
  registered_choice_expansion_replacements : (Syntax.tm * Syntax.tm) list;
}

type registered_choice_expansion_plan =
  | No_registered_choice_expansion
  | Ambiguous_registered_choice_expansion of string list
  | Unique_registered_choice_expansion of registered_choice_expansion

val unique_registered_choice_expansion_plan :
  normalize:(Syntax.tm -> Syntax.tm) ->
  witness_symbols:string list ->
  registered_witnesses:(string * Syntax.tm) list ->
  Syntax.pf ->
  registered_choice_expansion_plan

val substitute_named_term :
  string ->
  Syntax.tm ->
  Syntax.tm

val term_exists_head_types :
  string ->
  Syntax.tm ->
  Syntax.tp list

val term_exists_head_count :
  string ->
  Syntax.tm ->
  int

val term_head :
  Syntax.tm ->
  Syntax.tm

val rewrite_head_symbols_by_alias :
  alias_names:(string -> string list) ->
  (Syntax.tm * Syntax.tm) list ->
  Syntax.tm ->
  Syntax.tm

val skolem_branch_choice_matches_witness :
  normalize:(Syntax.tm -> Syntax.tm) ->
  alias_names:(string -> string list) ->
  Syntax.tm ->
  Vampire_kernel_syntax.skolem_branch_choice ->
  bool

val skolem_branch_witness_symbols :
  Vampire_kernel_syntax.skolem_branch_contract ->
  string list

val skolem_branch_choice_for_witness :
  alias_names:(string -> string list) ->
  Vampire_kernel_syntax.skolem_branch_contract list ->
  string ->
  (Vampire_kernel_syntax.skolem_branch_contract
   * Vampire_kernel_syntax.skolem_branch_choice) option

val skolem_branch_has_proposition_role :
  string ->
  Vampire_kernel_syntax.skolem_branch_contract ->
  bool

val skolem_branch_choice_matching_witness :
  alias_names:(string -> string list) ->
  string ->
  Vampire_kernel_syntax.skolem_branch_contract ->
  Vampire_kernel_syntax.skolem_branch_choice option

val skolem_branch_contract_choice_for_witness :
  alias_names:(string -> string list) ->
  branch_matches_formula:(Syntax.tm -> Syntax.tm option -> bool) ->
  witness:string ->
  source:Syntax.tm ->
  result:Syntax.tm ->
  Vampire_kernel_syntax.skolem_branch_contract list ->
  (Vampire_kernel_syntax.skolem_branch_contract
   * Vampire_kernel_syntax.skolem_branch_choice option) option

type skolem_branch_choice_instantiation = {
  skolem_choice_body : Syntax.tm;
  skolem_choice_predicate : Syntax.tm;
  skolem_choice_witnessed_body : Syntax.tm option;
}

type skolem_choice_transport_obligation = {
  skolem_transport_from_body : Syntax.tm;
  skolem_transport_to_body : Syntax.tm;
}

type skolem_choice_transport_terms = {
  skolem_transport_epsilon_witness : Syntax.tm;
  skolem_transport_epsilon_body : Syntax.tm;
  skolem_transport_witnessed_body : Syntax.tm option;
  skolem_transport_obligation : skolem_choice_transport_obligation option;
}

type skolem_choice_replay_step = {
  skolem_replay_body : Syntax.tm;
  skolem_replay_predicate : Syntax.tm;
  skolem_replay_choice_witness : Syntax.tm;
  skolem_replay_registered_witness : Syntax.tm;
  skolem_replay_choice_proof : Syntax.pf;
  skolem_replay_instantiated_body : Syntax.tm;
  skolem_replay_replacements : (Syntax.tm * Syntax.tm) list;
  skolem_replay_transport_obligation :
    skolem_choice_transport_obligation option;
}

val skolem_choice_transport_terms :
  normalize:(Syntax.tm -> Syntax.tm) ->
  eps_symbol:string ->
  skolem_branch_choice_instantiation ->
  skolem_choice_transport_terms

val skolem_choice_replay_step :
  ?registered_witness:Syntax.tm ->
  ?record_replacement:bool ->
  normalize:(Syntax.tm -> Syntax.tm) ->
  choice_theorem:string ->
  eps_symbol:string ->
  witness_type:Syntax.tp ->
  target_witness:Syntax.tm ->
  proof:Syntax.pf ->
  replacements:(Syntax.tm * Syntax.tm) list ->
  skolem_branch_choice_instantiation ->
  skolem_choice_replay_step

val lift_skolem_branch_choice_instantiation :
  ambient_shift:int ->
  skolem_branch_choice_instantiation ->
  skolem_branch_choice_instantiation

val skolem_branch_choice_instantiation :
  normalize:(Syntax.tm -> Syntax.tm) ->
  alias_names:(string -> string list) ->
  replacements:(Syntax.tm * Syntax.tm) list ->
  substitution_name:string option ->
  target_witness:Syntax.tm ->
  witness_type:Syntax.tp ->
  Vampire_kernel_syntax.skolem_branch_choice list ->
  skolem_branch_choice_instantiation option

val skolem_branch_choice_body :
  normalize:(Syntax.tm -> Syntax.tm) ->
  alias_names:(string -> string list) ->
  replacements:(Syntax.tm * Syntax.tm) list ->
  substitution_name:string option ->
  target_witness:Syntax.tm ->
  witness_type:Syntax.tp ->
  Vampire_kernel_syntax.skolem_branch_choice list ->
  Syntax.tm option

type skolem_helper_record = {
  skolem_helper_index : int;
  skolem_helper_tps : Syntax.tp list;
  skolem_helper_source : Syntax.tm;
  skolem_helper_target : Syntax.tm;
}

val skolem_helper_records :
  Syntax.tm list ->
  skolem_helper_record list

val term_contains_exists_head :
  string ->
  Syntax.tm ->
  bool

val replace_exact_terms_in_term :
  (Syntax.tm * Syntax.tm) list ->
  Syntax.tm ->
  Syntax.tm

val skolem_helper_target_compatible :
  normalize_at_depth:(int -> Syntax.tm -> Syntax.tm) ->
  exists_head:string ->
  int ->
  Syntax.tm ->
  Syntax.tm ->
  bool

val matching_skolem_helper :
  normalize_at_depth:(int -> Syntax.tm -> Syntax.tm) ->
  raw_normalize:(Syntax.tm -> Syntax.tm) ->
  exists_head:string ->
  local_depth:int ->
  replacements:(Syntax.tm * Syntax.tm) list ->
  source:Syntax.tm ->
  target:Syntax.tm ->
  skolem_helper_record list ->
  (skolem_helper_record * skolem_helper_record list) option
