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

val replace_exact_terms_in_proof :
  normalize:(Syntax.tm -> Syntax.tm) ->
  (Syntax.tm * Syntax.tm) list ->
  Syntax.pf ->
  Syntax.pf

val proof_contains_term_symbol :
  string list ->
  Syntax.pf ->
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

val substitute_named_term :
  string ->
  Syntax.tm ->
  Syntax.tm

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

type skolem_branch_choice_instantiation = {
  skolem_choice_body : Syntax.tm;
  skolem_choice_predicate : Syntax.tm;
}

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
