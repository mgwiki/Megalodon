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
