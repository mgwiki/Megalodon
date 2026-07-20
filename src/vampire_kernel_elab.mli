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

val bind_result_step_variables :
  result_step_variables:(string * Syntax.tp) list ->
  close_body:(Syntax.pf -> Syntax.pf) ->
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
