(*** Deterministic proof-term boundary for the Vampire/Megalodon small kernel. ***)

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
