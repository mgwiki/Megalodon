(*** Original Megalodon source bindings for Vampire certificates. ***)

type source_proof =
  | GlobalKnown of string * Syntax.tm
  | LocalHyp of int * Syntax.tm
  | Definitional of Syntax.tm * Syntax.pf
  | Generated of Syntax.tm * Syntax.pf

type source_context = {
  proof_delta : (string, int * Syntax.tm) Hashtbl.t;
  symbol_table : (string, int * Syntax.tp) Hashtbl.t;
  term_context : Syntax.tp list;
  local_term_projection : int option list;
  local_hypotheses : (string * Syntax.tm) list;
  local_definitions : (string * Syntax.tp * Syntax.tm) list;
}

type audit = {
  total : int;
  known_checked : int;
  known_missing : int;
  known_mismatch : int;
  local_checked : int;
  local_missing : int;
  local_mismatch : int;
  definition_resolved : int;
  local_definition_matched : int;
  definition_missing : int;
  generated_checked : int;
  unresolved : int;
  source_proofs : (string * Syntax.pf) list;
  resolved : (string * source_proof) list;
}

val resolve :
  ?strict:bool ->
  source_context ->
  Vampire_cert_v1.core_native_source_binding list ->
  audit
