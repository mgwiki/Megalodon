(*** Original Megalodon source bindings for Vampire certificates. ***)

open Syntax

type source_proof =
  | GlobalKnown of string * tm
  | LocalHyp of int * tm
  | Definitional of tm * pf
  | Generated of tm * pf

type source_context = {
  proof_delta : (string, int * tm) Hashtbl.t;
  symbol_table : (string, int * tp) Hashtbl.t;
  term_context : tp list;
  local_hypotheses : (string * tm) list;
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
  definition_missing : int;
  generated_checked : int;
  unresolved : int;
  source_proofs : (string * pf) list;
  resolved : (string * source_proof) list;
}

let empty_audit = {
  total = 0;
  known_checked = 0;
  known_missing = 0;
  known_mismatch = 0;
  local_checked = 0;
  local_missing = 0;
  local_mismatch = 0;
  definition_resolved = 0;
  definition_missing = 0;
  generated_checked = 0;
  unresolved = 0;
  source_proofs = [];
  resolved = [];
}

let known_source_kind kind =
  kind = "known" || kind = "axiom"

let definition_source_kind kind =
  kind = "def" || kind = "definition" || kind = "local_definition"

let local_source_kind kind =
  kind = "local_fact"

let generated_source_kind kind =
  kind = "set_reflexivity" || kind = "local_set_reflexivity"

let rec generated_set_reflexivity_proof = function
  | All (tp, body) ->
      begin match generated_set_reflexivity_proof body with
      | Some proof -> Some (TLam (tp, proof))
      | None -> None
      end
  | Imp (left, right) when left = right ->
      Some (PLam (left, Hyp 0))
  | proposition ->
      Vampire_cert_v1.native_core_reflexive_eq_proof proposition

let known_hash_proves context hash proposition =
  try
    match check_propofpf context.proof_delta context.symbol_table [] [] (Known hash) proposition [] with
    | Some _ -> true
    | None -> false
  with _ -> false

let hyp_proves context index proposition =
  try
    let local_props = List.map snd context.local_hypotheses in
    match check_propofpf context.proof_delta context.symbol_table context.term_context local_props (Hyp index) proposition [] with
    | Some _ -> true
    | None -> false
  with _ -> false

let local_hyp_index context name proposition =
  let rec scan i = function
    | [] -> None
    | (local_name, local_prop) :: rest ->
        if local_name = name then
          match conv local_prop proposition context.proof_delta [] with
          | Some _ -> Some i
          | None -> if hyp_proves context i proposition then Some i else None
        else
          scan (i + 1) rest
  in
  scan 0 context.local_hypotheses

let add_source_proof step proof audit =
  { audit with source_proofs = (step, proof) :: audit.source_proofs }

let add_resolved step source_proof audit =
  { audit with resolved = (step, source_proof) :: audit.resolved }

let resolve_one context audit binding =
  let open Vampire_cert_v1 in
  let step = binding.core_native_source_step in
  let kind = binding.core_native_source_map_kind in
  let hash = binding.core_native_source_hash in
  let proposition = binding.core_native_source_proposition in
  let audit = { audit with total = audit.total + 1 } in
  if hash <> "" && known_source_kind kind then
    if not (Hashtbl.mem context.proof_delta hash) then
      { audit with known_missing = audit.known_missing + 1 }
    else if known_hash_proves context hash proposition then
      audit
      |> add_source_proof step (Known hash)
      |> add_resolved step (GlobalKnown (hash, proposition))
      |> fun audit -> { audit with known_checked = audit.known_checked + 1 }
    else
      { audit with known_mismatch = audit.known_mismatch + 1 }
  else if local_source_kind kind then
    begin match local_hyp_index context binding.core_native_source_name proposition with
    | Some index ->
        audit
        |> add_source_proof step (Hyp index)
        |> add_resolved step (LocalHyp (index, proposition))
        |> fun audit -> { audit with local_checked = audit.local_checked + 1 }
    | None ->
        if List.exists (fun (name, _) -> name = binding.core_native_source_name) context.local_hypotheses then
          { audit with local_mismatch = audit.local_mismatch + 1 }
        else
          { audit with local_missing = audit.local_missing + 1 }
    end
  else if definition_source_kind kind then
    if hash <> "" && Hashtbl.mem context.proof_delta hash then
      { audit with definition_resolved = audit.definition_resolved + 1 }
    else
      { audit with definition_missing = audit.definition_missing + 1 }
  else if generated_source_kind kind then
    begin match generated_set_reflexivity_proof proposition with
    | Some proof ->
        audit
        |> add_source_proof step proof
        |> add_resolved step (Generated (proposition, proof))
        |> fun audit -> { audit with generated_checked = audit.generated_checked + 1 }
    | _ ->
        raise
          (Vampire_cert_v1.Error
             (step ^ ": generated source " ^ kind
              ^ " is not a provable reflexive Megalodon equality: "
              ^ tm_to_str proposition))
    end
  else
    { audit with unresolved = audit.unresolved + 1 }

let resolve ?(strict=false) context bindings =
  let audit =
    List.fold_left (resolve_one context) empty_audit bindings
  in
  let audit = {
    audit with
    source_proofs = List.rev audit.source_proofs;
    resolved = List.rev audit.resolved;
  } in
  if strict
     && (audit.known_missing > 0
         || audit.known_mismatch > 0
         || audit.local_missing > 0
         || audit.local_mismatch > 0
         || audit.definition_missing > 0) then
    raise
      (Vampire_cert_v1.Error
         "strict source-context audit failed: at least one source did not resolve in the Megalodon context");
  audit
