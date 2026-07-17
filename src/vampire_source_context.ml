(*** Original Megalodon source bindings for Vampire certificates. ***)

open Syntax

type source_proof =
  | GlobalKnown of string * tm
  | LocalHyp of int * tm
  | Definitional of tm * pf
  | Generated of tm * pf

type source_context = {
  proof_delta : (string, int * tm) Hashtbl.t;
  known_table : (string, string) Hashtbl.t;
  symbol_table : (string, int * tp) Hashtbl.t;
  term_context : tp list;
  local_term_projection : int option list;
  local_terms : (string * int * tp) list;
  local_hypotheses : (string * tm) list;
  local_definitions : (string * tp * tm) list;
}

type source_issue = {
  issue_step : string;
  issue_kind : string;
  issue_name : string;
  issue_hash : string;
  issue_reason : string;
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
  conjecture_checked : int;
  unresolved : int;
  source_proofs : (string * pf) list;
  resolved : (string * source_proof) list;
  issues : source_issue list;
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
  local_definition_matched = 0;
  definition_missing = 0;
  generated_checked = 0;
  conjecture_checked = 0;
  unresolved = 0;
  source_proofs = [];
  resolved = [];
  issues = [];
}

let known_source_kind kind =
  kind = "known" || kind = "axiom"

let definition_source_kind kind =
  kind = "def" || kind = "definition" || kind = "local_definition"

let local_definition_source_kind kind =
  kind = "local_definition"

let local_source_kind kind =
  kind = "local_fact"

let generated_source_kind kind =
  kind = "set_reflexivity" || kind = "local_set_reflexivity"

let conjecture_source_kind kind =
  kind = "conjecture" || kind = "negated_conjecture"

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

let megalodon_eq_poly_hash =
  "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a"

let rec collapse_expanded_equality = function
  | All (Ar (left_tp, Ar (right_tp, Prop)),
         Imp (Ap (Ap (DB 0, left_a), right_a),
              Ap (Ap (DB 0, right_b), left_b)))
    when left_tp = right_tp && left_a = left_b && right_a = right_b ->
      begin
        try
          let left = tmshift 0 (-1) left_a in
          let right = tmshift 0 (-1) right_a in
          Some (Ap (Ap (TpAp (TmH megalodon_eq_poly_hash, left_tp), left), right))
        with NegDB -> None
      end
  | All (tp, body) ->
      Option.map (fun body -> All (tp, body)) (collapse_expanded_equality body)
  | Imp (left, right) ->
      begin match collapse_expanded_equality left, collapse_expanded_equality right with
      | Some left, Some right -> Some (Imp (left, right))
      | Some left, None -> Some (Imp (left, right))
      | None, Some right -> Some (Imp (left, right))
      | None, None -> None
      end
  | _ -> None

let equality_sides ?default_tp = function
  | Ap (Ap (TpAp (TmH h, tp), left), right) when h = megalodon_eq_poly_hash ->
      Some (tp, left, right)
  | Ap (Ap (TmH h, left), right) when h = "=" || h = "eq" ->
      begin match default_tp with
      | Some tp -> Some (tp, left, right)
      | None -> None
      end
  | _ -> None

let equality_atom tp left right =
  Ap (Ap (TpAp (TmH megalodon_eq_poly_hash, tp), left), right)

let expanded_equality_prop tp left right =
  All
    (Ar (tp, Ar (tp, Prop)),
     Imp
       (Ap (Ap (DB 0, tmshift 0 1 left), tmshift 0 1 right),
        Ap (Ap (DB 0, tmshift 0 1 right), tmshift 0 1 left)))

let positive_equality_symmetry_proof tp left right proof =
  let predicate_sort = Ar (tp, Ar (tp, Prop)) in
  let premise =
    Ap (Ap (DB 0, tmshift 0 1 right), tmshift 0 1 left)
  in
  let motive =
    Lam (tp, Lam (tp, Ap (Ap (DB 2, DB 0), DB 1)))
  in
  TLam
    (predicate_sort,
     PLam
       (premise,
        PPfAp
          (PTmAp (pfshift 0 1 (pftmshift 0 1 proof), motive),
           Hyp 0)))

let rec tm_mentions_head name = function
  | TmH h -> h = name
  | TpAp (body, _) -> tm_mentions_head name body
  | Ap (left, right)
  | Imp (left, right) ->
      tm_mentions_head name left || tm_mentions_head name right
  | Lam (_, body)
  | All (_, body) ->
      tm_mentions_head name body
  | DB _ | Prim _ -> false

let local_definition_delta context =
  let rec localize depth = function
    | TmH name ->
        begin match List.find_opt (fun (local_name, _, _) -> local_name = name) context.local_terms with
        | Some (_, index, _) -> DB (index + depth)
        | None -> TmH name
        end
    | TpAp (body, tp) -> TpAp (localize depth body, tp)
    | Ap (left, right) -> Ap (localize depth left, localize depth right)
    | Lam (tp, body) -> Lam (tp, localize (depth + 1) body)
    | Imp (left, right) -> Imp (localize depth left, localize depth right)
    | All (tp, body) -> All (tp, localize (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  in
  let delta = Hashtbl.copy context.proof_delta in
  List.iter
    (fun (name, _, definition) ->
       Hashtbl.replace delta name (0, localize 0 definition))
    context.local_definitions;
  delta

let equality_candidate_proof tp left right =
  TLam
    (Ar (tp, Ar (tp, Prop)),
     PLam
       (Ap (Ap (DB 0, tmshift 0 1 left), tmshift 0 1 right),
        Hyp 0))

let rec local_definition_candidate_proof default_tp = function
  | All (tp, body) ->
      begin match local_definition_candidate_proof default_tp body with
      | Some proof -> Some (TLam (tp, proof))
      | None -> None
      end
  | Imp (left, right) ->
      Some (PLam (left, Hyp 0))
  | proposition ->
      begin match equality_sides ~default_tp proposition with
      | Some (eq_tp, left, right) ->
          Some (equality_candidate_proof eq_tp left right)
      | None -> None
      end

let local_definition_candidate_checks context proof proposition =
  try
    match check_propofpf
            (local_definition_delta context)
            context.symbol_table
            context.term_context
            []
            proof
            proposition
            []
    with
    | Some _ -> true
    | None -> false
  with _ -> false

let source_symbol_type context names =
  let rec find = function
    | [] -> None
    | name :: rest ->
        begin match Hashtbl.find_opt context.symbol_table name with
        | Some (0, tp) -> Some tp
        | Some _ | None -> find rest
        end
  in
  find names

let global_definition_proof context names proposition =
  let default_tp =
    match source_symbol_type context names with
    | Some tp -> tp
    | None -> Prop
  in
  match local_definition_candidate_proof default_tp proposition with
  | Some proof when local_definition_candidate_checks context proof proposition ->
      Some proof
  | Some _ | None ->
      if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
        prerr_endline
          ("source-context global definition mismatch for "
           ^ String.concat "," names
           ^ ": proposition="
           ^ tm_to_str proposition);
      None

let proof_proves context proof proposition =
  try
    match check_propofpf context.proof_delta context.symbol_table [] [] proof proposition [] with
    | Some _ -> true
    | None -> false
  with _ -> false

let proof_proves_in_context context term_context proof proposition =
  try
    match check_propofpf context.proof_delta context.symbol_table term_context [] proof proposition [] with
    | Some _ -> true
    | None -> false
  with _ -> false

let equality_symmetry_proof context term_context proof proposition =
  let target_candidates =
    match collapse_expanded_equality proposition with
    | Some collapsed when collapsed <> proposition -> [proposition; collapsed]
    | _ -> [proposition]
  in
  let rec search = function
    | [] -> None
    | target :: rest ->
        begin match equality_sides target with
        | Some (tp, left, right) ->
            let source = equality_atom tp right left in
            let expanded_source = expanded_equality_prop tp right left in
            if proof_proves_in_context context term_context proof source
               || proof_proves_in_context context term_context proof expanded_source
            then
              let symmetry_proof = positive_equality_symmetry_proof tp right left proof in
              if proof_proves_in_context context term_context symmetry_proof proposition then
                Some symmetry_proof
              else if proof_proves_in_context context term_context symmetry_proof target then
                Some symmetry_proof
              else
                search rest
            else
              search rest
        | None -> search rest
        end
  in
  search target_candidates

let rec proof_for_prop context term_context proof proposition =
  if proof_proves_in_context context term_context proof proposition then
    Some proof
  else
    let collapsed_or_symmetry =
      match collapse_expanded_equality proposition with
      | Some collapsed when collapsed <> proposition ->
          if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
            prerr_endline
              ("source-context collapsed expanded equality proposition: "
               ^ tm_to_str collapsed);
          if proof_proves_in_context context term_context proof collapsed
             && proof_proves_in_context context term_context proof proposition
          then Some proof
          else equality_symmetry_proof context term_context proof proposition
      | _ -> equality_symmetry_proof context term_context proof proposition
    in
    match collapsed_or_symmetry with
    | Some proof -> Some proof
    | None ->
    match proposition with
    | All (tp, body) ->
        let applied = PTmAp (pftmshift 0 1 proof, DB 0) in
        begin match proof_for_prop context (tp :: term_context) applied body with
        | Some body_proof ->
            let wrapped = TLam (tp, body_proof) in
            if proof_proves_in_context context term_context wrapped proposition then
              Some wrapped
            else
              None
        | None when not (free_in_tm_p body 0) ->
            begin
              try
                let body_without_unused = tmshift 0 (-1) body in
                match proof_for_prop context term_context proof body_without_unused with
                | Some body_proof ->
                    let wrapped = TLam (tp, body_proof) in
                    if proof_proves_in_context context term_context wrapped proposition then
                      Some wrapped
                    else
                      None
                | None -> None
              with NegDB -> None
            end
        | None -> None
        end
    | _ -> None

let rec known_proof_for_prop context hash proposition =
  let proof = Known hash in
  match proof_for_prop context [] proof proposition with
  | Some _ as result -> result
  | None ->
      (* Compatibility fallback for generated source facts with an unused
         leading binder but no corresponding binder in the original theorem. *)
      match proposition with
    | All (tp, body) when not (free_in_tm_p body 0) ->
        begin
          try
            let body_without_unused = tmshift 0 (-1) body in
            match known_proof_for_prop context hash body_without_unused with
            | Some body_proof ->
                let wrapped = TLam (tp, body_proof) in
                if proof_proves context wrapped proposition then Some wrapped else None
            | None -> None
          with NegDB -> None
        end
    | _ -> None

let known_candidate_hashes context binding =
  let open Vampire_cert_v1 in
  let add candidate candidates =
    if candidate = "" || List.mem candidate candidates then candidates
    else candidate :: candidates
  in
  let add_name name candidates =
    if name = "" then candidates
    else
      match Hashtbl.find_opt context.known_table name with
      | Some hash -> add hash candidates
      | None -> candidates
  in
  []
  |> add binding.core_native_source_hash
  |> add_name binding.core_native_source_name
  |> add_name binding.core_native_tptp_name
  |> List.rev

let resolve_known_source context binding proposition =
  let candidates = known_candidate_hashes context binding in
  let rec search = function
    | [] -> None
    | candidate :: rest ->
        if Hashtbl.mem context.proof_delta candidate then
          match known_proof_for_prop context candidate proposition with
          | Some proof -> Some (candidate, proof)
          | None -> search rest
        else
          search rest
  in
  match search candidates with
  | Some checked -> `Checked checked
  | None when List.exists (Hashtbl.mem context.proof_delta) candidates ->
      `Mismatch candidates
  | None ->
      `Missing candidates

let debug_known_hash_mismatch hash proposition =
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
    prerr_endline
      ("source-context known hash mismatch for "
       ^ hash
       ^ ": proposition="
       ^ tm_to_str proposition)

let project_local_term_context context tm =
  let rec project depth tm =
    match tm with
    | DB index when index < depth -> Some tm
    | DB index ->
        let source_index = index - depth in
        begin match List.nth_opt context.local_term_projection source_index with
        | Some (Some target_index) -> Some (DB (target_index + depth))
        | _ -> None
        end
    | TmH _ | Prim _ -> Some tm
    | TpAp (body, tp) ->
        Option.map (fun body -> TpAp (body, tp)) (project depth body)
    | Ap (left, right) ->
        begin match project depth left, project depth right with
        | Some left, Some right -> Some (Ap (left, right))
        | _ -> None
        end
    | Lam (tp, body) ->
        Option.map (fun body -> Lam (tp, body)) (project (depth + 1) body)
    | Imp (left, right) ->
        begin match project depth left, project depth right with
        | Some left, Some right -> Some (Imp (left, right))
        | _ -> None
        end
    | All (tp, body) ->
        Option.map (fun body -> All (tp, body)) (project (depth + 1) body)
  in
  project 0 tm

let hyp_proves context index proposition =
  try
    let local_props = List.map snd context.local_hypotheses in
    match check_propofpf
            (local_definition_delta context)
            context.symbol_table
            context.term_context
            local_props
            (Hyp index)
            proposition
            []
    with
    | Some _ -> true
    | None -> false
  with _ -> false

let local_hyp_index context name proposition =
  let projected_proposition =
    match project_local_term_context context proposition with
    | Some proposition -> proposition
    | None -> proposition
  in
  let rec scan i = function
    | [] -> None
    | (local_name, local_prop) :: rest ->
        if local_name = name then
          match conv local_prop projected_proposition (local_definition_delta context) [] with
          | Some _ -> Some i
          | None ->
              if hyp_proves context i projected_proposition then Some i
              else begin
                if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
                  prerr_endline
                    ("source-context local hypothesis mismatch for "
                     ^ name
                     ^ ": local="
                     ^ tm_to_str local_prop
                     ^ " certificate="
                     ^ tm_to_str proposition
                     ^ " projected="
                     ^ tm_to_str projected_proposition);
                None
              end
        else
          scan (i + 1) rest
  in
  scan 0 context.local_hypotheses

let local_definition_matches context name =
  List.find_opt (fun (local_name, _, _) -> local_name = name) context.local_definitions

let local_definition_proof context name proposition =
  match local_definition_matches context name with
  | None -> None
  | Some (_, tp, _) ->
      if not (tm_mentions_head name proposition) then
        None
      else
        begin match local_definition_candidate_proof tp proposition with
        | Some proof when local_definition_candidate_checks context proof proposition ->
            Some proof
        | Some _ | None ->
            if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then
              prerr_endline
                ("source-context local definition mismatch for "
                 ^ name
                 ^ ": proposition="
                 ^ tm_to_str proposition);
            None
        end

let add_source_proof step proof audit =
  { audit with source_proofs = (step, proof) :: audit.source_proofs }

let add_resolved step source_proof audit =
  { audit with resolved = (step, source_proof) :: audit.resolved }

let add_issue binding reason audit =
  let open Vampire_cert_v1 in
  {
    audit with
    issues =
      {
        issue_step = binding.core_native_source_step;
        issue_kind = binding.core_native_source_map_kind;
        issue_name = binding.core_native_source_name;
        issue_hash = binding.core_native_source_hash;
        issue_reason = reason;
      } :: audit.issues;
  }

let resolve_one context audit binding =
  let open Vampire_cert_v1 in
  let step = binding.core_native_source_step in
  let kind = binding.core_native_source_map_kind in
  let hash = binding.core_native_source_hash in
  let proposition = binding.core_native_source_proposition in
  let audit = { audit with total = audit.total + 1 } in
  if known_source_kind kind then
    match resolve_known_source context binding proposition with
    | `Checked (checked_hash, checked_proof) ->
        audit
        |> add_source_proof step checked_proof
        |> add_resolved step (GlobalKnown (checked_hash, proposition))
        |> fun audit -> { audit with known_checked = audit.known_checked + 1 }
    | `Missing _ ->
        { audit with known_missing = audit.known_missing + 1 }
        |> add_issue binding "known_missing"
    | `Mismatch candidates ->
        List.iter (fun candidate -> debug_known_hash_mismatch candidate proposition) candidates;
        { audit with known_mismatch = audit.known_mismatch + 1 }
        |> add_issue binding "known_mismatch"
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
          |> add_issue binding "local_mismatch"
        else
          { audit with local_missing = audit.local_missing + 1 }
          |> add_issue binding "local_missing"
    end
  else if definition_source_kind kind then
    if local_definition_source_kind kind then
      match local_definition_proof context binding.core_native_source_name proposition with
      | Some proof ->
          audit
          |> add_source_proof step proof
          |> add_resolved step (Definitional (proposition, proof))
          |> fun audit -> { audit with local_definition_matched = audit.local_definition_matched + 1 }
      | None ->
          { audit with definition_missing = audit.definition_missing + 1 }
          |> add_issue binding "definition_missing"
    else if hash <> "" && Hashtbl.mem context.proof_delta hash then
      match
        global_definition_proof
          context
          [binding.core_native_source_name; binding.core_native_tptp_name; hash]
          proposition
      with
      | Some proof ->
          audit
          |> add_source_proof step proof
          |> add_resolved step (Definitional (proposition, proof))
          |> fun audit -> { audit with definition_resolved = audit.definition_resolved + 1 }
      | None ->
          { audit with definition_missing = audit.definition_missing + 1 }
          |> add_issue binding "definition_missing"
    else
      { audit with definition_missing = audit.definition_missing + 1 }
      |> add_issue binding "definition_missing"
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
  else if binding.core_native_certificate_source_kind = "negated_conjecture"
          && conjecture_source_kind kind then
    { audit with conjecture_checked = audit.conjecture_checked + 1 }
  else
    { audit with unresolved = audit.unresolved + 1 }
    |> add_issue binding "unresolved"

let resolve ?(strict=false) context bindings =
  let audit =
    List.fold_left (resolve_one context) empty_audit bindings
  in
  let audit = {
    audit with
    source_proofs = List.rev audit.source_proofs;
    resolved = List.rev audit.resolved;
    issues = List.rev audit.issues;
  } in
  if strict
     && (audit.known_missing > 0
         || audit.known_mismatch > 0
         || audit.local_missing > 0
         || audit.local_mismatch > 0
         || audit.definition_missing > 0
         || audit.unresolved > 0) then
    raise
      (Vampire_cert_v1.Error
         "strict source-context audit failed: at least one source did not resolve to a checked proof in the Megalodon context");
  audit
