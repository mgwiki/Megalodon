(*** Deterministic proof-term boundary for the Vampire/Megalodon small kernel. ***)

open Syntax
open Vampire_kernel_syntax

exception Error of string

let error msg = raise (Error msg)

type clause_formula_basis = {
  false_tm : tm;
  or_tm : tm -> tm -> tm;
  atom_tm : tm -> tm;
}

let identity_atom tm = tm

let literal_prop basis = function
  | Pos atom -> basis.atom_tm atom
  | Neg atom -> Imp (basis.atom_tm atom, basis.false_tm)

let rec clause_prop basis = function
  | [] -> basis.false_tm
  | [literal] -> literal_prop basis literal
  | literal :: rest -> basis.or_tm (literal_prop basis literal) (clause_prop basis rest)

type proof_step = {
  step_id : string;
  step_clause : clause;
  step_prop : tm;
  step_proof : pf;
}

let input_step basis ~id ~clause proof =
  {
    step_id = id;
    step_clause = clause;
    step_prop = clause_prop basis clause;
    step_proof = proof;
  }

let db_for_result_variable ~result_step_variables name tp =
  let result_variable_count = List.length result_step_variables in
  let rec find index = function
    | [] -> None
    | (candidate_name, candidate_tp) :: rest ->
        if candidate_name = name && candidate_tp = tp then
          Some (DB (result_variable_count - index - 1))
        else find (index + 1) rest
  in
  find 0 result_step_variables

let first_result_variable_of_type ~result_step_variables tp =
  let result_variable_count = List.length result_step_variables in
  let rec find index = function
    | [] -> None
    | (_, candidate_tp) :: rest ->
        if candidate_tp = tp then Some (DB (result_variable_count - index - 1))
        else find (index + 1) rest
  in
  find 0 result_step_variables

let result_variables_of_type ~result_step_variables tp =
  let result_variable_count = List.length result_step_variables in
  let rec collect index = function
    | [] -> []
    | (_, candidate_tp) :: rest ->
        let tail = collect (index + 1) rest in
        if candidate_tp = tp then DB (result_variable_count - index - 1) :: tail
        else tail
  in
  collect 0 result_step_variables

let bind_result_step_variables ~result_step_variables ~close_body body_proof =
  let body_proof = close_body body_proof in
  List.fold_right
    (fun (_, tp) proof -> TLam (tp, proof))
    result_step_variables
    body_proof

let apply_parent_step_variables
    ?(shift_parent_proof=true)
    ~parent_step_variables
    ~result_step_variables
    ~resolve_parent_variable
    ~missing_parent_variable
    proof =
  let result_variable_count = List.length result_step_variables in
  List.fold_left
    (fun proof (name, tp) ->
       let arg =
         match resolve_parent_variable name tp with
         | Some tm -> tm
         | None -> error (missing_parent_variable name)
       in
       PTmAp (proof, arg))
    (if shift_parent_proof then pftmshift 0 result_variable_count proof else proof)
    parent_step_variables

let open_step_theorem_body_in_result_context
    ?(shift_parent_proof=true)
    ~id
    ~parent_step_variables
    ~result_step_variables
    ~subst
    ~close_witness
    proof =
  let result_variable_count = List.length result_step_variables in
  List.fold_left
    (fun proof (name, tp) ->
       let witness =
         match List.assoc_opt name subst with
         | Some tm -> close_witness tm
         | None ->
             begin match db_for_result_variable ~result_step_variables name tp with
             | Some tm -> tm
             | None ->
                 error
                   (id ^ ": native core open_step_theorem cannot instantiate dropped parent variable "
                    ^ name ^ " without an explicit substitution")
             end
       in
       PTmAp (proof, witness))
    (if shift_parent_proof then pftmshift 0 result_variable_count proof else proof)
    parent_step_variables

let skolem_choice_witness_proof
    ~choice_theorem
    ~eps_symbol
    ~witness_type
    ~predicate
    exists_proof =
  match predicate with
  | Lam (predicate_type, _) when predicate_type = witness_type ->
      let epsilon_witness = Ap (TmH eps_symbol, predicate) in
      epsilon_witness,
      PPfAp (PTmAp (Known choice_theorem, predicate), exists_proof)
  | Lam _ ->
      error "Skolem choice predicate has the wrong witness type"
  | _ ->
      error "Skolem choice predicate is not a lambda"

let church_exists_map_proof
    ~witness_type
    ~source_body
    ~target_body
    ~pointwise_proof
    exists_proof =
  let target_exists_case =
    All (witness_type, Imp (tmshift 1 1 target_body, DB 1))
  in
  let source_body_at_witness = tmshift 1 1 source_body in
  let pointwise_at_witness =
    PPfAp
      (PTmAp
         (pftmshift 0 2 (pfshift 0 2 pointwise_proof), DB 0),
       Hyp 0)
  in
  let target_body_at_witness =
    PPfAp (PTmAp (Hyp 1, DB 0), pointwise_at_witness)
  in
  let source_case =
    TLam (witness_type, PLam (source_body_at_witness, target_body_at_witness))
  in
  TLam
    (Prop,
     PLam
       (target_exists_case,
        PPfAp
          (PTmAp (pftmshift 0 1 (pfshift 0 1 exists_proof), DB 0),
           source_case)))

let church_exists_elim_proof ~target_prop ~continuation exists_proof =
  PPfAp (PTmAp (exists_proof, target_prop), continuation)

let replace_exact_terms_in_proof ~normalize replacements proof =
  let rec replace_top_opt depth tm =
    match
      replacements
      |> List.find_opt
           (fun (needle, _) ->
              normalize tm = (tmshift 0 depth needle |> normalize))
    with
    | Some (_, replacement) -> tmshift 0 depth replacement
    | None -> tm
  in
  let rec replace_tm depth tm =
    let replaced = replace_top_opt depth tm in
    if replaced <> tm then replaced
    else
      let rewritten =
        match tm with
        | TmH _ | DB _ | Prim _ -> tm
        | TpAp (body, tp) -> TpAp (replace_tm depth body, tp)
        | Ap (left, right) ->
            Ap (replace_tm depth left, replace_tm depth right)
        | Lam (tp, body) ->
            Lam (tp, replace_tm (depth + 1) body)
        | Imp (left, right) ->
            Imp (replace_tm depth left, replace_tm depth right)
        | All (tp, body) ->
            All (tp, replace_tm (depth + 1) body)
      in
      replace_top_opt depth rewritten
  in
  let rec replace_pf depth proof =
    match proof with
    | PTpAp (body, tp) -> PTpAp (replace_pf depth body, tp)
    | PTmAp (body, tm) ->
        PTmAp (replace_pf depth body, replace_tm depth tm)
    | PPfAp (left, right) ->
        PPfAp (replace_pf depth left, replace_pf depth right)
    | PLam (prop, body) ->
        PLam (replace_tm depth prop, replace_pf depth body)
    | TLam (tp, body) -> TLam (tp, replace_pf (depth + 1) body)
    | Hyp _ | Known _ -> proof
  in
  replace_pf 0 proof

let rec term_contains_symbol names = function
  | TmH name -> List.mem name names
  | TpAp (body, _) -> term_contains_symbol names body
  | Ap (left, right) | Imp (left, right) ->
      term_contains_symbol names left || term_contains_symbol names right
  | Lam (_, body) | All (_, body) -> term_contains_symbol names body
  | DB _ | Prim _ -> false

let proof_contains_term_symbol names proof =
  let rec pf_contains = function
    | PTpAp (body, _) -> pf_contains body
    | PTmAp (body, tm) ->
        pf_contains body || term_contains_symbol names tm
    | PPfAp (left, right) -> pf_contains left || pf_contains right
    | PLam (prop, body) ->
        term_contains_symbol names prop || pf_contains body
    | TLam (_, body) -> pf_contains body
    | Hyp _ | Known _ -> false
  in
  pf_contains proof

let proof_contains_exact_term ~normalize needle proof =
  let needle = normalize needle in
  let shifted_needle depth =
    tmshift 0 depth needle |> normalize
  in
  let rec tm_contains depth tm =
    normalize tm = shifted_needle depth
    ||
    match tm with
    | TpAp (body, _) -> tm_contains depth body
    | Ap (left, right) | Imp (left, right) ->
        tm_contains depth left || tm_contains depth right
    | Lam (_, body) | All (_, body) -> tm_contains (depth + 1) body
    | DB _ | TmH _ | Prim _ -> false
  in
  let rec pf_contains depth = function
    | PTpAp (body, _) -> pf_contains depth body
    | PTmAp (body, tm) -> pf_contains depth body || tm_contains depth tm
    | PPfAp (left, right) ->
        pf_contains depth left || pf_contains depth right
    | PLam (prop, body) ->
        tm_contains depth prop || pf_contains depth body
    | TLam (_, body) -> pf_contains (depth + 1) body
    | Hyp _ | Known _ -> false
  in
  pf_contains 0 proof

let first_enclosing_term_with_symbol names proof =
  let rec tm_detail path enclosing = function
    | TmH name when List.mem name names -> Some (path, enclosing)
    | TmH _ | DB _ | Prim _ -> None
    | TpAp (body, _) as tm -> tm_detail (path ^ ".tp") tm body
    | Ap (left, right) as tm ->
        begin match tm_detail (path ^ ".left") tm left with
        | Some _ as found -> found
        | None -> tm_detail (path ^ ".right") tm right
        end
    | Lam (_, body) | All (_, body) as tm ->
        tm_detail (path ^ ".body") tm body
    | Imp (left, right) as tm ->
        begin match tm_detail (path ^ ".left") tm left with
        | Some _ as found -> found
        | None -> tm_detail (path ^ ".right") tm right
        end
  in
  let tm_detail path tm = tm_detail path tm tm in
  let rec pf_detail path = function
    | PTpAp (body, _) -> pf_detail (path ^ ".tp") body
    | PTmAp (body, tm) ->
        begin match pf_detail (path ^ ".proof") body with
        | Some _ as found -> found
        | None -> tm_detail (path ^ ".term") tm
        end
    | PPfAp (left, right) ->
        begin match pf_detail (path ^ ".left") left with
        | Some _ as found -> found
        | None -> pf_detail (path ^ ".right") right
        end
    | PLam (prop, body) ->
        begin match tm_detail (path ^ ".prop") prop with
        | Some _ as found -> found
        | None -> pf_detail (path ^ ".body") body
        end
    | TLam (_, body) -> pf_detail (path ^ ".body") body
    | Hyp _ | Known _ -> None
  in
  pf_detail "root" proof

let enclosing_terms_with_symbol ~normalize names proof =
  let terms = ref [] in
  let add_choice enclosing =
    terms := normalize enclosing :: !terms
  in
  let rec tm_collect enclosing = function
    | TmH name when List.mem name names -> add_choice enclosing
    | TmH _ | DB _ | Prim _ -> ()
    | TpAp (body, _) as tm -> tm_collect tm body
    | Ap (left, right) as tm ->
        tm_collect tm left;
        tm_collect tm right
    | Lam (_, body) | All (_, body) as tm ->
        tm_collect tm body
    | Imp (left, right) as tm ->
        tm_collect tm left;
        tm_collect tm right
  in
  let tm_collect tm = tm_collect tm tm in
  let rec pf_collect = function
    | PTpAp (body, _) -> pf_collect body
    | PTmAp (body, tm) ->
        pf_collect body;
        tm_collect tm
    | PPfAp (left, right) ->
        pf_collect left;
        pf_collect right
    | PLam (prop, body) ->
        tm_collect prop;
        pf_collect body
    | TLam (_, body) -> pf_collect body
    | Hyp _ | Known _ -> ()
  in
  pf_collect proof;
  !terms |> List.sort_uniq compare

let enclosing_terms_with_symbol_depth ~normalize names proof =
  let terms = ref [] in
  let add_choice depth enclosing =
    terms := (depth, normalize enclosing) :: !terms
  in
  let rec tm_collect depth enclosing = function
    | TmH name when List.mem name names ->
        add_choice depth enclosing
    | TmH _ | DB _ | Prim _ -> ()
    | TpAp (body, _) as tm -> tm_collect depth tm body
    | Ap (left, right) as tm ->
        tm_collect depth tm left;
        tm_collect depth tm right
    | Lam (_, body) | All (_, body) as tm ->
        tm_collect (depth + 1) tm body
    | Imp (left, right) as tm ->
        tm_collect depth tm left;
        tm_collect depth tm right
  in
  let tm_collect depth tm = tm_collect depth tm tm in
  let rec pf_collect depth = function
    | PTpAp (body, _) -> pf_collect depth body
    | PTmAp (body, tm) ->
        pf_collect depth body;
        tm_collect depth tm
    | PPfAp (left, right) ->
        pf_collect depth left;
        pf_collect depth right
    | PLam (prop, body) ->
        tm_collect depth prop;
        pf_collect depth body
    | TLam (_, body) -> pf_collect (depth + 1) body
    | Hyp _ | Known _ -> ()
  in
  pf_collect 0 proof;
  !terms |> List.sort_uniq compare

let registered_witness_term_replacements
    ~normalize
    ~witness_symbols:_
    replacements
    proof =
  replacements
  |> List.filter_map
       (fun (name, witness) ->
          let witness = normalize witness in
          if proof_contains_exact_term ~normalize witness proof then
            Some (witness, TmH name)
          else
            None)
  |> List.sort_uniq compare

let contract_backed_branch_choice_term_replacements
    ~normalize
    ~choice_symbols
    ~replacement_names
    ~definition
    proof =
  let rec can_shift_down amount cutoff = function
    | DB index -> index < cutoff || index >= cutoff + amount
    | TpAp (body, _) -> can_shift_down amount cutoff body
    | Ap (left, right) | Imp (left, right) ->
        can_shift_down amount cutoff left
        && can_shift_down amount cutoff right
    | Lam (_, body) | All (_, body) ->
        can_shift_down amount (cutoff + 1) body
    | TmH _ | Prim _ -> true
  in
  enclosing_terms_with_symbol_depth
    ~normalize
    choice_symbols
    proof
  |> List.concat_map
       (fun (depth, actual_choice) ->
          replacement_names
          |> List.filter_map
               (fun replacement_name ->
                  try
                    if can_shift_down depth 0 actual_choice then
                      let local_template =
                        tmshift 0 (-depth) actual_choice
                        |> normalize
                      in
                      Some
                        (replacement_name, actual_choice, definition,
                         local_template)
                    else
                      None
                  with _ -> None))
  |> List.sort_uniq compare

type skolem_witness_transport = {
  skolem_transport_name : string;
  skolem_transport_choice_occurrence : tm;
  skolem_transport_definition : tm;
  skolem_transport_local_template : tm;
}

let contract_backed_skolem_witness_transports
    ~normalize
    ~choice_symbols
    ~replacement_names
    ~definition
    proof =
  contract_backed_branch_choice_term_replacements
    ~normalize
    ~choice_symbols
    ~replacement_names
    ~definition
    proof
  |> List.map
       (fun (replacement_name, actual_choice, definition, local_template) ->
          {
            skolem_transport_name = replacement_name;
            skolem_transport_choice_occurrence = actual_choice;
            skolem_transport_definition = definition;
            skolem_transport_local_template = local_template;
          })
  |> List.sort_uniq compare

let skolem_witness_transport_symbol_replacements transports =
  transports
  |> List.map
       (fun transport ->
          (transport.skolem_transport_name,
           transport.skolem_transport_choice_occurrence,
           transport.skolem_transport_definition,
           transport.skolem_transport_local_template))
  |> List.sort_uniq compare

let skolem_witness_transport_term_replacements transports =
  transports
  |> List.map
       (fun transport ->
          (transport.skolem_transport_choice_occurrence,
           transport.skolem_transport_definition))
  |> List.sort_uniq compare

let skolem_witness_transport_proof_replacements transports =
  transports
  |> List.concat_map
       (fun transport ->
          [
            (transport.skolem_transport_choice_occurrence,
             transport.skolem_transport_definition);
            (TmH transport.skolem_transport_name,
             transport.skolem_transport_definition);
          ])
  |> List.sort_uniq compare

let skolem_witness_transport_proof_replacements_with_aliases
    ~alias_names
    transports =
  transports
  |> List.concat_map
       (fun transport ->
          (transport.skolem_transport_choice_occurrence,
           transport.skolem_transport_definition)
          ::
          (transport.skolem_transport_name
           |> alias_names
           |> List.map
                (fun alias ->
                   (TmH alias, transport.skolem_transport_definition))))
  |> List.sort_uniq compare

let prioritized_skolem_witness_transport_proof_replacements
    ~normalize
    ~alias_names
    ~witness_symbols
    ~registered_witnesses
    ~transports
    proof =
  let transport_replacements =
    skolem_witness_transport_proof_replacements_with_aliases
      ~alias_names
      transports
  in
  let transport_names =
    transports
    |> List.concat_map
         (fun transport -> alias_names transport.skolem_transport_name)
    |> List.sort_uniq String.compare
  in
  let transport_shadows_name name =
    alias_names name
    |> List.exists (fun alias -> List.mem alias transport_names)
  in
  let unshadowed_registered_witnesses =
    registered_witnesses
    |> List.filter
         (fun (name, _) -> not (transport_shadows_name name))
  in
  let registered_replacements =
    registered_witness_term_replacements
      ~normalize
      ~witness_symbols
      unshadowed_registered_witnesses
      proof
  in
  let rec keep_first seen = function
    | [] -> []
    | (needle, replacement) :: rest when List.mem needle seen ->
        keep_first seen rest
    | (needle, replacement) :: rest ->
        (needle, replacement) :: keep_first (needle :: seen) rest
  in
  keep_first [] (transport_replacements @ registered_replacements)

type introduced_symbol_replacement_classification = {
  introduced_symbols_present : string list;
  introduced_symbols_with_direct_replacement : string list;
  introduced_symbols_without_direct_replacement : string list;
}

let classify_introduced_symbol_replacements
    ~alias_names
    ~introduced_symbols
    ~replacements
    proof =
  let introduced_aliases =
    introduced_symbols
    |> List.concat_map alias_names
    |> List.sort_uniq String.compare
  in
  let direct_replacement_names =
    replacements
    |> List.filter_map
         (function
           | TmH name, _ -> Some name
           | _ -> None)
    |> List.sort_uniq String.compare
  in
  let present =
    introduced_aliases
    |> List.filter
         (fun name -> proof_contains_term_symbol [name] proof)
    |> List.sort_uniq String.compare
  in
  let with_direct =
    present
    |> List.filter
         (fun name -> List.mem name direct_replacement_names)
    |> List.sort_uniq String.compare
  in
  let without_direct =
    present
    |> List.filter
         (fun name -> not (List.mem name with_direct))
    |> List.sort_uniq String.compare
  in
  {
    introduced_symbols_present = present;
    introduced_symbols_with_direct_replacement = with_direct;
    introduced_symbols_without_direct_replacement = without_direct;
  }

type skolem_witness_cleanup_plan = {
  skolem_cleanup_transports : skolem_witness_transport list;
  skolem_cleanup_ambiguous_choice_occurrences : tm list;
  skolem_cleanup_replacements : (tm * tm) list;
  skolem_cleanup_introduced_classification :
    introduced_symbol_replacement_classification;
}

let disambiguate_skolem_witness_transports transports =
  let ambiguous_choice_occurrences =
    transports
    |> List.map
         (fun transport ->
            (transport.skolem_transport_choice_occurrence,
             transport.skolem_transport_definition))
    |> List.fold_left
         (fun grouped (actual_choice, definition) ->
            let definitions =
              match List.assoc_opt actual_choice grouped with
              | Some definitions -> definitions
              | None -> []
            in
            (actual_choice,
             definition :: definitions
             |> List.sort_uniq compare)
            :: List.remove_assoc actual_choice grouped)
         []
    |> List.filter_map
         (fun (actual_choice, definitions) ->
            match definitions with
            | [] | [_] -> None
            | _ -> Some actual_choice)
    |> List.sort_uniq compare
  in
  let transports =
    transports
    |> List.filter
         (fun transport ->
            not
              (List.mem
                 transport.skolem_transport_choice_occurrence
                 ambiguous_choice_occurrences))
  in
  transports, ambiguous_choice_occurrences

let skolem_witness_cleanup_plan
    ~normalize
    ~alias_names
    ~witness_symbols
    ~introduced_symbols
    ~registered_witnesses
    ~transports
    proof =
  let transports, ambiguous_choice_occurrences =
    disambiguate_skolem_witness_transports transports
  in
  let replacements =
    prioritized_skolem_witness_transport_proof_replacements
      ~normalize
      ~alias_names
      ~witness_symbols
      ~registered_witnesses
      ~transports
      proof
  in
  let introduced_classification =
    classify_introduced_symbol_replacements
      ~alias_names
      ~introduced_symbols
      ~replacements
      proof
  in
  {
    skolem_cleanup_transports = transports;
    skolem_cleanup_ambiguous_choice_occurrences =
      ambiguous_choice_occurrences;
    skolem_cleanup_replacements = replacements;
    skolem_cleanup_introduced_classification =
      introduced_classification;
  }

type skolem_branch_choice_template_expansion_plan = {
  skolem_template_replacement_names : string list;
  skolem_template_local_templates : tm list;
}

let skolem_branch_choice_template_expansion_plan
    ~alias_names
    ~template_limit
    transports =
  let rec take n = function
    | _ when n <= 0 -> []
    | [] -> []
    | item :: rest -> item :: take (n - 1) rest
  in
  let local_templates =
    transports
    |> List.map (fun transport -> transport.skolem_transport_local_template)
    |> List.sort_uniq compare
    |> take template_limit
  in
  let replacement_names =
    transports
    |> List.concat_map
         (fun transport -> alias_names transport.skolem_transport_name)
    |> List.sort_uniq String.compare
  in
  {
    skolem_template_replacement_names = replacement_names;
    skolem_template_local_templates = local_templates;
  }

let skolem_branch_choice_template_replacements plan local_template =
  plan.skolem_template_replacement_names
  |> List.map (fun replacement_name -> replacement_name, local_template)

let canonical_witness_name name =
  if String.length name > 0 && name.[0] = '#' then
    String.sub name 1 (String.length name - 1)
  else
    name

type registered_choice_expansion = {
  registered_choice_expansion_name : string;
  registered_choice_expansion_terms : tm list;
  registered_choice_expansion_replacements : (tm * tm) list;
}

type registered_choice_expansion_plan =
  | No_registered_choice_expansion
  | Ambiguous_registered_choice_expansion of string list
  | Unique_registered_choice_expansion of registered_choice_expansion

let unique_registered_choice_expansion_plan
    ~normalize
    ~witness_symbols
    ~registered_witnesses
    proof =
  let unresolved_names =
    registered_witnesses
    |> List.filter_map
         (fun (name, witness) ->
            let witness = normalize witness in
            let witness_choice_symbols =
              witness_symbols
              |> List.filter
                   (fun symbol -> term_contains_symbol [symbol] witness)
            in
            if not (proof_contains_exact_term ~normalize witness proof)
               && witness_choice_symbols <> []
               && proof_contains_term_symbol witness_choice_symbols proof then
              Some (canonical_witness_name name)
            else
              None)
    |> List.filter (fun name -> name <> "")
    |> List.sort_uniq String.compare
  in
  match unresolved_names with
  | [name] ->
      let actual_choices =
        enclosing_terms_with_symbol_depth
          ~normalize
          witness_symbols
          proof
        |> List.filter_map
             (fun (depth, actual_choice) ->
                try
                  Some (tmshift 0 (-depth) actual_choice |> normalize)
                with _ -> None)
        |> List.sort_uniq compare
      in
      if actual_choices = [] then
        No_registered_choice_expansion
      else
        Unique_registered_choice_expansion
          {
            registered_choice_expansion_name = name;
            registered_choice_expansion_terms = actual_choices;
            registered_choice_expansion_replacements =
              actual_choices
              |> List.map (fun actual_choice -> actual_choice, TmH name);
          }
  | [] -> No_registered_choice_expansion
  | names -> Ambiguous_registered_choice_expansion names

let substitute_named_term name tm =
  let rec subst depth = function
    | TmH candidate when candidate = name -> DB depth
    | TpAp (body, tp) -> TpAp (subst depth body, tp)
    | Ap (TmH "vLAM", body) -> Ap (TmH "vLAM", subst depth body)
    | Ap (left, right) -> Ap (subst depth left, subst depth right)
    | Lam (tp, body) -> Lam (tp, subst (depth + 1) body)
    | Imp (left, right) -> Imp (subst depth left, subst depth right)
    | All (tp, body) -> All (tp, subst (depth + 1) body)
    | DB _ | TmH _ | Prim _ as tm -> tm
  in
  subst 0 tm

let term_exists_head_types exists_head tm =
  let rec collect = function
    | Ap (TmH head, Lam (tp, body)) when head = exists_head ->
        tp :: collect body
    | Ap (Ap (TmH "vampire_and", left), right)
    | Ap (Ap (TmH "vampire_or", left), right)
    | Imp (left, right) ->
        collect left @ collect right
    | All (_, body)
    | Lam (_, body)
    | TpAp (body, _) ->
        collect body
    | Ap (TmH head, body) when head = exists_head ->
        collect body
    | Ap (TmH "vLAM", body) ->
        collect body
    | Ap (left, right) ->
        collect left @ collect right
    | DB _ | TmH _ | Prim _ -> []
  in
  collect tm

let term_exists_head_count exists_head tm =
  List.length (term_exists_head_types exists_head tm)

let rec term_head = function
  | Ap (head, _) | TpAp (head, _) -> term_head head
  | head -> head

let rewrite_head_symbols_by_alias ~alias_names replacements tm =
  let replacement_for_name name =
    let names = alias_names name in
    replacements
    |> List.find_map
         (fun (target_witness, replacement) ->
            match term_head target_witness with
            | TmH target_name ->
                let target_names = alias_names target_name in
                if List.exists (fun name -> List.mem name target_names) names then
                  Some replacement
                else
                  None
            | _ -> None)
  in
  let rec rewrite depth = function
    | TmH name as tm ->
        begin match replacement_for_name name with
        | Some replacement -> tmshift 0 depth replacement
        | None -> tm
        end
    | TpAp (body, tp) -> TpAp (rewrite depth body, tp)
    | Ap (left, right) ->
        Ap (rewrite depth left, rewrite depth right)
    | Lam (tp, body) ->
        Lam (tp, rewrite (depth + 1) body)
    | Imp (left, right) ->
        Imp (rewrite depth left, rewrite depth right)
    | All (tp, body) ->
        All (tp, rewrite (depth + 1) body)
    | DB _ | Prim _ as tm -> tm
  in
  rewrite 0 tm

let skolem_branch_choice_matches_witness
    ~normalize
    ~alias_names
    target_witness
    choice =
  let term_matches =
    match choice.skolem_branch_choice_witness_term with
    | Some witness_term -> normalize witness_term = normalize target_witness
    | None -> false
  in
  term_matches
  ||
  match term_head target_witness with
  | TmH target_head ->
      let target_names = alias_names target_head in
      let choice_names = alias_names choice.skolem_branch_choice_symbol in
      List.exists (fun name -> List.mem name choice_names) target_names
  | _ -> false

let skolem_branch_witness_symbols branch =
  branch.skolem_branch_introduced_witnesses
  |> List.map (fun witness -> witness.skolem_witness_symbol)

let skolem_branch_choice_for_witness
    ~alias_names
    branches
    witness =
  let witness_names = alias_names witness in
  branches
  |> List.find_map
       (fun branch ->
          let branch_matches =
            skolem_branch_witness_symbols branch
            |> List.concat_map alias_names
            |> List.exists (fun name -> List.mem name witness_names)
          in
          if not branch_matches then
            None
          else
            branch.skolem_branch_choices
            |> List.find_map
                 (fun choice ->
                    let choice_names =
                      alias_names choice.skolem_branch_choice_symbol
                    in
                    if List.exists
                         (fun name -> List.mem name choice_names)
                         witness_names then
                      Some (branch, choice)
                    else
                      None))

let skolem_branch_has_proposition_role role branch =
  branch.skolem_branch_propositions
  |> List.exists
       (fun proposition ->
          proposition.skolem_branch_prop_role = role)

let skolem_branch_choice_matching_witness ~alias_names witness branch =
  let witness_names = alias_names witness in
  branch.skolem_branch_choices
  |> List.find_opt
       (fun choice ->
          let choice_names =
            alias_names choice.skolem_branch_choice_symbol
          in
          List.exists (fun name -> List.mem name choice_names) witness_names)

let skolem_branch_contract_choice_for_witness
    ~alias_names
    ~branch_matches_formula
    ~witness
    ~source
    ~result
    branches =
  let exact_matches =
    branches
    |> List.filter
         (fun branch ->
            skolem_branch_witness_symbols branch
            |> List.sort_uniq String.compare
            = [witness]
            && branch_matches_formula
                 source
                 branch.skolem_branch_source_formula
            && branch_matches_formula
                 result
                 branch.skolem_branch_target_formula
            && skolem_branch_has_proposition_role "source" branch
            && skolem_branch_has_proposition_role "target" branch)
  in
  match exact_matches with
  | [branch] ->
      Some
        (branch,
         skolem_branch_choice_matching_witness
           ~alias_names
           witness
           branch)
  | _ ->
      skolem_branch_choice_for_witness
        ~alias_names
        branches
        witness
      |> Option.map (fun (branch, choice) -> branch, Some choice)

type skolem_branch_choice_instantiation = {
  skolem_choice_body : tm;
  skolem_choice_predicate : tm;
  skolem_choice_witnessed_body : tm option;
}

type skolem_choice_transport_obligation = {
  skolem_transport_from_body : tm;
  skolem_transport_to_body : tm;
}

type skolem_choice_transport_terms = {
  skolem_transport_epsilon_witness : tm;
  skolem_transport_epsilon_body : tm;
  skolem_transport_witnessed_body : tm option;
  skolem_transport_obligation : skolem_choice_transport_obligation option;
}

let skolem_choice_transport_terms
    ~normalize
    ~eps_symbol
    instantiation =
  match instantiation.skolem_choice_predicate with
  | Lam _ ->
      let epsilon_witness =
        Ap (TmH eps_symbol, instantiation.skolem_choice_predicate)
        |> normalize
      in
      let epsilon_body =
        tmsubst
          instantiation.skolem_choice_body
          0
          epsilon_witness
        |> normalize
      in
      let witnessed_body =
        Option.map normalize instantiation.skolem_choice_witnessed_body
      in
      let obligation =
        match witnessed_body with
        | Some witnessed_body when witnessed_body <> epsilon_body ->
            Some
              {
                skolem_transport_from_body = epsilon_body;
                skolem_transport_to_body = witnessed_body;
              }
        | _ -> None
      in
      {
        skolem_transport_epsilon_witness = epsilon_witness;
        skolem_transport_epsilon_body = epsilon_body;
        skolem_transport_witnessed_body = witnessed_body;
        skolem_transport_obligation = obligation;
      }
  | _ ->
      error "Skolem choice transport predicate is not a lambda"

let lift_skolem_branch_choice_instantiation ~ambient_shift instantiation =
  if ambient_shift = 0 then instantiation
  else
    {
      skolem_choice_body =
        tmshift 1 ambient_shift instantiation.skolem_choice_body;
      skolem_choice_predicate =
        tmshift 0 ambient_shift instantiation.skolem_choice_predicate;
      skolem_choice_witnessed_body =
        Option.map
          (tmshift 0 ambient_shift)
          instantiation.skolem_choice_witnessed_body;
    }

let skolem_branch_choice_instantiation
    ~normalize
    ~alias_names
    ~replacements
    ~substitution_name
    ~target_witness
    ~witness_type
    choices =
  choices
  |> List.find_map
       (fun choice ->
          let variable = choice.skolem_branch_choice_replaced_variable in
          let variable_matches =
            match substitution_name with
            | Some name -> name = variable
            | None -> true
          in
          if variable_matches
             && choice.skolem_branch_choice_type = witness_type
             && skolem_branch_choice_matches_witness
                  ~normalize
                  ~alias_names
                  target_witness
                  choice then
            let body =
              choice.skolem_branch_choice_body
              |> rewrite_head_symbols_by_alias ~alias_names replacements
              |> substitute_named_term variable
            in
            let predicate =
              choice.skolem_branch_choice_predicate
              |> rewrite_head_symbols_by_alias ~alias_names replacements
            in
            let witnessed_body =
              choice.skolem_branch_choice_witnessed_body
              |> Option.map
                   (rewrite_head_symbols_by_alias ~alias_names replacements)
            in
            let witnessed_body_matches =
              match witnessed_body with
              | None -> true
              | Some witnessed_body ->
                  normalize witnessed_body
                  = normalize (tmsubst body 0 target_witness)
            in
            begin match normalize predicate with
            | Lam (predicate_type, predicate_body)
                when predicate_type = choice.skolem_branch_choice_type
                     && normalize predicate_body = normalize body
                     && witnessed_body_matches ->
                Some
                  {
                    skolem_choice_body = body;
                    skolem_choice_predicate = predicate;
                    skolem_choice_witnessed_body = witnessed_body;
                  }
            | Lam _ -> None
            | _ -> None
            end
          else
            None)

let skolem_branch_choice_body
    ~normalize
    ~alias_names
    ~replacements
    ~substitution_name
    ~target_witness
    ~witness_type
    choices =
  skolem_branch_choice_instantiation
    ~normalize
    ~alias_names
    ~replacements
    ~substitution_name
    ~target_witness
    ~witness_type
    choices
  |> Option.map (fun instantiation -> instantiation.skolem_choice_body)

type skolem_helper_record = {
  skolem_helper_index : int;
  skolem_helper_tps : tp list;
  skolem_helper_source : tm;
  skolem_helper_target : tm;
}

let skolem_helper_records formulas =
  let rec peel_foralls tps = function
    | All (tp, body) -> peel_foralls (tps @ [tp]) body
    | Imp (source, target) -> Some (tps, source, target)
    | _ -> None
  in
  formulas
  |> List.mapi (fun index formula -> index, peel_foralls [] formula)
  |> List.filter_map
       (fun (index, helper) ->
          match helper with
          | Some (tps, source, target) ->
              Some
                {
                  skolem_helper_index = index;
                  skolem_helper_tps = tps;
                  skolem_helper_source = source;
                  skolem_helper_target = target;
                }
          | None -> None)

let rec term_contains_exists_head exists_head = function
  | Ap (TmH head, Lam _) when head = exists_head -> true
  | TpAp (body, _) -> term_contains_exists_head exists_head body
  | Ap (left, right) | Imp (left, right) ->
      term_contains_exists_head exists_head left
      || term_contains_exists_head exists_head right
  | Lam (_, body) | All (_, body) ->
      term_contains_exists_head exists_head body
  | DB _ | TmH _ | Prim _ -> false

let replace_exact_terms_in_term replacements tm =
  let rec replace_top_opt depth tm =
    match
      replacements
      |> List.find_opt
           (fun (needle, _) -> tm = tmshift 0 depth needle)
    with
    | Some (_, replacement) -> tmshift 0 depth replacement
    | None -> tm
  in
  let rec replace depth tm =
    let replaced = replace_top_opt depth tm in
    if replaced <> tm then replaced
    else
      match tm with
      | TpAp (body, tp) -> TpAp (replace depth body, tp)
      | Ap (left, right) -> Ap (replace depth left, replace depth right)
      | Lam (tp, body) -> Lam (tp, replace (depth + 1) body)
      | Imp (left, right) -> Imp (replace depth left, replace depth right)
      | All (tp, body) -> All (tp, replace (depth + 1) body)
      | DB _ | TmH _ | Prim _ -> tm
  in
  replace 0 tm

let rec skolem_helper_target_compatible
    ~normalize_at_depth
    ~exists_head
    local_depth
    helper_target
    target =
  normalize_at_depth local_depth helper_target
  = normalize_at_depth local_depth target
  ||
  match helper_target, target with
  | All (helper_tp, helper_body), All (target_tp, target_body)
      when helper_tp = target_tp ->
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        (local_depth + 1)
        helper_body
        target_body
  | Imp (helper_left, helper_right), Imp (target_left, target_right) ->
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        local_depth
        helper_left
        target_left
      &&
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        local_depth
        helper_right
        target_right
  | Ap (Ap (TmH "vampire_and", helper_left), helper_right),
    Ap (Ap (TmH "vampire_and", target_left), target_right)
  | Ap (Ap (TmH "vampire_or", helper_left), helper_right),
    Ap (Ap (TmH "vampire_or", target_left), target_right) ->
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        local_depth
        helper_left
        target_left
      &&
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        local_depth
        helper_right
        target_right
  | Ap (TmH head, Lam _), _ when head = exists_head ->
      true
  | _ -> false

let matching_skolem_helper
    ~normalize_at_depth
    ~raw_normalize
    ~exists_head
    ~local_depth
    ~replacements
    ~source
    ~target
    helpers =
  let normalized_with_replacements local_depth replacements tm =
    replace_exact_terms_in_term replacements tm
    |> normalize_at_depth local_depth
  in
  let helper_target_matches_current helper_target target =
    let helper_target = replace_exact_terms_in_term replacements helper_target in
    let target = replace_exact_terms_in_term replacements target in
    if term_contains_exists_head exists_head helper_target then
      skolem_helper_target_compatible
        ~normalize_at_depth
        ~exists_head
        local_depth
        helper_target
        target
    else
      raw_normalize helper_target = raw_normalize target
  in
  let rec matching = function
    | [] -> None
    | helper :: rest ->
        if normalize_at_depth local_depth source
           = normalized_with_replacements
               local_depth
               replacements
               helper.skolem_helper_source
           && helper_target_matches_current
                helper.skolem_helper_target
                target
           && normalized_with_replacements
                local_depth
                replacements
                helper.skolem_helper_source
              <> normalized_with_replacements
                   local_depth
                   replacements
                   helper.skolem_helper_target then
          Some (helper, rest)
        else
          begin match matching rest with
          | Some (found, remaining) -> Some (found, helper :: remaining)
          | None -> None
          end
  in
  matching helpers
