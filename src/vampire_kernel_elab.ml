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
