(*** Deterministic checks for the Vampire/Megalodon small clause kernel. ***)

open Syntax
open Vampire_kernel_syntax

exception Error of string

let error msg = raise (Error msg)

let literal_atom = function
  | Pos tm -> tm
  | Neg tm -> tm

let complementary left right =
  match left, right with
  | Pos a, Neg b
  | Neg a, Pos b -> a = b
  | _ -> false

let remove_at index items what =
  if index < 0 then error (what ^ " index must be non-negative");
  let rec aux i = function
    | [] -> error (what ^ " index is out of bounds")
    | _ :: rest when i = index -> rest
    | item :: rest -> item :: aux (i + 1) rest
  in
  aux 0 items

let replace_at index replacement items what =
  if index < 0 then error (what ^ " index must be non-negative");
  let rec aux i = function
    | [] -> error (what ^ " index is out of bounds")
    | _ :: rest when i = index -> replacement :: rest
    | item :: rest -> item :: aux (i + 1) rest
  in
  aux 0 items

let nth index items what =
  if index < 0 then error (what ^ " index must be non-negative");
  try List.nth items index with Failure _ -> error (what ^ " index is out of bounds")

let rec remove_one item = function
  | [] -> None
  | x :: xs when x = item -> Some xs
  | x :: xs ->
      match remove_one item xs with
      | None -> None
      | Some ys -> Some (x :: ys)

let same_clause_multiset left right =
  let rec consume remaining = function
    | [] -> remaining = []
    | item :: rest ->
        begin match remove_one item remaining with
        | None -> false
        | Some remaining -> consume remaining rest
        end
  in
  List.length left = List.length right && consume left right

let rec subst_tm subst tm =
  match tm with
  | DB _ -> tm
  | TmH "=" -> tm
  | TmH h ->
      let rec lookup = function
        | [] -> tm
        | (key, value) :: rest ->
            if key = h then value else lookup rest
      in
      lookup subst
  | Prim _ -> tm
  | TpAp (body, tp) -> TpAp (subst_tm subst body, tp)
  | Ap (left, right) -> Ap (subst_tm subst left, subst_tm subst right)
  | Lam (tp, body) -> Lam (tp, subst_tm subst body)
  | Imp (left, right) -> Imp (subst_tm subst left, subst_tm subst right)
  | All (tp, body) -> All (tp, subst_tm subst body)

let subst_literal subst = function
  | Pos tm -> Pos (subst_tm subst tm)
  | Neg tm -> Neg (subst_tm subst tm)

let subst_clause subst clause =
  List.map (subst_literal subst) clause

let unique_clause clause =
  let rec add_unique acc = function
    | [] -> List.rev acc
    | literal :: rest ->
        if List.exists ((=) literal) acc then add_unique acc rest
        else add_unique (literal :: acc) rest
  in
  add_unique [] clause

let rec tm_at_position tm position what =
  match position with
  | [] -> tm
  | index :: rest ->
      let child =
        match tm, index with
        | TpAp (body, _), 0 -> body
        | Ap (TmH "vLAM", body), 0 -> body
        | Ap (left, _), 0 -> left
        | Ap (_, right), 1 -> right
        | Lam (_, body), 0 -> body
        | Imp (left, _), 0 -> left
        | Imp (_, right), 1 -> right
        | All (_, body), 0 -> body
        | _ -> error (what ^ " position is out of bounds")
      in
      tm_at_position child rest what

let rec replace_tm_at_position tm position replacement what =
  match position with
  | [] -> replacement
  | index :: rest ->
      match tm, index with
      | TpAp (body, tp), 0 -> TpAp (replace_tm_at_position body rest replacement what, tp)
      | Ap (TmH "vLAM", body), 0 ->
          Ap (TmH "vLAM", replace_tm_at_position body rest replacement what)
      | Ap (left, right), 0 -> Ap (replace_tm_at_position left rest replacement what, right)
      | Ap (left, right), 1 -> Ap (left, replace_tm_at_position right rest replacement what)
      | Lam (tp, body), 0 -> Lam (tp, replace_tm_at_position body rest replacement what)
      | Imp (left, right), 0 -> Imp (replace_tm_at_position left rest replacement what, right)
      | Imp (left, right), 1 -> Imp (left, replace_tm_at_position right rest replacement what)
      | All (tp, body), 0 -> All (tp, replace_tm_at_position body rest replacement what)
      | _ -> error (what ^ " position is out of bounds")

let try_tm_at_position tm position =
  try Some (tm_at_position tm position "term") with Error _ -> None

let replace_literal_atom literal atom =
  match literal with
  | Pos _ -> Pos atom
  | Neg _ -> Neg atom

let application_spine tm =
  let rec collect acc = function
    | Ap (fn, arg) -> collect (arg :: acc) fn
    | head -> head, acc
  in
  collect [] tm

type definition_rewrite = {
  definition_parent : string;
  definition_literal : int;
  target_literal : int;
  rewrite_position : int list;
  rewrite_from : tm;
  rewrite_to : tm;
}

let check_substitute ~id ~parent ~subst ~result =
  let expected = subst_clause subst parent in
  if not (same_clause_multiset expected result) then
    error (id ^ ": substitution result does not match parent under explicit substitution")

let check_condensation ~id ~parent ~subst ~result =
  let expected = unique_clause (subst_clause subst parent) in
  if List.length expected >= List.length parent then
    error (id ^ ": condensation did not remove a duplicate literal");
  if not (same_clause_multiset expected result) then
    error (id ^ ": condensation result does not match duplicate-collapsed substituted parent")

let check_factor ~id ~parent ~left_index ~right_index ~result =
  if left_index = right_index then
    error (id ^ ": factor literal indices must be distinct");
  let left_literal = nth left_index parent (id ^ " first factor literal") in
  let right_literal = nth right_index parent (id ^ " second factor literal") in
  if left_literal <> right_literal then
    error (id ^ ": factor currently accepts only identical literals");
  let remove_index = if left_index > right_index then left_index else right_index in
  let expected = remove_at remove_index parent (id ^ " removed factor literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": factor result does not match parent clause after duplicate removal")

let check_resolution ~id ~left ~right ~left_index ~right_index ~result =
  let left_pivot = nth left_index left (id ^ " left pivot") in
  let right_pivot = nth right_index right (id ^ " right pivot") in
  if not (complementary left_pivot right_pivot) then
    error (id ^ ": resolution pivots are not complementary");
  let left_rest = remove_at left_index left (id ^ " left pivot") in
  let right_rest = remove_at right_index right (id ^ " right pivot") in
  let expected = left_rest @ right_rest in
  if not (same_clause_multiset expected result) then
    error (id ^ ": resolution result does not match parent clauses after pivot removal")

let check_equality_resolution ~id ~equality_sides ~parent ~literal_index ~result =
  let literal = nth literal_index parent (id ^ " equality-resolution literal") in
  begin
    match literal with
    | Neg atom ->
        begin
          match equality_sides atom with
          | Some (left, right) when left = right -> ()
          | Some _ -> error (id ^ ": equality-resolution equality is not reflexive")
          | None -> error (id ^ ": equality-resolution literal is not an equality atom")
        end
    | Pos _ -> error (id ^ ": equality-resolution literal must be negative")
  end;
  let expected = remove_at literal_index parent (id ^ " equality-resolution literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-resolution result does not match parent after literal removal")

let check_equality_resolution_constraints
    ~id
    ~equality_sides
    ~same_literal
    ~parent
    ~literal_index
    ~selected
    ~constraints
    ~result =
  if constraints = [] then
    error (id ^ ": equality-resolution constraints must be non-empty");
  let literal = nth literal_index parent (id ^ " equality-resolution-constraints literal") in
  if not (same_literal literal selected) then
    error (id ^ ": selected literal does not match parent literal modulo Vampire variable renaming");
  begin
    match literal with
    | Neg atom ->
        begin match equality_sides atom with
        | Some _ -> ()
        | None -> error (id ^ ": selected literal is not an equality atom")
        end
    | Pos _ -> error (id ^ ": selected literal must be negative")
  end;
  let expected = remove_at literal_index parent (id ^ " equality-resolution-constraints literal") @ constraints in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-resolution constraints do not explain result")

let check_truth_conflict
    ~id
    ~equality_sides
    ~true_tm
    ~false_tm
    ~parent
    ~literal_index
    ~result =
  let literal = nth literal_index parent (id ^ " truth-conflict literal") in
  begin
    match literal with
    | Pos atom ->
        begin
          match equality_sides atom with
          | Some (left, right)
              when (left = true_tm && right = false_tm)
                || (left = false_tm && right = true_tm) -> ()
          | Some _ -> error (id ^ ": truth-conflict equality is not true = false")
          | None -> error (id ^ ": truth-conflict literal is not an equality atom")
        end
    | Neg _ -> error (id ^ ": truth-conflict literal must be positive")
  end;
  let expected = remove_at literal_index parent (id ^ " truth-conflict literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": truth-conflict result does not match parent after literal removal")

let check_equality_symmetry ~id ~swap_equality_literal ~parent ~literal_index ~result =
  let literal = nth literal_index parent (id ^ " equality-symmetry literal") in
  let swapped_literal =
    match swap_equality_literal literal with
    | Some swapped -> swapped
    | None -> error (id ^ ": equality-symmetry literal is not an equality")
  in
  let without_literal = remove_at literal_index parent (id ^ " equality-symmetry literal") in
  let expected = without_literal @ [swapped_literal] in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-symmetry result does not match parent clause")

let check_bool_simplify
    ~id
    ~swap_equality_literal
    ~clause_matches
    ~parent
    ~literal_index
    ~position_candidates
    ~from_tm
    ~to_tm
    ~result =
  let target_literal = nth literal_index parent (id ^ " Boolean simplification literal") in
  let target_atom = literal_atom target_literal in
  let position =
    let rec select = function
      | [] -> error (id ^ ": Boolean simplification position does not contain from term")
      | candidate :: rest ->
          begin
            match try_tm_at_position target_atom candidate with
            | Some found when found = from_tm -> candidate
            | _ -> select rest
          end
    in
    select position_candidates
  in
  let rewritten_atom =
    replace_tm_at_position target_atom position to_tm (id ^ " Boolean simplification target")
  in
  let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
  let parent_rest = remove_at literal_index parent (id ^ " Boolean simplification literal") in
  let result_matches rewritten_literal =
    let expected = parent_rest @ [rewritten_literal] in
    clause_matches expected result
  in
  if not (
      result_matches rewritten_literal
      ||
      match swap_equality_literal rewritten_literal with
      | Some swapped_literal -> result_matches swapped_literal
      | None -> false)
  then
    error (id ^ ": Boolean simplification result does not match explicit rewrite")

let check_paramodulate
    ~id
    ~equality_sides
    ~swap_equality_literal
    ~clause_matches
    ~equality_clause
    ~target_clause
    ~equality_index
    ~target_index
    ~position_candidates
    ~from_tm
    ~to_tm
    ~result =
  let equality_literal = nth equality_index equality_clause (id ^ " equality literal") in
  let target_literal = nth target_index target_clause (id ^ " target literal") in
  begin
    match equality_literal with
    | Pos atom ->
        begin
          match equality_sides atom with
          | Some (left, right) when left = from_tm && right = to_tm -> ()
          | Some (left, right) when right = from_tm && left = to_tm -> ()
          | Some _ -> error (id ^ ": paramodulation from/to terms do not match equality literal")
          | None -> error (id ^ ": paramodulation equality literal is not an equality atom")
        end
    | Neg _ -> error (id ^ ": paramodulation equality literal must be positive")
  end;
  let target_atom = literal_atom target_literal in
  let position =
    let rec select = function
      | [] -> error (id ^ ": paramodulation position does not contain from term")
      | candidate :: rest ->
          begin
            match try_tm_at_position target_atom candidate with
            | Some found when found = from_tm -> candidate
            | _ -> select rest
          end
    in
    select position_candidates
  in
  let rewritten_atom = replace_tm_at_position target_atom position to_tm (id ^ " target") in
  let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
  let equality_rest = remove_at equality_index equality_clause (id ^ " equality literal") in
  let target_rest = remove_at target_index target_clause (id ^ " target literal") in
  let expected = equality_rest @ target_rest @ [rewritten_literal] in
  if not (clause_matches expected result) then
    begin match swap_equality_literal rewritten_literal with
    | Some swapped_literal ->
        let swapped_expected = equality_rest @ target_rest @ [swapped_literal] in
        if not (clause_matches swapped_expected result) then
          error (id ^ ": paramodulation result does not match explicit rewrite")
    | None -> error (id ^ ": paramodulation result does not match explicit rewrite")
    end

let rec term_disagreement_constraints ~diseq_literal left right =
  if left = right then []
  else
    let left_head, left_args = application_spine left in
    let right_head, right_args = application_spine right in
    if left_head = right_head && List.length left_args = List.length right_args then
      let rec collect acc = function
        | [], [] -> List.rev acc
        | left_arg :: left_rest, right_arg :: right_rest ->
            let constraints =
              if left_arg = right_arg then []
              else
                let nested =
                  term_disagreement_constraints ~diseq_literal left_arg right_arg
                in
                if nested = [] then [diseq_literal left_arg right_arg] else nested
            in
            collect (List.rev_append constraints acc) (left_rest, right_rest)
        | _ -> [diseq_literal left right]
      in
      collect [] (left_args, right_args)
    else
      [diseq_literal left right]

let equality_factoring_constraint_candidates ~diseq_literal selected_sides other_sides =
  let selected_left, selected_right = selected_sides in
  let other_left, other_right = other_sides in
  let candidates = ref [] in
  let add_simple shared selected_other other_other =
    if shared then begin
      candidates := [diseq_literal selected_other other_other] :: !candidates;
      candidates := [diseq_literal other_other selected_other] :: !candidates
    end
  in
  let add_decomposed selected_shared selected_other other_shared other_other =
    let constraints =
      diseq_literal selected_shared other_shared
      :: term_disagreement_constraints ~diseq_literal selected_other other_other
    in
    let reversed =
      diseq_literal other_shared selected_shared
      :: term_disagreement_constraints ~diseq_literal other_other selected_other
    in
    candidates := constraints :: reversed :: !candidates
  in
  add_simple (selected_right = other_right) selected_left other_left;
  add_simple (selected_right = other_left) selected_left other_right;
  add_simple (selected_left = other_right) selected_right other_left;
  add_simple (selected_left = other_left) selected_right other_right;
  add_decomposed selected_right selected_left other_right other_left;
  add_decomposed selected_right selected_left other_left other_right;
  add_decomposed selected_left selected_right other_right other_left;
  add_decomposed selected_left selected_right other_left other_right;
  List.filter (fun constraints -> constraints <> []) !candidates

let equality_factoring_explicit_constraint_candidates
    ~id
    ~diseq_literal
    ~selected_sides
    ~other_sides
    ~selected_lhs
    ~other_rhs =
  let selected_left, selected_right = selected_sides in
  let other_left, other_right = other_sides in
  let selected_choices =
    List.filter
      (fun (lhs, _) -> lhs = selected_lhs)
      [(selected_left, selected_right); (selected_right, selected_left)]
  in
  let other_choices =
    List.filter
      (fun (rhs, _) -> rhs = other_rhs)
      [(other_left, other_right); (other_right, other_left)]
  in
  if selected_choices = [] then
    error (id ^ ": equality-factoring selected_lhs does not name a selected equality side");
  if other_choices = [] then
    error (id ^ ": equality-factoring other_rhs does not name an other equality side");
  let candidates =
    List.fold_left
      (fun acc (selected_shared, selected_other) ->
        List.fold_left
          (fun acc (other_other, other_shared) ->
            if selected_shared = other_shared then
              [diseq_literal selected_other other_other] :: acc
            else
              acc)
          acc other_choices)
      [] selected_choices
  in
  if candidates = [] then
    error (id ^ ": equality-factoring explicit sides do not identify matching unified sides");
  candidates

let check_negative_equality_constraints ~id ~equality_sides constraints =
  List.iter
    (function
      | Neg atom ->
          begin match equality_sides atom with
          | Some _ -> ()
          | None -> error (id ^ ": equality-factoring constraint is not an equality atom")
          end
      | Pos _ -> error (id ^ ": equality-factoring constraint must be negative"))
    constraints

let equality_factoring_context
    ~id
    ~equality_sides
    ~diseq_literal_like
    ~parent
    ~selected_index
    ~other_index
    ~subst =
  if selected_index = other_index then
    error (id ^ ": equality-factoring literal indices must be distinct");
  let selected_literal = nth selected_index parent (id ^ " selected equality") in
  let other_literal = nth other_index parent (id ^ " other equality") in
  let selected_sub = subst_literal subst selected_literal in
  let other_sub = subst_literal subst other_literal in
  let selected_atom, selected_sides =
    match selected_sub with
    | Pos atom ->
        begin match equality_sides atom with
        | Some sides -> atom, sides
        | None -> error (id ^ ": selected literal is not an equality")
        end
    | Neg _ -> error (id ^ ": selected literal must be positive")
  in
  let other_sides =
    match other_sub with
    | Pos atom ->
        begin match equality_sides atom with
        | Some sides -> sides
        | None -> error (id ^ ": other literal is not an equality")
        end
    | Neg _ -> error (id ^ ": other literal must be positive")
  in
  let substituted_parent = subst_clause subst parent in
  let without_selected = remove_at selected_index substituted_parent (id ^ " selected equality") in
  let diseq_literal = diseq_literal_like selected_atom in
  selected_sides, other_sides, without_selected, diseq_literal

let equality_factoring_candidates id explicit_sides selected_sides other_sides diseq_literal =
  match explicit_sides with
  | None ->
      equality_factoring_constraint_candidates
        ~diseq_literal
        selected_sides
        other_sides
  | Some (selected_lhs, other_rhs) ->
      equality_factoring_explicit_constraint_candidates
        ~id
        ~diseq_literal
        ~selected_sides
        ~other_sides
        ~selected_lhs
        ~other_rhs

let check_equality_factoring
    ~id
    ~equality_sides
    ~diseq_literal_like
    ~clause_matches
    ~parent
    ~selected_index
    ~other_index
    ~explicit_sides
    ~subst
    ~result =
  let selected_sides, other_sides, without_selected, diseq_literal =
    equality_factoring_context
      ~id
      ~equality_sides
      ~diseq_literal_like
      ~parent
      ~selected_index
      ~other_index
      ~subst
  in
  let candidates =
    equality_factoring_candidates id explicit_sides selected_sides other_sides diseq_literal
  in
  if candidates = [] then
    error (id ^ ": selected and other equalities do not yield factoring constraints");
  if not (List.exists
      (fun candidate_constraints ->
        let expected = without_selected @ candidate_constraints in
        clause_matches expected result)
      candidates) then
    error (id ^ ": equality-factoring result does not match explicit factoring")

let check_equality_factoring_constraints
    ~id
    ~equality_sides
    ~diseq_literal_like
    ~clause_matches
    ~parent
    ~selected_index
    ~other_index
    ~explicit_sides
    ~subst
    ~constraints
    ~result =
  if constraints = [] then
    error (id ^ ": equality-factoring constraints must be non-empty");
  check_negative_equality_constraints ~id ~equality_sides constraints;
  let selected_sides, other_sides, without_selected, diseq_literal =
    equality_factoring_context
      ~id
      ~equality_sides
      ~diseq_literal_like
      ~parent
      ~selected_index
      ~other_index
      ~subst
  in
  let expected = without_selected @ constraints in
  if not (clause_matches expected result) then
    error (id ^ ": equality-factoring constraints do not explain result");
  let candidates =
    equality_factoring_candidates id explicit_sides selected_sides other_sides diseq_literal
  in
  if not (List.exists (fun candidate -> clause_matches candidate constraints) candidates) then
    error (id ^ ": equality-factoring constraints are not explained by selected and other equalities")

let check_definition_rewrite_chain
    ~id
    ~equality_sides
    ~source
    ~definition_parent
    ~rewrites
    ~result =
  if rewrites = [] then error (id ^ ": definition_rewrite_chain needs at least one rewrite");
  let check_definition rewrite =
    let definition_clause = definition_parent rewrite.definition_parent in
    let definition_literal =
      nth rewrite.definition_literal definition_clause (id ^ " definition literal")
    in
    match definition_literal with
    | Pos atom ->
        begin match equality_sides atom with
        | Some (left, right)
            when (left = rewrite.rewrite_from && right = rewrite.rewrite_to)
              || (right = rewrite.rewrite_from && left = rewrite.rewrite_to) -> ()
        | Some _ -> error (id ^ ": definition rewrite from/to terms do not match definition parent")
        | None -> error (id ^ ": definition rewrite parent literal is not an equality")
        end
    | Neg _ -> error (id ^ ": definition rewrite parent literal must be positive")
  in
  let current =
    List.fold_left
      (fun current rewrite ->
         check_definition rewrite;
         let target_literal =
           nth rewrite.target_literal current (id ^ " definition rewrite target literal")
         in
         let target_atom = literal_atom target_literal in
         begin match try_tm_at_position target_atom rewrite.rewrite_position with
         | Some found when found = rewrite.rewrite_from -> ()
         | Some _ -> error (id ^ ": definition rewrite position does not contain from term")
         | None -> error (id ^ ": definition rewrite position is invalid")
         end;
         let rewritten_atom =
           replace_tm_at_position target_atom rewrite.rewrite_position rewrite.rewrite_to id
         in
         let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
         replace_at
           rewrite.target_literal
           rewritten_literal
           current
           (id ^ " definition rewrite target literal"))
      source
      rewrites
  in
  if not (same_clause_multiset current result) then
    error (id ^ ": definition_rewrite_chain result does not match explicit rewrite sequence")
