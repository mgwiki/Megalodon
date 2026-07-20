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

let remove_one_literal ~same_literal item clause what =
  let rec aux = function
    | [] -> error what
    | literal :: rest when same_literal literal item -> rest
    | literal :: rest -> literal :: aux rest
  in
  aux clause

let check_subsumption_resolution
    ~id
    ~same_literal
    ~complementary
    ~clause_contains
    ~clause_matches
    ~main
    ~side
    ~selected
    ~side_pivot
    ~side_subst
    ~result =
  let main_rest =
    remove_one_literal
      ~same_literal
      selected
      main
      (id ^ ": selected literal is not present in main parent")
  in
  if not (clause_matches main_rest result) then
    error (id ^ ": subsumption-resolution result does not match main parent after selected literal removal");
  let side_pivot_sub = subst_literal side_subst side_pivot in
  if not (complementary selected side_pivot_sub) then
    error (id ^ ": side pivot does not complement selected literal under side substitution");
  let rec check_side skipped_pivot = function
    | [] ->
        if not skipped_pivot then
          error (id ^ ": side pivot is not present in side parent")
    | literal :: rest ->
        if not skipped_pivot && same_literal literal side_pivot then
          check_side true rest
        else
          let substituted = subst_literal side_subst literal in
          if complementary selected substituted
             || clause_contains substituted result then
            check_side skipped_pivot rest
          else
            error (id ^ ": side parent contains a literal not discharged by the selected literal or preserved in the result")
  in
  check_side false side

let check_unit_resulting_resolution
    ~id
    ~is_split_literal
    ~complementary
    ~clause_contains
    ~clause_matches
    ~unit_clause
    ~main
    ~traces
    ~result =
  if traces = [] then error (id ^ ": unit_resulting_resolution trace is empty");
  let non_split_length clause =
    List.length (List.filter (fun lit -> not (is_split_literal lit)) clause)
  in
  let rec check_trace current = function
    | [] -> current
    | trace :: rest ->
        let unit_clause = unit_clause trace.urr_unit_parent in
        if non_split_length unit_clause <> 1 then
          error (id ^ ": URR unit parent " ^ trace.urr_unit_parent ^ " is not a unit clause");
        if not (complementary trace.urr_selected_substituted trace.urr_unit_substituted) then
          error (id ^ ": URR substituted selected and unit literals are not complementary");
        let current_non_split_length = non_split_length current in
        let remaining_non_split_length = non_split_length trace.urr_remaining in
        if remaining_non_split_length >= current_non_split_length then
          error (id ^ ": URR trace did not remove a literal");
        let selected_is_linked =
          clause_contains trace.urr_selected current
          || clause_contains trace.urr_selected_substituted current
        in
        if not selected_is_linked && current_non_split_length = remaining_non_split_length + 1 then
          error (id ^ ": URR selected literal is not linked to the current clause");
        check_trace trace.urr_remaining rest
  in
  let final_remaining = check_trace main traces in
  if not (clause_matches final_remaining result) then
    error (id ^ ": URR result does not match final trace remaining clause")

let check_cnf_literal ~id ~parent_clause ~result =
  if not (same_clause_multiset parent_clause result) then
    error (id ^ ": cnf_literal result does not match source literal")

let check_formula_term_copy ~id ~parent ~result =
  if parent <> result then
    error (id ^ ": formula_term_copy result does not match parent")

let check_formula_copy ~id ~literal_of_formula ~parent ~result =
  match parent with
  | `Clause parent_clause ->
      if not (same_clause_multiset parent_clause [result]) then
        error (id ^ ": formula_copy result does not match parent")
  | `Formula parent_formula ->
      let expected = literal_of_formula parent_formula in
      if expected <> result then
        error (id ^ ": formula_copy result does not match formula parent")

let check_fool_bool
    ~id
    ~equality_to_true
    ~typed_prop_equality_to_true
    ~parent_clause
    ~result =
  let expected =
    match parent_clause with
    | [Pos atom] -> [Pos (equality_to_true atom); Pos (typed_prop_equality_to_true atom)]
    | [Neg atom] -> [Neg (equality_to_true atom); Neg (typed_prop_equality_to_true atom)]
    | _ -> error (id ^ ": fool_bool parent is not a singleton formula")
  in
  if not (List.exists (fun candidate -> same_clause_multiset [candidate] [result]) expected) then
    error (id ^ ": fool_bool result is not the Boolean-term equality to true")

let true_false_equality_var ~equality_sides = function
  | Pos atom ->
      begin match equality_sides atom with
      | Some (TmH h, other) when h = "f__true" || h = "f__false" -> Some (h, other)
      | Some (other, TmH h) when h = "f__true" || h = "f__false" -> Some (h, other)
      | _ -> None
      end
  | Neg _ -> None

let simple_fool_exhaustiveness_clause ~equality_sides = function
  | [left; right] ->
      begin
        match
          true_false_equality_var ~equality_sides left,
          true_false_equality_var ~equality_sides right
        with
        | Some ("f__true", x), Some ("f__false", y)
        | Some ("f__false", x), Some ("f__true", y) -> x = y
        | _ -> false
      end
  | _ -> false

let check_fool_exhaustiveness ~id ~equality_sides ~clause =
  if not (simple_fool_exhaustiveness_clause ~equality_sides clause) then
    match clause with
    | [_; _] ->
        error (id ^ ": fool_exhaustiveness is not true/false exhaustiveness for one Boolean term")
    | _ -> error (id ^ ": fool_exhaustiveness must have exactly two literals")

let check_fool_distinctness ~id ~equality_sides ~clause =
  match clause with
  | [Neg atom] ->
      begin match equality_sides atom with
      | Some (TmH "f__true", TmH "f__false")
      | Some (TmH "f__false", TmH "f__true") -> ()
      | Some _ -> error (id ^ ": fool_distinctness is not true != false")
      | None -> error (id ^ ": fool_distinctness literal is not an equality")
      end
  | [_] -> error (id ^ ": fool_distinctness literal must be negative")
  | _ -> error (id ^ ": fool_distinctness must be a singleton clause")

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

let rec rewrite_tm_all_once from_tm to_tm tm =
  if tm = from_tm then to_tm
  else
    match tm with
    | TpAp (body, tp) -> TpAp (rewrite_tm_all_once from_tm to_tm body, tp)
    | Ap (left, right) ->
        Ap (rewrite_tm_all_once from_tm to_tm left, rewrite_tm_all_once from_tm to_tm right)
    | Lam (tp, body) -> Lam (tp, rewrite_tm_all_once from_tm to_tm body)
    | Imp (left, right) ->
        Imp (rewrite_tm_all_once from_tm to_tm left, rewrite_tm_all_once from_tm to_tm right)
    | All (tp, body) -> All (tp, rewrite_tm_all_once from_tm to_tm body)
    | DB _ | TmH _ | Prim _ -> tm

let rewrite_literal_all_once from_tm to_tm literal =
  replace_literal_atom literal (rewrite_tm_all_once from_tm to_tm (literal_atom literal))

let check_superposition
    ~id
    ~equality_sides
    ~swap_equality_literal
    ~side_matches
    ~clause_matches
    ~raw_variable_name
    ~target_clause
    ~raw_equality_clause
    ~equality_clause
    ~target_index
    ~equality_index
    ~position_candidates
    ~from_tm
    ~to_tm
    ~result =
  let raw_equality_literal =
    nth equality_index raw_equality_clause (id ^ " raw equality literal")
  in
  let equality_literal = nth equality_index equality_clause (id ^ " equality literal") in
  let target_literal = nth target_index target_clause (id ^ " target literal") in
  begin
    match equality_literal with
    | Pos atom ->
        begin
          match equality_sides atom with
          | Some (left, right) when side_matches left from_tm && side_matches right to_tm -> ()
          | Some (left, right) when side_matches right from_tm && side_matches left to_tm -> ()
          | Some _ -> error (id ^ ": superposition from/to terms do not match equality literal")
          | None -> error (id ^ ": superposition equality literal is not an equality atom")
        end
    | Neg _ -> error (id ^ ": superposition equality literal must be positive")
  end;
  let target_atom = literal_atom target_literal in
  let position =
    let rec select = function
      | [] -> error (id ^ ": superposition position does not contain from term")
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
  let simultaneous_rewritten_literal =
    rewrite_literal_all_once from_tm to_tm target_literal
  in
  let equality_rest = remove_at equality_index equality_clause (id ^ " equality literal") in
  let target_rest = remove_at target_index target_clause (id ^ " target literal") in
  let target_rest_variants =
    let clause_wide_target_rest = List.map (rewrite_literal_all_once from_tm to_tm) target_rest in
    if clause_wide_target_rest = target_rest then [target_rest]
    else [target_rest; clause_wide_target_rest]
  in
  let result_matches_with_equality_rest equality_rest rewritten_literal =
    List.exists
      (fun target_rest ->
        let expected = equality_rest @ target_rest @ [rewritten_literal] in
        clause_matches expected result)
      target_rest_variants
  in
  let result_matches equality_rest =
    let rewritten_literals =
      if simultaneous_rewritten_literal = rewritten_literal then [rewritten_literal]
      else [rewritten_literal; simultaneous_rewritten_literal]
    in
    List.exists
      (fun rewritten_literal ->
        result_matches_with_equality_rest equality_rest rewritten_literal
        ||
        match swap_equality_literal rewritten_literal with
        | Some swapped_literal -> result_matches_with_equality_rest equality_rest swapped_literal
        | None -> false)
      rewritten_literals
  in
  let result_matches_raw_variable_orientation () =
    match raw_equality_literal with
    | Pos raw_atom ->
        begin match equality_sides raw_atom with
        | Some (raw_left, raw_right) ->
            let variants =
              match raw_variable_name raw_left, raw_variable_name raw_right with
              | Some left_name, Some right_name ->
                  [[left_name, from_tm; right_name, to_tm];
                   [right_name, from_tm; left_name, to_tm]]
              | Some left_name, None -> [[left_name, from_tm]]
              | None, Some right_name -> [[right_name, from_tm]]
              | None, None -> []
            in
            List.exists
              (fun subst ->
                let raw_rest =
                  remove_at equality_index raw_equality_clause (id ^ " raw equality literal")
                in
                let equality_rest = subst_clause subst raw_rest in
                result_matches equality_rest)
              variants
        | None -> false
        end
    | Neg _ -> false
  in
  if not (result_matches equality_rest || result_matches_raw_variable_orientation ()) then
    error (id ^ ": superposition result does not match explicit rewrite")

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

let rec term_head = function
  | Ap (head, _) | TpAp (head, _) -> term_head head
  | head -> head

let check_skolem_branch_contract
    ~id
    ~index
    ~normalize
    ~alias_names
    ~introduced_symbol_names
    ~source_formula
    ~target_formula
    ~propositions
    ~choices =
  let check_expected label expected proposition =
    match expected with
    | Some expected
        when normalize expected <> normalize proposition.skolem_branch_prop_formula ->
        error
          (Printf.sprintf
             "%s: typed Skolem branch contract %d proposition role %s does not match branch %s formula"
             id index proposition.skolem_branch_prop_role label)
    | _ -> ()
  in
  List.iter
    (fun proposition ->
       match proposition.skolem_branch_prop_role with
       | "source" -> check_expected "source" source_formula proposition
       | "target" -> check_expected "target" target_formula proposition
       | "" ->
           error
             (Printf.sprintf
                "%s: typed Skolem branch contract %d has an empty branch proposition role"
                id index)
       | _ -> ())
    propositions;
  List.iter
    (fun choice ->
       if choice.skolem_branch_choice_symbol = "" then
         error
           (Printf.sprintf
              "%s: typed Skolem branch contract %d has an empty branch choice symbol"
              id index);
       if choice.skolem_branch_choice_replaced_variable = "" then
         error
           (Printf.sprintf
              "%s: typed Skolem branch contract %d has an empty branch choice replaced variable"
              id index);
       if not (List.mem choice.skolem_branch_choice_symbol introduced_symbol_names) then
         error
           (Printf.sprintf
              "%s: typed Skolem branch contract %d choice symbol %s is not introduced by the branch"
              id index choice.skolem_branch_choice_symbol);
       let expected_predicate =
         let expected_body =
           substitute_named_term
             choice.skolem_branch_choice_replaced_variable
             choice.skolem_branch_choice_body
         in
         Lam (choice.skolem_branch_choice_type, expected_body)
         |> normalize
       in
       if normalize choice.skolem_branch_choice_predicate <> expected_predicate then
         error
           (Printf.sprintf
              "%s: typed Skolem branch contract %d choice predicate does not match its body"
              id index);
       match choice.skolem_branch_choice_witness_term with
       | Some witness_term ->
           begin match term_head witness_term with
           | TmH head ->
               let expected_names = alias_names choice.skolem_branch_choice_symbol in
               let actual_names = alias_names head in
               if not
                    (List.exists
                       (fun actual -> List.mem actual expected_names)
                       actual_names) then
                 error
                   (Printf.sprintf
                      "%s: typed Skolem branch contract %d choice witness term head does not match symbol %s"
                      id index choice.skolem_branch_choice_symbol)
           | _ ->
               error
                 (Printf.sprintf
                    "%s: typed Skolem branch contract %d choice witness term is not headed by a symbol"
                    id index)
           end
       | None -> ())
    choices
