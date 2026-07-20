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
