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
