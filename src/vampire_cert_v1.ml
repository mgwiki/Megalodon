(*** Native strict Vampire/Megalodon certificate v1 importer. ***)

open Syntax

type sexpr =
  | Atom of string
  | Str of string
  | List of sexpr list

exception Error of string

type source =
  | SourceAxiom of string
  | SourceNegatedConjecture of string
  | SourceDefinition of string
  | SourceSetReflexivity of string

type literal =
  | Pos of tm
  | Neg of tm

type clause = literal list

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | FormulaCopy of string * string * literal
  | FoolBool of string * string * literal
  | CnfLiteral of string * string * clause
  | Substitute of string * string * (string * tm) list * clause
  | Resolve of string * string * string * int * int * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | Paramodulate of string * string * string * int * int * int list * tm * tm * clause
  | Contradiction of string * string

type certificate = {
  problem : string option;
  steps : step list;
}

let error msg = raise (Error msg)

let is_space = function
  | ' ' | '\n' | '\r' | '\t' -> true
  | _ -> false

let is_delim = function
  | '(' | ')' | '"' -> true
  | c -> is_space c

let parse_sexpr text =
  let len = String.length text in
  let rec skip i =
    if i < len && is_space text.[i] then skip (i + 1) else i
  in
  let rec parse_string buf i =
    if i >= len then error "unterminated string";
    match text.[i] with
    | '"' -> (Str (Buffer.contents buf), i + 1)
    | '\\' when i + 1 < len ->
        let c =
          match text.[i + 1] with
          | 'n' -> '\n'
          | 'r' -> '\r'
          | 't' -> '\t'
          | c -> c
        in
        Buffer.add_char buf c;
        parse_string buf (i + 2)
    | c ->
        Buffer.add_char buf c;
        parse_string buf (i + 1)
  and parse_atom start i =
    if i >= len || is_delim text.[i] then
      if i = start then error "expected atom" else (Atom (String.sub text start (i - start)), i)
    else parse_atom start (i + 1)
  and parse_list acc i =
    let i = skip i in
    if i >= len then error "unterminated list";
    if text.[i] = ')' then (List (List.rev acc), i + 1)
    else
      let item, j = parse_one i in
      parse_list (item :: acc) j
  and parse_one i =
    let i = skip i in
    if i >= len then error "expected S-expression";
    match text.[i] with
    | '(' -> parse_list [] (i + 1)
    | ')' -> error "unexpected ')'"
    | '"' -> parse_string (Buffer.create 16) (i + 1)
    | _ -> parse_atom i i
  in
  let parsed, i = parse_one 0 in
  if skip i <> len then error "trailing input after S-expression";
  parsed

let atom = function
  | Atom x -> x
  | Str x -> x
  | List _ -> error "expected atom"

let int_atom sexpr =
  try int_of_string (atom sexpr) with Failure _ -> error "expected integer"

let rec parse_tp = function
  | List [Atom "PROP"] -> Prop
  | List [Atom "SET"] -> Set
  | List [Atom "TPVAR"; n] -> TpVar (int_atom n)
  | List [Atom "AR"; a; b] -> Ar (parse_tp a, parse_tp b)
  | _ -> error "expected Megalodon type S-expression"

let rec parse_tm = function
  | List [Atom "DB"; n] -> DB (int_atom n)
  | List [Atom "TMH"; h] -> TmH (atom h)
  | List [Atom "PRIM"; n] -> Prim (int_atom n)
  | List [Atom "TPAP"; m; a] -> TpAp (parse_tm m, parse_tp a)
  | List [Atom "AP"; m; n] -> Ap (parse_tm m, parse_tm n)
  | List [Atom "LAM"; a; m] -> Lam (parse_tp a, parse_tm m)
  | List [Atom "IMP"; m; n] -> Imp (parse_tm m, parse_tm n)
  | List [Atom "ALL"; a; m] -> All (parse_tp a, parse_tm m)
  | _ -> error "expected Megalodon term S-expression"

let parse_source = function
  | List [Atom "source"; Atom "axiom"; name] -> SourceAxiom (atom name)
  | List [Atom "source"; Atom "negated_conjecture"; name] -> SourceNegatedConjecture (atom name)
  | List [Atom "source"; Atom "definition"; name] -> SourceDefinition (atom name)
  | List [Atom "source"; Atom "set_reflexivity"; name] -> SourceSetReflexivity (atom name)
  | List (Atom "source" :: Atom bad :: _) when String.length bad >= 8 && String.sub bad 0 8 = "vampire_" ->
      error ("strict certificate v1 rejects source " ^ bad)
  | List (Atom "source" :: _) -> error "unsupported certificate source"
  | _ -> error "expected certificate source"

let parse_literal = function
  | List [Atom "pos"; tm] -> Pos (parse_tm tm)
  | List [Atom "neg"; tm] -> Neg (parse_tm tm)
  | _ -> error "expected clause literal"

let parse_clause = function
  | List (Atom "clause" :: literals) -> List.map parse_literal literals
  | _ -> error "expected clause"

let parse_parents = function
  | List [Atom "parents"; a; b] -> (atom a, atom b)
  | _ -> error "expected two parents"

let parse_pivot = function
  | List [Atom "pivot"; a; b] -> (int_atom a, int_atom b)
  | _ -> error "expected pivot"

let parse_parent = function
  | List [Atom "parent"; parent] -> atom parent
  | _ -> error "expected parent"

let parse_indexed_parent name = function
  | List [Atom label; parent; index] when label = name -> (atom parent, int_atom index)
  | _ -> error ("expected " ^ name ^ " parent and literal index")

let parse_literal_index = function
  | List [Atom "literal"; index] -> int_atom index
  | _ -> error "expected literal index"

let parse_literal_pair = function
  | List [Atom "literals"; left; right] -> (int_atom left, int_atom right)
  | _ -> error "expected literal-index pair"

let parse_position = function
  | List (Atom "position" :: indices) -> List.map int_atom indices
  | _ -> error "expected position"

let parse_tm_field name = function
  | List [Atom label; tm] when label = name -> parse_tm tm
  | _ -> error ("expected " ^ name ^ " term")

let parse_substitution = function
  | List (Atom "subst" :: entries) ->
      List.map
        (function
          | List [name; tm] -> (atom name, parse_tm tm)
          | _ -> error "expected substitution binding")
        entries
  | _ -> error "expected substitution"

let parse_result = function
  | List [Atom "result"; clause] -> parse_clause clause
  | _ -> error "expected result clause"

let parse_literal_result = function
  | List [Atom "result"; literal] -> parse_literal literal
  | _ -> error "expected result literal"

let parse_step = function
  | List [Atom "input"; id; source; clause] ->
      Input (atom id, parse_source source, parse_clause clause)
  | List [Atom "formula_input"; id; source; literal] ->
      FormulaInput (atom id, parse_source source, parse_literal literal)
  | List [Atom "formula_copy"; id; parent; result] ->
      FormulaCopy (atom id, parse_parent parent, parse_literal_result result)
  | List [Atom "fool_bool"; id; parent; result] ->
      FoolBool (atom id, parse_parent parent, parse_literal_result result)
  | List [Atom "cnf_literal"; id; parent; result] ->
      CnfLiteral (atom id, parse_parent parent, parse_result result)
  | List [Atom "substitute"; id; parent; subst; result] ->
      Substitute (atom id, parse_parent parent, parse_substitution subst, parse_result result)
  | List [Atom "resolve"; id; parents; pivot; result] ->
      let a, b = parse_parents parents in
      let i, j = parse_pivot pivot in
      Resolve (atom id, a, b, i, j, parse_result result)
  | List [Atom "factor"; id; parent; literals; result] ->
      let i, j = parse_literal_pair literals in
      Factor (atom id, parse_parent parent, i, j, parse_result result)
  | List [Atom "equality_resolution"; id; parent; literal; result] ->
      EqualityResolution (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
  | List [Atom "paramodulate"; id; equality; target; position; from_tm; to_tm; result] ->
      let equality_parent, equality_index = parse_indexed_parent "equality" equality in
      let target_parent, target_index = parse_indexed_parent "target" target in
      Paramodulate (
        atom id,
        equality_parent,
        target_parent,
        equality_index,
        target_index,
        parse_position position,
        parse_tm_field "from" from_tm,
        parse_tm_field "to" to_tm,
        parse_result result)
  | List [Atom "contradiction"; id; parent] ->
      Contradiction (atom id, atom parent)
  | List (Atom rule :: _) ->
      error ("strict certificate v1 importer does not support rule " ^ rule)
  | _ -> error "expected certificate step"

let step_id = function
  | Input (id, _, _) -> id
  | FormulaInput (id, _, _) -> id
  | FormulaCopy (id, _, _) -> id
  | FoolBool (id, _, _) -> id
  | CnfLiteral (id, _, _) -> id
  | Substitute (id, _, _, _) -> id
  | Resolve (id, _, _, _, _, _) -> id
  | Factor (id, _, _, _, _) -> id
  | EqualityResolution (id, _, _, _) -> id
  | Paramodulate (id, _, _, _, _, _, _, _, _) -> id
  | Contradiction (id, _) -> id

let check_duplicate_ids steps =
  let seen = Hashtbl.create 17 in
  List.iter
    (fun step ->
      let id = step_id step in
      if Hashtbl.mem seen id then error ("duplicate certificate step id " ^ id);
      Hashtbl.add seen id ())
    steps

let parse_problem = function
  | List [Atom "problem"; name] -> Some (atom name)
  | _ -> None

let parse_certificate text =
  match parse_sexpr text with
  | List (Atom "certificate" :: Atom "vampire-megalodon" :: Atom "1" :: rest) ->
      let problem, step_forms =
        match rest with
        | first :: tail ->
            begin match parse_problem first with
            | Some _ as problem -> (problem, tail)
            | None -> (None, rest)
            end
        | [] -> (None, [])
      in
      let steps = List.map parse_step step_forms in
      check_duplicate_ids steps;
      { problem; steps }
  | _ -> error "expected (certificate vampire-megalodon 1 ...)"

let literal_atom = function
  | Pos tm -> tm
  | Neg tm -> tm

let complementary left right =
  match left, right with
  | Pos a, Neg b -> a = b
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
        match remove_one item remaining with
        | None -> false
        | Some remaining -> consume remaining rest
  in
  List.length left = List.length right && consume left right

let lookup_clause checked id =
  try List.assoc id checked with Not_found -> error ("unknown certificate parent " ^ id)

let rec subst_tm subst tm =
  match tm with
  | DB _ -> tm
  | TmH h ->
      begin
        try List.assoc h subst with Not_found -> tm
      end
  | Prim _ -> tm
  | TpAp (m, a) -> TpAp (subst_tm subst m, a)
  | Ap (m, n) -> Ap (subst_tm subst m, subst_tm subst n)
  | Lam (a, m) -> Lam (a, subst_tm subst m)
  | Imp (m, n) -> Imp (subst_tm subst m, subst_tm subst n)
  | All (a, m) -> All (a, subst_tm subst m)

let subst_literal subst = function
  | Pos tm -> Pos (subst_tm subst tm)
  | Neg tm -> Neg (subst_tm subst tm)

let subst_clause subst clause = List.map (subst_literal subst) clause

let rec tm_at_position tm position what =
  match position with
  | [] -> tm
  | index :: rest ->
      let child =
        match tm, index with
        | TpAp (m, _), 0 -> m
        | Ap (m, _), 0 -> m
        | Ap (_, n), 1 -> n
        | Lam (_, m), 0 -> m
        | Imp (m, _), 0 -> m
        | Imp (_, n), 1 -> n
        | All (_, m), 0 -> m
        | _ -> error (what ^ " position is out of bounds")
      in
      tm_at_position child rest what

let rec replace_tm_at_position tm position replacement what =
  match position with
  | [] -> replacement
  | index :: rest ->
      match tm, index with
      | TpAp (m, a), 0 -> TpAp (replace_tm_at_position m rest replacement what, a)
      | Ap (m, n), 0 -> Ap (replace_tm_at_position m rest replacement what, n)
      | Ap (m, n), 1 -> Ap (m, replace_tm_at_position n rest replacement what)
      | Lam (a, m), 0 -> Lam (a, replace_tm_at_position m rest replacement what)
      | Imp (m, n), 0 -> Imp (replace_tm_at_position m rest replacement what, n)
      | Imp (m, n), 1 -> Imp (m, replace_tm_at_position n rest replacement what)
      | All (a, m), 0 -> All (a, replace_tm_at_position m rest replacement what)
      | _ -> error (what ^ " position is out of bounds")

let replace_literal_atom literal atom =
  match literal with
  | Pos _ -> Pos atom
  | Neg _ -> Neg atom

let check_input_source = function
  | SourceAxiom name
  | SourceNegatedConjecture name
  | SourceDefinition name
  | SourceSetReflexivity name ->
      if name = "" then error "input source name must be non-empty"

let check_cnf_literal checked id parent_id result =
  let parent_clause = lookup_clause checked parent_id in
  begin match parent_clause with
  | [_] -> ()
  | _ -> error (id ^ ": cnf_literal parent is not a literal formula")
  end;
  if not (same_clause_multiset parent_clause result) then
    error (id ^ ": cnf_literal result does not match source literal")

let equality_to_true atom =
  Ap (Ap (TmH "=", atom), TmH "f__true")

let check_formula_copy checked id parent_id result =
  let parent_clause = lookup_clause checked parent_id in
  if not (same_clause_multiset parent_clause [result]) then
    error (id ^ ": formula_copy result does not match parent")

let check_fool_bool checked id parent_id result =
  let parent_clause = lookup_clause checked parent_id in
  let expected =
    match parent_clause with
    | [Pos atom] -> Pos (equality_to_true atom)
    | [Neg atom] -> Neg (equality_to_true atom)
    | _ -> error (id ^ ": fool_bool parent is not a singleton formula")
  in
  if not (same_clause_multiset [expected] [result]) then
    error (id ^ ": fool_bool result is not the Boolean-term equality to true")

let check_resolution checked id left_id right_id left_index right_index result =
  let left_clause = lookup_clause checked left_id in
  let right_clause = lookup_clause checked right_id in
  let left_pivot = nth left_index left_clause (id ^ " left pivot") in
  let right_pivot = nth right_index right_clause (id ^ " right pivot") in
  if not (complementary left_pivot right_pivot) then
    error (id ^ ": resolution pivots are not complementary");
  let left_rest = remove_at left_index left_clause (id ^ " left pivot") in
  let right_rest = remove_at right_index right_clause (id ^ " right pivot") in
  let expected = left_rest @ right_rest in
  if not (same_clause_multiset expected result) then
    error (id ^ ": resolution result does not match parent clauses after pivot removal")

let check_substitute checked id parent_id subst result =
  let parent_clause = lookup_clause checked parent_id in
  let expected = subst_clause subst parent_clause in
  if not (same_clause_multiset expected result) then
    error (id ^ ": substitution result does not match parent under explicit substitution")

let check_factor checked id parent_id left_index right_index result =
  if left_index = right_index then error (id ^ ": factor literal indices must be distinct");
  let parent_clause = lookup_clause checked parent_id in
  let left_literal = nth left_index parent_clause (id ^ " first factor literal") in
  let right_literal = nth right_index parent_clause (id ^ " second factor literal") in
  if left_literal <> right_literal then
    error (id ^ ": native certificate v1 currently factors only identical literals");
  let remove_index = if left_index > right_index then left_index else right_index in
  let expected = remove_at remove_index parent_clause (id ^ " removed factor literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": factor result does not match parent clause after duplicate removal")

let equality_sides = function
  | Ap (Ap (TmH h, left), right) when h = "=" || h = "eq" -> Some (left, right)
  | _ -> None

let swap_literal_equality = function
  | Pos atom ->
      begin match equality_sides atom with
      | Some (left, right) -> Some (Pos (Ap (Ap (TmH "=", right), left)))
      | None -> None
      end
  | Neg atom ->
      begin match equality_sides atom with
      | Some (left, right) -> Some (Neg (Ap (Ap (TmH "=", right), left)))
      | None -> None
      end

let check_equality_resolution checked id parent_id literal_index result =
  let parent_clause = lookup_clause checked parent_id in
  let literal = nth literal_index parent_clause (id ^ " equality-resolution literal") in
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
  let expected = remove_at literal_index parent_clause (id ^ " equality-resolution literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-resolution result does not match parent after literal removal")

let check_paramodulate checked id equality_parent_id target_parent_id equality_index target_index position from_tm to_tm result =
  let equality_clause = lookup_clause checked equality_parent_id in
  let target_clause = lookup_clause checked target_parent_id in
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
  let found = tm_at_position target_atom position (id ^ " target") in
  if found <> from_tm then error (id ^ ": paramodulation position does not contain from term");
  let rewritten_atom = replace_tm_at_position target_atom position to_tm (id ^ " target") in
  let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
  let equality_rest = remove_at equality_index equality_clause (id ^ " equality literal") in
  let target_rest = remove_at target_index target_clause (id ^ " target literal") in
  let expected = equality_rest @ target_rest @ [rewritten_literal] in
  if not (same_clause_multiset expected result) then
    begin match swap_literal_equality rewritten_literal with
    | Some swapped_literal ->
        let swapped_expected = equality_rest @ target_rest @ [swapped_literal] in
        if not (same_clause_multiset swapped_expected result) then
          error (id ^ ": paramodulation result does not match explicit rewrite")
    | None -> error (id ^ ": paramodulation result does not match explicit rewrite")
    end

let check_step checked = function
  | Input (id, source, clause) ->
      check_input_source source;
      (id, clause) :: checked
  | FormulaInput (id, source, literal) ->
      check_input_source source;
      (id, [literal]) :: checked
  | FormulaCopy (id, parent_id, result) ->
      check_formula_copy checked id parent_id result;
      (id, [result]) :: checked
  | FoolBool (id, parent_id, result) ->
      check_fool_bool checked id parent_id result;
      (id, [result]) :: checked
  | CnfLiteral (id, parent_id, result) ->
      check_cnf_literal checked id parent_id result;
      (id, result) :: checked
  | Substitute (id, parent_id, subst, result) ->
      check_substitute checked id parent_id subst result;
      (id, result) :: checked
  | Resolve (id, left_id, right_id, left_index, right_index, result) ->
      check_resolution checked id left_id right_id left_index right_index result;
      (id, result) :: checked
  | Factor (id, parent_id, left_index, right_index, result) ->
      check_factor checked id parent_id left_index right_index result;
      (id, result) :: checked
  | EqualityResolution (id, parent_id, literal_index, result) ->
      check_equality_resolution checked id parent_id literal_index result;
      (id, result) :: checked
  | Paramodulate (id, equality_parent_id, target_parent_id, equality_index, target_index, position, from_tm, to_tm, result) ->
      check_paramodulate checked id equality_parent_id target_parent_id equality_index target_index position from_tm to_tm result;
      (id, result) :: checked
  | Contradiction (id, parent_id) ->
      let clause = lookup_clause checked parent_id in
      if clause <> [] then error (id ^ ": contradiction parent is not the empty clause");
      (id, []) :: checked

let check_certificate cert =
  let checked = List.fold_left check_step [] cert.steps in
  begin match checked with
  | (_, []) :: _ -> ()
  | (id, _) :: _ -> error (id ^ ": final certificate step is not the empty clause")
  | [] -> error "certificate contains no steps"
  end;
  List.rev checked
