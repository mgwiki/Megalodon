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

type checked_item =
  | CheckedClause of clause
  | CheckedFormula of tm

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | FormulaTermInput of string * source * tm
  | FormulaTermCopy of string * string * tm
  | RectifyFormula of string * string * tm
  | FoolFormula of string * string * tm
  | EnnfFormula of string * string * tm
  | SkolemFormula of string * string * (string * tm) list * tm
  | SkolemFormulaComputed of string * string * (string * tm) list
  | CnfFormulaClause of string * string * int * clause
  | FormulaCopy of string * string * literal
  | FoolBool of string * string * literal
  | CnfLiteral of string * string * clause
  | PredicateDefinition of string * string * tm
  | PredicateDefinitionFold of string * string * string * tm
  | DefinitionInput of string * clause
  | FoolExhaustiveness of string * clause
  | FoolDistinctness of string * clause
  | Substitute of string * string * (string * tm) list * clause
  | Resolve of string * string * string * int * int * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | EqualityFactoring of string * string * int * int * (string * tm) list * clause
  | TruthConflict of string * string * int * clause
  | EqualitySymmetry of string * string * int * clause
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

let rec subst_named_tm name replacement = function
  | TmH h when h = name -> replacement
  | TpAp (m, a) -> TpAp (subst_named_tm name replacement m, a)
  | Ap (m, n) -> Ap (subst_named_tm name replacement m, subst_named_tm name replacement n)
  | Lam (tp, body) -> Lam (tp, subst_named_tm name replacement body)
  | Imp (m, n) -> Imp (subst_named_tm name replacement m, subst_named_tm name replacement n)
  | All (tp, body) -> All (tp, subst_named_tm name replacement body)
  | tm -> tm

let rec parse_tm = function
  | List [Atom "DB"; n] -> DB (int_atom n)
  | List [Atom "TMH"; h] -> TmH (atom h)
  | List [Atom "PRIM"; n] -> Prim (int_atom n)
  | List [Atom "TPAP"; m; a] -> TpAp (parse_tm m, parse_tp a)
  | List [Atom "AP"; m; n] -> Ap (parse_tm m, parse_tm n)
  | List [Atom "LAM"; a; m] -> Lam (parse_tp a, parse_tm m)
  | List [Atom "LAMV"; name; a; m] ->
      ignore (parse_tp a);
      Ap (TmH "vLAM", subst_named_tm (atom name) (TmH "db0") (parse_tm m))
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

let parse_symbol = function
  | List [Atom "symbol"; symbol] -> atom symbol
  | _ -> error "expected symbol"

let parse_named_parent name = function
  | List [Atom label; parent] when label = name -> atom parent
  | _ -> error ("expected " ^ name ^ " parent")

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

let parse_formula_result = function
  | List [Atom "result"; List [Atom "formula"; tm]] -> parse_tm tm
  | _ -> error "expected result formula"

let parse_formula = function
  | List [Atom "formula"; tm] -> parse_tm tm
  | _ -> error "expected formula"

let parse_index = function
  | List [Atom "index"; index] -> int_atom index
  | _ -> error "expected index"

let parse_named_index name = function
  | List [Atom label; index] when label = name -> int_atom index
  | _ -> error ("expected " ^ name ^ " index")

let parse_step = function
  | List [Atom "input"; id; source; clause] ->
      Input (atom id, parse_source source, parse_clause clause)
  | List [Atom "formula_input"; id; source; literal] ->
      FormulaInput (atom id, parse_source source, parse_literal literal)
  | List [Atom "formula_term_input"; id; source; formula] ->
      FormulaTermInput (atom id, parse_source source, parse_formula formula)
  | List [Atom "formula_term_copy"; id; parent; result] ->
      FormulaTermCopy (atom id, parse_parent parent, parse_formula_result result)
  | List [Atom "rectify_formula"; id; parent; result] ->
      RectifyFormula (atom id, parse_parent parent, parse_formula_result result)
  | List [Atom "fool_formula"; id; parent; result] ->
      FoolFormula (atom id, parse_parent parent, parse_formula_result result)
  | List [Atom "ennf_formula"; id; parent; result] ->
      EnnfFormula (atom id, parse_parent parent, parse_formula_result result)
  | List [Atom "skolem_formula"; id; parent; subst; result] ->
      SkolemFormula (atom id, parse_parent parent, parse_substitution subst, parse_formula_result result)
  | List [Atom "skolem_formula_computed"; id; parent; subst] ->
      SkolemFormulaComputed (atom id, parse_parent parent, parse_substitution subst)
  | List [Atom "cnf_formula_clause"; id; parent; index; result] ->
      CnfFormulaClause (atom id, parse_parent parent, parse_index index, parse_result result)
  | List [Atom "formula_copy"; id; parent; result] ->
      FormulaCopy (atom id, parse_parent parent, parse_literal_result result)
  | List [Atom "fool_bool"; id; parent; result] ->
      FoolBool (atom id, parse_parent parent, parse_literal_result result)
  | List [Atom "cnf_literal"; id; parent; result] ->
      CnfLiteral (atom id, parse_parent parent, parse_result result)
  | List [Atom "predicate_definition"; id; symbol; result] ->
      PredicateDefinition (atom id, parse_symbol symbol, parse_formula_result result)
  | List [Atom "predicate_definition_fold"; id; source; definition; result] ->
      PredicateDefinitionFold
        (atom id, parse_named_parent "source" source, parse_named_parent "definition" definition, parse_formula_result result)
  | List [Atom "definition_input"; id; result] ->
      DefinitionInput (atom id, parse_result result)
  | List [Atom "fool_exhaustiveness"; id; result] ->
      FoolExhaustiveness (atom id, parse_result result)
  | List [Atom "fool_distinctness"; id; result] ->
      FoolDistinctness (atom id, parse_result result)
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
  | List [Atom "equality_factoring"; id; parent; selected; other; subst; result] ->
      EqualityFactoring (
        atom id,
        parse_parent parent,
        parse_named_index "selected" selected,
        parse_named_index "other" other,
        parse_substitution subst,
        parse_result result)
  | List [Atom "truth_conflict"; id; parent; literal; result] ->
      TruthConflict (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
  | List [Atom "equality_symmetry"; id; parent; literal; result] ->
      EqualitySymmetry (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
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
  | FormulaTermInput (id, _, _) -> id
  | FormulaTermCopy (id, _, _) -> id
  | RectifyFormula (id, _, _) -> id
  | FoolFormula (id, _, _) -> id
  | EnnfFormula (id, _, _) -> id
  | SkolemFormula (id, _, _, _) -> id
  | SkolemFormulaComputed (id, _, _) -> id
  | CnfFormulaClause (id, _, _, _) -> id
  | FormulaCopy (id, _, _) -> id
  | FoolBool (id, _, _) -> id
  | CnfLiteral (id, _, _) -> id
  | PredicateDefinition (id, _, _) -> id
  | PredicateDefinitionFold (id, _, _, _) -> id
  | DefinitionInput (id, _) -> id
  | FoolExhaustiveness (id, _) -> id
  | FoolDistinctness (id, _) -> id
  | Substitute (id, _, _, _) -> id
  | Resolve (id, _, _, _, _, _) -> id
  | Factor (id, _, _, _, _) -> id
  | EqualityResolution (id, _, _, _) -> id
  | EqualityFactoring (id, _, _, _, _, _) -> id
  | TruthConflict (id, _, _, _) -> id
  | EqualitySymmetry (id, _, _, _) -> id
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
  match (try List.assoc id checked with Not_found -> error ("unknown certificate parent " ^ id)) with
  | CheckedClause clause -> clause
  | CheckedFormula _ -> error (id ^ " is a formula parent, but a clause parent was expected")

let lookup_formula checked id =
  match (try List.assoc id checked with Not_found -> error ("unknown certificate parent " ^ id)) with
  | CheckedFormula formula -> formula
  | CheckedClause _ -> error (id ^ " is a clause parent, but a formula parent was expected")

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

let try_tm_at_position tm position =
  try Some (tm_at_position tm position "term") with Error _ -> None

let replace_literal_atom literal atom =
  match literal with
  | Pos _ -> Pos atom
  | Neg _ -> Neg atom

let equality_sides = function
  | Ap (Ap (TmH h, left), right) when h = "=" || h = "eq" -> Some (left, right)
  | _ -> None

let equality_to_true atom =
  Ap (Ap (TmH "=", atom), TmH "f__true")

let paramodulation_position_candidates target_atom position =
  let base = [position] in
  match equality_sides target_atom, position with
  | Some _, 1 :: rest -> base @ [[0; 1] @ rest]
  | Some _, [0; 1] -> base @ [[1]]
  | _ -> base

let vampire_false = TmH "vampire_false"

let vampire_or left right =
  Ap (Ap (TmH "vampire_or", left), right)

let vampire_and left right =
  Ap (Ap (TmH "vampire_and", left), right)

let vampire_exists tp body =
  Ap (TmH "vampire_exists_prop", Lam (tp, body))

let rec app2_name = function
  | Ap (Ap (TmH h, left), right) -> Some (h, left, right)
  | _ -> None

let is_vampire_false = function
  | TmH "vampire_false" -> true
  | _ -> false

let neg_formula tm =
  Imp (tm, vampire_false)

let is_vampire_var_name name =
  let len = String.length name in
  len >= 2 && name.[0] = 'X' &&
  let rec digits i =
    i = len || (name.[i] >= '0' && name.[i] <= '9' && digits (i + 1))
  in
  digits 1

let add_vampire_var_renaming left right left_to_right right_to_left =
  if left = right then Some (left_to_right, right_to_left)
  else if is_vampire_var_name left && is_vampire_var_name right then
    let left_ok =
      try List.assoc left left_to_right = right with Not_found -> true
    in
    let right_ok =
      try List.assoc right right_to_left = left with Not_found -> true
    in
    if left_ok && right_ok then
      let left_to_right =
        if List.mem_assoc left left_to_right then left_to_right
        else (left, right) :: left_to_right
      in
      let right_to_left =
        if List.mem_assoc right right_to_left then right_to_left
        else (right, left) :: right_to_left
      in
      Some (left_to_right, right_to_left)
    else None
  else None

let rec tm_equal_mod_vampire_var_renaming left right left_to_right right_to_left =
  match left, right with
  | DB i, DB j when i = j -> Some (left_to_right, right_to_left)
  | TmH h, TmH k -> add_vampire_var_renaming h k left_to_right right_to_left
  | Prim i, Prim j when i = j -> Some (left_to_right, right_to_left)
  | TpAp (m, a), TpAp (n, b) when a = b ->
      tm_equal_mod_vampire_var_renaming m n left_to_right right_to_left
  | Ap (m1, m2), Ap (n1, n2) ->
      begin match tm_equal_mod_vampire_var_renaming m1 n1 left_to_right right_to_left with
      | None -> None
      | Some (left_to_right, right_to_left) ->
          tm_equal_mod_vampire_var_renaming m2 n2 left_to_right right_to_left
      end
  | Lam (a, m), Lam (b, n) when a = b ->
      tm_equal_mod_vampire_var_renaming m n left_to_right right_to_left
  | Imp (m1, m2), Imp (n1, n2) ->
      begin match tm_equal_mod_vampire_var_renaming m1 n1 left_to_right right_to_left with
      | None -> None
      | Some (left_to_right, right_to_left) ->
          tm_equal_mod_vampire_var_renaming m2 n2 left_to_right right_to_left
      end
  | All (a, m), All (b, n) when a = b ->
      tm_equal_mod_vampire_var_renaming m n left_to_right right_to_left
  | _ -> None

let same_mod_vampire_var_renaming left right =
  match tm_equal_mod_vampire_var_renaming left right [] [] with
  | Some _ -> true
  | None -> false

let add_scoped_vampire_var_renaming left right frames =
  if left = right then Some frames
  else if is_vampire_var_name left && is_vampire_var_name right then
    match frames with
    | [] -> None
    | (left_to_right, right_to_left) :: outer ->
        let left_ok =
          try List.assoc left left_to_right = right with Not_found -> true
        in
        let right_ok =
          try List.assoc right right_to_left = left with Not_found -> true
        in
        if left_ok && right_ok then
          let left_to_right =
            if List.mem_assoc left left_to_right then left_to_right
            else (left, right) :: left_to_right
          in
          let right_to_left =
            if List.mem_assoc right right_to_left then right_to_left
            else (right, left) :: right_to_left
          in
          Some ((left_to_right, right_to_left) :: outer)
        else None
  else None

let rec tm_equal_mod_scoped_vampire_var_renaming left right frames =
  match left, right with
  | DB i, DB j when i = j -> Some frames
  | TmH h, TmH k -> add_scoped_vampire_var_renaming h k frames
  | Prim i, Prim j when i = j -> Some frames
  | TpAp (m, a), TpAp (n, b) when a = b ->
      tm_equal_mod_scoped_vampire_var_renaming m n frames
  | Ap (m1, m2), Ap (n1, n2) ->
      begin match tm_equal_mod_scoped_vampire_var_renaming m1 n1 frames with
      | None -> None
      | Some frames -> tm_equal_mod_scoped_vampire_var_renaming m2 n2 frames
      end
  | Lam (a, m), Lam (b, n) when a = b ->
      begin match tm_equal_mod_scoped_vampire_var_renaming m n (([], []) :: frames) with
      | None -> None
      | Some _ -> Some frames
      end
  | Imp (m1, m2), Imp (n1, n2) ->
      begin match tm_equal_mod_scoped_vampire_var_renaming m1 n1 frames with
      | None -> None
      | Some frames -> tm_equal_mod_scoped_vampire_var_renaming m2 n2 frames
      end
  | All (a, m), All (b, n) when a = b ->
      begin match tm_equal_mod_scoped_vampire_var_renaming m n (([], []) :: frames) with
      | None -> None
      | Some _ -> Some frames
      end
  | _ -> None

let same_mod_scoped_vampire_var_renaming left right =
  match tm_equal_mod_scoped_vampire_var_renaming left right [([], [])] with
  | Some _ -> true
  | None -> false

let is_equality_atom tm =
  match equality_sides tm with
  | Some _ -> true
  | None -> false

let rec fool_formula_tm tm =
  match tm with
  | Imp (left, right) -> Imp (fool_formula_tm left, fool_formula_tm right)
  | All (tp, body) -> All (tp, fool_formula_tm body)
  | Ap (Ap (TmH "vampire_or", left), right) -> vampire_or (fool_formula_tm left) (fool_formula_tm right)
  | Ap (Ap (TmH "vampire_and", left), right) -> vampire_and (fool_formula_tm left) (fool_formula_tm right)
  | Ap (TmH "vampire_exists_prop", Lam (tp, body)) -> vampire_exists tp (fool_formula_tm body)
  | Lam (tp, body) -> Lam (tp, fool_formula_tm body)
  | TmH "vampire_true"
  | TmH "vampire_false" -> tm
  | _ when is_equality_atom tm -> tm
  | TmH h when is_vampire_var_name h -> Ap (Ap (TmH "=", TmH "f__true"), tm)
  | _ -> equality_to_true tm

let rec ennf_pos tm =
  match tm with
  | Imp (left, false_tm) when is_vampire_false false_tm -> ennf_neg left
  | Imp (left, right) -> vampire_or (ennf_neg left) (ennf_pos right)
  | All (tp, body) -> All (tp, ennf_pos body)
  | Ap (Ap (TmH "vampire_or", left), right) -> vampire_or (ennf_pos left) (ennf_pos right)
  | Ap (Ap (TmH "vampire_and", left), right) -> vampire_and (ennf_pos left) (ennf_pos right)
  | _ -> tm
and ennf_neg tm =
  match tm with
  | Imp (left, right) -> vampire_and (ennf_pos left) (ennf_neg right)
  | All (tp, body) -> vampire_exists tp (ennf_neg body)
  | Ap (Ap (TmH "vampire_or", left), right) -> vampire_and (ennf_neg left) (ennf_neg right)
  | Ap (Ap (TmH "vampire_and", left), right) -> vampire_or (ennf_neg left) (ennf_neg right)
  | _ -> neg_formula tm

let rec skolemize_formula_tm subst tm =
  match tm with
  | Imp (left, right) -> Imp (skolemize_formula_tm subst left, skolemize_formula_tm subst right)
  | All (tp, body) -> All (tp, skolemize_formula_tm subst body)
  | Ap (Ap (TmH "vampire_or", left), right) -> vampire_or (skolemize_formula_tm subst left) (skolemize_formula_tm subst right)
  | Ap (Ap (TmH "vampire_and", left), right) -> vampire_and (skolemize_formula_tm subst left) (skolemize_formula_tm subst right)
  | Ap (TmH "vampire_exists_prop", Lam (_, body)) ->
      skolemize_formula_tm subst (subst_tm subst body)
  | Lam (tp, body) -> Lam (tp, skolemize_formula_tm subst body)
  | _ -> tm

let rec normalize_bool_equality_orientation tm =
  let normalize = normalize_bool_equality_orientation in
  match tm with
  | Ap (Ap (TmH "=", left), TmH h) when h = "f__true" || h = "f__false" ->
      Ap (Ap (TmH "=", TmH h), normalize left)
  | Ap (Ap (TmH "=", left), right) ->
      Ap (Ap (TmH "=", normalize left), normalize right)
  | TpAp (m, a) -> TpAp (normalize m, a)
  | Ap (m, n) -> Ap (normalize m, normalize n)
  | Lam (tp, body) -> Lam (tp, normalize body)
  | Imp (left, right) -> Imp (normalize left, normalize right)
  | All (tp, body) -> All (tp, normalize body)
  | _ -> tm

let rec strip_forall = function
  | All (_, body) -> strip_forall body
  | tm -> tm

let literal_of_formula_tm tm =
  match tm with
  | Imp (atom, false_tm) when is_vampire_false false_tm -> Neg atom
  | _ -> Pos tm

let formula_tm_of_literal = function
  | Pos tm -> tm
  | Neg tm -> Imp (tm, vampire_false)

let rec cnf_clauses tm =
  match strip_forall tm with
  | Ap (Ap (TmH "vampire_and", left), right) ->
      cnf_clauses left @ cnf_clauses right
  | Ap (Ap (TmH "vampire_or", left), right) ->
      let left_clauses = cnf_clauses left in
      let right_clauses = cnf_clauses right in
      List.concat
        (List.map
           (fun right_clause ->
             List.map (fun left_clause -> left_clause @ right_clause) left_clauses)
           right_clauses)
  | atom -> [[literal_of_formula_tm atom]]

let check_input_source = function
  | SourceAxiom name
  | SourceNegatedConjecture name
  | SourceDefinition name
  | SourceSetReflexivity name ->
      if name = "" then error "input source name must be non-empty"

let check_cnf_literal checked id parent_id result =
  let parent_clause =
    match (try List.assoc parent_id checked with Not_found -> error ("unknown certificate parent " ^ parent_id)) with
    | CheckedFormula parent_formula -> [literal_of_formula_tm parent_formula]
    | CheckedClause parent_clause ->
        begin match parent_clause with
        | [_] -> parent_clause
        | _ -> error (id ^ ": cnf_literal parent is not a literal formula")
        end
  in
  if not (same_clause_multiset parent_clause result) then
    error (id ^ ": cnf_literal result does not match source literal")

let check_formula_term_copy checked id parent_id result =
  let parent_formula = lookup_formula checked parent_id in
  if parent_formula <> result then
    error (id ^ ": formula_term_copy result does not match parent")

let check_rectify_formula checked id parent_id result =
  let parent_formula = lookup_formula checked parent_id in
  let normalized_parent = normalize_bool_equality_orientation parent_formula in
  let normalized_result = normalize_bool_equality_orientation result in
  if not (same_mod_vampire_var_renaming parent_formula result
          || same_mod_scoped_vampire_var_renaming parent_formula result
          || same_mod_vampire_var_renaming normalized_parent normalized_result
          || same_mod_scoped_vampire_var_renaming normalized_parent normalized_result) then
    error (id ^ ": rectify_formula result is not a bijective Vampire-variable renaming of parent")

let check_fool_formula checked id parent_id result =
  let parent_formula = lookup_formula checked parent_id in
  let expected = fool_formula_tm parent_formula in
  if expected <> result
    && normalize_bool_equality_orientation expected <> normalize_bool_equality_orientation result then
    error (id ^ ": fool_formula result does not match recursive FOOL Boolean lifting")

let check_ennf_formula checked id parent_id result =
  let parent_formula = lookup_formula checked parent_id in
  let expected = ennf_pos parent_formula in
  if expected <> result then
    error (id ^ ": ennf_formula result does not match deterministic ENNF transformation")

let check_skolem_formula checked id parent_id subst result =
  let parent_formula = lookup_formula checked parent_id in
  let expected = skolemize_formula_tm subst parent_formula in
  if expected <> result
    && normalize_bool_equality_orientation expected <> normalize_bool_equality_orientation result then
    error (id ^ ": skolem_formula result does not match explicit skolem substitution")

let check_skolem_formula_computed checked parent_id subst =
  let parent_formula = lookup_formula checked parent_id in
  skolemize_formula_tm subst parent_formula

let check_cnf_formula_clause checked id parent_id index result =
  if index < 0 then error (id ^ ": cnf_formula_clause index must be non-negative");
  let parent_formula = lookup_formula checked parent_id in
  let clauses = cnf_clauses parent_formula in
  let expected = nth index clauses (id ^ " CNF clause") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": cnf_formula_clause result does not match deterministic CNF projection")

let check_formula_copy checked id parent_id result =
  match (try List.assoc parent_id checked with Not_found -> error ("unknown certificate parent " ^ parent_id)) with
  | CheckedClause parent_clause ->
      if not (same_clause_multiset parent_clause [result]) then
        error (id ^ ": formula_copy result does not match parent")
  | CheckedFormula parent_formula ->
      let expected = literal_of_formula_tm parent_formula in
      if expected <> result then
        error (id ^ ": formula_copy result does not match formula parent")

let check_fool_bool checked id parent_id result =
  let parent_clause =
    match (try List.assoc parent_id checked with Not_found -> error ("unknown certificate parent " ^ parent_id)) with
    | CheckedClause clause -> clause
    | CheckedFormula formula -> [literal_of_formula_tm formula]
  in
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

let check_definition_input id clause =
  match clause with
  | [Pos atom] ->
      begin match equality_sides atom with
      | Some _ -> ()
      | None -> error (id ^ ": definition_input is not an equality")
      end
  | [_] -> error (id ^ ": definition_input literal must be positive")
  | _ -> error (id ^ ": definition_input must be a singleton equality clause")

let rec head_symbol = function
  | TmH h -> Some h
  | Ap (fn, _) -> head_symbol fn
  | TpAp (fn, _) -> head_symbol fn
  | _ -> None

let rec tm_contains_symbol symbol = function
  | TmH h -> h = symbol
  | Prim _ | DB _ -> false
  | TpAp (tm, _) -> tm_contains_symbol symbol tm
  | Ap (left, right)
  | Imp (left, right) ->
      tm_contains_symbol symbol left || tm_contains_symbol symbol right
  | Lam (_, body)
  | All (_, body) ->
      tm_contains_symbol symbol body

let definiendum_head atom =
  match equality_sides atom with
  | Some (TmH h, other) when h = "f__true" || h = "f__false" -> head_symbol other
  | Some (other, TmH h) when h = "f__true" || h = "f__false" -> head_symbol other
  | _ -> head_symbol atom

let rec strip_universal_binders = function
  | All (_, body) -> strip_universal_binders body
  | tm -> tm

let predicate_definition_parts id formula =
  let body = strip_universal_binders formula in
  let is_negated_definiendum = function
    | Imp (atom, false_tm) when is_vampire_false false_tm ->
        begin match definiendum_head atom with
        | Some defined -> Some (defined, atom)
        | None -> None
        end
    | _ -> None
  in
  match body with
  | Ap (Ap (TmH "vampire_or", left), right) ->
      begin match is_negated_definiendum left with
      | Some (defined, atom) when not (tm_contains_symbol defined right) -> (atom, right)
      | _ ->
          begin match is_negated_definiendum right with
          | Some (defined, atom) when not (tm_contains_symbol defined left) -> (atom, left)
          | _ -> error (id ^ ": predicate_definition is not a non-recursive definitional disjunction")
          end
      end
  | _ -> error (id ^ ": predicate_definition must be a definitional disjunction")

let check_predicate_definition id symbol formula =
  if symbol = "" then error (id ^ ": predicate_definition symbol must be non-empty");
  ignore (predicate_definition_parts id formula)

let combine_replacement left right =
  match left, right with
  | None, _ | _, None -> None
  | Some left_replaced, Some right_replaced ->
      if left_replaced && right_replaced then None
      else Some (left_replaced || right_replaced)

let rec tm_matches_one_replacement source target needle replacement =
  if source = needle && target = replacement then Some true
  else if source = target then Some false
  else
    match source, target with
    | TpAp (source_tm, source_tp), TpAp (target_tm, target_tp) when source_tp = target_tp ->
        tm_matches_one_replacement source_tm target_tm needle replacement
    | Ap (source_left, source_right), Ap (target_left, target_right)
    | Imp (source_left, source_right), Imp (target_left, target_right) ->
        combine_replacement
          (tm_matches_one_replacement source_left target_left needle replacement)
          (tm_matches_one_replacement source_right target_right needle replacement)
    | Lam (source_tp, source_body), Lam (target_tp, target_body)
    | All (source_tp, source_body), All (target_tp, target_body) when source_tp = target_tp ->
        tm_matches_one_replacement source_body target_body needle replacement
    | _ -> None

let check_predicate_definition_fold checked id source_id definition_id result =
  let source = lookup_formula checked source_id in
  let definition = lookup_formula checked definition_id in
  let definiendum, body = predicate_definition_parts definition_id definition in
  match tm_matches_one_replacement source result body definiendum with
  | Some true -> ()
  | _ -> error (id ^ ": predicate_definition_fold result is not one definition-body replacement")

let true_false_equality_var = function
  | Pos atom ->
      begin match equality_sides atom with
      | Some (TmH h, other) when h = "f__true" || h = "f__false" -> Some (h, other)
      | Some (other, TmH h) when h = "f__true" || h = "f__false" -> Some (h, other)
      | _ -> None
      end
  | Neg _ -> None

let check_fool_exhaustiveness id clause =
  match clause with
  | [left; right] ->
      begin match true_false_equality_var left, true_false_equality_var right with
      | Some ("f__true", x), Some ("f__false", y)
      | Some ("f__false", x), Some ("f__true", y) when x = y -> ()
      | _ -> error (id ^ ": fool_exhaustiveness is not true/false exhaustiveness for one Boolean term")
      end
  | _ -> error (id ^ ": fool_exhaustiveness must have exactly two literals")

let check_fool_distinctness id clause =
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

let check_equality_factoring checked id parent_id selected_index other_index subst result =
  if selected_index = other_index then error (id ^ ": equality-factoring literal indices must be distinct");
  let parent_clause = lookup_clause checked parent_id in
  let selected_literal = nth selected_index parent_clause (id ^ " selected equality") in
  let other_literal = nth other_index parent_clause (id ^ " other equality") in
  let selected_sub = subst_literal subst selected_literal in
  let other_sub = subst_literal subst other_literal in
  let selected_sides =
    match selected_sub with
    | Pos atom ->
        begin match equality_sides atom with
        | Some sides -> sides
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
  let selected_left, selected_right = selected_sides in
  let other_left, other_right = other_sides in
  let diseq left right = Neg (Ap (Ap (TmH "=", left), right)) in
  let candidates = ref [] in
  let add shared selected_other other_other =
    if shared then begin
      candidates := diseq selected_other other_other :: !candidates;
      candidates := diseq other_other selected_other :: !candidates
    end
  in
  add (selected_right = other_right) selected_left other_left;
  add (selected_right = other_left) selected_left other_right;
  add (selected_left = other_right) selected_right other_left;
  add (selected_left = other_left) selected_right other_right;
  if !candidates = [] then error (id ^ ": selected and other equalities do not share a side after substitution");
  let substituted_parent = subst_clause subst parent_clause in
  let without_selected = remove_at selected_index substituted_parent (id ^ " selected equality") in
  if not (List.exists (fun candidate -> same_clause_multiset (without_selected @ [candidate]) result) !candidates) then
    error (id ^ ": equality-factoring result does not match explicit factoring")

let check_truth_conflict checked id parent_id literal_index result =
  let parent_clause = lookup_clause checked parent_id in
  let literal = nth literal_index parent_clause (id ^ " truth-conflict literal") in
  begin
    match literal with
    | Pos atom ->
        begin
          match equality_sides atom with
          | Some (TmH "f__true", TmH "f__false")
          | Some (TmH "f__false", TmH "f__true") -> ()
          | Some _ -> error (id ^ ": truth-conflict equality is not true = false")
          | None -> error (id ^ ": truth-conflict literal is not an equality atom")
        end
    | Neg _ -> error (id ^ ": truth-conflict literal must be positive")
  end;
  let expected = remove_at literal_index parent_clause (id ^ " truth-conflict literal") in
  if not (same_clause_multiset expected result) then
    error (id ^ ": truth-conflict result does not match parent after literal removal")

let check_equality_symmetry checked id parent_id literal_index result =
  let parent_clause = lookup_clause checked parent_id in
  let literal = nth literal_index parent_clause (id ^ " equality-symmetry literal") in
  let swapped_literal =
    match swap_literal_equality literal with
    | Some swapped -> swapped
    | None -> error (id ^ ": equality-symmetry literal is not an equality")
  in
  let without_literal = remove_at literal_index parent_clause (id ^ " equality-symmetry literal") in
  let expected = without_literal @ [swapped_literal] in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-symmetry result does not match parent clause")

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
    select (paramodulation_position_candidates target_atom position)
  in
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
      (id, CheckedClause clause) :: checked
  | FormulaInput (id, source, literal) ->
      check_input_source source;
      (id, CheckedFormula (formula_tm_of_literal literal)) :: checked
  | FormulaTermInput (id, source, formula) ->
      check_input_source source;
      (id, CheckedFormula formula) :: checked
  | FormulaTermCopy (id, parent_id, result) ->
      check_formula_term_copy checked id parent_id result;
      (id, CheckedFormula result) :: checked
  | RectifyFormula (id, parent_id, result) ->
      check_rectify_formula checked id parent_id result;
      (id, CheckedFormula result) :: checked
  | FoolFormula (id, parent_id, result) ->
      check_fool_formula checked id parent_id result;
      (id, CheckedFormula result) :: checked
  | EnnfFormula (id, parent_id, result) ->
      check_ennf_formula checked id parent_id result;
      (id, CheckedFormula result) :: checked
  | SkolemFormula (id, parent_id, subst, result) ->
      check_skolem_formula checked id parent_id subst result;
      (id, CheckedFormula result) :: checked
  | SkolemFormulaComputed (id, parent_id, subst) ->
      let result = check_skolem_formula_computed checked parent_id subst in
      (id, CheckedFormula result) :: checked
  | CnfFormulaClause (id, parent_id, index, result) ->
      check_cnf_formula_clause checked id parent_id index result;
      (id, CheckedClause result) :: checked
  | FormulaCopy (id, parent_id, result) ->
      check_formula_copy checked id parent_id result;
      (id, CheckedClause [result]) :: checked
  | FoolBool (id, parent_id, result) ->
      check_fool_bool checked id parent_id result;
      (id, CheckedClause [result]) :: checked
  | CnfLiteral (id, parent_id, result) ->
      check_cnf_literal checked id parent_id result;
      (id, CheckedClause result) :: checked
  | PredicateDefinition (id, symbol, result) ->
      check_predicate_definition id symbol result;
      (id, CheckedFormula result) :: checked
  | PredicateDefinitionFold (id, source_id, definition_id, result) ->
      check_predicate_definition_fold checked id source_id definition_id result;
      (id, CheckedFormula result) :: checked
  | DefinitionInput (id, clause) ->
      check_definition_input id clause;
      (id, CheckedClause clause) :: checked
  | FoolExhaustiveness (id, clause) ->
      check_fool_exhaustiveness id clause;
      (id, CheckedClause clause) :: checked
  | FoolDistinctness (id, clause) ->
      check_fool_distinctness id clause;
      (id, CheckedClause clause) :: checked
  | Substitute (id, parent_id, subst, result) ->
      check_substitute checked id parent_id subst result;
      (id, CheckedClause result) :: checked
  | Resolve (id, left_id, right_id, left_index, right_index, result) ->
      check_resolution checked id left_id right_id left_index right_index result;
      (id, CheckedClause result) :: checked
  | Factor (id, parent_id, left_index, right_index, result) ->
      check_factor checked id parent_id left_index right_index result;
      (id, CheckedClause result) :: checked
  | EqualityResolution (id, parent_id, literal_index, result) ->
      check_equality_resolution checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | EqualityFactoring (id, parent_id, selected_index, other_index, subst, result) ->
      check_equality_factoring checked id parent_id selected_index other_index subst result;
      (id, CheckedClause result) :: checked
  | TruthConflict (id, parent_id, literal_index, result) ->
      check_truth_conflict checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | EqualitySymmetry (id, parent_id, literal_index, result) ->
      check_equality_symmetry checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | Paramodulate (id, equality_parent_id, target_parent_id, equality_index, target_index, position, from_tm, to_tm, result) ->
      check_paramodulate checked id equality_parent_id target_parent_id equality_index target_index position from_tm to_tm result;
      (id, CheckedClause result) :: checked
  | Contradiction (id, parent_id) ->
      let clause = lookup_clause checked parent_id in
      if clause <> [] then error (id ^ ": contradiction parent is not the empty clause");
      (id, CheckedClause []) :: checked

let check_certificate cert =
  let checked = List.fold_left check_step [] cert.steps in
  begin match checked with
  | (_, CheckedClause []) :: _ -> ()
  | (id, CheckedClause _) :: _ -> error (id ^ ": final certificate step is not the empty clause")
  | (id, CheckedFormula _) :: _ -> error (id ^ ": final certificate step is a formula, not the empty clause")
  | [] -> error "certificate contains no steps"
  end;
  List.rev checked
