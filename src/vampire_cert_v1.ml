(*** Native strict Vampire/Megalodon certificate v1 importer. ***)

open Syntax

type sexpr =
  | Atom of string
  | Str of string
  | List of sexpr list

exception Error of string

type source =
  | SourceAxiom of string
  | SourceConjecture of string
  | SourceNegatedConjecture of string
  | SourceDefinition of string
  | SourceSetReflexivity of string

type literal =
  | Pos of tm
  | Neg of tm

type clause = literal list

type sat_lit = int * bool

type sat_clause = sat_lit list

type sat_proof_step =
  | SatInput of int * sat_clause
  | SatRup of int * int list * sat_clause

type inequality_split = {
  split_name_parent : string;
  split_source : literal;
  split_name_literal : literal;
  split_replacement : literal;
}

type definition_rewrite = {
  definition_parent : string;
  definition_literal : int;
  target_literal : int;
  rewrite_position : int list;
  rewrite_from : tm;
  rewrite_to : tm;
}

type urr_trace = {
  urr_unit_parent : string;
  urr_selected : literal;
  urr_selected_substituted : literal;
  urr_unit_substituted : literal;
  urr_remaining : clause;
}

type rectify_renaming = {
  rectify_source : tm;
  rectify_subst : (string * tm) list;
  rectify_target : tm;
}

type checked_item =
  | CheckedClause of clause
  | CheckedFormula of tm

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | FormulaTermInput of string * source * tm
  | FormulaTermCopy of string * string * tm
  | RectifyFormula of string * string * rectify_renaming list * tm
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
  | PredicateDefinitionFoldChain of string * string * string list * tm
  | DefinitionInput of string * clause
  | DefinitionRewriteChain of string * string * definition_rewrite list * clause
  | AvatarComponent of string * clause
  | AvatarRefutation of string * sat_clause list * sat_proof_step list option * clause
  | FoolExhaustiveness of string * clause
  | FoolDistinctness of string * clause
  | InequalityNameIntro of string * clause
  | InequalitySplit of string * string * inequality_split list * clause
  | Substitute of string * string * (string * tm) list * clause
  | Condensation of string * string * (string * tm) list * clause
  | UnitResultingResolution of string * string * urr_trace list * clause
  | Resolve of string * string * string * int * int * clause
  | SubsumptionResolution of string * string * string * literal * literal * (string * tm) list * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | EqualityResolutionConstraints of string * string * int * literal * clause * clause
  | EqualityFactoring of string * string * int * int * (string * tm) list * clause
  | EqualityFactoringConstraints of string * string * int * int * (string * tm) list * clause * clause
  | TruthConflict of string * string * int * clause
  | EqualitySymmetry of string * string * int * clause
  | BoolSimplify of string * string * int * int list * tm * tm * clause
  | Paramodulate of string * string * string * int * int * int list * tm * tm * clause
  | Superposition of string * string * string * int * int * (string * tm) list * (string * tm) list * int list * tm * tm * clause
  | Contradiction of string * string

type certificate_metadata = {
  symbol_declarations : string list;
  step_propositions : (string * string) list;
  step_variable_sorts : (string * string list) list;
  step_extras : (string * string * string list) list;
}

type certificate = {
  problem : string option;
  metadata : certificate_metadata;
  steps : step list;
}

type source_map_entry = {
  source_map_kind : string;
  source_map_tptp_name : string;
  source_map_source_name : string;
  source_map_hash : string;
  source_map_decl_hash : string option;
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

let subst_named_tm name tm =
  let db_name depth = TmH ("db" ^ string_of_int depth) in
  let rec subst depth = function
    | TmH h when h = name -> db_name depth
    | TpAp (m, a) -> TpAp (subst depth m, a)
    | Ap (TmH "vLAM", body) -> Ap (TmH "vLAM", subst (depth + 1) body)
    | Ap (m, n) -> Ap (subst depth m, subst depth n)
    | Lam (tp, body) -> Lam (tp, subst (depth + 1) body)
    | Imp (m, n) -> Imp (subst depth m, subst depth n)
    | All (tp, body) -> All (tp, subst (depth + 1) body)
    | tm -> tm
  in
  subst 0 tm

let rec parse_tm = function
  | List [Atom "DB"; n] -> DB (int_atom n)
  | List [Atom "TMH"; h] -> TmH (atom h)
  | List [Atom "PRIM"; n] -> Prim (int_atom n)
  | List [Atom "TPAP"; m; a] -> TpAp (parse_tm m, parse_tp a)
  | List [Atom "AP"; m; n] -> Ap (parse_tm m, parse_tm n)
  | List [Atom "LAM"; a; m] -> Lam (parse_tp a, parse_tm m)
  | List [Atom "LAMV"; name; a; m] ->
      ignore (parse_tp a);
      Ap (TmH "vLAM", subst_named_tm (atom name) (parse_tm m))
  | List [Atom "IMP"; m; n] -> Imp (parse_tm m, parse_tm n)
  | List [Atom "ALL"; a; m] -> All (parse_tp a, parse_tm m)
  | List [Atom "ALLV"; name; a; m] ->
      All (parse_tp a, subst_named_tm (atom name) (parse_tm m))
  | _ -> error "expected Megalodon term S-expression"

let parse_source = function
  | List [Atom "source"; Atom "axiom"; name] -> SourceAxiom (atom name)
  | List [Atom "source"; Atom "conjecture"; name] -> SourceConjecture (atom name)
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

let bool_atom = function
  | Atom "true" -> true
  | Atom "false" -> false
  | _ -> error "expected Boolean atom"

let parse_sat_lit = function
  | List [Atom "lit"; var; polarity] -> (int_atom var, bool_atom polarity)
  | _ -> error "expected SAT literal"

let parse_sat_clause = function
  | List (Atom "sat_clause" :: literals) -> List.map parse_sat_lit literals
  | _ -> error "expected SAT clause"

let parse_sat_clauses = function
  | List (Atom "sat_clauses" :: clauses) -> List.map parse_sat_clause clauses
  | _ -> error "expected SAT clause list"

let parse_sat_parents = function
  | List (Atom "parents" :: parents) -> List.map int_atom parents
  | _ -> error "expected SAT parent list"

let parse_sat_result = function
  | List [Atom "result"; clause] -> parse_sat_clause clause
  | _ -> error "expected SAT result"

let parse_sat_proof_step = function
  | List [Atom "sat_input"; id; clause] ->
      SatInput (int_atom id, parse_sat_clause clause)
  | List [Atom "sat_rup"; id; parents; result] ->
      SatRup (int_atom id, parse_sat_parents parents, parse_sat_result result)
  | _ -> error "expected SAT proof step"

let parse_sat_proof = function
  | List (Atom "sat_proof" :: steps) -> List.map parse_sat_proof_step steps
  | _ -> error "expected SAT proof"

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

let parse_named_literal name = function
  | List [Atom label; literal] when label = name -> parse_literal literal
  | _ -> error ("expected " ^ name ^ " literal")

let parse_named_parents name = function
  | List (Atom label :: parents) when label = name -> List.map atom parents
  | _ -> error ("expected " ^ name ^ " parent list")

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
      let rec parse seen = function
        | [] -> []
        | List [name; tm] :: rest ->
            let name = atom name in
            if name = "" then error "substitution binding has an empty variable name";
            if List.mem name seen then
              error ("duplicate substitution binding for " ^ name);
            (name, parse_tm tm) :: parse (name :: seen) rest
        | _ -> error "expected substitution binding"
      in
      parse [] entries
  | _ -> error "expected substitution"

let parse_result = function
  | List [Atom "result"; clause] -> parse_clause clause
  | _ -> error "expected result clause"

let parse_inequality_split = function
  | List [Atom "split"; name_parent; source; name_literal; replacement] ->
      {
        split_name_parent = parse_named_parent "name_parent" name_parent;
        split_source = parse_named_literal "source" source;
        split_name_literal = parse_named_literal "name_literal" name_literal;
        split_replacement = parse_named_literal "replacement" replacement;
      }
  | _ -> error "expected inequality split item"

let parse_inequality_splits = function
  | List (Atom "splits" :: splits) -> List.map parse_inequality_split splits
  | _ -> error "expected inequality split list"

let parse_definition_rewrite = function
  | List [Atom "rewrite"; definition; target_literal; position; from_tm; to_tm] ->
      let definition_parent, definition_literal = parse_indexed_parent "definition" definition in
      let target_literal =
        match target_literal with
        | List [Atom "target_literal"; index] -> int_atom index
        | _ -> error "expected target literal index"
      in
      {
        definition_parent;
        definition_literal;
        target_literal;
        rewrite_position = parse_position position;
        rewrite_from = parse_tm_field "from" from_tm;
        rewrite_to = parse_tm_field "to" to_tm;
      }
  | _ -> error "expected definition rewrite"

let parse_definition_rewrites = function
  | List (Atom "rewrites" :: rewrites) -> List.map parse_definition_rewrite rewrites
  | _ -> error "expected definition rewrite list"

let parse_literal_result = function
  | List [Atom "result"; literal] -> parse_literal literal
  | _ -> error "expected result literal"

let parse_formula_result = function
  | List [Atom "result"; List [Atom "formula"; tm]] -> parse_tm tm
  | _ -> error "expected result formula"

let parse_formula_field name = function
  | List [Atom label; List [Atom "formula"; tm]] when label = name -> parse_tm tm
  | _ -> error ("expected " ^ name ^ " formula")

let parse_rectify_renaming = function
  | List [Atom "renaming"; source; subst; target] ->
      {
        rectify_source = parse_formula_field "source" source;
        rectify_subst = parse_substitution subst;
        rectify_target = parse_formula_field "target" target;
      }
  | _ -> error "expected rectify renaming"

let parse_rectify_renamings = function
  | List (Atom "renamings" :: renamings) ->
      List.map parse_rectify_renaming renamings
  | _ -> error "expected rectify renamings"

let parse_formula = function
  | List [Atom "formula"; tm] -> parse_tm tm
  | _ -> error "expected formula"

let parse_index = function
  | List [Atom "index"; index] -> int_atom index
  | _ -> error "expected index"

let parse_named_index name = function
  | List [Atom label; index] when label = name -> int_atom index
  | _ -> error ("expected " ^ name ^ " index")

let parse_constraints = function
  | List (Atom "constraints" :: constraints) -> List.map parse_literal constraints
  | _ -> error "expected constraints"

let parse_selected = function
  | List [Atom "selected"; literal] -> parse_literal literal
  | _ -> error "expected selected literal"

let parse_selected_substituted = function
  | List [Atom "selected_substituted"; literal] -> parse_literal literal
  | _ -> error "expected selected_substituted literal"

let parse_unit_substituted = function
  | List [Atom "unit_substituted"; literal] -> parse_literal literal
  | _ -> error "expected unit_substituted literal"

let parse_remaining = function
  | List [Atom "remaining"; clause] -> parse_clause clause
  | _ -> error "expected remaining clause"

let parse_urr_trace_step = function
  | List [Atom "step"; unit; selected; selected_substituted; unit_substituted; remaining] ->
      {
        urr_unit_parent = parse_named_parent "unit" unit;
        urr_selected = parse_selected selected;
        urr_selected_substituted = parse_selected_substituted selected_substituted;
        urr_unit_substituted = parse_unit_substituted unit_substituted;
        urr_remaining = parse_remaining remaining;
      }
  | _ -> error "expected unit_resulting_resolution trace step"

let parse_urr_trace = function
  | List (Atom "trace" :: steps) -> List.map parse_urr_trace_step steps
  | _ -> error "expected unit_resulting_resolution trace"

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
      RectifyFormula (atom id, parse_parent parent, [], parse_formula_result result)
  | List [Atom "rectify_formula"; id; parent; renamings; result] ->
      RectifyFormula
        (atom id, parse_parent parent, parse_rectify_renamings renamings, parse_formula_result result)
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
  | List [Atom "predicate_definition_fold_chain"; id; source; definitions; result] ->
      PredicateDefinitionFoldChain
        (atom id, parse_named_parent "source" source, parse_named_parents "definitions" definitions, parse_formula_result result)
  | List [Atom "definition_input"; id; result] ->
      DefinitionInput (atom id, parse_result result)
  | List [Atom "definition_rewrite_chain"; id; parent; rewrites; result] ->
      DefinitionRewriteChain (atom id, parse_parent parent, parse_definition_rewrites rewrites, parse_result result)
  | List [Atom "avatar_component"; id; result] ->
      AvatarComponent (atom id, parse_result result)
  | List [Atom "avatar_refutation"; id; sat_clauses; result] ->
      AvatarRefutation (atom id, parse_sat_clauses sat_clauses, None, parse_result result)
  | List [Atom "avatar_refutation"; id; sat_clauses; sat_proof; result] ->
      AvatarRefutation (atom id, parse_sat_clauses sat_clauses, Some (parse_sat_proof sat_proof), parse_result result)
  | List [Atom "fool_exhaustiveness"; id; result] ->
      FoolExhaustiveness (atom id, parse_result result)
  | List [Atom "fool_distinctness"; id; result] ->
      FoolDistinctness (atom id, parse_result result)
  | List [Atom "inequality_name_intro"; id; result] ->
      InequalityNameIntro (atom id, parse_result result)
  | List [Atom "inequality_split"; id; source; splits; result] ->
      InequalitySplit (atom id, parse_named_parent "source" source, parse_inequality_splits splits, parse_result result)
  | List [Atom "substitute"; id; parent; subst; result] ->
      Substitute (atom id, parse_parent parent, parse_substitution subst, parse_result result)
  | List [Atom "condensation"; id; parent; subst; result] ->
      Condensation (atom id, parse_parent parent, parse_substitution subst, parse_result result)
  | List [Atom "unit_resulting_resolution"; id; main; trace; result] ->
      UnitResultingResolution (atom id, parse_named_parent "main" main, parse_urr_trace trace, parse_result result)
  | List [Atom "resolve"; id; parents; pivot; result] ->
      let a, b = parse_parents parents in
      let i, j = parse_pivot pivot in
      Resolve (atom id, a, b, i, j, parse_result result)
  | List [Atom "subsumption_resolution"; id; parents; selected; side_pivot; side_subst; result] ->
      let a, b = parse_parents parents in
      SubsumptionResolution (
        atom id,
        a,
        b,
        parse_named_literal "selected" selected,
        parse_named_literal "side_pivot" side_pivot,
        parse_substitution side_subst,
        parse_result result)
  | List [Atom "factor"; id; parent; literals; result] ->
      let i, j = parse_literal_pair literals in
      Factor (atom id, parse_parent parent, i, j, parse_result result)
  | List [Atom "equality_resolution"; id; parent; literal; result] ->
      EqualityResolution (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
  | List [Atom "equality_resolution_constraints"; id; parent; literal; selected; constraints; result] ->
      EqualityResolutionConstraints (
        atom id,
        parse_parent parent,
        parse_literal_index literal,
        parse_selected selected,
        parse_constraints constraints,
        parse_result result)
  | List [Atom "equality_factoring"; id; parent; selected; other; subst; result] ->
      EqualityFactoring (
        atom id,
        parse_parent parent,
        parse_named_index "selected" selected,
        parse_named_index "other" other,
        parse_substitution subst,
        parse_result result)
  | List [Atom "equality_factoring_constraints"; id; parent; selected; other; subst; constraints; result] ->
      EqualityFactoringConstraints (
        atom id,
        parse_parent parent,
        parse_named_index "selected" selected,
        parse_named_index "other" other,
        parse_substitution subst,
        parse_constraints constraints,
        parse_result result)
  | List [Atom "truth_conflict"; id; parent; literal; result] ->
      TruthConflict (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
  | List [Atom "equality_symmetry"; id; parent; literal; result] ->
      EqualitySymmetry (atom id, parse_parent parent, parse_literal_index literal, parse_result result)
  | List [Atom "bool_simplify"; id; parent; literal; position; from_tm; to_tm; result] ->
      BoolSimplify (
        atom id,
        parse_parent parent,
        parse_literal_index literal,
        parse_position position,
        parse_tm_field "from" from_tm,
        parse_tm_field "to" to_tm,
        parse_result result)
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
  | List [Atom "superposition"; id; target; equality; target_subst; equality_subst; position; from_tm; to_tm; result] ->
      let target_parent, target_index = parse_indexed_parent "target" target in
      let equality_parent, equality_index = parse_indexed_parent "equality" equality in
      Superposition (
        atom id,
        target_parent,
        equality_parent,
        target_index,
        equality_index,
        parse_substitution target_subst,
        parse_substitution equality_subst,
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
  | RectifyFormula (id, _, _, _) -> id
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
  | PredicateDefinitionFoldChain (id, _, _, _) -> id
  | DefinitionInput (id, _) -> id
  | DefinitionRewriteChain (id, _, _, _) -> id
  | AvatarComponent (id, _) -> id
  | AvatarRefutation (id, _, _, _) -> id
  | FoolExhaustiveness (id, _) -> id
  | FoolDistinctness (id, _) -> id
  | InequalityNameIntro (id, _) -> id
  | InequalitySplit (id, _, _, _) -> id
  | Substitute (id, _, _, _) -> id
  | Condensation (id, _, _, _) -> id
  | UnitResultingResolution (id, _, _, _) -> id
  | Resolve (id, _, _, _, _, _) -> id
  | SubsumptionResolution (id, _, _, _, _, _, _) -> id
  | Factor (id, _, _, _, _) -> id
  | EqualityResolution (id, _, _, _) -> id
  | EqualityResolutionConstraints (id, _, _, _, _, _) -> id
  | EqualityFactoring (id, _, _, _, _, _) -> id
  | EqualityFactoringConstraints (id, _, _, _, _, _, _) -> id
  | TruthConflict (id, _, _, _) -> id
  | EqualitySymmetry (id, _, _, _) -> id
  | BoolSimplify (id, _, _, _, _, _, _) -> id
  | Paramodulate (id, _, _, _, _, _, _, _, _) -> id
  | Superposition (id, _, _, _, _, _, _, _, _, _, _) -> id
  | Contradiction (id, _) -> id

let step_rule_name = function
  | Input _ -> "input"
  | FormulaInput _ -> "formula_input"
  | FormulaTermInput _ -> "formula_term_input"
  | FormulaTermCopy _ -> "formula_term_copy"
  | RectifyFormula _ -> "rectify_formula"
  | FoolFormula _ -> "fool_formula"
  | EnnfFormula _ -> "ennf_formula"
  | SkolemFormula _ -> "skolem_formula"
  | SkolemFormulaComputed _ -> "skolem_formula_computed"
  | CnfFormulaClause _ -> "cnf_formula_clause"
  | FormulaCopy _ -> "formula_copy"
  | FoolBool _ -> "fool_bool"
  | CnfLiteral _ -> "cnf_literal"
  | PredicateDefinition _ -> "predicate_definition"
  | PredicateDefinitionFold _ -> "predicate_definition_fold"
  | PredicateDefinitionFoldChain _ -> "predicate_definition_fold_chain"
  | DefinitionInput _ -> "definition_input"
  | DefinitionRewriteChain _ -> "definition_rewrite_chain"
  | AvatarComponent _ -> "avatar_component"
  | AvatarRefutation _ -> "avatar_refutation"
  | FoolExhaustiveness _ -> "fool_exhaustiveness"
  | FoolDistinctness _ -> "fool_distinctness"
  | InequalityNameIntro _ -> "inequality_name_intro"
  | InequalitySplit _ -> "inequality_split"
  | Substitute _ -> "substitute"
  | Condensation _ -> "condensation"
  | UnitResultingResolution _ -> "unit_resulting_resolution"
  | Resolve _ -> "resolve"
  | SubsumptionResolution _ -> "subsumption_resolution"
  | Factor _ -> "factor"
  | EqualityResolution _ -> "equality_resolution"
  | EqualityResolutionConstraints _ -> "equality_resolution_constraints"
  | EqualityFactoring _ -> "equality_factoring"
  | EqualityFactoringConstraints _ -> "equality_factoring_constraints"
  | TruthConflict _ -> "truth_conflict"
  | EqualitySymmetry _ -> "equality_symmetry"
  | BoolSimplify _ -> "bool_simplify"
  | Paramodulate _ -> "paramodulate"
  | Superposition _ -> "superposition"
  | Contradiction _ -> "contradiction"

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

let empty_certificate_metadata = {
  symbol_declarations = [];
  step_propositions = [];
  step_variable_sorts = [];
  step_extras = [];
}

let parse_string_list = function
  | List items -> List.map atom items
  | _ -> error "expected a metadata string list"

let parse_certificate_metadata metadata = function
  | List [Atom "symbol_declaration"; decl] ->
      Some {
        metadata with
        symbol_declarations = metadata.symbol_declarations @ [atom decl];
      }
  | List [Atom "step_proposition"; id; proposition] ->
      Some {
        metadata with
        step_propositions = metadata.step_propositions @ [(atom id, atom proposition)];
      }
  | List [Atom "step_variable_sorts"; id; sorts] ->
      Some {
        metadata with
        step_variable_sorts =
          metadata.step_variable_sorts @ [(atom id, parse_string_list sorts)];
      }
  | List [Atom "step_extra"; id; kind; fields] ->
      Some {
        metadata with
        step_extras =
          metadata.step_extras @ [(atom id, atom kind, parse_string_list fields)];
      }
  | List (Atom (("symbol_declaration" | "step_proposition" | "step_variable_sorts" | "step_extra") as tag) :: _) ->
      error ("malformed certificate metadata record " ^ tag)
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
      let metadata, step_forms =
        List.fold_left
          (fun (metadata, steps) form ->
             match parse_certificate_metadata metadata form with
             | Some metadata -> (metadata, steps)
             | None -> (metadata, steps @ [form]))
          (empty_certificate_metadata, [])
          step_forms
      in
      let steps = List.map parse_step step_forms in
      check_duplicate_ids steps;
      { problem; metadata; steps }
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
        | Ap (TmH "vLAM", body), 0 -> body
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
      | Ap (TmH "vLAM", body), 0 ->
          Ap (TmH "vLAM", replace_tm_at_position body rest replacement what)
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

let rec rewrite_tm_all_once from_tm to_tm tm =
  if tm = from_tm then to_tm
  else
    match tm with
    | TpAp (m, a) -> TpAp (rewrite_tm_all_once from_tm to_tm m, a)
    | Ap (m, n) ->
        Ap (rewrite_tm_all_once from_tm to_tm m, rewrite_tm_all_once from_tm to_tm n)
    | Lam (a, m) -> Lam (a, rewrite_tm_all_once from_tm to_tm m)
    | Imp (m, n) ->
        Imp (rewrite_tm_all_once from_tm to_tm m, rewrite_tm_all_once from_tm to_tm n)
    | All (a, m) -> All (a, rewrite_tm_all_once from_tm to_tm m)
    | DB _ | TmH _ | Prim _ -> tm

let rewrite_literal_all_once from_tm to_tm literal =
  replace_literal_atom literal (rewrite_tm_all_once from_tm to_tm (literal_atom literal))

let equality_sides = function
  | Ap (Ap (TmH h, left), right) when h = "=" || h = "eq" -> Some (left, right)
  | _ -> None

let equality_to_true atom =
  Ap (Ap (TmH "=", atom), TmH "f__true")

let paramodulation_position_candidates target_atom position =
  let base = [position] in
  match equality_sides target_atom, position with
  | Some _, 0 :: 1 :: rest -> base @ [[1] @ rest]
  | Some _, 1 :: rest -> base @ [[0; 1] @ rest]
  | Some _, 0 :: rest -> base @ [[0; 1] @ rest]
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

let vampire_var_index name =
  if is_vampire_var_name name then
    Some (int_of_string (String.sub name 1 (String.length name - 1)))
  else
    None

let max_vampire_var_name tm =
  let better current candidate =
    match current, vampire_var_index candidate with
    | None, Some _ -> Some candidate
    | Some old, Some candidate_index ->
        begin match vampire_var_index old with
        | Some old_index when candidate_index > old_index -> Some candidate
        | _ -> current
        end
    | _ -> current
  in
  let rec loop current = function
    | TmH h -> better current h
    | TpAp (m, _) -> loop current m
    | Ap (m, n) -> loop (loop current m) n
    | Lam (_, body) -> loop current body
    | Imp (left, right) -> loop (loop current left) right
    | All (_, body) -> loop current body
    | DB _ | Prim _ -> current
  in
  loop None tm

let guarded_lambda_vampire_var_name tm =
  let rec loop = function
    | Ap (Ap (TmH "In", TmH h), _) when is_vampire_var_name h -> Some h
    | Ap (Ap (TmH "vampire_and", left), right)
    | Ap (Ap (TmH "vampire_or", left), right) ->
        begin match loop left with
        | Some _ as found -> found
        | None -> loop right
        end
    | Ap (TmH "vampire_exists_prop", _)
    | Lam _ -> None
    | TpAp (m, _) -> loop m
    | Ap (m, n) ->
        begin match loop m with
        | Some _ as found -> found
        | None -> loop n
        end
    | Imp (left, right) ->
        begin match loop left with
        | Some _ as found -> found
        | None -> loop right
        end
    | All (_, body) -> loop body
    | DB _ | TmH _ | Prim _ -> None
  in
  loop tm

let bind_anonymous_lambda_body body =
  match guarded_lambda_vampire_var_name body with
  | Some name -> subst_named_tm name body
  | None ->
  match max_vampire_var_name body with
  | Some name -> subst_named_tm name body
  | None -> body

let first_vampire_var_name tm =
  let rec loop = function
    | TmH h when is_vampire_var_name h -> Some h
    | TpAp (m, _) -> loop m
    | Ap (m, n) ->
        begin match loop m with
        | Some _ as found -> found
        | None -> loop n
        end
    | Lam (_, body) -> loop body
    | Imp (left, right) ->
        begin match loop left with
        | Some _ as found -> found
        | None -> loop right
        end
    | All (_, body) -> loop body
    | DB _ | TmH _ | Prim _ -> None
  in
  loop tm

let application_spine tm =
  let rec loop args = function
    | Ap (m, n) -> loop (n :: args) m
    | head -> (head, args)
  in
  loop [] tm

let rec principal_antecedent_var tm =
  match application_spine tm with
  | TmH "=", atom :: _ -> principal_antecedent_var atom
  | TmH h, arg :: _ when is_vampire_var_name h ->
      begin match first_vampire_var_name arg with
      | Some _ as found -> found
      | None -> Some h
      end
  | TmH _, arg :: _ -> first_vampire_var_name arg
  | _ -> first_vampire_var_name tm

let bind_anonymous_forall_body body =
  let preferred =
    match body with
    | Imp (left, _) -> principal_antecedent_var left
    | _ -> first_vampire_var_name body
  in
  match preferred with
  | Some name -> subst_named_tm name body
  | None -> bind_anonymous_lambda_body body

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

let rec tm_equal_mod_scoped_vampire_var_renaming_and_equality left right frames =
  let try_pair left_a right_a left_b right_b frames =
    match tm_equal_mod_scoped_vampire_var_renaming_and_equality left_a right_a frames with
    | None -> None
    | Some frames ->
        tm_equal_mod_scoped_vampire_var_renaming_and_equality left_b right_b frames
  in
  match equality_sides left, equality_sides right with
  | Some (left_lhs, left_rhs), Some (right_lhs, right_rhs) ->
      begin match try_pair left_lhs right_lhs left_rhs right_rhs frames with
      | Some _ as result -> result
      | None -> try_pair left_lhs right_rhs left_rhs right_lhs frames
      end
  | _ ->
      match left, right with
      | DB i, DB j when i = j -> Some frames
      | TmH h, TmH k -> add_scoped_vampire_var_renaming h k frames
      | Prim i, Prim j when i = j -> Some frames
      | TpAp (m, a), TpAp (n, b) when a = b ->
          tm_equal_mod_scoped_vampire_var_renaming_and_equality m n frames
      | Ap (m1, m2), Ap (n1, n2) ->
          begin match tm_equal_mod_scoped_vampire_var_renaming_and_equality m1 n1 frames with
          | None -> None
          | Some frames -> tm_equal_mod_scoped_vampire_var_renaming_and_equality m2 n2 frames
          end
      | Lam (a, m), Lam (b, n) when a = b ->
          begin match tm_equal_mod_scoped_vampire_var_renaming_and_equality m n (([], []) :: frames) with
          | None -> None
          | Some _ -> Some frames
          end
      | Imp (m1, m2), Imp (n1, n2) ->
          begin match tm_equal_mod_scoped_vampire_var_renaming_and_equality m1 n1 frames with
          | None -> None
          | Some frames -> tm_equal_mod_scoped_vampire_var_renaming_and_equality m2 n2 frames
          end
      | All (a, m), All (b, n) when a = b ->
          begin match tm_equal_mod_scoped_vampire_var_renaming_and_equality m n (([], []) :: frames) with
          | None -> None
          | Some _ -> Some frames
          end
      | _ -> None

let same_mod_scoped_vampire_var_renaming_and_equality left right =
  match tm_equal_mod_scoped_vampire_var_renaming_and_equality left right [([], [])] with
  | Some _ -> true
  | None -> false

let is_equality_atom tm =
  match equality_sides tm with
  | Some _ -> true
  | None -> false

let rec fool_term_tm tm =
  match tm with
  | TmH "vampire_true" -> TmH "f__true"
  | TmH "vampire_false" -> TmH "f__false"
  | Imp (body, false_tm) when is_vampire_false false_tm ->
      Ap (TmH "vNOT", fool_term_tm body)
  | Imp (left, right) ->
      Ap (Ap (TmH "vIMP", fool_term_tm left), fool_term_tm right)
  | All (_, body) ->
      Ap (TmH "vPI", Ap (TmH "vLAM", fool_term_tm (bind_anonymous_forall_body body)))
  | Ap (TmH "vampire_exists_prop", Lam (_, body)) ->
      Ap (TmH "vSIGMA", Ap (TmH "vLAM", fool_term_tm (bind_anonymous_lambda_body body)))
  | Ap (TmH "vampire_exists_prop", Ap (TmH "vLAM", body)) ->
      Ap (TmH "vSIGMA", Ap (TmH "vLAM", fool_term_tm body))
  | Ap (Ap (TmH "vampire_or", left), right) ->
      Ap (Ap (TmH "vOR", fool_term_tm left), fool_term_tm right)
  | Ap (Ap (TmH "vampire_and", left), right) ->
      Ap (Ap (TmH "vAND", fool_term_tm left), fool_term_tm right)
  | Ap (Ap (TmH "=", left), right) ->
      Ap (Ap (TmH "vEQ", fool_term_tm left), fool_term_tm right)
  | TpAp (m, a) -> TpAp (fool_term_tm m, a)
  | Ap (m, n) -> Ap (fool_term_tm m, fool_term_tm n)
  | Lam (tp, body) -> Lam (tp, fool_term_tm body)
  | _ -> tm

let rec fool_formula_tm tm =
  match tm with
  | Imp (left, right) -> Imp (fool_formula_tm left, fool_formula_tm right)
  | All (tp, body) -> All (tp, fool_formula_tm body)
  | Ap (Ap (TmH "vampire_or", left), right) -> vampire_or (fool_formula_tm left) (fool_formula_tm right)
  | Ap (Ap (TmH "vampire_and", left), right) -> vampire_and (fool_formula_tm left) (fool_formula_tm right)
  | Ap (TmH "vampire_exists_prop", Lam (tp, body)) -> vampire_exists tp (fool_formula_tm body)
  | Ap (TmH "vampire_exists_prop", Ap (TmH "vLAM", body)) -> vampire_exists Set (fool_formula_tm body)
  | Lam (tp, body) -> Lam (tp, fool_formula_tm body)
  | TmH "vampire_true"
  | TmH "vampire_false" -> tm
  | Ap (Ap (TmH "=", left), right) ->
      Ap (Ap (TmH "=", fool_term_tm left), fool_term_tm right)
  | _ when is_equality_atom tm -> tm
  | TmH h when is_vampire_var_name h -> Ap (Ap (TmH "=", TmH "f__true"), tm)
  | _ -> equality_to_true (fool_term_tm tm)

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
  | Ap (TmH "vampire_exists_prop", Ap (TmH "vLAM", body)) ->
      skolemize_formula_tm subst (subst_tm subst body)
  | TpAp (m, a) -> TpAp (skolemize_formula_tm subst m, a)
  | Ap (m, n) -> Ap (skolemize_formula_tm subst m, skolemize_formula_tm subst n)
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

let rec normalize_equality_orientation tm =
  let normalize = normalize_equality_orientation in
  match tm with
  | Ap (Ap (TmH "=", left), right) ->
      let left = normalize left in
      let right = normalize right in
      if compare left right <= 0 then Ap (Ap (TmH "=", left), right)
      else Ap (Ap (TmH "=", right), left)
  | TpAp (m, a) -> TpAp (normalize m, a)
  | Ap (m, n) -> Ap (normalize m, normalize n)
  | Lam (tp, body) -> Lam (tp, normalize body)
  | Imp (left, right) -> Imp (normalize left, normalize right)
  | All (tp, body) -> All (tp, normalize body)
  | _ -> tm

let normalize_literal_equality_orientation = function
  | Pos atom -> Pos (normalize_equality_orientation atom)
  | Neg atom -> Neg (normalize_equality_orientation atom)

let same_clause_set_mod_equality left right =
  let unique literals =
    let rec add_unique acc = function
      | [] -> List.rev acc
      | literal :: rest ->
          if List.exists ((=) literal) acc then add_unique acc rest
          else add_unique (literal :: acc) rest
    in
    add_unique [] (List.map normalize_literal_equality_orientation literals)
  in
  same_clause_multiset (unique left) (unique right)

let same_clause_mod_vampire_var_renaming left right =
  let literal_equal state left right =
    match left, right with
    | Pos m, Pos n
    | Neg m, Neg n ->
        let left_to_right, right_to_left = state in
        tm_equal_mod_vampire_var_renaming m n left_to_right right_to_left
    | _ -> None
  in
  let rec pick state literal prefix = function
    | [] -> None
    | candidate :: rest ->
        begin match literal_equal state candidate literal with
        | Some state -> Some (state, List.rev_append prefix rest)
        | None -> pick state literal (candidate :: prefix) rest
        end
  in
  let rec consume state remaining = function
    | [] -> remaining = []
    | literal :: rest ->
        begin match pick state literal [] remaining with
        | Some (state, remaining) -> consume state remaining rest
        | None -> false
        end
  in
  List.length left = List.length right && consume ([], []) left right

let same_clause_mod_vampire_var_renaming_and_equality left right =
  same_clause_mod_vampire_var_renaming
    (List.map normalize_literal_equality_orientation left)
    (List.map normalize_literal_equality_orientation right)

let rebuild_binary head = function
  | [] -> TmH head
  | item :: rest ->
      List.fold_left
        (fun acc item -> Ap (Ap (TmH head, acc), item))
        item rest

let rec collect_binary head tm =
  match tm with
  | Ap (Ap (TmH h, left), right) when h = head ->
      collect_binary head left @ collect_binary head right
  | _ -> [tm]

let rec normalize_fool_bool_association tm =
  let normalize = normalize_fool_bool_association in
  match tm with
  | Ap (Ap (TmH h, left), right) when h = "vAND" || h = "vOR" ->
      let items = collect_binary h (normalize left) @ collect_binary h (normalize right) in
      rebuild_binary h items
  | Ap (Ap (TmH h, left), right) when h = "vampire_and" || h = "vampire_or" ->
      let items = collect_binary h (normalize left) @ collect_binary h (normalize right) in
      rebuild_binary h items
  | TpAp (m, a) -> TpAp (normalize m, a)
  | Ap (m, n) -> Ap (normalize m, normalize n)
  | Lam (tp, body) -> Lam (tp, normalize body)
  | Imp (left, right) -> Imp (normalize left, normalize right)
  | All (tp, body) -> All (tp, normalize body)
  | _ -> tm

let normalize_fool_formula_shape tm =
  tm
  |> normalize_bool_equality_orientation
  |> normalize_fool_bool_association
  |> normalize_equality_orientation
  |> normalize_fool_bool_association

let rec debug_tm tm =
  match tm with
  | DB i -> "(DB " ^ string_of_int i ^ ")"
  | TmH h -> "(TMH \"" ^ String.escaped h ^ "\")"
  | Prim i -> "(PRIM " ^ string_of_int i ^ ")"
  | TpAp (m, _) -> "(TPAP " ^ debug_tm m ^ " _)"
  | Ap (m, n) -> "(AP " ^ debug_tm m ^ " " ^ debug_tm n ^ ")"
  | Lam (_, body) -> "(LAM _ " ^ debug_tm body ^ ")"
  | Imp (left, right) -> "(IMP " ^ debug_tm left ^ " " ^ debug_tm right ^ ")"
  | All (_, body) -> "(ALL _ " ^ debug_tm body ^ ")"

let debug_certificate_mismatch id expected result =
  if Sys.getenv_opt "MEGALODON_CERT_DEBUG" = Some "1" then begin
    prerr_endline (id ^ " expected: " ^ debug_tm expected);
    prerr_endline (id ^ " result: " ^ debug_tm result);
    prerr_endline (id ^ " expected_bool_norm: " ^ debug_tm (normalize_bool_equality_orientation expected));
    prerr_endline (id ^ " result_bool_norm: " ^ debug_tm (normalize_bool_equality_orientation result));
    prerr_endline (id ^ " expected_fool_norm: " ^ debug_tm (normalize_fool_formula_shape expected));
    prerr_endline (id ^ " result_fool_norm: " ^ debug_tm (normalize_fool_formula_shape result))
  end

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
  | SourceConjecture name
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

let validate_rectify_renaming id index renaming =
  let substituted = subst_tm renaming.rectify_subst renaming.rectify_source in
  let substituted_matches =
    substituted = renaming.rectify_target
    || normalize_bool_equality_orientation substituted
       = normalize_bool_equality_orientation renaming.rectify_target
    || normalize_equality_orientation substituted
       = normalize_equality_orientation renaming.rectify_target
  in
  let explicit_renaming_matches =
    same_mod_scoped_vampire_var_renaming renaming.rectify_source renaming.rectify_target
    || same_mod_scoped_vampire_var_renaming_and_equality renaming.rectify_source renaming.rectify_target
    || same_mod_scoped_vampire_var_renaming
         (normalize_bool_equality_orientation renaming.rectify_source)
         (normalize_bool_equality_orientation renaming.rectify_target)
    || same_mod_scoped_vampire_var_renaming_and_equality
         (normalize_bool_equality_orientation renaming.rectify_source)
         (normalize_bool_equality_orientation renaming.rectify_target)
    || same_mod_scoped_vampire_var_renaming
         (normalize_equality_orientation renaming.rectify_source)
         (normalize_equality_orientation renaming.rectify_target)
  in
  if not (substituted_matches || explicit_renaming_matches) then
    error
      (id ^ ": rectify_formula renaming " ^ string_of_int index
       ^ " target is not produced by its substitution or by scoped variable renaming")

let rectification_has_renaming renamings left right =
  List.exists
    (fun renaming ->
      renaming.rectify_source = left && renaming.rectify_target = right)
    renamings

let rec tm_matches_rectify_renamings renamings left right =
  left = right
  || rectification_has_renaming renamings left right
  ||
  match left, right with
  | TpAp (m, a), TpAp (n, b) when a = b ->
      tm_matches_rectify_renamings renamings m n
  | Ap (m1, m2), Ap (n1, n2) ->
      tm_matches_rectify_renamings renamings m1 n1
      && tm_matches_rectify_renamings renamings m2 n2
  | Lam (a, m), Lam (b, n) when a = b ->
      tm_matches_rectify_renamings renamings m n
  | Imp (m1, m2), Imp (n1, n2) ->
      tm_matches_rectify_renamings renamings m1 n1
      && tm_matches_rectify_renamings renamings m2 n2
  | All (a, m), All (b, n) when a = b ->
      tm_matches_rectify_renamings renamings m n
  | _ -> false

let check_rectify_formula checked id parent_id renamings result =
  let parent_formula = lookup_formula checked parent_id in
  match renamings with
  | _ :: _ ->
      List.iteri (validate_rectify_renaming id) renamings;
      let normalized_parent = normalize_bool_equality_orientation parent_formula in
      let normalized_result = normalize_bool_equality_orientation result in
      let equality_normalized_parent = normalize_equality_orientation normalized_parent in
      let equality_normalized_result = normalize_equality_orientation normalized_result in
      if not (tm_matches_rectify_renamings renamings parent_formula result
              || same_mod_scoped_vampire_var_renaming parent_formula result
              || same_mod_scoped_vampire_var_renaming_and_equality parent_formula result
              || same_mod_scoped_vampire_var_renaming normalized_parent normalized_result
              || same_mod_scoped_vampire_var_renaming_and_equality normalized_parent normalized_result
              || same_mod_scoped_vampire_var_renaming equality_normalized_parent equality_normalized_result
              || same_mod_scoped_vampire_var_renaming_and_equality equality_normalized_parent equality_normalized_result) then
        error (id ^ ": rectify_formula result is not explained by explicit Vampire renamings")
  | [] ->
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
    && normalize_bool_equality_orientation expected <> normalize_bool_equality_orientation result
    && normalize_equality_orientation expected <> normalize_equality_orientation result then begin
    if normalize_fool_formula_shape expected = normalize_fool_formula_shape result then ()
    else begin
    debug_certificate_mismatch id expected result;
    error (id ^ ": fool_formula result does not match recursive FOOL Boolean lifting")
    end
  end

let check_ennf_formula checked id parent_id result =
  let parent_formula = lookup_formula checked parent_id in
  let expected = ennf_pos parent_formula in
  if expected <> result then
    error (id ^ ": ennf_formula result does not match deterministic ENNF transformation")

let check_skolem_formula checked id parent_id subst result =
  let parent_formula = lookup_formula checked parent_id in
  let expected = skolemize_formula_tm subst parent_formula in
  if expected <> result
    && normalize_bool_equality_orientation expected <> normalize_bool_equality_orientation result
    && normalize_equality_orientation expected <> normalize_equality_orientation result then
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

let unique_clause clause =
  let rec add_unique acc = function
    | [] -> List.rev acc
    | literal :: rest ->
        if List.exists ((=) literal) acc then add_unique acc rest
        else add_unique (literal :: acc) rest
  in
  add_unique [] clause

let check_condensation checked id parent_id subst result =
  let parent_clause = lookup_clause checked parent_id in
  let expected = unique_clause (subst_clause subst parent_clause) in
  if List.length expected >= List.length parent_clause then
    error (id ^ ": condensation did not remove a duplicate literal");
  if not (same_clause_multiset expected result) then
    error (id ^ ": condensation result does not match duplicate-collapsed substituted parent")

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

let check_definition_rewrite_chain checked id source_id rewrites result =
  if rewrites = [] then error (id ^ ": definition_rewrite_chain needs at least one rewrite");
  let source_clause = lookup_clause checked source_id in
  let check_definition rewrite =
    let definition_clause = lookup_clause checked rewrite.definition_parent in
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
         replace_at rewrite.target_literal rewritten_literal current (id ^ " definition rewrite target literal"))
      source_clause
      rewrites
  in
  if not (same_clause_multiset current result) then
    error (id ^ ": definition_rewrite_chain result does not match explicit rewrite sequence")

let string_starts_with prefix value =
  let prefix_len = String.length prefix in
  String.length value >= prefix_len && String.sub value 0 prefix_len = prefix

let split_literal_name = function
  | Pos (TmH name)
  | Neg (TmH name) ->
      if string_starts_with "split_" name then Some name else None
  | _ -> None

let split_literal_number lit =
  match split_literal_name lit with
  | Some name ->
      (try
          let n =
            int_of_string (String.sub name 6 (String.length name - 6))
          in
          if n > 0 then Some n else None
        with Failure _ -> None)
  | None -> None

let is_split_literal = function
  | lit -> split_literal_name lit <> None

let check_avatar_component id clause =
  let has_split = List.exists is_split_literal clause in
  let has_component_literal = List.exists (fun lit -> not (is_split_literal lit)) clause in
  if not has_split then
    error (id ^ ": avatar_component must contain a split literal");
  if not has_component_literal then
    error (id ^ ": avatar_component must contain a component literal")

let check_avatar_component_strict id clause =
  let split_literals, component_literals =
    List.partition is_split_literal clause
  in
  begin match split_literals with
  | [split_literal] ->
      begin match split_literal_number split_literal with
      | Some _ -> ()
      | None -> error (id ^ ": strict avatar_component split literal must be split_N with positive N")
      end
  | [] ->
      error (id ^ ": strict avatar_component must contain exactly one split literal")
  | _ :: _ :: _ ->
      error (id ^ ": strict avatar_component must contain exactly one split literal")
  end;
  if component_literals = [] then
    error (id ^ ": strict avatar_component must contain a component literal")

let validate_sat_clauses id clauses =
  if clauses = [] then error (id ^ ": avatar_refutation must contain SAT clauses");
  List.iter
    (List.iter
       (fun (var, _) ->
         if var <= 0 then error (id ^ ": SAT variable indices must be positive")))
    clauses

let rec sat_satisfiable clauses =
  if clauses = [] then true
  else if List.exists (function [] -> true | _ -> false) clauses then false
  else
    let var =
      match clauses with
      | ((var, _) :: _) :: _ -> var
      | [] :: _ -> assert false
      | [] -> assert false
    in
    let simplify value clauses =
      let simplify_clause clause =
        let rec loop acc = function
          | [] -> Some (List.rev acc)
          | (lit_var, lit_polarity) :: rest when lit_var = var ->
              if lit_polarity = value then None else loop acc rest
          | lit :: rest -> loop (lit :: acc) rest
        in
        loop [] clause
      in
      List.fold_right
        (fun clause acc ->
          match simplify_clause clause with
          | Some simplified -> simplified :: acc
          | None -> acc)
        clauses
        []
    in
    sat_satisfiable (simplify true clauses) || sat_satisfiable (simplify false clauses)

let normalize_sat_clause clause =
  List.sort compare clause

let normalize_sat_clauses clauses =
  List.sort compare (List.map normalize_sat_clause clauses)

let sat_assign id assignments (var, value) =
  match List.assoc_opt var assignments with
  | Some existing when existing = value -> Some assignments
  | Some _ -> None
  | None -> Some ((var, value) :: assignments)

type sat_clause_eval =
  | SatSatisfied
  | SatConflict
  | SatUnit of sat_lit
  | SatUndetermined

let eval_sat_clause assignments clause =
  let rec loop unassigned = function
    | [] ->
        begin match unassigned with
        | [] -> SatConflict
        | [lit] -> SatUnit lit
        | _ -> SatUndetermined
        end
    | ((var, value) as lit) :: rest ->
        begin match List.assoc_opt var assignments with
        | Some assigned when assigned = value -> SatSatisfied
        | Some _ -> loop unassigned rest
        | None -> loop (lit :: unassigned) rest
        end
  in
  loop [] clause

let sat_rup_holds antecedents derived =
  let clauses =
    antecedents @ List.map (fun lit -> [lit]) (List.map (fun (var, polarity) -> (var, not polarity)) derived)
  in
  let rec propagate assignments =
    let rec find_unit = function
      | [] -> `NoUnit
      | clause :: rest ->
          begin match eval_sat_clause assignments clause with
          | SatSatisfied -> find_unit rest
          | SatConflict -> `Conflict
          | SatUnit lit -> `Unit lit
          | SatUndetermined -> find_unit rest
          end
    in
    match find_unit clauses with
    | `Conflict -> true
    | `NoUnit -> false
    | `Unit lit ->
        begin match sat_assign "sat_rup" assignments lit with
        | Some assignments' -> propagate assignments'
        | None -> true
        end
  in
  propagate []

let check_sat_proof id sat_clauses proof =
  if proof = [] then error (id ^ ": avatar_refutation SAT proof must be non-empty");
  let rec add checked input_clauses = function
    | [] -> (checked, input_clauses)
    | step :: rest ->
        begin match step with
        | SatInput (sid, clause) ->
            if sid <= 0 then error (id ^ ": SAT proof step ids must be positive");
            if List.mem_assoc sid checked then error (id ^ ": duplicate SAT proof step id");
            add ((sid, clause) :: checked) (clause :: input_clauses) rest
        | SatRup (sid, parents, clause) ->
            if sid <= 0 then error (id ^ ": SAT proof step ids must be positive");
            if List.mem_assoc sid checked then error (id ^ ": duplicate SAT proof step id");
            if parents = [] then error (id ^ ": SAT RUP step must have parents");
            let antecedents =
              List.map
                (fun parent ->
                  match List.assoc_opt parent checked with
                  | Some clause -> clause
                  | None -> error (id ^ ": SAT RUP parent is not an earlier proof step"))
                parents
            in
            if not (sat_rup_holds antecedents clause) then
              error (id ^ ": SAT RUP step does not follow from its parents");
            add ((sid, clause) :: checked) input_clauses rest
        end
  in
  let checked, input_clauses = add [] [] proof in
  if normalize_sat_clauses input_clauses <> normalize_sat_clauses sat_clauses then
    error (id ^ ": SAT proof inputs do not match avatar_refutation SAT clauses");
  begin match checked with
  | (_, []) :: _ -> ()
  | _ -> error (id ^ ": SAT proof final step is not the empty clause")
  end

let check_avatar_refutation id sat_clauses proof result =
  validate_sat_clauses id sat_clauses;
  if result <> [] then error (id ^ ": avatar_refutation result must be the empty clause");
  begin match proof with
  | Some proof -> check_sat_proof id sat_clauses proof
  | None ->
      if sat_satisfiable sat_clauses then
        error (id ^ ": avatar_refutation SAT clauses are satisfiable")
  end

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
      | Some (defined, atom) when not (tm_contains_symbol defined right) -> (defined, atom, right)
      | _ ->
          begin match is_negated_definiendum right with
          | Some (defined, atom) when not (tm_contains_symbol defined left) -> (defined, atom, left)
          | _ -> error (id ^ ": predicate_definition is not a non-recursive definitional disjunction")
          end
      end
  | _ -> error (id ^ ": predicate_definition must be a definitional disjunction")

let check_predicate_definition id symbol formula =
  if symbol = "" then error (id ^ ": predicate_definition symbol must be non-empty");
  let defined, _, _ = predicate_definition_parts id formula in
  if symbol <> defined then
    error (id ^ ": predicate_definition symbol " ^ symbol ^ " does not match definiendum " ^ defined)

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
  let _, definiendum, body = predicate_definition_parts definition_id definition in
  match tm_matches_one_replacement source result body definiendum with
  | Some true -> ()
  | _ -> error (id ^ ": predicate_definition_fold result is not one definition-body replacement")

let rec tm_one_replacement_results source needle replacement =
  let here = if source = needle then [replacement] else [] in
  let below =
    match source with
    | TpAp (m, a) ->
        List.map (fun m' -> TpAp (m', a)) (tm_one_replacement_results m needle replacement)
    | Ap (m, n) ->
        List.map (fun m' -> Ap (m', n)) (tm_one_replacement_results m needle replacement)
        @ List.map (fun n' -> Ap (m, n')) (tm_one_replacement_results n needle replacement)
    | Lam (tp, body) ->
        List.map (fun body' -> Lam (tp, body')) (tm_one_replacement_results body needle replacement)
    | Imp (left, right) ->
        List.map (fun left' -> Imp (left', right)) (tm_one_replacement_results left needle replacement)
        @ List.map (fun right' -> Imp (left, right')) (tm_one_replacement_results right needle replacement)
    | All (tp, body) ->
        List.map (fun body' -> All (tp, body')) (tm_one_replacement_results body needle replacement)
    | _ -> []
  in
  here @ below

let unique_terms terms =
  let rec loop seen = function
    | [] -> List.rev seen
    | term :: rest ->
        if List.exists ((=) term) seen then loop seen rest
        else loop (term :: seen) rest
  in
  loop [] terms

let check_predicate_definition_fold_chain checked id source_id definition_ids result =
  if definition_ids = [] then error (id ^ ": predicate_definition_fold_chain needs at least one definition");
  let source = lookup_formula checked source_id in
  let candidates =
    List.fold_left
      (fun candidates definition_id ->
         let definition = lookup_formula checked definition_id in
         let _, definiendum, body = predicate_definition_parts definition_id definition in
         let next =
           unique_terms
             (List.fold_left
                (fun acc candidate ->
                   tm_one_replacement_results candidate body definiendum @ acc)
                [] candidates)
         in
         if next = [] then
           error (id ^ ": predicate_definition_fold_chain could not apply definition " ^ definition_id);
         next)
      [source]
      definition_ids
  in
  if not (List.exists ((=) result) candidates) then
    error (id ^ ": predicate_definition_fold_chain result is not a sequence of definition-body replacements")

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

let bool_constant_name value = if value then "f__true" else "f__false"

let bool_name_literal value = function
  | Pos atom ->
      let expected = bool_constant_name value in
      begin match equality_sides atom with
      | Some (TmH h, named) when h = expected -> Some named
      | Some (named, TmH h) when h = expected -> Some named
      | _ -> None
      end
  | Neg _ -> None

let name_application = function
  | Ap (head, arg) -> Some (head, arg)
  | _ -> None

let check_vampire_inequality_name_head id head =
  match head_symbol head with
  | Some name when string_starts_with "sP" name -> ()
  | Some name -> error (id ^ ": inequality splitting name head " ^ name ^ " is not a Vampire split-name symbol")
  | None -> error (id ^ ": inequality splitting name has no head symbol")

let check_inequality_name_intro id clause =
  match clause with
  | [literal] ->
      begin match bool_name_literal false literal with
      | Some named ->
          begin match name_application named with
          | Some (head, _) -> check_vampire_inequality_name_head id head
          | None -> error (id ^ ": inequality_name_intro literal is not a name application")
          end
      | None -> error (id ^ ": inequality_name_intro must be a positive equality to f__false")
      end
  | _ -> error (id ^ ": inequality_name_intro must be a singleton clause")

let check_inequality_split checked id source_id splits result =
  if splits = [] then error (id ^ ": inequality_split has no split items");
  let source_clause = lookup_clause checked source_id in
  let rec consume remaining replacements = function
    | [] -> remaining @ List.rev replacements
    | split :: rest ->
        let name_clause = lookup_clause checked split.split_name_parent in
        if not (same_clause_multiset name_clause [split.split_name_literal]) then
          error (id ^ ": inequality_split name literal does not match name parent " ^ split.split_name_parent);
        let remaining =
          match remove_one split.split_source remaining with
          | Some remaining -> remaining
          | None -> error (id ^ ": inequality_split source literal is not available in source parent")
        in
        let name_head, split_term =
          match bool_name_literal false split.split_name_literal with
          | Some named ->
              begin match name_application named with
              | Some (head, arg) ->
                  check_vampire_inequality_name_head id head;
                  (head, arg)
              | None -> error (id ^ ": inequality_split name literal is not a name application")
              end
          | None -> error (id ^ ": inequality_split name literal must be a positive equality to f__false")
        in
        let other_side =
          match split.split_source with
          | Neg atom ->
              begin match equality_sides atom with
              | Some (left, right) when left = split_term -> right
              | Some (left, right) when right = split_term -> left
              | Some _ -> error (id ^ ": inequality_split source equality does not contain the named split term")
              | None -> error (id ^ ": inequality_split source literal is not an equality")
              end
          | Pos _ -> error (id ^ ": inequality_split source literal must be negative")
        in
        begin match bool_name_literal true split.split_replacement with
        | Some named ->
            begin match name_application named with
            | Some (replacement_head, replacement_arg)
                when replacement_head = name_head && replacement_arg = other_side -> ()
            | Some _ -> error (id ^ ": inequality_split replacement does not apply the same name to the other equality side")
            | None -> error (id ^ ": inequality_split replacement is not a name application")
            end
        | None -> error (id ^ ": inequality_split replacement must be a positive equality to f__true")
        end;
        consume remaining (split.split_replacement :: replacements) rest
  in
  let expected = consume source_clause [] splits in
  if not (same_clause_multiset expected result) then
    error (id ^ ": inequality_split result does not match source with split replacements")

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

let same_literal_mod_vampire_vars left right =
  match left, right with
  | Pos left_atom, Pos right_atom
  | Neg left_atom, Neg right_atom ->
      left_atom = right_atom
      || same_mod_scoped_vampire_var_renaming left_atom right_atom
      || same_mod_scoped_vampire_var_renaming_and_equality left_atom right_atom
      || normalize_equality_orientation left_atom = normalize_equality_orientation right_atom
      || same_mod_scoped_vampire_var_renaming
           (normalize_equality_orientation left_atom)
           (normalize_equality_orientation right_atom)
      || same_mod_scoped_vampire_var_renaming_and_equality
           (normalize_equality_orientation left_atom)
           (normalize_equality_orientation right_atom)
  | _ -> false

let complementary_mod_equality left right =
  match left, right with
  | Pos left_atom, Neg right_atom
  | Neg left_atom, Pos right_atom ->
      same_literal_mod_vampire_vars (Pos left_atom) (Pos right_atom)
  | _ -> false

let remove_one_literal_mod item items what =
  let rec aux prefix = function
    | [] -> error what
    | literal :: rest when same_literal_mod_vampire_vars literal item ->
        List.rev_append prefix rest
    | literal :: rest -> aux (literal :: prefix) rest
  in
  aux [] items

let clause_contains_literal_mod item clause =
  List.exists (fun literal -> same_literal_mod_vampire_vars literal item) clause

let check_subsumption_resolution checked id main_parent_id side_parent_id selected side_pivot side_subst result =
  let main_clause = lookup_clause checked main_parent_id in
  let side_clause = lookup_clause checked side_parent_id in
  let main_rest =
    remove_one_literal_mod selected main_clause (id ^ ": selected literal is not present in main parent")
  in
  let expected_result_ok =
    same_clause_multiset main_rest result
    || same_clause_set_mod_equality main_rest result
  in
  if not expected_result_ok then
    error (id ^ ": subsumption-resolution result does not match main parent after selected literal removal");
  let side_pivot_sub = subst_literal side_subst side_pivot in
  if not (complementary_mod_equality selected side_pivot_sub) then
    error (id ^ ": side pivot does not complement selected literal under side substitution");
  let rec check_side skipped_pivot = function
    | [] ->
        if not skipped_pivot then
          error (id ^ ": side pivot is not present in side parent")
    | literal :: rest ->
        if not skipped_pivot && same_literal_mod_vampire_vars literal side_pivot then
          check_side true rest
        else
          let substituted = subst_literal side_subst literal in
          if complementary_mod_equality selected substituted
             || clause_contains_literal_mod substituted result then
            check_side skipped_pivot rest
          else
            error (id ^ ": side parent contains a literal not discharged by the selected literal or preserved in the result")
  in
  check_side false side_clause

let clause_matches_native_trace left right =
  same_clause_multiset left right
  || same_clause_set_mod_equality left right
  || same_clause_mod_vampire_var_renaming left right

let check_unit_resulting_resolution checked id main_parent_id traces result =
  if traces = [] then error (id ^ ": unit_resulting_resolution trace is empty");
  let main_clause = lookup_clause checked main_parent_id in
  let non_split_length clause =
    List.length (List.filter (fun lit -> not (is_split_literal lit)) clause)
  in
  let rec check_trace current = function
    | [] -> current
    | trace :: rest ->
        let unit_clause = lookup_clause checked trace.urr_unit_parent in
        if non_split_length unit_clause <> 1 then
          error (id ^ ": URR unit parent " ^ trace.urr_unit_parent ^ " is not a unit clause");
        if not (complementary_mod_equality trace.urr_selected_substituted trace.urr_unit_substituted) then
          error (id ^ ": URR substituted selected and unit literals are not complementary");
        let current_non_split_length = non_split_length current in
        let remaining_non_split_length = non_split_length trace.urr_remaining in
        if remaining_non_split_length >= current_non_split_length then
          error (id ^ ": URR trace did not remove a literal");
        let selected_is_linked =
          clause_contains_literal_mod trace.urr_selected current
          || clause_contains_literal_mod trace.urr_selected_substituted current
        in
        if not selected_is_linked && current_non_split_length = remaining_non_split_length + 1 then
          error (id ^ ": URR selected literal is not linked to the current clause");
        check_trace trace.urr_remaining rest
  in
  let final_remaining = check_trace main_clause traces in
  if not (clause_matches_native_trace final_remaining result) then
    error (id ^ ": URR result does not match final trace remaining clause")

let check_equality_resolution_constraints checked id parent_id literal_index selected constraints result =
  if constraints = [] then error (id ^ ": equality-resolution constraints must be non-empty");
  let parent_clause = lookup_clause checked parent_id in
  let literal = nth literal_index parent_clause (id ^ " equality-resolution-constraints literal") in
  if not (same_literal_mod_vampire_vars literal selected) then
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
  let expected = remove_at literal_index parent_clause (id ^ " equality-resolution-constraints literal") @ constraints in
  if not (same_clause_multiset expected result) then
    error (id ^ ": equality-resolution constraints do not explain result")

let diseq_literal left right = Neg (Ap (Ap (TmH "=", left), right))

let rec term_disagreement_constraints left right =
  if left = right then []
  else
    let left_head, left_args = application_spine left in
    let right_head, right_args = application_spine right in
    if left_head = right_head && List.length left_args = List.length right_args then
      let rec collect acc = function
        | [], [] -> List.rev acc
        | l :: ls, r :: rs ->
            let constraints =
              if l = r then []
              else
                let nested = term_disagreement_constraints l r in
                if nested = [] then [diseq_literal l r] else nested
            in
            collect (List.rev_append constraints acc) (ls, rs)
        | _ -> [diseq_literal left right]
      in
      collect [] (left_args, right_args)
    else
      [diseq_literal left right]

let equality_factoring_constraint_candidates selected_sides other_sides =
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
      :: term_disagreement_constraints selected_other other_other
    in
    let reversed =
      diseq_literal other_shared selected_shared
      :: term_disagreement_constraints other_other selected_other
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

let check_negative_equality_constraints id constraints =
  List.iter
    (function
      | Neg atom ->
          begin match equality_sides atom with
          | Some _ -> ()
          | None -> error (id ^ ": equality-factoring constraint is not an equality atom")
          end
      | Pos _ -> error (id ^ ": equality-factoring constraint must be negative"))
    constraints

let equality_factoring_context checked id parent_id selected_index other_index subst =
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
  let substituted_parent = subst_clause subst parent_clause in
  let without_selected = remove_at selected_index substituted_parent (id ^ " selected equality") in
  selected_sides, other_sides, without_selected

let check_equality_factoring checked id parent_id selected_index other_index subst result =
  let selected_sides, other_sides, without_selected =
    equality_factoring_context checked id parent_id selected_index other_index subst
  in
  let candidates = equality_factoring_constraint_candidates selected_sides other_sides in
  if candidates = [] then error (id ^ ": selected and other equalities do not yield factoring constraints");
  if not (List.exists
      (fun candidate_constraints ->
        let expected = without_selected @ candidate_constraints in
        same_clause_multiset expected result
        || same_clause_set_mod_equality expected result)
      candidates) then
    error (id ^ ": equality-factoring result does not match explicit factoring")

let check_equality_factoring_constraints checked id parent_id selected_index other_index subst constraints result =
  if constraints = [] then error (id ^ ": equality-factoring constraints must be non-empty");
  check_negative_equality_constraints id constraints;
  let selected_sides, other_sides, without_selected =
    equality_factoring_context checked id parent_id selected_index other_index subst
  in
  let expected = without_selected @ constraints in
  if not (same_clause_multiset expected result || same_clause_set_mod_equality expected result) then
    error (id ^ ": equality-factoring constraints do not explain result");
  let candidates = equality_factoring_constraint_candidates selected_sides other_sides in
  if not (List.exists
      (fun candidate ->
        same_clause_multiset candidate constraints
        || same_clause_set_mod_equality candidate constraints)
      candidates) then
    error (id ^ ": equality-factoring constraints are not explained by selected and other equalities")

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

let check_bool_simplify checked id parent_id literal_index position from_tm to_tm result =
  let parent_clause = lookup_clause checked parent_id in
  let target_literal = nth literal_index parent_clause (id ^ " Boolean simplification literal") in
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
    select (paramodulation_position_candidates target_atom position)
  in
  let rewritten_atom = replace_tm_at_position target_atom position to_tm (id ^ " Boolean simplification target") in
  let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
  let parent_rest = remove_at literal_index parent_clause (id ^ " Boolean simplification literal") in
  let result_matches rewritten_literal =
    let expected = parent_rest @ [rewritten_literal] in
    same_clause_multiset expected result
    || same_clause_set_mod_equality expected result
    || same_clause_mod_vampire_var_renaming expected result
    || same_clause_mod_vampire_var_renaming_and_equality expected result
  in
  if not (
    result_matches rewritten_literal
    ||
    match swap_literal_equality rewritten_literal with
    | Some swapped_literal -> result_matches swapped_literal
    | None -> false)
  then
    error (id ^ ": Boolean simplification result does not match explicit rewrite")

let check_superposition checked id target_parent_id equality_parent_id target_index equality_index target_subst equality_subst position from_tm to_tm result =
  let target_clause = subst_clause target_subst (lookup_clause checked target_parent_id) in
  let raw_equality_clause = lookup_clause checked equality_parent_id in
  let equality_clause = subst_clause equality_subst raw_equality_clause in
  let raw_equality_literal = nth equality_index raw_equality_clause (id ^ " raw equality literal") in
  let equality_literal = nth equality_index equality_clause (id ^ " equality literal") in
  let target_literal = nth target_index target_clause (id ^ " target literal") in
  let side_matches left right =
    left = right
    || same_mod_vampire_var_renaming left right
    || same_mod_scoped_vampire_var_renaming left right
    || same_mod_scoped_vampire_var_renaming_and_equality left right
  in
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
    select (paramodulation_position_candidates target_atom position)
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
        same_clause_multiset expected result
        || same_clause_set_mod_equality expected result
        || same_clause_mod_vampire_var_renaming expected result
        || same_clause_mod_vampire_var_renaming_and_equality expected result)
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
        match swap_literal_equality rewritten_literal with
        | Some swapped_literal -> result_matches_with_equality_rest equality_rest swapped_literal
        | None -> false)
      rewritten_literals
  in
  let raw_variable_name = function
    | TmH name when is_vampire_var_name name -> Some name
    | _ -> None
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
                let raw_rest = remove_at equality_index raw_equality_clause (id ^ " raw equality literal") in
                let equality_rest = subst_clause subst raw_rest in
                result_matches equality_rest)
              variants
        | None -> false
        end
    | Neg _ -> false
  in
  if not (result_matches equality_rest || result_matches_raw_variable_orientation ()) then
    error (id ^ ": superposition result does not match explicit rewrite")

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
  | RectifyFormula (id, parent_id, renamings, result) ->
      check_rectify_formula checked id parent_id renamings result;
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
  | PredicateDefinitionFoldChain (id, source_id, definition_ids, result) ->
      check_predicate_definition_fold_chain checked id source_id definition_ids result;
      (id, CheckedFormula result) :: checked
  | DefinitionInput (id, clause) ->
      check_definition_input id clause;
      (id, CheckedClause clause) :: checked
  | DefinitionRewriteChain (id, source_id, rewrites, result) ->
      check_definition_rewrite_chain checked id source_id rewrites result;
      (id, CheckedClause result) :: checked
  | AvatarComponent (id, clause) ->
      check_avatar_component id clause;
      (id, CheckedClause clause) :: checked
  | AvatarRefutation (id, sat_clauses, proof, result) ->
      check_avatar_refutation id sat_clauses proof result;
      (id, CheckedClause result) :: checked
  | FoolExhaustiveness (id, clause) ->
      check_fool_exhaustiveness id clause;
      (id, CheckedClause clause) :: checked
  | FoolDistinctness (id, clause) ->
      check_fool_distinctness id clause;
      (id, CheckedClause clause) :: checked
  | InequalityNameIntro (id, clause) ->
      check_inequality_name_intro id clause;
      (id, CheckedClause clause) :: checked
  | InequalitySplit (id, source_id, splits, result) ->
      check_inequality_split checked id source_id splits result;
      (id, CheckedClause result) :: checked
  | Substitute (id, parent_id, subst, result) ->
      check_substitute checked id parent_id subst result;
      (id, CheckedClause result) :: checked
  | Condensation (id, parent_id, subst, result) ->
      check_condensation checked id parent_id subst result;
      (id, CheckedClause result) :: checked
  | UnitResultingResolution (id, main_parent_id, traces, result) ->
      check_unit_resulting_resolution checked id main_parent_id traces result;
      (id, CheckedClause result) :: checked
  | Resolve (id, left_id, right_id, left_index, right_index, result) ->
      check_resolution checked id left_id right_id left_index right_index result;
      (id, CheckedClause result) :: checked
  | SubsumptionResolution (id, main_parent_id, side_parent_id, selected, side_pivot, side_subst, result) ->
      check_subsumption_resolution checked id main_parent_id side_parent_id selected side_pivot side_subst result;
      (id, CheckedClause result) :: checked
  | Factor (id, parent_id, left_index, right_index, result) ->
      check_factor checked id parent_id left_index right_index result;
      (id, CheckedClause result) :: checked
  | EqualityResolution (id, parent_id, literal_index, result) ->
      check_equality_resolution checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | EqualityResolutionConstraints (id, parent_id, literal_index, selected, constraints, result) ->
      check_equality_resolution_constraints checked id parent_id literal_index selected constraints result;
      (id, CheckedClause result) :: checked
  | EqualityFactoring (id, parent_id, selected_index, other_index, subst, result) ->
      check_equality_factoring checked id parent_id selected_index other_index subst result;
      (id, CheckedClause result) :: checked
  | EqualityFactoringConstraints (id, parent_id, selected_index, other_index, subst, constraints, result) ->
      check_equality_factoring_constraints checked id parent_id selected_index other_index subst constraints result;
      (id, CheckedClause result) :: checked
  | TruthConflict (id, parent_id, literal_index, result) ->
      check_truth_conflict checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | EqualitySymmetry (id, parent_id, literal_index, result) ->
      check_equality_symmetry checked id parent_id literal_index result;
      (id, CheckedClause result) :: checked
  | BoolSimplify (id, parent_id, literal_index, position, from_tm, to_tm, result) ->
      check_bool_simplify checked id parent_id literal_index position from_tm to_tm result;
      (id, CheckedClause result) :: checked
  | Paramodulate (id, equality_parent_id, target_parent_id, equality_index, target_index, position, from_tm, to_tm, result) ->
      check_paramodulate checked id equality_parent_id target_parent_id equality_index target_index position from_tm to_tm result;
      (id, CheckedClause result) :: checked
  | Superposition (id, target_parent_id, equality_parent_id, target_index, equality_index, target_subst, equality_subst, position, from_tm, to_tm, result) ->
      check_superposition checked id target_parent_id equality_parent_id target_index equality_index target_subst equality_subst position from_tm to_tm result;
      (id, CheckedClause result) :: checked
  | Contradiction (id, parent_id) ->
      let clause = lookup_clause checked parent_id in
      if clause <> [] then error (id ^ ": contradiction parent is not the empty clause");
      (id, CheckedClause []) :: checked

let check_step_strict checked = function
  | AvatarComponent (id, clause) ->
      check_avatar_component_strict id clause;
      check_step checked (AvatarComponent (id, clause))
  | AvatarRefutation (id, _, None, _) ->
      error (id ^ ": strict certificate v1 requires SAT proof traces for AVATAR refutations")
  | AvatarRefutation _ as step -> check_step checked step
  | SkolemFormulaComputed (id, _, _) ->
      error (id ^ ": strict certificate v1 rejects computed skolem formulas without explicit Vampire results")
  | step -> check_step checked step

let check_certificate_with step_checker cert =
  let checked = List.fold_left step_checker [] cert.steps in
  begin match checked with
  | (_, CheckedClause []) :: _ -> ()
  | (id, CheckedClause _) :: _ -> error (id ^ ": final certificate step is not the empty clause")
  | (id, CheckedFormula _) :: _ -> error (id ^ ": final certificate step is a formula, not the empty clause")
  | [] -> error "certificate contains no steps"
  end;
  List.rev checked

let check_certificate cert =
  check_certificate_with check_step cert

let check_certificate_strict cert =
  check_certificate_with check_step_strict cert

let emit_error msg = error ("simple Megalodon emitter: " ^ msg)

let simple_normalize_vlam_text ?(lambda_binder_sort = fun _ -> None) text =
  let is_name_char = function
    | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> true
    | _ -> false
  in
  let is_token_at source token i =
    let len = String.length source in
    let token_len = String.length token in
    i + token_len <= len
    && String.sub source i token_len = token
    && (i = 0 || not (is_name_char source.[i - 1]))
    && (i + token_len = len || not (is_name_char source.[i + token_len]))
  in
  let rec skip_spaces source i =
    if i < String.length source && is_space source.[i] then skip_spaces source (i + 1) else i
  in
  let rec parse_paren source depth i =
    let len = String.length source in
    if i >= len then emit_error "unterminated parenthesized vLAM argument";
    match source.[i] with
    | '(' -> parse_paren source (depth + 1) (i + 1)
    | ')' when depth = 1 -> i + 1
    | ')' -> parse_paren source (depth - 1) (i + 1)
    | _ -> parse_paren source depth (i + 1)
  in
  let parse_arg source i =
    let len = String.length source in
    let start = skip_spaces source i in
    if start >= len then emit_error "vLAM has no argument";
    if source.[start] = '(' then
      let stop = parse_paren source 1 (start + 1) in
      (String.sub source (start + 1) (stop - start - 2), stop)
    else
      let rec atom_end j =
        if j >= len || is_space source.[j] || source.[j] = ')' then j else atom_end (j + 1)
      in
      let stop = atom_end start in
      (String.sub source start (stop - start), stop)
  in
  let fresh_index = ref 0 in
  let fresh_binder () =
    let name = "vdb" ^ string_of_int !fresh_index in
    incr fresh_index;
    name
  in
  let rec parse_db_token source i =
    let len = String.length source in
    if i + 2 <= len
       && String.sub source i 2 = "db"
       && (i = 0 || not (is_name_char source.[i - 1])) then begin
      let rec digits j =
        if j < len then
          match source.[j] with
          | '0'..'9' -> digits (j + 1)
          | _ -> j
        else j
      in
      let stop = digits (i + 2) in
      if stop > i + 2
         && (stop = len || not (is_name_char source.[stop])) then
        Some
          (int_of_string (String.sub source (i + 2) (stop - i - 2)), stop)
      else None
    end else None
  in
  let rec normalize env source =
    let source_len = String.length source in
    let rec loop i =
      if i >= source_len then ""
      else if is_token_at source "vLAM" i then
        let body, stop = parse_arg source (i + 4) in
        render_lambda env body ^ loop stop
      else begin
        match parse_db_token source i with
        | Some (index, stop) ->
            let replacement =
              match List.nth_opt env index with
              | Some (name, _) -> name
              | None -> "db" ^ string_of_int index
            in
            replacement ^ loop stop
        | None -> String.make 1 source.[i] ^ loop (i + 1)
      end
    in
    loop 0
  and binder_sort body =
    let vlam_text_candidates body =
      let body = String.trim body in
      ["vLAM " ^ body; "vLAM (" ^ body ^ ")"]
    in
    match vlam_text_candidates body |> List.find_map lambda_binder_sort with
    | Some sort -> sort
    | None -> "set"
  and render_lambda env body =
    let sort = binder_sort body in
    let name = fresh_binder () in
    let normalized_body = normalize ((name, sort) :: env) (String.trim body) in
    "(fun " ^ name ^ ":" ^ sort ^ " => " ^ normalized_body ^ ")"
  in
  normalize [] text

let metadata_step_proposition cert id =
  let parse_lambda_sorts fields =
    fields
    |> List.fold_left
         (fun acc field ->
            match String.index_opt field '=' with
            | None -> acc
            | Some eq ->
                let key = String.sub field 0 eq in
                let value = String.sub field (eq + 1) (String.length field - eq - 1) in
                (key, value) :: acc)
         []
  in
  let current_lambda_sorts =
    cert.metadata.step_extras
    |> List.filter (fun (step_id, _, _) -> step_id = id)
    |> List.concat_map (fun (_, _, fields) -> fields)
    |> parse_lambda_sorts
  in
  let global_lambda_sorts =
    cert.metadata.step_extras
    |> List.concat_map (fun (_, _, fields) -> fields)
    |> parse_lambda_sorts
  in
  let lambda_binder_sort_from fields text =
    let is_step_lambda_key key =
      let prefix = "step_lambda_" in
      let prefix_len = String.length prefix in
      let len = String.length key in
      len > prefix_len
      && String.sub key 0 prefix_len = prefix
      &&
      let rec digits i =
        i >= len || (match key.[i] with '0'..'9' -> digits (i + 1) | _ -> false)
      in
      digits prefix_len
    in
    let matching_prefix =
      fields
      |> List.find_map
           (fun (key, value) ->
              if value = text && is_step_lambda_key key then
                Some key
              else None)
    in
    match matching_prefix with
    | None -> None
    | Some key -> List.assoc_opt (key ^ "_binder_sort") fields
  in
  let lambda_binder_sort text =
    match lambda_binder_sort_from current_lambda_sorts text with
    | Some sort -> Some sort
    | None -> lambda_binder_sort_from global_lambda_sorts text
  in
  Option.map
    (simple_normalize_vlam_text ~lambda_binder_sort)
    (List.assoc_opt id cert.metadata.step_propositions)

let metadata_step_variable_sorts cert id =
  match List.assoc_opt id cert.metadata.step_variable_sorts with
  | Some sorts -> sorts
  | None -> []

let variable_sort_pair sort =
  match String.index_opt sort ':' with
  | Some colon when colon > 0 ->
      Some
        (String.sub sort 0 colon,
         String.sub sort (colon + 1) (String.length sort - colon - 1))
  | _ -> None

let metadata_step_variable_sort_pairs cert id =
  metadata_step_variable_sorts cert id
  |> List.filter_map variable_sort_pair

let metadata_step_extra_fields cert id kind =
  cert.metadata.step_extras
  |> List.filter_map
       (fun (step_id, step_kind, fields) ->
          if step_id = id && step_kind = kind then Some fields else None)

let metadata_step_extra_field cert id kind key =
  let prefix = key ^ "=" in
  let prefix_len = String.length prefix in
  metadata_step_extra_fields cert id kind
  |> List.find_map
       (fun fields ->
          List.find_map
            (fun field ->
               if String.length field >= prefix_len
                  && String.sub field 0 prefix_len = prefix then
                 Some (String.sub field prefix_len (String.length field - prefix_len))
	               else None)
	            fields)

let metadata_definition_lhs_sort_pairs cert id =
  let is_db_name name =
    let len = String.length name in
    let rec digits i =
      i >= len || (match name.[i] with '0'..'9' -> digits (i + 1) | _ -> false)
    in
    len > 2 && String.sub name 0 2 = "db" && digits 2
  in
  let field_value fields key =
    let prefix = key ^ "=" in
    let prefix_len = String.length prefix in
    fields
    |> List.find_map
         (fun field ->
            if String.length field >= prefix_len
               && String.sub field 0 prefix_len = prefix then
              Some (String.sub field prefix_len (String.length field - prefix_len))
            else None)
  in
  metadata_step_extra_fields cert id "function_definition"
  |> List.filter_map
       (fun fields ->
          match field_value fields "lhs", field_value fields "equality_sort" with
          | Some lhs, Some sort when is_db_name lhs -> Some (lhs, sort)
          | _ -> None)

let metadata_higher_order_definition_db_names cert =
  cert.metadata.step_extras
  |> List.concat_map
       (fun (id, kind, _) ->
          if kind <> "function_definition" then []
          else
            metadata_definition_lhs_sort_pairs cert id
            |> List.filter_map
                 (fun (name, sort) ->
                    if sort <> "set" && sort <> "prop" then Some name else None))
  |> List.sort_uniq String.compare

let metadata_lambda_sort_env cert =
  let parse_fields fields =
    let kvs =
      fields
      |> List.filter_map
           (fun field ->
              match String.index_opt field '=' with
              | None -> None
              | Some eq ->
                  Some
                    (String.sub field 0 eq,
                     String.sub field (eq + 1) (String.length field - eq - 1)))
    in
    let is_lambda_key key =
      let prefixes = ["step_lambda_"; "target_lambda_"] in
      List.exists
        (fun prefix ->
           let prefix_len = String.length prefix in
           let len = String.length key in
           len > prefix_len
           && String.sub key 0 prefix_len = prefix
           &&
           let rec digits i =
             i >= len || (match key.[i] with '0'..'9' -> digits (i + 1) | _ -> false)
           in
           digits prefix_len)
        prefixes
    in
    kvs
    |> List.filter_map
         (fun (key, term) ->
            if is_lambda_key key then
              match List.assoc_opt (key ^ "_sort") kvs with
              | Some sort -> Some (term, sort)
              | None -> None
            else None)
  in
  cert.metadata.step_extras
  |> List.concat_map (fun (_, _, fields) -> parse_fields fields)
  |> List.sort_uniq compare

let simple_unsupported_step cert step =
  let id = step_id step in
  let base = "unsupported rule " ^ step_rule_name step ^ " at step " ^ id in
  let with_prop =
    match metadata_step_proposition cert id with
    | Some proposition -> base ^ "; proposition: " ^ proposition
    | None -> base
  in
  match metadata_step_variable_sorts cert id with
  | [] -> with_prop
  | sorts -> with_prop ^ "; variable_sorts: " ^ String.concat ", " sorts

let simple_formula_prop cert id =
  match metadata_step_proposition cert id with
  | Some proposition -> proposition
  | None ->
      emit_error
        ("formula step " ^ id ^ " has no step_proposition metadata; rebuild Vampire proof output with native metadata")

let simple_parent_prop cert parent_id =
  match metadata_step_proposition cert parent_id with
  | Some proposition -> proposition
  | None -> emit_error ("parent step " ^ parent_id ^ " has no step_proposition metadata")

let simple_declared_name line =
  let variable_prefix = "Variable " in
  let prefix_len = String.length variable_prefix in
  if String.length line > prefix_len
     && String.sub line 0 prefix_len = variable_prefix then
    match String.index_opt line ':' with
    | Some colon when colon > prefix_len ->
        Some (String.sub line prefix_len (colon - prefix_len))
    | _ -> None
  else None

let metadata_declared_names cert =
  cert.metadata.symbol_declarations
  |> List.filter_map simple_declared_name

let metadata_variable_sorts cert =
  cert.metadata.step_variable_sorts
  |> List.concat_map snd
  |> List.filter_map variable_sort_pair
  |> List.sort_uniq compare

let megalodon_ident s =
  let n = String.length s in
  if n = 0 then emit_error "empty identifier";
  let is_alpha c =
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c = '_'
  in
  let is_ident c = is_alpha c || ('0' <= c && c <= '9') || c = '\'' in
  if not (is_alpha s.[0]) then emit_error ("unsupported identifier " ^ s);
  String.iter
    (fun c ->
       if not (is_ident c) then emit_error ("unsupported identifier " ^ s))
    s;
  s

let megalodon_safe_ident prefix s =
  let is_alpha c =
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c = '_'
  in
  let is_ident c = is_alpha c || ('0' <= c && c <= '9') || c = '\'' in
  let buf = Buffer.create (String.length prefix + String.length s + 8) in
  Buffer.add_string buf prefix;
  String.iter
    (fun c ->
       if is_ident c then Buffer.add_char buf c
       else Buffer.add_string buf (Printf.sprintf "_x%02X" (Char.code c)))
    s;
  let result = Buffer.contents buf in
  if result = "" then "x"
  else if is_alpha result.[0] then result
  else "x_" ^ result

let is_hex_char = function
  | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
  | _ -> false

let hex_value = function
  | '0' .. '9' as c -> Char.code c - Char.code '0'
  | 'a' .. 'f' as c -> 10 + Char.code c - Char.code 'a'
  | 'A' .. 'F' as c -> 10 + Char.code c - Char.code 'A'
  | _ -> 0

let decode_megalodon_tptp_name name =
  let encoded =
    if name = "emptyname" then name
    else if String.length name > 2
            && String.sub name 0 2 = "c_"
            && (name.[2] = '_'
                || ('A' <= name.[2] && name.[2] <= 'Z')
                || ('0' <= name.[2] && name.[2] <= '9')) then
      String.sub name 2 (String.length name - 2)
    else name
  in
  let buf = Buffer.create (String.length encoded) in
  let rec loop i =
    if i >= String.length encoded then ()
    else if encoded.[i] = '_'
            && i + 2 < String.length encoded
            && is_hex_char encoded.[i + 1]
            && is_hex_char encoded.[i + 2] then
      begin
        Buffer.add_char buf
          (Char.chr ((hex_value encoded.[i + 1] * 16) + hex_value encoded.[i + 2]));
        loop (i + 3)
      end
    else
      begin
        Buffer.add_char buf encoded.[i];
        loop (i + 1)
      end
  in
  loop 0;
  Buffer.contents buf

let simple_source_kind_and_tptp_name = function
  | SourceAxiom name -> ("axiom", name)
  | SourceConjecture name -> ("conjecture", name)
  | SourceNegatedConjecture name -> ("negated_conjecture", name)
  | SourceDefinition name -> ("definition", name)
  | SourceSetReflexivity name -> ("set_reflexivity", name)

let simple_source_label source_map source =
  let kind, tptp_name = simple_source_kind_and_tptp_name source in
  let displayed_name =
    match List.find_opt (fun entry -> entry.source_map_tptp_name = tptp_name) source_map with
    | Some entry when entry.source_map_source_name <> "" -> entry.source_map_source_name
    | _ -> decode_megalodon_tptp_name tptp_name
  in
  kind ^ "_" ^ displayed_name

let simple_fresh_name used base =
  let base = megalodon_safe_ident "" base in
  let rec choose n =
    let candidate =
      if n = 0 then base else base ^ "_" ^ string_of_int n
    in
    if List.mem candidate !used then choose (n + 1)
    else begin
      used := candidate :: !used;
      candidate
    end
  in
  choose 0

let simple_term_name = function
  | TmH name -> megalodon_ident name
  | _ -> emit_error "only named set terms are supported in simple native emission"

let is_vampire_bool_const = function
  | TmH "f__true" | TmH "vampire_true" | TmH "f__false" | TmH "vampire_false" -> true
  | _ -> false

let is_db_ident name =
  let len = String.length name in
  let rec digits i =
    i >= len || (match name.[i] with '0'..'9' -> digits (i + 1) | _ -> false)
  in
  len > 2 && String.sub name 0 2 = "db" && digits 2

let simple_db_alias_env : string list ref = ref []

let simple_vlam_name_counter = ref 0

let simple_fresh_vlam_name () =
  let name = "vdb" ^ string_of_int !simple_vlam_name_counter in
  incr simple_vlam_name_counter;
  name

let simple_db_index name =
  if is_db_ident name then
    Some (int_of_string (String.sub name 2 (String.length name - 2)))
  else None

let simple_db_alias_by_index index =
  List.nth_opt !simple_db_alias_env index

let simple_name_expr name =
  match Option.bind (simple_db_index name) simple_db_alias_by_index with
  | Some alias -> alias
  | None -> megalodon_ident name

let simple_with_db_aliases aliases f =
  let previous = !simple_db_alias_env in
  simple_db_alias_env := aliases @ previous;
  match f () with
  | result ->
      simple_db_alias_env := previous;
      result
  | exception exn ->
      simple_db_alias_env := previous;
      raise exn

let simple_bool_const_prop = function
  | TmH "f__true" | TmH "vampire_true" -> Some "vampire_true"
  | TmH "f__false" | TmH "vampire_false" -> Some "vampire_false"
  | _ -> None

let rec flatten_application = function
  | Ap (fn, arg) ->
      let head, args = flatten_application fn in
      (head, args @ [arg])
  | tm -> (tm, [])

let rec flatten_value_application = function
  | Ap (TmH "vLAM", _) as tm -> (tm, [])
  | Ap (fn, arg) ->
      let head, args = flatten_value_application fn in
      (head, args @ [arg])
  | tm -> (tm, [])

let simple_lambda_sort_env : (string * string) list ref = ref []

let rec simple_source_tm_expr tm =
  let render_arg arg =
    match arg with
    | TmH _ | DB _ | Prim _ -> simple_source_tm_expr arg
    | _ -> "(" ^ simple_source_tm_expr arg ^ ")"
  in
  match tm with
  | TmH name -> megalodon_ident name
  | DB i -> "db" ^ string_of_int i
  | Prim i -> "prim_" ^ string_of_int i
  | TpAp (tm, _) -> simple_source_tm_expr tm
  | Ap (TmH "vLAM", body) ->
      let body_text = simple_source_tm_expr body in
      begin match body with
      | TmH _ | DB _ | Prim _ -> "vLAM " ^ body_text
      | _ -> "vLAM (" ^ body_text ^ ")"
      end
  | Ap _ ->
      let head, args = flatten_value_application tm in
      String.concat " " (simple_source_tm_expr head :: List.map render_arg args)
  | Lam _ | All _ | Imp _ ->
      emit_error "logical terms are not supported in source-term rendering"

let simple_lambda_sort tm =
  match tm with
  | Ap (TmH "vLAM", _) ->
      List.assoc_opt (simple_source_tm_expr tm) !simple_lambda_sort_env
  | _ -> None

let rec simple_tp_expr = function
  | Prop -> "prop"
  | Set -> "set"
  | TpVar _ -> emit_error "type variables are not supported in simple native emission"
  | Ar (left, right) ->
      let left_text =
        match left with
        | Ar _ -> "(" ^ simple_tp_expr left ^ ")"
        | _ -> simple_tp_expr left
      in
      left_text ^ "->" ^ simple_tp_expr right

let rec simple_vlam_expr body =
  let logical_head = function
    | "vLAM" | "vPI" | "vOR" | "vAND" | "vNOT" | "vIMP"
    | "vampire_or" | "vampire_and" | "vampire_true" | "vampire_false"
    | "f__true" | "f__false" -> true
    | _ -> false
  in
  let rec contains_db = function
    | TmH name -> is_db_ident name
    | DB _ -> true
    | Prim _ -> false
    | TpAp (tm, _) -> contains_db tm
    | Ap (fn, arg) -> contains_db fn || contains_db arg
    | Lam (_, body) | All (_, body) -> contains_db body
    | Imp (left, right) -> contains_db left || contains_db right
  in
  let rec db_in_nonlogical_application tm =
    let head, args = flatten_application tm in
    let here =
      match head with
      | TmH name when not (logical_head name) ->
          List.exists contains_db args
      | _ -> false
    in
    here ||
    match tm with
    | TmH _ | DB _ | Prim _ -> false
    | TpAp (tm, _) -> db_in_nonlogical_application tm
    | Ap (fn, arg) -> db_in_nonlogical_application fn || db_in_nonlogical_application arg
    | Lam (_, body) | All (_, body) -> db_in_nonlogical_application body
    | Imp (left, right) -> db_in_nonlogical_application left || db_in_nonlogical_application right
  in
  let rec has_prop_logical_head tm =
    let head, args = flatten_application tm in
    let here =
      match head with
      | TmH ("vOR" | "vAND" | "vNOT" | "vIMP" | "vampire_or" | "vampire_and") -> true
      | _ -> false
    in
    here || List.exists has_prop_logical_head args
  in
  let binder_sort body =
    if db_in_nonlogical_application body then "set"
    else if has_prop_logical_head body then "prop"
    else "set"
  in
  let rec collect arity = function
    | Ap (TmH "vLAM", body) ->
        let sorts, final_body = collect (arity + 1) body in
        (binder_sort body :: sorts, final_body)
    | body -> ([binder_sort body], body)
  in
  let sorts, body = collect 1 body in
  let arity = List.length sorts in
  let rec binders n acc =
    if n <= 0 then acc else binders (n - 1) (acc @ [simple_fresh_vlam_name ()])
  in
  let binders = binders arity [] in
  let body_text =
    simple_with_db_aliases (List.rev binders)
      (fun () -> simple_tm_expr body)
  in
  "("
	  ^ String.concat " => "
	      ((List.combine sorts binders
	        |> List.map (fun (sort, name) -> "fun " ^ name ^ ":" ^ sort))
	       @ [body_text])
	  ^ ")"

and simple_lam_expr tp body =
  let rec collect acc = function
    | Lam (tp, body) -> collect (acc @ [tp]) body
    | body -> (acc, body)
  in
  let sorts, body = collect [tp] body in
  let arity = List.length sorts in
  let rec binders i acc =
    if i < 0 then acc else binders (i - 1) (acc @ ["db" ^ string_of_int i])
  in
  let binders = binders (arity - 1) [] in
  "("
  ^ String.concat " => "
      ((List.combine sorts binders
        |> List.map (fun (sort, name) -> "fun " ^ name ^ ":" ^ simple_tp_expr sort))
       @ [simple_tm_expr body])
  ^ ")"

and simple_tm_expr tm =
  match simple_bool_const_prop tm with
  | Some name -> name
  | None ->
      begin match tm with
      | Lam (tp, body) -> simple_lam_expr tp body
      | _ ->
      let head, args = flatten_application tm in
      begin match head, args with
      | TmH "vLAM", body :: rest ->
          let head_text = simple_vlam_expr body in
          begin match rest with
          | [] -> head_text
          | _ ->
              let arg_text arg =
                match arg with
                | TmH _ | DB _ -> simple_tm_expr arg
                | _ -> "(" ^ simple_tm_expr arg ^ ")"
              in
              String.concat " " (head_text :: List.map arg_text rest)
          end
      | _ ->
          let head_text =
            match head with
            | TmH name -> simple_name_expr name
            | DB i ->
                begin match simple_db_alias_by_index i with
                | Some alias -> alias
                | None -> "db" ^ string_of_int i
                end
            | Imp _ | All _ | Lam _ | TpAp _ | Prim _ ->
                emit_error "only named/application terms are supported in simple native emission"
            | _ -> "(" ^ simple_tm_expr head ^ ")"
          in
          match args with
          | [] -> head_text
          | _ ->
              let arg_text arg =
                match arg with
                | TmH _ | DB _ -> simple_tm_expr arg
                | _ -> "(" ^ simple_tm_expr arg ^ ")"
	              in
	              String.concat " " (head_text :: List.map arg_text args)
	      end
      end

let simple_prop_equality left right =
  "vampire_eq_prop (" ^ simple_tm_expr left ^ ") (" ^ simple_tm_expr right ^ ")"

let simple_atom_prop = function
  | TmH name -> simple_name_expr name
  | atom ->
      begin match equality_sides atom with
      | Some (left, right) when is_vampire_bool_const left || is_vampire_bool_const right ->
          simple_prop_equality left right
      | Some (left, right) ->
          simple_tm_expr left ^ " = " ^ simple_tm_expr right
      | None ->
          simple_tm_expr atom
      end

let simple_literal_prop = function
  | Pos atom -> simple_atom_prop atom
  | Neg atom -> "(" ^ simple_atom_prop atom ^ " -> False)"

let rec simple_clause_prop = function
  | [] -> "False"
  | [lit] -> simple_literal_prop lit
  | lit :: rest -> "(" ^ simple_literal_prop lit ^ " \\/ " ^ simple_clause_prop rest ^ ")"

let simple_prop_arg prop = "(" ^ prop ^ ")"

let simple_true_proof = "(fun p:prop => fun H:p => H)"

let simple_prop_equal_mod_app_parens left right =
  let has_reserved_syntax text =
    let contains needle =
      let len = String.length text in
      let needle_len = String.length needle in
      let rec loop i =
        i + needle_len <= len
        && (String.sub text i needle_len = needle || loop (i + 1))
      in
      needle_len = 0 || loop 0
    in
    contains "forall "
    || contains " -> "
    || contains "\\/"
    || contains "="
    || contains "=>"
    || contains ":"
  in
  let ident_start = function
    | 'A'..'Z' | 'a'..'z' | '_' -> true
    | _ -> false
  in
  let removable_inner text =
    let text = String.trim text in
    text <> "" && ident_start text.[0] && not (has_reserved_syntax text)
  in
  let normalize_once text =
    let len = String.length text in
    let buffer = Buffer.create len in
    let rec find_close depth i =
      if i >= len then None
      else
        match text.[i] with
        | '(' -> find_close (depth + 1) (i + 1)
        | ')' ->
            if depth = 0 then Some i else find_close (depth - 1) (i + 1)
        | _ -> find_close depth (i + 1)
    in
    let rec loop changed i =
      if i >= len then changed
      else if text.[i] = '(' then
        match find_close 0 (i + 1) with
        | Some close ->
            let inner = String.sub text (i + 1) (close - i - 1) in
            if removable_inner inner then begin
              Buffer.add_string buffer inner;
              loop true (close + 1)
            end else begin
              Buffer.add_char buffer text.[i];
              loop changed (i + 1)
            end
        | None ->
            Buffer.add_char buffer text.[i];
            loop changed (i + 1)
      else begin
        Buffer.add_char buffer text.[i];
        loop changed (i + 1)
      end
    in
    let changed = loop false 0 in
    (changed, Buffer.contents buffer)
  in
  let rec normalize text =
    let changed, text = normalize_once text in
    if changed then normalize text else text
  in
  normalize left = normalize right

let collect_simple_names cert =
  let declared_names = metadata_declared_names cert in
  let variable_sorts = metadata_variable_sorts cert in
  let typed_variable_names = List.map fst variable_sorts in
  let is_known name =
    List.mem name declared_names
    || List.mem name typed_variable_names
    || List.mem name
         [
           "False"; "True"; "or"; "vampire_or"; "vampire_and"; "vampire_exists_set";
           "vampire_exists_prop"; "vampire_false"; "vampire_true"; "vampire_eq_prop";
           "vampire_exists_set_set_prop";
           "vampire_eq_prop_to_prop_to_prop";
           "vampire_eq_set_to_set"; "vampire_eq_set_to_prop";
           "vampire_eq_set_to_set_to_prop"; "vampire_eq_set_to_set_to_set";
           "vampire_eq_lp_set_to_set_rp_to_set";
           "vampire_eq_lp_set_to_prop_rp_to_set";
           "vampire_eq_set_to_lp_set_to_set_rp_to_set";
           "vampire_eq_lp_set_to_set_rp_to_set_to_set";
           "vampire_eq_lp_set_to_set_to_set_rp_to_set_to_set";
           "vampire_eq_set_to_lp_set_to_set_to_set_rp_to_set_to_set";
           "f__true"; "f__false"; "vLAM"; "vPI"
         ]
  in
  let add_prop acc name =
    let name = megalodon_ident name in
    let props, terms = acc in
    if is_known name || List.mem name props then acc else (name :: props, terms)
  in
  let add_term acc term =
    let name = simple_term_name term in
    let props, terms = acc in
    if is_known name || List.mem name terms then acc else (props, name :: terms)
  in
  let rec add_term_expr acc = function
    | TmH name when is_vampire_bool_const (TmH name) || is_known name -> acc
    | TmH _ as term -> add_term acc term
    | DB _ -> acc
    | Ap (fn, arg) -> add_term_expr (add_term_expr acc fn) arg
    | TpAp (fn, _) -> add_term_expr acc fn
    | Lam (_, body) -> add_term_expr acc body
    | Imp (left, right) -> add_prop_expr (add_prop_expr acc left) right
    | All (_, body) -> add_prop_expr acc body
    | Prim _ -> acc
  and add_prop_expr acc = function
    | TmH name when is_vampire_bool_const (TmH name) || is_known name -> acc
    | TmH name -> add_prop acc name
    | Ap _ as atom ->
        begin match equality_sides atom with
        | Some (left, right) when is_vampire_bool_const left || is_vampire_bool_const right ->
            add_prop_expr (add_prop_expr acc left) right
        | Some (left, right) -> add_term_expr (add_term_expr acc left) right
        | None ->
            let head, args = flatten_application atom in
            let acc =
              match head with
              | TmH name when is_known name -> acc
              | TmH _ -> add_prop_expr acc head
              | _ -> add_prop_expr acc head
            in
            List.fold_left add_term_expr acc args
        end
    | TpAp (fn, _) -> add_prop_expr acc fn
    | Lam (_, body) -> add_prop_expr acc body
    | Imp (left, right) -> add_prop_expr (add_prop_expr acc left) right
    | All (_, body) -> add_prop_expr acc body
    | DB _ | Prim _ -> acc
  in
  let add_atom acc atom =
    match equality_sides atom with
    | Some (left, right) when is_vampire_bool_const left || is_vampire_bool_const right ->
        add_prop_expr (add_prop_expr acc left) right
    | Some (left, right) -> add_term_expr (add_term_expr acc left) right
    | None -> add_prop_expr acc atom
  in
  let add_literal acc = function
    | Pos atom | Neg atom -> add_atom acc atom
  in
  let add_clause acc clause = List.fold_left add_literal acc clause in
  let add_step acc = function
    | Input (_, _, clause) -> add_clause acc clause
    | FormulaInput (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | FormulaTermInput (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | FormulaTermCopy (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | RectifyFormula (id, _, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | FormulaCopy (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | FoolFormula (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | FoolBool (id, _, lit) ->
        ignore (simple_formula_prop cert id);
        add_literal acc lit
    | EnnfFormula (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | SkolemFormula (id, _, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | SkolemFormulaComputed (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | CnfLiteral (id, _, clause) ->
        ignore (simple_formula_prop cert id);
        add_clause acc clause
    | CnfFormulaClause (id, _, _, clause) ->
        ignore (simple_formula_prop cert id);
        add_clause acc clause
    | FoolExhaustiveness (_, clause) -> add_clause acc clause
    | FoolDistinctness (_, clause) -> add_clause acc clause
    | PredicateDefinition (id, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | PredicateDefinitionFold (id, _, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | PredicateDefinitionFoldChain (id, _, _, _) ->
        ignore (simple_formula_prop cert id);
        acc
    | DefinitionInput (_, clause) -> add_clause acc clause
    | Substitute (_, _, _, clause) -> add_clause acc clause
    | Condensation (_, _, _, clause) -> add_clause acc clause
    | UnitResultingResolution (_, _, _, clause) -> add_clause acc clause
    | SubsumptionResolution (_, _, _, _, _, _, clause) -> add_clause acc clause
    | Resolve (_, _, _, _, _, clause) -> add_clause acc clause
    | Factor (_, _, _, _, clause) -> add_clause acc clause
    | EqualitySymmetry (_, _, _, clause) -> add_clause acc clause
    | EqualityResolution (_, _, _, clause) -> add_clause acc clause
    | EqualityResolutionConstraints (_, _, _, _, _, clause) -> add_clause acc clause
    | EqualityFactoring (_, _, _, _, _, clause) -> add_clause acc clause
    | EqualityFactoringConstraints (_, _, _, _, _, _, clause) -> add_clause acc clause
    | TruthConflict (_, _, _, clause) -> add_clause acc clause
    | BoolSimplify (_, _, _, _, _, _, clause) -> add_clause acc clause
    | Paramodulate (_, _, _, _, _, _, _, _, clause) -> add_clause acc clause
    | Superposition (_, _, _, _, _, _, _, _, _, _, clause) -> add_clause acc clause
    | DefinitionRewriteChain (_, _, _, clause) -> add_clause acc clause
    | AvatarComponent (_, clause) -> add_clause acc clause
    | AvatarRefutation (_, _, _, clause) -> add_clause acc clause
    | InequalityNameIntro (_, clause) -> add_clause acc clause
    | InequalitySplit (_, _, _, clause) -> add_clause acc clause
    | Contradiction _ -> acc
  in
  let props, terms = List.fold_left add_step ([], []) cert.steps in
  let terms =
    terms
    |> List.filter (fun name -> not (is_db_ident name && List.mem name props))
  in
  let collisions = List.filter (fun name -> List.mem name terms) props in
  begin match collisions with
  | [] -> ()
  | name :: _ ->
      emit_error ("identifier " ^ name ^ " is used both as a proposition and a set term")
  end;
  (List.sort String.compare props, List.sort String.compare terms)

let lookup_simple_clause checked id =
  match List.assoc_opt id checked with
  | Some clause -> clause
  | None -> emit_error ("missing parent " ^ id)

let lookup_simple_name names id =
  match List.assoc_opt id names with
  | Some name -> name
  | None -> emit_error ("missing emitted parent name " ^ id)

let simple_clause_nth id label index clause =
  if index < 0 || index >= List.length clause then
    emit_error (id ^ ": " ^ label ^ " index is out of bounds");
  List.nth clause index

let simple_remove_index id label index clause =
  if index < 0 || index >= List.length clause then
    emit_error (id ^ ": " ^ label ^ " index is out of bounds");
  List.mapi (fun i lit -> (i, lit)) clause
  |> List.filter (fun (i, _) -> i <> index)
  |> List.map snd

let simple_sorts_subset smaller larger =
  List.for_all
    (fun (name, sort) -> List.exists (fun (name', sort') -> name = name' && sort = sort') larger)
    smaller

let simple_wrap_forall_intro sorts proof =
  List.fold_right
    (fun (name, sort) body ->
       "(fun " ^ megalodon_ident name ^ ":" ^ sort ^ " => " ^ body ^ ")")
    sorts
    proof

let simple_apply_forall_vars proof sorts =
  List.fold_left
    (fun acc (name, _) -> "(" ^ acc ^ " " ^ megalodon_ident name ^ ")")
    proof
    sorts

let simple_resolution_proof
    literal_prop parent_sorts_of result_sorts id left_id right_id left_index right_index result checked names =
  let left_clause = lookup_simple_clause checked left_id in
  let right_clause = lookup_simple_clause checked right_id in
  let left_pivot = simple_clause_nth id "left" left_index left_clause in
  let right_pivot = simple_clause_nth id "right" right_index right_clause in
  if not (complementary left_pivot right_pivot) then
    emit_error (id ^ ": pivots are not complementary");
  let left_rest = simple_remove_index id "left" left_index left_clause in
  let right_rest = simple_remove_index id "right" right_index right_clause in
  let positive_parent, negative_parent, positive_index, negative_index, positive_rest, negative_rest =
    match left_pivot, right_pivot with
    | Pos _, Neg _ -> left_id, right_id, left_index, right_index, left_rest, right_rest
    | Neg _, Pos _ -> right_id, left_id, right_index, left_index, right_rest, left_rest
    | _ -> emit_error (id ^ ": pivots are not complementary")
  in
  let positive_parent_name =
    simple_apply_forall_vars (lookup_simple_name names positive_parent) (parent_sorts_of positive_parent)
  in
  let negative_parent_name =
    simple_apply_forall_vars (lookup_simple_name names negative_parent) (parent_sorts_of negative_parent)
  in
  let wrap proof = simple_wrap_forall_intro result_sorts proof in
  match positive_rest, negative_rest, result with
  | [tail], [], [res] when tail = res ->
      if positive_index <> 0 then
        emit_error (id ^ ": simple binary-tail resolution expects the positive pivot at the clause head");
      let target = literal_prop res in
      let target_arg = simple_prop_arg target in
      wrap
        (Printf.sprintf
           "(%s %s (fun Hlit_0 => ((%s Hlit_0) %s)) (fun Htail_1 => Htail_1))"
           positive_parent_name target_arg negative_parent_name target_arg)
  | [], [tail], [res] when tail = res ->
      if negative_index <> 0 then
        emit_error (id ^ ": simple binary-tail resolution expects the negative pivot at the clause head");
      let target = literal_prop res in
      let target_arg = simple_prop_arg target in
      wrap
        (Printf.sprintf
           "(%s %s (fun Hlit_0 => ((Hlit_0 %s) %s)) (fun Htail_1 => Htail_1))"
           negative_parent_name target_arg positive_parent_name target_arg)
  | [], [], [] ->
      if positive_index <> 0 || negative_index <> 0 then
        emit_error (id ^ ": simple unit resolution expects pivots at the clause head");
      wrap (Printf.sprintf "((%s %s) False)" negative_parent_name positive_parent_name)
  | _ ->
      emit_error (id ^ ": simple emitter supports only unit resolution and binary-tail unit resolution")

let rec simple_resolution_clause_proof
    clause_body_prop parent_sorts_of result_sorts id left_id right_id left_index right_index result checked names =
  let left_clause = lookup_simple_clause checked left_id in
  let right_clause = lookup_simple_clause checked right_id in
  let left_pivot = simple_clause_nth id "left" left_index left_clause in
  let right_pivot = simple_clause_nth id "right" right_index right_clause in
  if not (complementary left_pivot right_pivot) then
    emit_error (id ^ ": pivots are not complementary");
  let left_rest = simple_remove_index id "left" left_index left_clause in
  let right_rest = simple_remove_index id "right" right_index right_clause in
  let expected = left_rest @ right_rest in
  if not (same_clause_multiset expected result) then
    emit_error (id ^ ": simple resolution proof expects parent rests as result");
  let positive_parent, negative_parent, positive_index, negative_index =
    match left_pivot, right_pivot with
    | Pos _, Neg _ -> left_id, right_id, left_index, right_index
    | Neg _, Pos _ -> right_id, left_id, right_index, left_index
    | _ -> emit_error (id ^ ": pivots are not complementary")
  in
  let positive_clause = lookup_simple_clause checked positive_parent in
  let negative_clause = lookup_simple_clause checked negative_parent in
  let positive_parent_name =
    simple_apply_forall_vars (lookup_simple_name names positive_parent) (parent_sorts_of positive_parent)
  in
  let negative_parent_name =
    simple_apply_forall_vars (lookup_simple_name names negative_parent) (parent_sorts_of negative_parent)
  in
  let target_prop = clause_body_prop result in
  let target_arg = simple_prop_arg target_prop in
  let negative_pivot_branch neg_proof pos_proof =
    Printf.sprintf "((%s %s) %s)" neg_proof pos_proof target_arg
  in
  let rec consume_negative selected_index source_clause source_proof pos_proof depth =
    match source_clause with
    | [] -> emit_error "cannot resolve against the empty negative clause"
    | [lit] ->
        begin match selected_index with
        | Some 0 -> negative_pivot_branch source_proof pos_proof
        | Some _ -> emit_error "resolution negative pivot index is out of bounds"
        | None -> simple_clause_intro_proof result lit source_proof
        end
    | lit :: rest ->
        let head_name = "Hres_neg_lit_" ^ string_of_int depth in
        let tail_name = "Hres_neg_tail_" ^ string_of_int depth in
        let head_branch =
          match selected_index with
          | Some 0 -> negative_pivot_branch head_name pos_proof
          | _ -> simple_clause_intro_proof result lit head_name
        in
        let rest_selected =
          match selected_index with
          | Some 0 -> None
          | Some n -> Some (n - 1)
          | None -> None
        in
        let tail_branch = consume_negative rest_selected rest tail_name pos_proof (depth + 1) in
        Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
          source_proof target_arg
          head_name head_branch
          tail_name tail_branch
  in
  let rec consume_positive selected_index source_clause source_proof depth =
    match source_clause with
    | [] -> emit_error "cannot resolve from the empty positive clause"
    | [lit] ->
        begin match selected_index with
        | Some 0 -> consume_negative (Some negative_index) negative_clause negative_parent_name source_proof 0
        | Some _ -> emit_error "resolution positive pivot index is out of bounds"
        | None -> simple_clause_intro_proof result lit source_proof
        end
    | lit :: rest ->
        let head_name = "Hres_pos_lit_" ^ string_of_int depth in
        let tail_name = "Hres_pos_tail_" ^ string_of_int depth in
        let head_branch =
          match selected_index with
          | Some 0 -> consume_negative (Some negative_index) negative_clause negative_parent_name head_name 0
          | _ -> simple_clause_intro_proof result lit head_name
        in
        let rest_selected =
          match selected_index with
          | Some 0 -> None
          | Some n -> Some (n - 1)
          | None -> None
        in
        let tail_branch = consume_positive rest_selected rest tail_name (depth + 1) in
        Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
          source_proof target_arg
          head_name head_branch
          tail_name tail_branch
  in
  simple_wrap_forall_intro result_sorts
    (consume_positive (Some positive_index) positive_clause positive_parent_name 0)

and simple_clause_intro_proof clause lit proof =
  match clause with
  | [] -> emit_error "cannot introduce a literal into the empty clause"
  | [single] when single = lit -> proof
  | head :: tail when head = lit ->
      Printf.sprintf "(fun vclause_goal Hhead Htail => Hhead %s)" proof
  | _ :: tail ->
      let tail_proof = simple_clause_intro_proof tail lit proof in
      Printf.sprintf "(fun vclause_goal Hhead Htail => Htail %s)" tail_proof

let rec simple_clause_projection_proof target_prop target_clause source_clause source_proof depth =
  match source_clause with
  | [] -> emit_error "cannot project from the empty clause"
  | [lit] -> simple_clause_intro_proof target_clause lit source_proof
  | lit :: rest ->
      let head_name = "Hproj_lit_" ^ string_of_int depth in
      let tail_name = "Hproj_tail_" ^ string_of_int depth in
      let head_branch = simple_clause_intro_proof target_clause lit head_name in
      let tail_branch =
        simple_clause_projection_proof target_prop target_clause rest tail_name (depth + 1)
      in
      Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
        source_proof (simple_prop_arg target_prop)
        head_name head_branch
        tail_name tail_branch

let rec simple_clause_remove_reflexive_disequality_proof
    target_prop target_clause selected_index source_clause source_proof depth =
  let selected_branch lit proof =
    match lit with
    | Neg atom ->
        begin match equality_sides atom with
        | Some (left, right) when left = right ->
            Printf.sprintf "((%s (fun Q H => H)) %s)" proof (simple_prop_arg target_prop)
        | Some _ ->
            emit_error "equality-resolution selected literal is not reflexive"
        | None ->
            emit_error "equality-resolution selected literal is not an equality"
        end
    | Pos _ ->
        emit_error "equality-resolution selected literal is not negative"
  in
  match source_clause with
  | [] -> emit_error "cannot remove a literal from the empty clause"
  | [lit] ->
      begin match selected_index with
      | Some 0 -> selected_branch lit source_proof
      | Some _ -> emit_error "equality-resolution selected index is out of bounds"
      | None -> simple_clause_intro_proof target_clause lit source_proof
      end
  | lit :: rest ->
      let head_name = "Heqres_lit_" ^ string_of_int depth in
      let tail_name = "Heqres_tail_" ^ string_of_int depth in
      let head_branch =
        match selected_index with
        | Some 0 -> selected_branch lit head_name
        | _ -> simple_clause_intro_proof target_clause lit head_name
      in
      let rest_selected =
        match selected_index with
        | Some 0 -> None
        | Some n -> Some (n - 1)
        | None -> None
      in
      let tail_branch =
        simple_clause_remove_reflexive_disequality_proof
          target_prop target_clause rest_selected rest tail_name (depth + 1)
      in
      Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
        source_proof (simple_prop_arg target_prop)
        head_name head_branch
        tail_name tail_branch

let rec simple_clause_remove_truth_conflict_proof
    target_prop target_clause selected_index source_clause source_proof depth =
  let true_proof = "(fun p:prop => fun H:p => H)" in
  let is_true = function
    | TmH "f__true" | TmH "vampire_true" -> true
    | _ -> false
  in
  let is_false = function
    | TmH "f__false" | TmH "vampire_false" -> true
    | _ -> false
  in
  let selected_branch lit proof =
    match lit with
    | Pos atom ->
        begin match equality_sides atom with
        | Some (left, right) when is_true left && is_false right ->
            Printf.sprintf "((%s (fun Z:prop => Z) %s) %s)"
              proof true_proof (simple_prop_arg target_prop)
        | Some (left, right) when is_false left && is_true right ->
            Printf.sprintf "((%s (fun Z:prop => Z -> %s) (fun Hfalse:False => Hfalse %s)) %s)"
              proof (simple_prop_arg target_prop) (simple_prop_arg target_prop) true_proof
        | Some _ ->
            emit_error "truth-conflict selected equality is not true = false"
        | None ->
            emit_error "truth-conflict selected literal is not an equality"
        end
    | Neg _ ->
        emit_error "truth-conflict selected literal is not positive"
  in
  match source_clause with
  | [] -> emit_error "cannot remove a literal from the empty clause"
  | [lit] ->
      begin match selected_index with
      | Some 0 -> selected_branch lit source_proof
      | Some _ -> emit_error "truth-conflict selected index is out of bounds"
      | None -> simple_clause_intro_proof target_clause lit source_proof
      end
  | lit :: rest ->
      let head_name = "Htruth_lit_" ^ string_of_int depth in
      let tail_name = "Htruth_tail_" ^ string_of_int depth in
      let head_branch =
        match selected_index with
        | Some 0 -> selected_branch lit head_name
        | _ -> simple_clause_intro_proof target_clause lit head_name
      in
      let rest_selected =
        match selected_index with
        | Some 0 -> None
        | Some n -> Some (n - 1)
        | None -> None
      in
      let tail_branch =
        simple_clause_remove_truth_conflict_proof
          target_prop target_clause rest_selected rest tail_name (depth + 1)
      in
      Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
        source_proof (simple_prop_arg target_prop)
        head_name head_branch
        tail_name tail_branch

let simple_factor_proof clause_body_prop parent_sorts result_sorts id parent_id left_index right_index result checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  let left = simple_clause_nth id "left" left_index parent_clause in
  let right = simple_clause_nth id "right" right_index parent_clause in
  if left <> right then emit_error (id ^ ": factor literals are not identical");
  let remove_index = if left_index > right_index then left_index else right_index in
  let expected = simple_remove_index id "removed factor" remove_index parent_clause in
  if expected <> result then
    emit_error (id ^ ": simple factor proof expects the result to remove the later duplicate");
  let target = clause_body_prop result in
  let parent_name =
    simple_apply_forall_vars (lookup_simple_name names parent_id) parent_sorts
  in
  simple_wrap_forall_intro result_sorts
    (simple_clause_projection_proof target result parent_clause parent_name 0)

let simple_equality_resolution_proof id parent_id literal_index result parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  let literal = simple_clause_nth id "equality-resolution" literal_index parent_clause in
  begin match parent_clause, literal, result with
  | [kept; Neg atom], Neg _, [res] when literal_index = 1 && kept = res ->
      begin match equality_sides atom with
      | Some (left, right) when left = right ->
          let target = simple_literal_prop kept in
          let target_arg = simple_prop_arg target in
          let parent_name = lookup_simple_name names parent_id in
          let parent_expr = simple_apply_forall_vars parent_name parent_sorts in
          let proof =
            Printf.sprintf "(%s %s (fun Hkeep_0 => Hkeep_0) (fun Hneq_1 => ((Hneq_1 (fun Q H => H)) %s)))"
              parent_expr target_arg target_arg
          in
          simple_wrap_forall_intro result_sorts proof
      | Some _ -> emit_error (id ^ ": equality-resolution equality is not reflexive")
      | None -> emit_error (id ^ ": equality-resolution literal is not an equality")
      end
  | _ ->
      emit_error (id ^ ": simple emitter supports only binary clauses ending in a reflexive disequality")
  end

let simple_equality_resolution_clause_proof
    clause_body_prop id parent_id literal_index result parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  ignore (simple_clause_nth id "equality-resolution" literal_index parent_clause);
  let target = clause_body_prop result in
  let parent_name =
    simple_apply_forall_vars (lookup_simple_name names parent_id) parent_sorts
  in
  simple_wrap_forall_intro result_sorts
    (simple_clause_remove_reflexive_disequality_proof
       target result (Some literal_index) parent_clause parent_name 0)

let simple_truth_conflict_clause_proof
    clause_body_prop id parent_id literal_index result parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  ignore (simple_clause_nth id "truth-conflict" literal_index parent_clause);
  let target = clause_body_prop result in
  let parent_name =
    simple_apply_forall_vars (lookup_simple_name names parent_id) parent_sorts
  in
  simple_wrap_forall_intro result_sorts
    (simple_clause_remove_truth_conflict_proof
       target result (Some literal_index) parent_clause parent_name 0)

let simple_copy_proof id parent_id result checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  if parent_clause <> result then
    emit_error (id ^ ": simple emitter supports only exact clause copies for substitution");
  lookup_simple_name names parent_id

let simple_tm_names tm =
  let rec collect acc = function
    | TmH name -> if List.mem name acc then acc else name :: acc
    | DB _ | Prim _ -> acc
    | TpAp (m, _) -> collect acc m
    | Ap (m, n) -> collect (collect acc m) n
    | Lam (_, body) -> collect acc body
    | Imp (left, right) -> collect (collect acc left) right
    | All (_, body) -> collect acc body
  in
  collect [] tm

let simple_clause_names clause =
  clause
  |> List.fold_left
       (fun acc literal ->
          List.fold_left
            (fun acc name -> if List.mem name acc then acc else name :: acc)
            acc
            (simple_tm_names (literal_atom literal)))
       []

let simple_clause_vlam_bound_names clause =
  let rec add_name acc name =
    if is_db_ident name && not (List.mem name acc) then name :: acc else acc
  in
  let rec names_under_vlam acc = function
    | TmH name -> add_name acc name
    | DB _ | Prim _ -> acc
    | TpAp (tm, _) -> names_under_vlam acc tm
    | Ap (fn, arg) -> names_under_vlam (names_under_vlam acc fn) arg
    | Lam (_, body) | All (_, body) -> names_under_vlam acc body
    | Imp (left, right) -> names_under_vlam (names_under_vlam acc left) right
  in
  let rec scan acc = function
    | Ap (TmH "vLAM", body) -> names_under_vlam acc body
    | TmH _ | DB _ | Prim _ -> acc
    | TpAp (tm, _) -> scan acc tm
    | Ap (fn, arg) -> scan (scan acc fn) arg
    | Lam (_, body) | All (_, body) -> scan acc body
    | Imp (left, right) -> scan (scan acc left) right
  in
  clause
  |> List.fold_left (fun acc literal -> scan acc (literal_atom literal)) []
  |> List.sort_uniq compare

let simple_clause_contains_vlam clause =
  let rec contains = function
    | TmH "vLAM" -> true
    | TmH _ | DB _ | Prim _ -> false
    | TpAp (tm, _) -> contains tm
    | Ap (fn, arg) -> contains fn || contains arg
    | Lam (_, body) | All (_, body) -> contains body
    | Imp (left, right) -> contains left || contains right
  in
  List.exists (fun literal -> contains (literal_atom literal)) clause

let simple_quantify_prop variable_sorts prop =
  List.fold_right
    (fun (name, sort) body -> "forall " ^ megalodon_ident name ^ ":" ^ sort ^ ", " ^ body)
    variable_sorts
    prop

let simple_variable_sorts_for_names names available_sorts =
  available_sorts
  |> List.filter (fun (name, _) -> List.mem name names)
  |> List.fold_left
       (fun acc (name, sort) ->
          if List.exists (fun (existing, _) -> existing = name) acc then acc
          else acc @ [(name, sort)])
       []

let simple_unique_variable_sorts sorts =
  List.fold_left
    (fun acc (name, sort) ->
       if List.exists (fun (existing, _) -> existing = name) acc then acc
       else acc @ [(name, sort)])
    []
    sorts

let simple_type_env_with_variables variable_sorts type_env =
  let variable_sorts =
    variable_sorts
    |> List.filter (fun (name, _) -> not (List.mem_assoc name type_env))
  in
  variable_sorts @ type_env

let simple_clause_prop_and_sorts_for_step ?(available_sorts=[]) cert id clause =
  match metadata_step_proposition cert id with
  | Some proposition -> (proposition, metadata_step_variable_sort_pairs cert id)
  | None ->
      let prop = simple_clause_prop clause in
      let names = simple_clause_names clause in
      let variable_sorts = simple_variable_sorts_for_names names available_sorts in
      (simple_quantify_prop variable_sorts prop, variable_sorts)

let simple_clause_prop_for_step ?(available_sorts=[]) cert id clause =
  fst (simple_clause_prop_and_sorts_for_step ~available_sorts cert id clause)

let simple_strip_outer_parens typ =
  let rec loop typ =
    let typ = String.trim typ in
    let len = String.length typ in
    if len >= 2 && typ.[0] = '(' && typ.[len - 1] = ')' then begin
      let depth = ref 0 in
      let balanced_outer = ref true in
      for i = 0 to len - 1 do
        begin match typ.[i] with
        | '(' -> incr depth
        | ')' ->
            decr depth;
            if !depth = 0 && i < len - 1 then balanced_outer := false
        | _ -> ()
        end
      done;
      if !balanced_outer && !depth = 0 then
        loop (String.sub typ 1 (len - 2))
      else typ
    end else typ
  in
  loop typ

let simple_replace_all ~pattern ~replacement text =
  let pattern_len = String.length pattern in
  if pattern_len = 0 then text
  else
    let text_len = String.length text in
    let buf = Buffer.create text_len in
    let rec loop i =
      if i >= text_len then ()
      else if i + pattern_len <= text_len
              && String.sub text i pattern_len = pattern then begin
        Buffer.add_string buf replacement;
        loop (i + pattern_len)
      end else begin
        Buffer.add_char buf text.[i];
        loop (i + 1)
      end
    in
    loop 0;
    Buffer.contents buf

let simple_fix_known_higher_order_binders text =
  text
  |> simple_replace_all
       ~pattern:"In_rec_i ((fun db1:set => fun db0:set => If_i"
       ~replacement:"In_rec_i ((fun db1:set => fun db0:set->set => If_i"
  |> simple_replace_all
       ~pattern:"In_rec_i (fun db1:set => fun db0:set => If_i"
       ~replacement:"In_rec_i (fun db1:set => fun db0:set->set => If_i"

let simple_split_arrow_type typ =
  let typ = simple_strip_outer_parens typ in
  let len = String.length typ in
  let depth = ref 0 in
  let found = ref None in
  let i = ref 0 in
  while !i + 1 < len && !found = None do
    begin match typ.[!i] with
    | '(' -> incr depth
    | ')' -> decr depth
    | '-' when !depth = 0 && typ.[!i + 1] = '>' -> found := Some !i
    | _ -> ()
    end;
    incr i
  done;
  match !found with
  | None -> None
  | Some pos ->
      let left = String.sub typ 0 pos |> simple_strip_outer_parens in
      let right =
        String.sub typ (pos + 2) (len - pos - 2)
        |> simple_strip_outer_parens
      in
      Some (left, right)

let simple_arrow_sort domain codomain =
  let domain =
    match simple_split_arrow_type domain with
    | Some _ -> "(" ^ domain ^ ")"
    | None -> domain
  in
  domain ^ "->" ^ codomain

let simple_binder_sort_expr sort =
  match simple_split_arrow_type sort with
  | Some _ -> "(" ^ sort ^ ")"
  | None -> sort

let simple_symbol_type_env cert =
  let builtins =
    [
      ("False", "prop"); ("True", "prop"); ("or", "prop->prop->prop");
      ("vampire_or", "prop->prop->prop"); ("vampire_and", "prop->prop->prop");
      ("vampire_exists_set", "(set->prop)->prop");
      ("vampire_exists_prop", "(prop->prop)->prop");
      ("vampire_exists_set_prop", "((set->prop)->prop)->prop");
      ("vampire_exists_set_set", "((set->set)->prop)->prop");
      ("vampire_exists_set_set_prop", "((set->set->prop)->prop)->prop");
      ("vampire_false", "prop"); ("vampire_true", "prop");
      ("vampire_eq_prop", "prop->prop->prop");
      ("vampire_eq_prop_to_set", "(prop->set)->(prop->set)->prop");
      ("vampire_eq_prop_to_prop_to_prop", "(prop->prop->prop)->(prop->prop->prop)->prop");
      ("vampire_eq_set_to_set", "(set->set)->(set->set)->prop");
      ("vampire_eq_set_to_prop", "(set->prop)->(set->prop)->prop");
      ("vampire_eq_set_to_set_to_prop", "(set->set->prop)->(set->set->prop)->prop");
      ("vampire_eq_set_to_set_to_set", "(set->set->set)->(set->set->set)->prop");
      ("vampire_eq_lp_set_to_set_rp_to_set", "((set->set)->set)->((set->set)->set)->prop");
      ("vampire_eq_lp_set_to_prop_rp_to_set", "((set->prop)->set)->((set->prop)->set)->prop");
      ("vampire_eq_set_to_lp_set_to_set_rp_to_set", "(set->((set->set)->set))->(set->((set->set)->set))->prop");
      ("vampire_eq_lp_set_to_set_rp_to_set_to_set", "((set->set)->set->set)->((set->set)->set->set)->prop");
      ("vampire_eq_lp_set_to_set_to_set_rp_to_set_to_set", "((set->set->set)->set->set)->((set->set->set)->set->set)->prop");
      ("vampire_eq_set_to_lp_set_to_set_to_set_rp_to_set_to_set", "(set->((set->set->set)->set->set))->(set->((set->set->set)->set->set))->prop");
      ("vPI", "(set->prop)->prop");
      ("f__true", "prop"); ("f__false", "prop")
    ]
  in
  let parse_decl decl =
    let line = String.trim decl in
    if not (string_starts_with "Variable " line) then None
    else
      let body =
        String.sub line 9 (String.length line - 9)
        |> String.trim
      in
      match String.index_opt body ':' with
      | None -> None
      | Some colon ->
          let name = String.sub body 0 colon |> String.trim |> megalodon_ident in
          let typ =
            String.sub body (colon + 1) (String.length body - colon - 1)
            |> String.trim
          in
          let typ =
            if String.length typ > 0 && typ.[String.length typ - 1] = '.' then
              String.sub typ 0 (String.length typ - 1)
            else typ
          in
          Some (name, simple_strip_outer_parens typ)
  in
  cert.metadata.symbol_declarations
  |> List.filter_map parse_decl
  |> List.rev_append builtins
  |> List.sort_uniq compare

let simple_add_inferred_sort type_env acc name sort =
  let name = megalodon_ident name in
  if List.mem_assoc name type_env then acc
  else if List.exists (fun (existing, existing_sort) -> existing = name && existing_sort = sort) acc then acc
  else acc @ [(name, sort)]

let simple_infer_tm_variable_sorts ?expected type_env tm =
  let rec infer expected acc = function
    | TmH name ->
        let name = megalodon_ident name in
        let known = List.assoc_opt name type_env in
        let sort = match known with Some sort -> Some sort | None -> expected in
        let acc =
          match expected, known with
          | Some sort, None -> simple_add_inferred_sort type_env acc name sort
          | _ -> acc
        in
        (sort, acc)
    | DB _ | Prim _ -> (expected, acc)
    | TpAp (fn, _) -> infer expected acc fn
    | Ap (fn, arg) ->
        let fn_sort, acc = infer None acc fn in
        let domain, codomain =
          match Option.bind fn_sort simple_split_arrow_type with
          | Some (domain, codomain) -> (Some domain, Some codomain)
          | None -> (None, None)
        in
        let arg_sort, acc = infer domain acc arg in
        let acc =
          match fn, fn_sort, domain, arg_sort, expected with
          | TmH name, None, None, Some domain, Some codomain ->
              simple_add_inferred_sort type_env acc name (domain ^ "->" ^ codomain)
          | _ -> acc
        in
        let result_sort = match codomain with Some _ -> codomain | None -> expected in
        (result_sort, acc)
    | Lam (_, body) ->
        let _, acc = infer None acc body in
        (expected, acc)
    | Imp (left, right) ->
        let _, acc = infer (Some "prop") acc left in
        let _, acc = infer (Some "prop") acc right in
        (Some "prop", acc)
    | All (_, body) ->
        let _, acc = infer (Some "prop") acc body in
        (Some "prop", acc)
  in
  snd (infer expected [] tm)

let rec simple_tm_sort type_env = function
  | TmH name -> List.assoc_opt (megalodon_ident name) type_env
  | DB _ | Prim _ -> None
  | TpAp (fn, _) -> simple_tm_sort type_env fn
  | Ap (TmH "vLAM", _) as tm -> simple_lambda_sort tm
  | Ap (fn, _) ->
      begin match Option.bind (simple_tm_sort type_env fn) simple_split_arrow_type with
      | Some (_, codomain) -> Some codomain
      | None -> None
      end
  | Lam _ | Imp _ | All _ -> None

let simple_infer_literal_variable_sorts type_env = function
  | Pos atom | Neg atom ->
      begin match equality_sides atom with
      | Some (left, right) ->
          let left_sort = simple_tm_sort type_env left in
          let right_sort = simple_tm_sort type_env right in
          simple_infer_tm_variable_sorts ?expected:right_sort type_env left
          @ simple_infer_tm_variable_sorts ?expected:left_sort type_env right
          |> simple_unique_variable_sorts
      | None -> simple_infer_tm_variable_sorts ~expected:"prop" type_env atom
      end

let simple_infer_clause_variable_sorts type_env clause =
  clause
  |> List.concat_map (simple_infer_literal_variable_sorts type_env)
  |> simple_unique_variable_sorts

let rec simple_tm_expr_with_expected type_env expected tm =
  match simple_bool_const_prop tm with
  | Some name -> name
  | None ->
      begin match tm with
      | Ap (TmH "vLAM", body) ->
          simple_vlam_expr_with_expected type_env expected body
      | Ap (fn, arg) ->
          let head, args = flatten_value_application tm in
          let arg_sorts = List.map (simple_tm_sort type_env) args in
          let all_arg_sorts =
            List.fold_right
              (fun sort acc ->
                 match sort, acc with
                 | Some sort, Some sorts -> Some (sort :: sorts)
                 | _ -> None)
              arg_sorts
              (Some [])
          in
          begin match head, expected, all_arg_sorts with
          | Ap (TmH "vLAM", _), Some result_sort, Some arg_sorts ->
              let head_expected =
                List.fold_right simple_arrow_sort arg_sorts result_sort
              in
              let head_text =
                "(" ^ simple_tm_expr_with_expected type_env (Some head_expected) head ^ ")"
              in
              let arg_texts =
                List.map2
                  (fun arg sort ->
                     match arg with
                     | TmH _ | DB _ -> simple_tm_expr_with_expected type_env (Some sort) arg
                     | _ -> "(" ^ simple_tm_expr_with_expected type_env (Some sort) arg ^ ")")
                  args
                  arg_sorts
              in
              String.concat " " (head_text :: arg_texts)
          | _ ->
              let fn_sort = simple_tm_sort type_env fn in
              let domain, codomain =
                match Option.bind fn_sort simple_split_arrow_type with
                | Some (domain, codomain) -> (Some domain, Some codomain)
                | None -> (simple_tm_sort type_env arg, None)
              in
              let fn_expected =
                match fn_sort, domain with
                | None, Some domain ->
                    Some (simple_arrow_sort domain (match expected with Some sort -> sort | None -> "set"))
                | _ -> None
              in
              let fn_text =
                match fn with
                | TmH _ | DB _ -> simple_tm_expr_with_expected type_env fn_expected fn
                | _ -> "(" ^ simple_tm_expr_with_expected type_env fn_expected fn ^ ")"
              in
              let arg_text =
                match arg with
                | TmH _ | DB _ -> simple_tm_expr_with_expected type_env domain arg
                | _ -> "(" ^ simple_tm_expr_with_expected type_env domain arg ^ ")"
              in
              ignore codomain;
              fn_text ^ " " ^ arg_text
          end
      | _ -> simple_tm_expr tm
      end

and simple_vlam_expr_with_expected type_env expected body =
  let expected =
    match expected with
    | Some _ -> expected
    | None -> simple_lambda_sort (Ap (TmH "vLAM", body))
  in
  let rec collect sorts expected body =
    match Option.bind expected simple_split_arrow_type with
    | Some (domain, codomain) ->
        begin match body with
        | Ap (TmH "vLAM", nested) -> collect (sorts @ [domain]) (Some codomain) nested
        | _ -> (sorts @ [domain], Some codomain, body)
        end
    | None -> emit_error "typed vLAM rendering requires an arrow expected type"
  in
  match expected with
  | None -> simple_vlam_expr body
  | Some _ ->
      begin match
        try Some (collect [] expected body)
        with Error _ -> None
      with
      | None -> simple_vlam_expr body
      | Some (sorts, final_expected, body) ->
          let arity = List.length sorts in
          let rec binders n acc =
            if n <= 0 then acc else binders (n - 1) (acc @ [simple_fresh_vlam_name ()])
          in
          let binders = binders arity [] in
          let body_type_env = List.combine binders sorts @ type_env in
          let body_text =
            simple_with_db_aliases (List.rev binders)
              (fun () -> simple_tm_expr_with_expected body_type_env final_expected body)
          in
          "("
          ^ String.concat " => "
              ((List.combine sorts binders
                |> List.map (fun (sort, name) -> "fun " ^ name ^ ":" ^ simple_binder_sort_expr sort))
               @ [body_text])
          ^ ")"
      end

let simple_equality_symbol_for_sort sort =
  match simple_strip_outer_parens sort with
  | "prop" -> Some "vampire_eq_prop"
  | "set->set" -> Some "vampire_eq_set_to_set"
  | "set->prop" -> Some "vampire_eq_set_to_prop"
  | "set->set->prop" -> Some "vampire_eq_set_to_set_to_prop"
  | "set->set->set" -> Some "vampire_eq_set_to_set_to_set"
  | "(set->set)->set" -> Some "vampire_eq_lp_set_to_set_rp_to_set"
  | "(set->prop)->set" -> Some "vampire_eq_lp_set_to_prop_rp_to_set"
  | "set->((set->set)->set)"
  | "set->(set->set)->set" -> Some "vampire_eq_set_to_lp_set_to_set_rp_to_set"
  | "(set->set)->set->set" -> Some "vampire_eq_lp_set_to_set_rp_to_set_to_set"
  | "(set->set->set)->set->set" -> Some "vampire_eq_lp_set_to_set_to_set_rp_to_set_to_set"
  | "set->((set->set->set)->set->set)"
  | "set->(set->set->set)->set->set" ->
      Some "vampire_eq_set_to_lp_set_to_set_to_set_rp_to_set_to_set"
  | _ -> None

let simple_equality_prop_with_type_env type_env left right =
  let left_expected = simple_tm_sort type_env right in
  let right_expected = simple_tm_sort type_env left in
  let left_text = simple_tm_expr_with_expected type_env left_expected left in
  let right_text = simple_tm_expr_with_expected type_env right_expected right in
  match left_expected, right_expected with
  | Some "set", _ | _, Some "set" -> left_text ^ " = " ^ right_text
  | Some sort, _ | _, Some sort ->
      begin match simple_equality_symbol_for_sort sort with
      | Some equality -> equality ^ " (" ^ left_text ^ ") (" ^ right_text ^ ")"
      | None -> left_text ^ " = " ^ right_text
      end
  | None, None -> left_text ^ " = " ^ right_text

let simple_atom_prop_with_type_env type_env atom =
  match equality_sides atom with
  | Some (left, right) when is_vampire_bool_const left || is_vampire_bool_const right ->
      simple_prop_equality left right
  | Some (left, right) -> simple_equality_prop_with_type_env type_env left right
  | None -> simple_tm_expr_with_expected type_env None atom

let simple_literal_prop_with_type_env type_env = function
  | Pos atom -> simple_atom_prop_with_type_env type_env atom
  | Neg atom -> "(" ^ simple_atom_prop_with_type_env type_env atom ^ " -> False)"

let rec simple_clause_prop_with_type_env type_env = function
  | [] -> "False"
  | [lit] -> simple_literal_prop_with_type_env type_env lit
  | lit :: rest ->
      "(" ^ simple_literal_prop_with_type_env type_env lit
      ^ " \\/ "
      ^ simple_clause_prop_with_type_env type_env rest
      ^ ")"

let simple_literal_equality_symmetry_proof type_env source_literal proof =
  let sym_helper left right source_proof =
    if is_vampire_bool_const left || is_vampire_bool_const right then
      let left_text = simple_tm_expr_with_expected type_env (Some "prop") left in
      let right_text = simple_tm_expr_with_expected type_env (Some "prop") right in
      "vampire_eq_prop_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
    else
      let sort =
        match simple_tm_sort type_env left, simple_tm_sort type_env right with
        | Some sort, _ | _, Some sort -> simple_strip_outer_parens sort
        | None, None -> "set"
      in
      match sort with
      | "set" ->
          let left_text = simple_tm_expr_with_expected type_env (Some "set") left in
          let right_text = simple_tm_expr_with_expected type_env (Some "set") right in
          "vampire_eq_set_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
      | "prop" ->
          let left_text = simple_tm_expr_with_expected type_env (Some "prop") left in
          let right_text = simple_tm_expr_with_expected type_env (Some "prop") right in
          "vampire_eq_prop_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
      | _ ->
          emit_error ("simple equality-symmetry does not support equality at sort " ^ sort)
  in
  match source_literal with
  | Pos atom ->
      begin match equality_sides atom with
      | Some (left, right) -> sym_helper left right proof
      | None -> emit_error "simple equality-symmetry literal is not an equality"
      end
  | Neg atom ->
      begin match equality_sides atom with
      | Some (left, right) ->
          "(fun Hswapped_eq => " ^ proof ^ " ("
          ^ sym_helper right left "Hswapped_eq"
          ^ "))"
      | None -> emit_error "simple equality-symmetry literal is not an equality"
      end

let simple_paramodulate_unit_proof
    clause_body_prop type_env id equality_parent_id target_parent_id equality_index target_index position
    from_tm to_tm result equality_sorts target_sorts result_sorts checked names =
  let equality_clause = lookup_simple_clause checked equality_parent_id in
  let target_clause = lookup_simple_clause checked target_parent_id in
  let equality_literal = simple_clause_nth id "paramodulation equality" equality_index equality_clause in
  let target_literal = simple_clause_nth id "paramodulation target" target_index target_clause in
  let equality_rest = simple_remove_index id "paramodulation equality" equality_index equality_clause in
  let target_rest = simple_remove_index id "paramodulation target" target_index target_clause in
  let equality_atom =
    match equality_literal with
    | Pos atom -> atom
    | Neg _ -> emit_error (id ^ ": paramodulation equality literal is not positive")
  in
  let left, right =
    match equality_sides equality_atom with
    | Some sides -> sides
    | None -> emit_error (id ^ ": paramodulation equality literal is not an equality")
  in
  let target_atom = literal_atom target_literal in
  let rewrite_position =
    let rec select = function
      | [] -> emit_error (id ^ ": paramodulation position does not contain from term")
      | candidate :: rest ->
          begin match try_tm_at_position target_atom candidate with
          | Some found when found = from_tm -> candidate
          | _ -> select rest
          end
    in
    select (paramodulation_position_candidates target_atom position)
  in
  let rewritten_atom = replace_tm_at_position target_atom rewrite_position to_tm (id ^ " target") in
  let rewritten_literal = replace_literal_atom target_literal rewritten_atom in
  let expected = equality_rest @ target_rest @ [rewritten_literal] in
  let result_literal, result_literal_needs_symmetry =
    if same_clause_multiset expected result then
      rewritten_literal, false
    else
      match swap_literal_equality rewritten_literal with
      | Some swapped_literal
          when same_clause_multiset (equality_rest @ target_rest @ [swapped_literal]) result ->
          swapped_literal, true
      | _ ->
          emit_error
            (id ^ ": simple paramodulation proof expects target rest plus the rewritten literal")
  in
  let sort =
    match simple_tm_sort type_env from_tm, simple_tm_sort type_env to_tm with
    | Some sort, _ | _, Some sort -> simple_strip_outer_parens sort
    | None, None -> emit_error (id ^ ": cannot infer paramodulation rewrite sort")
  in
  let equality_expr =
    simple_apply_forall_vars (lookup_simple_name names equality_parent_id) equality_sorts
  in
  let target_expr =
    simple_apply_forall_vars (lookup_simple_name names target_parent_id) target_sorts
  in
  let render_tm ?expected tm =
    simple_tm_expr_with_expected type_env expected tm
  in
  let rewrite_selected_proof equality_lit_proof target_lit_proof =
    if sort = "prop" then begin
      let var_name = "vpm_z" in
      let var_tm = TmH var_name in
      let ctx_atom = replace_tm_at_position target_atom rewrite_position var_tm (id ^ " context") in
      let ctx_literal = replace_literal_atom target_literal ctx_atom in
      let ctx_type_env = (var_name, "prop") :: type_env in
      let ctx_prop = simple_literal_prop_with_type_env ctx_type_env ctx_literal in
      let ctx = "(fun " ^ var_name ^ ":prop => " ^ ctx_prop ^ ")" in
      if left = from_tm && right = to_tm then
        Printf.sprintf "(%s %s %s)" equality_lit_proof ctx target_lit_proof
      else if right = from_tm && left = to_tm then
        let prop_arg tm =
          let text = render_tm ~expected:"prop" tm in
          match tm with
          | TmH _ | DB _ -> text
          | _ -> "(" ^ text ^ ")"
        in
        let left_text = prop_arg left in
        let right_text = prop_arg right in
        Printf.sprintf "((vampire_eq_prop_sym %s %s %s) %s %s)"
          left_text right_text equality_lit_proof ctx target_lit_proof
      else
        emit_error (id ^ ": paramodulation from/to terms do not match equality literal")
    end else begin
      let left_is_from = left = from_tm && right = to_tm in
      let right_is_from = right = from_tm && left = to_tm in
      if not (left_is_from || right_is_from) then
        emit_error (id ^ ": paramodulation from/to terms do not match equality literal");
      let left_var = "vpm_left" in
      let right_var = "vpm_right" in
      let replacement = TmH (if left_is_from then left_var else right_var) in
      let ctx_atom = replace_tm_at_position target_atom rewrite_position replacement (id ^ " context") in
      let ctx_literal = replace_literal_atom target_literal ctx_atom in
      let ctx_type_env = (left_var, sort) :: (right_var, sort) :: type_env in
      let ctx_prop = simple_literal_prop_with_type_env ctx_type_env ctx_literal in
      let binder_sort = simple_binder_sort_expr sort in
      let ctx =
        "(fun " ^ left_var ^ ":" ^ binder_sort
        ^ " => fun " ^ right_var ^ ":" ^ binder_sort
        ^ " => " ^ ctx_prop ^ ")"
      in
      Printf.sprintf "(%s %s %s)" equality_lit_proof ctx target_lit_proof
    end
  in
  let result_literal_proof equality_lit_proof target_lit_proof =
    let direct_proof = rewrite_selected_proof equality_lit_proof target_lit_proof in
    if result_literal_needs_symmetry then
      "(" ^ simple_literal_equality_symmetry_proof type_env rewritten_literal direct_proof ^ ")"
    else
      direct_proof
  in
  let target_prop = clause_body_prop result in
  let rec consume_target equality_lit_proof selected_index source_clause source_proof depth =
    match source_clause with
    | [] -> emit_error "cannot paramodulate from the empty clause"
    | [lit] ->
        begin match selected_index with
        | Some 0 ->
            simple_clause_intro_proof result result_literal
              (result_literal_proof equality_lit_proof source_proof)
        | Some _ -> emit_error "paramodulation selected target index is out of bounds"
        | None -> simple_clause_intro_proof result lit source_proof
        end
    | lit :: rest ->
        let head_name = "Hparamod_lit_" ^ string_of_int depth in
        let tail_name = "Hparamod_tail_" ^ string_of_int depth in
        let head_branch =
          match selected_index with
          | Some 0 ->
              simple_clause_intro_proof result result_literal
                (result_literal_proof equality_lit_proof head_name)
          | _ -> simple_clause_intro_proof result lit head_name
        in
        let rest_selected =
          match selected_index with
          | Some 0 -> None
          | Some n -> Some (n - 1)
          | None -> None
        in
        let tail_branch =
          consume_target equality_lit_proof rest_selected rest tail_name (depth + 1)
        in
        Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
          source_proof (simple_prop_arg target_prop)
          head_name head_branch
          tail_name tail_branch
  in
  let rec consume_equality selected_index source_clause source_proof depth =
    match source_clause with
    | [] -> emit_error "cannot paramodulate from an empty equality clause"
    | [lit] ->
        begin match selected_index with
        | Some 0 -> consume_target source_proof (Some target_index) target_clause target_expr 0
        | Some _ -> emit_error "paramodulation equality index is out of bounds"
        | None -> simple_clause_intro_proof result lit source_proof
        end
    | lit :: rest ->
        let head_name = "Hparamod_eq_lit_" ^ string_of_int depth in
        let tail_name = "Hparamod_eq_tail_" ^ string_of_int depth in
        let head_branch =
          match selected_index with
          | Some 0 -> consume_target head_name (Some target_index) target_clause target_expr 0
          | _ -> simple_clause_intro_proof result lit head_name
        in
        let rest_selected =
          match selected_index with
          | Some 0 -> None
          | Some n -> Some (n - 1)
          | None -> None
        in
        let tail_branch = consume_equality rest_selected rest tail_name (depth + 1) in
        Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
          source_proof (simple_prop_arg target_prop)
          head_name head_branch
          tail_name tail_branch
  in
  simple_wrap_forall_intro result_sorts
    (consume_equality (Some equality_index) equality_clause equality_expr 0)

let simple_substitute_proof
    clause_body_prop type_env id parent_id subst result parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  let substituted_parent = subst_clause subst parent_clause in
  if not (same_clause_multiset substituted_parent result) then
    emit_error (id ^ ": simple substitution proof expects the explicit substituted parent clause");
  let subst_sources = List.map fst subst in
  if not
       (List.for_all
          (fun source_name ->
             List.exists (fun (name, _) -> name = source_name) parent_sorts)
          subst_sources) then
    emit_error (id ^ ": simple substitution proof only instantiates quantified parent variables");
  let arg_for_parent_var (name, sort) =
    let tm =
      match List.assoc_opt name subst with
      | Some tm -> tm
      | None -> TmH name
    in
    let text = simple_tm_expr_with_expected type_env (Some sort) tm in
    match tm with
    | TmH _ | DB _ -> text
    | _ -> "(" ^ text ^ ")"
  in
  let parent_expr =
    List.fold_left
      (fun acc parent_sort -> "(" ^ acc ^ " " ^ arg_for_parent_var parent_sort ^ ")")
      (lookup_simple_name names parent_id)
      parent_sorts
  in
  let target = clause_body_prop result in
  simple_wrap_forall_intro result_sorts
    (simple_clause_projection_proof target result substituted_parent parent_expr 0)

let simple_substituted_parent_expr type_env subst parent_sorts parent_name =
  let subst_sources = List.map fst subst in
  if not
       (List.for_all
          (fun source_name ->
             List.exists (fun (name, _) -> name = source_name) parent_sorts)
          subst_sources) then
    emit_error "substitution proof only instantiates quantified parent variables";
  let arg_for_parent_var (name, sort) =
    let tm =
      match List.assoc_opt name subst with
      | Some tm -> tm
      | None -> TmH name
    in
    let text = simple_tm_expr_with_expected type_env (Some sort) tm in
    match tm with
    | TmH _ | DB _ -> text
    | _ -> "(" ^ text ^ ")"
  in
  List.fold_left
    (fun acc parent_sort -> "(" ^ acc ^ " " ^ arg_for_parent_var parent_sort ^ ")")
    parent_name
    parent_sorts

let simple_condensation_clause_proof
    clause_body_prop type_env id parent_id subst result parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  let substituted_parent = subst_clause subst parent_clause in
  let expected = unique_clause substituted_parent in
  if expected <> result then
    emit_error (id ^ ": simple condensation proof expects the duplicate-collapsed substituted parent clause");
  if List.length expected >= List.length parent_clause then
    emit_error (id ^ ": simple condensation proof expects at least one duplicate literal removal");
  let parent_expr =
    simple_substituted_parent_expr
      type_env subst parent_sorts (lookup_simple_name names parent_id)
  in
  let target = clause_body_prop result in
  simple_wrap_forall_intro result_sorts
    (simple_clause_projection_proof target result substituted_parent parent_expr 0)

let simple_condensation_proof id parent_id subst result checked names =
  if subst <> [] then
    emit_error (id ^ ": simple emitter does not support term-changing condensation");
  let parent_clause = lookup_simple_clause checked parent_id in
  match parent_clause, result with
  | [a; b], [res] when a = b && a = res ->
      let target = simple_literal_prop res in
      let target_arg = simple_prop_arg target in
      let parent_name = lookup_simple_name names parent_id in
      Printf.sprintf "(%s %s (fun Hlit_0 => Hlit_0) (fun Htail_1 => Htail_1))"
        parent_name target_arg
  | _ ->
      emit_error (id ^ ": simple emitter supports only two-literal propositional condensation")

let simple_equality_symmetry_body id parent_id literal_index result checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  let literal = simple_clause_nth id "equality-symmetry" literal_index parent_clause in
  let swapped =
    match swap_literal_equality literal with
    | Some swapped -> swapped
    | None -> emit_error (id ^ ": equality-symmetry literal is not an equality")
  in
  begin match parent_clause, literal, result with
  | [Pos atom], Pos _, [res] when res = swapped ->
      begin match equality_sides atom with
      | Some _ ->
          "symmetry. exact " ^ lookup_simple_name names parent_id ^ "."
      | None -> emit_error (id ^ ": equality-symmetry literal is not an equality")
      end
  | _ ->
      emit_error (id ^ ": simple emitter supports only unit positive equality symmetry")
  end

let simple_equality_symmetry_proof type_env source_literal proof =
  let sym_helper left right source_proof =
    if is_vampire_bool_const left || is_vampire_bool_const right then
      let left_text = simple_tm_expr_with_expected type_env (Some "prop") left in
      let right_text = simple_tm_expr_with_expected type_env (Some "prop") right in
      "vampire_eq_prop_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
    else
      let sort =
        match simple_tm_sort type_env left, simple_tm_sort type_env right with
        | Some sort, _ | _, Some sort -> simple_strip_outer_parens sort
        | None, None -> "set"
      in
      match sort with
      | "set" ->
          let left_text = simple_tm_expr_with_expected type_env (Some "set") left in
          let right_text = simple_tm_expr_with_expected type_env (Some "set") right in
          "vampire_eq_set_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
      | "prop" ->
          let left_text = simple_tm_expr_with_expected type_env (Some "prop") left in
          let right_text = simple_tm_expr_with_expected type_env (Some "prop") right in
          "vampire_eq_prop_sym (" ^ left_text ^ ") (" ^ right_text ^ ") " ^ source_proof
      | _ ->
          emit_error ("simple equality-symmetry does not support equality at sort " ^ sort)
  in
  match source_literal with
  | Pos atom ->
      begin match equality_sides atom with
      | Some (left, right) -> sym_helper left right proof
      | None -> emit_error "simple equality-symmetry literal is not an equality"
      end
  | Neg atom ->
      begin match equality_sides atom with
      | Some (left, right) ->
          "(fun Hswapped_eq => " ^ proof ^ " ("
          ^ sym_helper right left "Hswapped_eq"
          ^ "))"
      | None -> emit_error "simple equality-symmetry literal is not an equality"
      end

let rec simple_clause_equality_symmetry_proof
    type_env target_prop target_clause selected_index source_clause source_proof depth =
  match source_clause with
  | [] -> emit_error "simple equality-symmetry cannot map an empty source clause"
  | [lit] ->
      begin match selected_index with
      | Some 0 ->
          let swapped =
            match swap_literal_equality lit with
            | Some swapped -> swapped
            | None -> emit_error "simple equality-symmetry literal is not an equality"
          in
          simple_clause_intro_proof
            target_clause swapped
            ("(" ^ simple_equality_symmetry_proof type_env lit source_proof ^ ")")
      | Some _ -> emit_error "simple equality-symmetry selected index is out of bounds"
      | None -> simple_clause_intro_proof target_clause lit source_proof
      end
  | lit :: rest ->
      let head_name = "Hsym_lit_" ^ string_of_int depth in
      let tail_name = "Hsym_tail_" ^ string_of_int depth in
      let head_branch =
        match selected_index with
        | Some 0 ->
            let swapped =
              match swap_literal_equality lit with
              | Some swapped -> swapped
              | None -> emit_error "simple equality-symmetry literal is not an equality"
            in
            simple_clause_intro_proof
              target_clause swapped
              ("(" ^ simple_equality_symmetry_proof type_env lit head_name ^ ")")
        | _ -> simple_clause_intro_proof target_clause lit head_name
      in
      let rest_selected =
        match selected_index with
        | Some 0 -> None
        | Some n -> Some (n - 1)
        | None -> None
      in
      let tail_branch =
        simple_clause_equality_symmetry_proof
          type_env target_prop target_clause rest_selected rest tail_name (depth + 1)
      in
      Printf.sprintf "(%s %s (fun %s => %s) (fun %s => %s))"
        source_proof (simple_prop_arg target_prop)
        head_name head_branch
        tail_name tail_branch

let simple_equality_symmetry_clause_proof
    type_env id parent_id literal_index result target_prop parent_sorts result_sorts checked names =
  let parent_clause = lookup_simple_clause checked parent_id in
  ignore (simple_clause_nth id "equality-symmetry" literal_index parent_clause);
  let parent_name = lookup_simple_name names parent_id in
  let parent_expr = simple_apply_forall_vars parent_name parent_sorts in
  let proof =
    simple_clause_equality_symmetry_proof
      type_env target_prop result (Some literal_index) parent_clause parent_expr 0
  in
  simple_wrap_forall_intro result_sorts proof

let simple_prop_term_expr type_env source_atom tm =
  if tm = source_atom then simple_atom_prop_with_type_env type_env source_atom
  else simple_tm_expr_with_expected type_env (Some "prop") tm

let simple_fool_bool_proof
    type_env parent_sorts result_sorts id parent_literal result_literal names parent_id =
  let parent_name =
    simple_apply_forall_vars (lookup_simple_name names parent_id) parent_sorts
  in
  let source_atom, source_negative =
    match parent_literal with
    | Pos atom -> atom, false
    | Neg atom -> atom, true
  in
  let target_atom, target_negative =
    match result_literal with
    | Pos atom -> atom, false
    | Neg atom -> atom, true
  in
  if source_negative <> target_negative then
    emit_error (id ^ ": FOOL bool replay expected matching literal polarity");
  let left, right =
    match equality_sides target_atom with
    | Some (left, right) -> left, right
    | None -> emit_error (id ^ ": FOOL bool target is not equality-to-true")
  in
  let left_is_source = left = source_atom in
  let right_is_source = right = source_atom in
  let left_is_true = is_vampire_bool_const left && not (is_vampire_false left) in
  let right_is_true = is_vampire_bool_const right && not (is_vampire_false right) in
  if not ((left_is_source && right_is_true) || (left_is_true && right_is_source)) then
    emit_error (id ^ ": FOOL bool target does not wrap the parent atom with true");
  let left_text = simple_prop_term_expr type_env source_atom left in
  let right_text = simple_prop_term_expr type_env source_atom right in
  let source_text = simple_atom_prop_with_type_env type_env source_atom in
  let eq_text = simple_atom_prop_with_type_env type_env target_atom in
  let proof =
    if not source_negative then
      let left_to_right, right_to_left =
        if left_is_source then
          (Printf.sprintf "(fun H:%s => %s)" source_text simple_true_proof,
           Printf.sprintf "(fun H:%s => %s)" right_text parent_name)
        else
          (Printf.sprintf "(fun H:%s => %s)" left_text parent_name,
           Printf.sprintf "(fun H:%s => %s)" source_text simple_true_proof)
      in
      Printf.sprintf "(vampire_eq_prop_ext (%s) (%s) %s %s)"
        left_text right_text left_to_right right_to_left
    else
      let source_from_eq =
        if left_is_source then
          Printf.sprintf "((vampire_eq_prop_sym (%s) (%s) Heq_fool) (fun Z:prop => Z) %s)"
            left_text right_text simple_true_proof
        else
          Printf.sprintf "(Heq_fool (fun Z:prop => Z) %s)" simple_true_proof
      in
      Printf.sprintf "(fun Heq_fool:%s => %s %s)" eq_text parent_name source_from_eq
  in
  simple_wrap_forall_intro result_sorts proof

let emit_simple_megalodon ?(theorem_name="vampire_certificate_native") ?(source_map=[]) cert =
  ignore (check_certificate cert);
  simple_lambda_sort_env := metadata_lambda_sort_env cert;
  let prop_names, term_names = collect_simple_names cert in
  let lines = ref
    [
      "Definition False : prop := forall p:prop, p.";
      "Definition True : prop := forall p:prop, p -> p.";
      "Definition vampire_false : prop := False.";
      "Definition vampire_true : prop := True.";
      "Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.";
      "Infix \\/ 785 left := or.";
      "Definition vampire_or : prop -> prop -> prop := or.";
      "Definition vampire_and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.";
      "Definition vampire_exists_set : (set -> prop) -> prop := fun P:set->prop => forall q:prop, (forall x:set, P x -> q) -> q.";
      "Definition vampire_exists_prop : (prop -> prop) -> prop := fun P:prop->prop => forall q:prop, (forall x:prop, P x -> q) -> q.";
      "Definition vampire_exists_set_prop : ((set->prop) -> prop) -> prop := fun P:(set->prop)->prop => forall q:prop, (forall x:set->prop, P x -> q) -> q.";
      "Definition vampire_exists_set_set : ((set->set) -> prop) -> prop := fun P:(set->set)->prop => forall q:prop, (forall x:set->set, P x -> q) -> q.";
      "Definition vampire_exists_set_set_prop : ((set->set->prop) -> prop) -> prop := fun P:(set->set->prop)->prop => forall q:prop, (forall x:set->set->prop, P x -> q) -> q.";
      "Definition vampire_eq_prop : prop -> prop -> prop := fun A B:prop => forall Q:prop->prop, Q A -> Q B.";
      "Section Eq.";
      "Variable A:SType.";
      "Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.";
      "End Eq.";
      "Infix = 502 := eq.";
      "Theorem vampire_eq_prop_sym : forall A:prop, forall B:prop, vampire_eq_prop A B -> vampire_eq_prop B A.";
      "let A B.";
      "assume H.";
      "let Q.";
      "assume HQ.";
      "exact H (fun Z:prop => Q Z -> Q A) (fun HA => HA) HQ.";
      "Qed.";
      "Theorem vampire_eq_set_sym : forall x:set, forall y:set, x = y -> y = x.";
      "let x y.";
      "assume H.";
      "let Q.";
      "assume HQ.";
      "exact H (fun a b:set => Q b a) HQ.";
      "Qed.";
      "Definition vampire_eq_prop_to_set : (prop->set)->(prop->set)->prop := fun x y:prop->set => forall Q:(prop->set)->(prop->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_prop_to_prop_to_prop : (prop->prop->prop)->(prop->prop->prop)->prop := fun x y:prop->prop->prop => forall Q:(prop->prop->prop)->(prop->prop->prop)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_set : (set->set)->(set->set)->prop := fun x y:set->set => forall Q:(set->set)->(set->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_prop : (set->prop)->(set->prop)->prop := fun x y:set->prop => forall Q:(set->prop)->(set->prop)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_set_to_prop : (set->set->prop)->(set->set->prop)->prop := fun x y:set->set->prop => forall Q:(set->set->prop)->(set->set->prop)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_set_to_set : (set->set->set)->(set->set->set)->prop := fun x y:set->set->set => forall Q:(set->set->set)->(set->set->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_lp_set_to_set_rp_to_set : ((set->set)->set)->((set->set)->set)->prop := fun x y:(set->set)->set => forall Q:((set->set)->set)->((set->set)->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_lp_set_to_prop_rp_to_set : ((set->prop)->set)->((set->prop)->set)->prop := fun x y:(set->prop)->set => forall Q:((set->prop)->set)->((set->prop)->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_lp_set_to_set_rp_to_set : (set->((set->set)->set))->(set->((set->set)->set))->prop := fun x y:set->((set->set)->set) => forall Q:(set->((set->set)->set))->(set->((set->set)->set))->prop, Q x y -> Q y x.";
      "Definition vampire_eq_lp_set_to_set_rp_to_set_to_set : ((set->set)->set->set)->((set->set)->set->set)->prop := fun x y:(set->set)->set->set => forall Q:((set->set)->set->set)->((set->set)->set->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_lp_set_to_set_to_set_rp_to_set_to_set : ((set->set->set)->set->set)->((set->set->set)->set->set)->prop := fun x y:(set->set->set)->set->set => forall Q:((set->set->set)->set->set)->((set->set->set)->set->set)->prop, Q x y -> Q y x.";
      "Definition vampire_eq_set_to_lp_set_to_set_to_set_rp_to_set_to_set : (set->((set->set->set)->set->set))->(set->((set->set->set)->set->set))->prop := fun x y:set->((set->set->set)->set->set) => forall Q:(set->((set->set->set)->set->set))->(set->((set->set->set)->set->set))->prop, Q x y -> Q y x.";
      "Definition vPI : (set->prop)->prop := fun P:set->prop => forall x:set, P x.";
      "Definition vampire_set_ap : set->set->set := fun x y:set => x.";
      "Notation SetImplicitOp vampire_set_ap.";
    ]
  in
  let add_line_once line =
    if not (List.mem line !lines) then lines := !lines @ [line]
  in
  List.iter add_line_once cert.metadata.symbol_declarations;
  let higher_order_definition_db_names = metadata_higher_order_definition_db_names cert in
  List.iter
    (fun name ->
       if not (is_db_ident name && List.mem name higher_order_definition_db_names) then
         add_line_once ("Variable " ^ name ^ ":prop."))
    prop_names;
  List.iter
    (fun name ->
       if not (is_db_ident name && List.mem name higher_order_definition_db_names) then
         add_line_once ("Variable " ^ name ^ ":set."))
    term_names;
  let used_names = ref (prop_names @ term_names) in
  let emitted_names = ref [] in
  let emitted_props = ref [] in
  let emitted_var_sorts = ref [] in
  let checked = ref [] in
  let assumptions = ref [] in
  let bridge_assumptions = ref [] in
  let claims = ref [] in
  let uses_vampire_eq_prop_ext = ref false in
  let final_empty = ref None in
  let add_emitted id name =
    emitted_names := (id, name) :: !emitted_names
  in
  let add_emitted_prop id prop =
    emitted_props := (id, prop) :: !emitted_props
  in
  let add_emitted_var_sorts id sorts =
    emitted_var_sorts := (id, sorts) :: !emitted_var_sorts
  in
  let add_emitted_prop_and_sorts id prop sorts =
    add_emitted_prop id prop;
    add_emitted_var_sorts id sorts
  in
  let input_name id source =
    simple_fresh_name used_names ("src_" ^ simple_source_label source_map source ^ "__" ^ id)
  in
  let derived_name id = simple_fresh_name used_names id in
  let add_checked id clause =
    checked := (id, clause) :: !checked;
    if clause = [] then final_empty := Some id
  in
  let variable_sorts_for_ids ids =
    ids
    |> List.concat_map
         (fun id ->
            match List.assoc_opt id !emitted_var_sorts with
            | Some sorts -> sorts
            | None -> metadata_step_variable_sort_pairs cert id)
    |> simple_unique_variable_sorts
  in
  let symbol_type_env = simple_symbol_type_env cert in
  let declared_symbol_names =
    metadata_declared_names cert
    |> List.map megalodon_ident
    |> List.sort_uniq compare
  in
  let collected_global_names =
    prop_names @ term_names
    |> List.filter (fun name -> not (is_db_ident name))
    |> List.sort_uniq compare
  in
  let optional_megalodon_ident name =
    try Some (megalodon_ident name) with Error _ -> None
  in
  let local_clause_names clause =
    let vlam_bound_names = simple_clause_vlam_bound_names clause in
    simple_clause_names clause
    |> List.filter_map
         (fun name ->
            match optional_megalodon_ident name with
            | Some ident
              when ident <> "vLAM"
                   && ident <> "vPI"
                   && not (List.mem_assoc ident symbol_type_env)
                   && not (List.mem ident collected_global_names)
                   && not (List.mem ident declared_symbol_names)
                   && not (List.mem ident vlam_bound_names) -> Some ident
            | _ -> None)
  in
  let substitution_variable_sorts parent_id subst =
    let parent_sorts = variable_sorts_for_ids [parent_id] in
    subst
    |> List.concat_map
         (fun (source_name, target) ->
            let source_sort = List.assoc_opt source_name parent_sorts in
            let direct =
              match target, source_sort with
              | TmH target_name, Some sort -> [(megalodon_ident target_name, sort)]
              | _ -> []
            in
            let inferred =
              simple_infer_tm_variable_sorts ?expected:source_sort symbol_type_env target
            in
            direct @ inferred)
    |> simple_unique_variable_sorts
  in
  let clause_prop_and_sorts_for_ids ?(extra_sorts=[]) id parent_ids result =
    let vlam_bound_names = simple_clause_vlam_bound_names result in
    let available_sorts =
      extra_sorts
      @ simple_infer_clause_variable_sorts symbol_type_env result
      @ variable_sorts_for_ids (id :: parent_ids)
      |> simple_unique_variable_sorts
      |> List.filter (fun (name, _) -> not (List.mem name vlam_bound_names))
    in
    let names = local_clause_names result in
    let variable_sorts = simple_variable_sorts_for_names names available_sorts in
    let local_type_env = simple_type_env_with_variables available_sorts symbol_type_env in
    match metadata_step_proposition cert id with
    | Some prop when parent_ids = [] ->
        let metadata_sorts = metadata_step_variable_sort_pairs cert id in
        let definition_sorts = metadata_definition_lhs_sort_pairs cert id in
        let metadata_sorts =
          metadata_sorts @ definition_sorts
          |> simple_unique_variable_sorts
        in
        let prop = simple_fix_known_higher_order_binders prop in
        (simple_quantify_prop definition_sorts prop, metadata_sorts)
    | Some _ | None ->
        try
          let prop = simple_clause_prop_with_type_env local_type_env result in
          (simple_fix_known_higher_order_binders (simple_quantify_prop variable_sorts prop), variable_sorts)
        with Error _ ->
          let prop = simple_clause_prop result in
          (simple_fix_known_higher_order_binders (simple_quantify_prop variable_sorts prop), variable_sorts)
  in
  let formula_literal_prop_and_sorts id literal =
    let sorts = metadata_step_variable_sort_pairs cert id in
    match metadata_step_proposition cert id with
    | Some prop -> (simple_fix_known_higher_order_binders prop, sorts)
    | None ->
        let prop =
          try
            match literal with
            | Pos atom -> simple_atom_prop_with_type_env symbol_type_env atom
            | Neg atom -> "(" ^ simple_atom_prop_with_type_env symbol_type_env atom ^ " -> False)"
          with Error _ -> simple_formula_prop cert id
        in
        (prop, sorts)
  in
  let formula_tm_prop_and_sorts id formula =
    let sorts = metadata_step_variable_sort_pairs cert id in
    match metadata_step_proposition cert id with
    | Some prop -> (simple_fix_known_higher_order_binders prop, sorts)
    | None ->
        let prop =
          try simple_atom_prop_with_type_env symbol_type_env formula
          with Error _ -> simple_formula_prop cert id
        in
        (prop, sorts)
  in
  let emitted_parent_prop parent_id =
    match List.assoc_opt parent_id !emitted_props with
    | Some proposition -> proposition
    | None ->
    match metadata_step_proposition cert parent_id with
    | Some proposition -> proposition
    | None ->
    match List.assoc_opt parent_id !checked with
    | Some clause -> simple_clause_prop clause
    | None -> simple_parent_prop cert parent_id
  in
  let add_bridge_claim ?(kind="native") id parent_id name target_prop target_sorts =
    let parent_name = lookup_simple_name !emitted_names parent_id in
    let bridge_name = simple_fresh_name used_names ("bridge_" ^ kind ^ "__" ^ id) in
    let source_prop = emitted_parent_prop parent_id in
    bridge_assumptions :=
      !bridge_assumptions @ [(bridge_name, "(" ^ source_prop ^ ") -> (" ^ target_prop ^ ")")];
    add_emitted_prop_and_sorts id target_prop target_sorts;
    claims := !claims @ [(name, target_prop, "exact (" ^ bridge_name ^ " " ^ parent_name ^ ").")]
  in
  let add_clause_inference_bridge ?(extra_sorts=[]) kind id parent_ids result =
    let name = derived_name id in
    let target_prop, target_sorts = clause_prop_and_sorts_for_ids ~extra_sorts id parent_ids result in
    let parent_names = List.map (lookup_simple_name !emitted_names) parent_ids in
    let parent_props = List.map emitted_parent_prop parent_ids in
    let bridge_name = simple_fresh_name used_names ("bridge_" ^ kind ^ "__" ^ id) in
    let bridge_type =
      String.concat " -> " (List.map (fun prop -> "(" ^ prop ^ ")") parent_props @ [target_prop])
    in
    let bridge_application =
      match parent_names with
      | [] -> bridge_name
      | _ -> "(" ^ String.concat " " (bridge_name :: parent_names) ^ ")"
    in
    add_emitted id name;
    add_emitted_prop_and_sorts id target_prop target_sorts;
    bridge_assumptions := !bridge_assumptions @ [(bridge_name, bridge_type)];
    claims := !claims @ [(name, target_prop, "exact " ^ bridge_application ^ ".")];
    add_checked id result
  in
  let add_formula_inference_bridge kind id parent_ids target_prop =
    let target_sorts = metadata_step_variable_sort_pairs cert id in
    let name = derived_name id in
    let parent_names = List.map (lookup_simple_name !emitted_names) parent_ids in
    let parent_props = List.map emitted_parent_prop parent_ids in
    let bridge_name = simple_fresh_name used_names ("bridge_" ^ kind ^ "__" ^ id) in
    let bridge_type =
      String.concat " -> " (List.map (fun prop -> "(" ^ prop ^ ")") parent_props @ [target_prop])
    in
    let bridge_application =
      match parent_names with
      | [] -> bridge_name
      | _ -> "(" ^ String.concat " " (bridge_name :: parent_names) ^ ")"
    in
    add_emitted id name;
    add_emitted_prop_and_sorts id target_prop target_sorts;
    bridge_assumptions := !bridge_assumptions @ [(bridge_name, bridge_type)];
    claims := !claims @ [(name, target_prop, "exact " ^ bridge_application ^ ".")]
  in
  List.iter
    (function
      | Input (id, source, clause) ->
          let name = input_name id source in
          let prop, sorts = clause_prop_and_sorts_for_ids id [] clause in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id clause
      | FormulaInput (id, source, literal) ->
          let name = input_name id source in
          let prop, sorts = formula_literal_prop_and_sorts id literal in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)]
      | FormulaTermInput (id, source, formula) ->
          let name = input_name id source in
          let prop, sorts = formula_tm_prop_and_sorts id formula in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)]
      | FormulaTermCopy (id, parent_id, formula) ->
          let name = derived_name id in
          let proof = lookup_simple_name !emitted_names parent_id in
          let prop, sorts = formula_tm_prop_and_sorts id formula in
          if emitted_parent_prop parent_id = prop then begin
            add_emitted id name;
            add_emitted_prop_and_sorts id prop sorts;
            claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")]
          end else
            add_formula_inference_bridge "formula_term_copy" id [parent_id] prop
      | RectifyFormula (id, parent_id, _, formula) ->
          let name = derived_name id in
          let proof = lookup_simple_name !emitted_names parent_id in
          let prop, sorts = formula_tm_prop_and_sorts id formula in
          if emitted_parent_prop parent_id = prop then begin
            add_emitted id name;
            add_emitted_prop_and_sorts id prop sorts;
            claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")]
          end else
            add_formula_inference_bridge "rectify_formula" id [parent_id] prop
      | FormulaCopy (id, parent_id, literal) ->
          let name = derived_name id in
          let proof = lookup_simple_name !emitted_names parent_id in
          let prop, sorts = formula_literal_prop_and_sorts id literal in
          if emitted_parent_prop parent_id = prop then begin
            add_emitted id name;
            add_emitted_prop_and_sorts id prop sorts;
            claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")]
          end else
            add_formula_inference_bridge "formula_copy" id [parent_id] prop
      | FoolFormula (id, parent_id, formula) ->
          let name = derived_name id in
          let target_prop, target_sorts = formula_tm_prop_and_sorts id formula in
          add_emitted id name;
          add_bridge_claim ~kind:"fool" id parent_id name target_prop target_sorts
      | FoolBool (id, parent_id, result) ->
          let name = derived_name id in
          let target_prop, target_sorts = formula_literal_prop_and_sorts id result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ target_sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let literal_prop literal =
            try simple_literal_prop_with_type_env type_env literal
            with Error _ -> simple_literal_prop literal
          in
          let parent_literal_from_result =
            let target_atom, negative =
              match result with
              | Pos atom -> atom, false
              | Neg atom -> atom, true
            in
            match equality_sides target_atom with
            | Some (left, right) ->
                let source =
                  match is_vampire_bool_const left, is_vampire_bool_const right with
                  | true, false when not (is_vampire_false left) -> Some right
                  | false, true when not (is_vampire_false right) -> Some left
                  | _ -> None
                in
                begin match source with
                | Some atom -> if negative then Neg atom else Pos atom
                | None -> result
                end
            | None -> result
          in
          let parent_prop = simple_quantify_prop parent_sorts (literal_prop parent_literal_from_result) in
          let structural_target_prop =
            simple_quantify_prop target_sorts (literal_prop result)
          in
          begin match
            if emitted_parent_prop parent_id <> parent_prop
               || target_prop <> structural_target_prop then None
            else
              try Some (simple_fool_bool_proof
                          type_env parent_sorts target_sorts id
                          parent_literal_from_result result !emitted_names parent_id)
              with Error _ -> None
          with
          | Some proof ->
              uses_vampire_eq_prop_ext := true;
              add_emitted id name;
              add_emitted_prop_and_sorts id target_prop target_sorts;
              claims := !claims @ [(name, target_prop, "exact " ^ proof ^ ".")]
          | None ->
              add_emitted id name;
              add_bridge_claim ~kind:"fool" id parent_id name target_prop target_sorts
          end
      | EnnfFormula (id, parent_id, formula) ->
          let name = derived_name id in
          let target_prop, target_sorts = formula_tm_prop_and_sorts id formula in
          add_emitted id name;
          add_bridge_claim ~kind:"normal_form" id parent_id name target_prop target_sorts
      | SkolemFormula (id, parent_id, _, formula) ->
          let target_prop, _ = formula_tm_prop_and_sorts id formula in
          add_formula_inference_bridge "skolem_formula" id [parent_id] target_prop
      | SkolemFormulaComputed (id, parent_id, _) ->
          add_formula_inference_bridge "skolem_formula" id [parent_id] (simple_formula_prop cert id)
      | CnfLiteral (id, parent_id, result) ->
          let name = derived_name id in
          let target_prop, target_sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          if emitted_parent_prop parent_id = target_prop
             || simple_prop_equal_mod_app_parens (emitted_parent_prop parent_id) target_prop then begin
            add_emitted id name;
            add_emitted_prop_and_sorts id target_prop target_sorts;
            claims := !claims @
              [(name, target_prop, "exact " ^ lookup_simple_name !emitted_names parent_id ^ ".")]
          end else begin
            add_emitted id name;
            add_bridge_claim ~kind:"cnf" id parent_id name target_prop target_sorts
          end;
          add_checked id result
      | CnfFormulaClause (id, parent_id, _, result) ->
          let name = derived_name id in
          let target_prop, target_sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          if emitted_parent_prop parent_id = target_prop
             || simple_prop_equal_mod_app_parens (emitted_parent_prop parent_id) target_prop then begin
            add_emitted id name;
            add_emitted_prop_and_sorts id target_prop target_sorts;
            claims := !claims @
              [(name, target_prop, "exact " ^ lookup_simple_name !emitted_names parent_id ^ ".")]
          end else begin
            add_emitted id name;
            add_bridge_claim ~kind:"cnf" id parent_id name target_prop target_sorts
          end;
          add_checked id result
      | FoolExhaustiveness (id, result) ->
          let name = simple_fresh_name used_names ("theory_fool_exhaustiveness__" ^ id) in
          let prop, sorts = simple_clause_prop_and_sorts_for_step cert id result in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id result
      | FoolDistinctness (id, result) ->
          let name = simple_fresh_name used_names ("theory_fool_distinctness__" ^ id) in
          let prop, sorts = simple_clause_prop_and_sorts_for_step cert id result in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id result
      | PredicateDefinition (id, _, formula) ->
          let name = simple_fresh_name used_names ("theory_predicate_definition__" ^ id) in
          let prop, sorts = formula_tm_prop_and_sorts id formula in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)]
      | PredicateDefinitionFold (id, source_id, definition_id, formula) ->
          let target_prop, _ = formula_tm_prop_and_sorts id formula in
          add_formula_inference_bridge "predicate_definition_fold" id [source_id; definition_id] target_prop
      | PredicateDefinitionFoldChain (id, source_id, definition_ids, formula) ->
          let target_prop, _ = formula_tm_prop_and_sorts id formula in
          add_formula_inference_bridge "predicate_definition_fold_chain" id (source_id :: definition_ids) target_prop
      | DefinitionInput (id, result) ->
          let name = simple_fresh_name used_names ("definition_input__" ^ id) in
          let prop, sorts = clause_prop_and_sorts_for_ids id [] result in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id result
      | AvatarComponent (id, result) ->
          let name = simple_fresh_name used_names ("avatar_component__" ^ id) in
          let prop, sorts = simple_clause_prop_and_sorts_for_step cert id result in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id result
      | AvatarRefutation (id, _, _, result) ->
          let name = simple_fresh_name used_names ("avatar_refutation__" ^ id) in
          let prop, sorts = simple_clause_prop_and_sorts_for_step cert id result in
          add_emitted id name;
          add_emitted_prop_and_sorts id prop sorts;
          assumptions := !assumptions @ [(name, prop)];
          add_checked id result
      | Substitute (id, parent_id, subst, result) ->
          let subst_sorts = substitution_variable_sorts parent_id subst in
          let prop, sorts = clause_prop_and_sorts_for_ids ~extra_sorts:subst_sorts id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ subst_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let substituted_parent = subst_clause subst parent_clause in
          let substituted_sources = List.map fst subst in
          let remaining_parent_sorts =
            parent_sorts
            |> List.filter (fun (name, _) -> not (List.mem name substituted_sources))
          in
          let needed_sorts =
            remaining_parent_sorts @ subst_sorts |> simple_unique_variable_sorts
          in
          let structurally_safe =
            same_clause_multiset substituted_parent result
            && simple_sorts_subset needed_sorts sorts
            && emitted_parent_prop parent_id = structural_clause_prop parent_sorts parent_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            try
              let proof = simple_copy_proof id parent_id result !checked !emitted_names in
              Some (proof, emitted_parent_prop parent_id, variable_sorts_for_ids [parent_id])
            with Error _ ->
              if not structurally_safe then None
              else
                try
                  let proof =
                    simple_substitute_proof
                      clause_body_prop type_env id parent_id subst result
                      parent_sorts sorts !checked !emitted_names
                  in
                  Some (proof, prop, sorts)
                with Error _ -> None
          with
          | Some (proof, claim_prop, claim_sorts) ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id claim_prop claim_sorts;
              claims := !claims @ [(name, claim_prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge
                ~extra_sorts:subst_sorts
                "substitute" id [parent_id] result
          end
      | Condensation (id, parent_id, subst, result) ->
          let subst_sorts = substitution_variable_sorts parent_id subst in
          let prop, sorts = clause_prop_and_sorts_for_ids ~extra_sorts:subst_sorts id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ subst_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let substituted_parent = subst_clause subst parent_clause in
          let substituted_sources = List.map fst subst in
          let remaining_parent_sorts =
            parent_sorts
            |> List.filter (fun (name, _) -> not (List.mem name substituted_sources))
          in
          let needed_sorts =
            remaining_parent_sorts @ subst_sorts |> simple_unique_variable_sorts
          in
          let structurally_safe =
            unique_clause substituted_parent = result
            && simple_sorts_subset needed_sorts sorts
            && emitted_parent_prop parent_id = structural_clause_prop parent_sorts parent_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            try Some (simple_condensation_proof id parent_id subst result !checked !emitted_names)
            with Error _ ->
              if not structurally_safe then None
              else
                try Some (simple_condensation_clause_proof
                            clause_body_prop type_env id parent_id subst result
                            parent_sorts sorts !checked !emitted_names)
                with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge
                ~extra_sorts:subst_sorts
                "condensation" id [parent_id] result
          end
      | Resolve (id, left_id, right_id, left_index, right_index, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [left_id; right_id] result in
          let left_sorts = variable_sorts_for_ids [left_id] in
          let right_sorts = variable_sorts_for_ids [right_id] in
          let type_env =
            simple_type_env_with_variables
              (left_sorts @ right_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let left_clause = lookup_simple_clause !checked left_id in
          let right_clause = lookup_simple_clause !checked right_id in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let literal_prop literal =
            try simple_literal_prop_with_type_env type_env literal
            with Error _ -> simple_literal_prop literal
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let structurally_safe =
            simple_sorts_subset left_sorts sorts
            && simple_sorts_subset right_sorts sorts
            && emitted_parent_prop left_id = structural_clause_prop left_sorts left_clause
            && emitted_parent_prop right_id = structural_clause_prop right_sorts right_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            if not structurally_safe then None
            else
              let parent_sorts_of parent_id =
                if parent_id = left_id then left_sorts
                else if parent_id = right_id then right_sorts
                else variable_sorts_for_ids [parent_id]
              in
              match
                try Some (simple_resolution_clause_proof
                            clause_body_prop parent_sorts_of sorts
                            id left_id right_id left_index right_index result
                            !checked !emitted_names)
                with Error _ -> None
              with
              | Some proof -> Some proof
              | None ->
                  try Some (simple_resolution_proof
                              literal_prop parent_sorts_of
                              sorts id left_id right_id left_index right_index result
                              !checked !emitted_names)
                  with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "resolve" id [left_id; right_id] result
          end
      | Factor (id, parent_id, left_index, right_index, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let structurally_safe =
            simple_sorts_subset parent_sorts sorts
            && emitted_parent_prop parent_id = structural_clause_prop parent_sorts parent_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            if not structurally_safe then None
            else
              try Some (simple_factor_proof
                          clause_body_prop parent_sorts sorts id parent_id left_index right_index result
                          !checked !emitted_names)
              with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "factor" id [parent_id] result
          end
      | EqualitySymmetry (id, parent_id, literal_index, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let target_body_prop =
            try simple_clause_prop_with_type_env type_env result
            with Error _ -> simple_clause_prop result
          in
          let parent_body_prop =
            try simple_clause_prop_with_type_env type_env parent_clause
            with Error _ -> simple_clause_prop parent_clause
          in
          let parent_structural_prop =
            simple_quantify_prop parent_sorts parent_body_prop
          in
          let target_structural_prop =
            simple_quantify_prop sorts target_body_prop
          in
          begin match
            if emitted_parent_prop parent_id <> parent_structural_prop
               || prop <> target_structural_prop then
              None
            else
              try Some (simple_equality_symmetry_clause_proof
                          type_env id parent_id literal_index result target_body_prop
                          parent_sorts sorts !checked !emitted_names)
              with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "equality_symmetry" id [parent_id] result
          end
      | EqualityResolution (id, parent_id, literal_index, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let structurally_safe =
            simple_sorts_subset parent_sorts sorts
            && emitted_parent_prop parent_id = structural_clause_prop parent_sorts parent_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            if structurally_safe then
              try Some (simple_equality_resolution_clause_proof
                          clause_body_prop id parent_id literal_index result
                          parent_sorts sorts !checked !emitted_names)
              with Error _ ->
                try Some (simple_equality_resolution_proof
                            id parent_id literal_index result parent_sorts sorts
                            !checked !emitted_names)
                with Error _ -> None
            else
              try Some (simple_equality_resolution_proof
                          id parent_id literal_index result parent_sorts sorts
                          !checked !emitted_names)
              with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "equality_resolution" id [parent_id] result
          end
      | UnitResultingResolution (id, parent_id, _, result) ->
          add_clause_inference_bridge "unit_resulting_resolution" id [parent_id] result
      | SubsumptionResolution (id, left_id, right_id, _, _, subst, result) ->
          add_clause_inference_bridge
            ~extra_sorts:(substitution_variable_sorts left_id subst)
            "subsumption_resolution" id [left_id; right_id] result
      | EqualityResolutionConstraints (id, parent_id, _, _, _, result) ->
          add_clause_inference_bridge "equality_resolution_constraints" id [parent_id] result
      | EqualityFactoring (id, parent_id, _, _, subst, result) ->
          add_clause_inference_bridge
            ~extra_sorts:(substitution_variable_sorts parent_id subst)
            "equality_factoring" id [parent_id] result
      | EqualityFactoringConstraints (id, parent_id, _, _, subst, _, result) ->
          add_clause_inference_bridge
            ~extra_sorts:(substitution_variable_sorts parent_id subst)
            "equality_factoring_constraints" id [parent_id] result
      | TruthConflict (id, parent_id, literal_index, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [parent_id] result in
          let parent_sorts = variable_sorts_for_ids [parent_id] in
          let parent_clause = lookup_simple_clause !checked parent_id in
          let type_env =
            simple_type_env_with_variables
              (parent_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let structurally_safe =
            simple_sorts_subset parent_sorts sorts
            && emitted_parent_prop parent_id = structural_clause_prop parent_sorts parent_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            if not structurally_safe then None
            else
              try Some (simple_truth_conflict_clause_proof
                          clause_body_prop id parent_id literal_index result
                          parent_sorts sorts !checked !emitted_names)
              with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "truth_conflict" id [parent_id] result
          end
      | BoolSimplify (id, parent_id, _, _, _, _, result) ->
          add_clause_inference_bridge "bool_simplify" id [parent_id] result
      | Paramodulate (id, equality_parent_id, target_parent_id, equality_index, target_index, position, from_tm, to_tm, result) ->
          let prop, sorts = clause_prop_and_sorts_for_ids id [equality_parent_id; target_parent_id] result in
          let equality_sorts = variable_sorts_for_ids [equality_parent_id] in
          let target_sorts = variable_sorts_for_ids [target_parent_id] in
          let equality_clause = lookup_simple_clause !checked equality_parent_id in
          let target_clause = lookup_simple_clause !checked target_parent_id in
          let type_env =
            simple_type_env_with_variables
              (equality_sorts @ target_sorts @ sorts |> simple_unique_variable_sorts)
              symbol_type_env
          in
          let clause_body_prop clause =
            try simple_clause_prop_with_type_env type_env clause
            with Error _ -> simple_clause_prop clause
          in
          let structural_clause_prop sorts clause =
            simple_quantify_prop sorts (clause_body_prop clause)
          in
          let structurally_safe =
            simple_sorts_subset equality_sorts sorts
            && simple_sorts_subset target_sorts sorts
            && emitted_parent_prop equality_parent_id = structural_clause_prop equality_sorts equality_clause
            && emitted_parent_prop target_parent_id = structural_clause_prop target_sorts target_clause
            && prop = structural_clause_prop sorts result
          in
          begin match
            if not structurally_safe then None
            else
              try Some (simple_paramodulate_unit_proof
                          clause_body_prop type_env id equality_parent_id target_parent_id equality_index target_index position
                          from_tm to_tm result equality_sorts target_sorts sorts !checked !emitted_names)
              with Error _ -> None
          with
          | Some proof ->
              let name = derived_name id in
              add_emitted id name;
              add_emitted_prop_and_sorts id prop sorts;
              claims := !claims @ [(name, prop, "exact " ^ proof ^ ".")];
              add_checked id result
          | None ->
              add_clause_inference_bridge "paramodulate" id [equality_parent_id; target_parent_id] result
          end
      | Superposition (id, target_parent_id, equality_parent_id, _, _, target_subst, equality_subst, _, _, _, result) ->
          add_clause_inference_bridge
            ~extra_sorts:
              (substitution_variable_sorts target_parent_id target_subst
               @ substitution_variable_sorts equality_parent_id equality_subst)
            "superposition" id [target_parent_id; equality_parent_id] result
      | DefinitionRewriteChain (id, parent_id, _, result) ->
          add_clause_inference_bridge "definition_rewrite" id [parent_id] result
      | InequalityNameIntro (id, result) ->
          add_clause_inference_bridge "inequality_name_intro" id [] result
      | InequalitySplit (id, parent_id, _, result) ->
          add_clause_inference_bridge "inequality_split" id [parent_id] result
      | Contradiction (id, parent_id) ->
          let name = derived_name id in
          let parent_clause = lookup_simple_clause !checked parent_id in
          if parent_clause <> [] then
            emit_error (id ^ ": contradiction parent is not empty");
          let parent_name = lookup_simple_name !emitted_names parent_id in
          add_emitted id name;
          add_emitted_prop_and_sorts id "False" [];
          claims := !claims @ [(name, "False", "exact " ^ parent_name ^ ".")];
          add_checked id []
      )
    cert.steps;
  let final =
    match !final_empty with
    | Some id -> id
    | None -> emit_error "certificate has no empty clause"
  in
  let proof_assumptions =
    if !uses_vampire_eq_prop_ext then
      [("vampire_eq_prop_ext",
        "forall p q:prop, (p -> q) -> (q -> p) -> vampire_eq_prop p q")]
    else []
  in
  let theorem_assumptions = proof_assumptions @ !assumptions @ !bridge_assumptions in
  let theorem_type =
    String.concat " -> "
      (List.map (fun (_, prop) -> "(" ^ prop ^ ")") theorem_assumptions @ ["False"])
  in
  lines := !lines @ [Printf.sprintf "Theorem %s : %s." (megalodon_ident theorem_name) theorem_type];
  List.iter
    (fun (name, prop) ->
       lines := !lines @ [Printf.sprintf "assume %s: %s." (megalodon_ident name) prop])
    theorem_assumptions;
  List.iter
    (fun (name, prop, proof) ->
       lines := !lines @
         [
           Printf.sprintf "claim %s: %s." (megalodon_ident name) prop;
           Printf.sprintf "{ %s }" proof;
         ])
    !claims;
  let final_name = lookup_simple_name !emitted_names final in
  lines := !lines @ [Printf.sprintf "exact %s." (megalodon_ident final_name); "Qed."];
  String.concat "\n" !lines ^ "\n"

let source_map_prefix = "% megalodon_source_map "

let source_map_entry_of_sexpr = function
  | List [Atom kind; tptp_name; source_name; source_hash] ->
      {
        source_map_kind = kind;
        source_map_tptp_name = atom tptp_name;
        source_map_source_name = atom source_name;
        source_map_hash = atom source_hash;
        source_map_decl_hash = None;
      }
  | _ -> error "malformed Megalodon source-map comment"

let lines_of_text text =
  let len = String.length text in
  let rec next_line start i acc =
    if i = len then
      if start = len then List.rev acc
      else List.rev (String.sub text start (len - start) :: acc)
    else if text.[i] = '\n' then
      next_line (i + 1) (i + 1) (String.sub text start (i - start) :: acc)
    else
      next_line start (i + 1) acc
  in
  next_line 0 0 []

let parse_source_map text =
  let prefix_len = String.length source_map_prefix in
  let lines = lines_of_text text in
  let trim_ascii value =
    let len = String.length value in
    let rec left i =
      if i < len && is_space value.[i] then left (i + 1) else i
    in
    let rec right i =
      if i >= 0 && is_space value.[i] then right (i - 1) else i
    in
    let l = left 0 in
    let r = right (len - 1) in
    if r < l then "" else String.sub value l (r - l + 1)
  in
  let is_hex = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false
  in
  let looks_like_hash value =
    String.length value = 64
    &&
    let rec loop i =
      i = 64 || (is_hex value.[i] && loop (i + 1))
    in
    loop 0
  in
  let thf_decl_hash_of_line line =
    if string_starts_with "thf(" line then
      try
        let comma = String.index_from line 4 ',' in
        let name = String.sub line 4 (comma - 4) in
        let percent = String.rindex line '%' in
        let hash =
          String.sub line (percent + 1) (String.length line - percent - 1)
          |> trim_ascii
        in
        if looks_like_hash hash then Some (name, hash) else None
      with Not_found | Invalid_argument _ -> None
    else None
  in
  let decl_hashes = Hashtbl.create 101 in
  List.iter
    (fun line ->
      match thf_decl_hash_of_line line with
      | Some (name, hash) -> Hashtbl.replace decl_hashes name hash
      | None -> ())
    lines;
  let decl_hash name =
    try Some (Hashtbl.find decl_hashes name) with Not_found -> None
  in
  List.fold_left
    (fun entries line ->
      if string_starts_with source_map_prefix line then
        let body = String.sub line prefix_len (String.length line - prefix_len) in
        let entry = source_map_entry_of_sexpr (parse_sexpr body) in
        { entry with source_map_decl_hash = decl_hash entry.source_map_tptp_name } :: entries
      else
        entries)
    []
    lines
  |> List.rev

let source_name = function
  | SourceAxiom name
  | SourceConjecture name
  | SourceNegatedConjecture name
  | SourceDefinition name
  | SourceSetReflexivity name -> name

let source_kind_name = function
  | SourceAxiom _ -> "axiom"
  | SourceConjecture _ -> "conjecture"
  | SourceNegatedConjecture _ -> "negated_conjecture"
  | SourceDefinition _ -> "definition"
  | SourceSetReflexivity _ -> "set_reflexivity"

let source_of_step = function
  | Input (id, source, _)
  | FormulaInput (id, source, _)
  | FormulaTermInput (id, source, _) -> Some (id, source)
  | _ -> None

let certificate_source_count cert =
  List.fold_left
    (fun count step ->
      match source_of_step step with
      | Some _ -> count + 1
      | None -> count)
    0
    cert.steps

let source_map_kind_compatible source entry =
  match source, entry.source_map_kind with
  | SourceAxiom _, ("known" | "axiom" | "local_fact" | "set_reflexivity" | "local_set_reflexivity") -> true
  | SourceConjecture _, "conjecture" -> true
  | SourceDefinition _, ("def" | "definition" | "local_definition") -> true
  | SourceNegatedConjecture _, ("conjecture" | "negated_conjecture") -> true
  | SourceSetReflexivity _, ("set_reflexivity" | "local_set_reflexivity") -> true
  | SourceAxiom _, _ -> false
  | SourceConjecture _, _ -> false
  | SourceDefinition _, _ -> false
  | SourceNegatedConjecture _, _ -> false
  | SourceSetReflexivity _, _ -> false

let source_map_entry_well_formed entry =
  let is_hex = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false
  in
  let looks_like_hash value =
    String.length value = 64
    &&
    let rec loop i =
      i = 64 || (is_hex value.[i] && loop (i + 1))
    in
    loop 0
  in
  if entry.source_map_tptp_name = "" then
    error "Megalodon source-map entry has an empty TPTP name";
  if entry.source_map_source_name = "" then
    error ("Megalodon source-map entry for " ^ entry.source_map_tptp_name ^ " has an empty source name");
  match entry.source_map_kind with
  | "known" | "def" ->
      if entry.source_map_hash = "" then
        error
          ("Megalodon source-map entry for "
           ^ entry.source_map_tptp_name
           ^ " is a global "
           ^ entry.source_map_kind
           ^ " but has an empty source hash");
      if not (looks_like_hash entry.source_map_hash) then
        error
          ("Megalodon source-map entry for "
           ^ entry.source_map_tptp_name
           ^ " is a global "
           ^ entry.source_map_kind
           ^ " but has a malformed source hash");
      begin match entry.source_map_decl_hash with
      | Some declared when declared = entry.source_map_hash -> ()
      | Some declared ->
          error
            ("Megalodon source-map entry for "
             ^ entry.source_map_tptp_name
             ^ " has source hash "
             ^ entry.source_map_hash
             ^ " but the THF declaration is tagged "
             ^ declared)
      | None ->
          error
            ("Megalodon source-map entry for "
             ^ entry.source_map_tptp_name
             ^ " has source hash "
             ^ entry.source_map_hash
             ^ " but the THF declaration has no matching trailing hash")
      end
  | _ -> ()

let source_map_entry_requires_reflexive_equality entry =
  match entry.source_map_kind with
  | "set_reflexivity" | "local_set_reflexivity" -> true
  | _ -> false

let source_map_entry_requires_equality entry =
  match entry.source_map_kind with
  | "def" | "definition" | "local_definition"
  | "set_reflexivity" | "local_set_reflexivity" -> true
  | _ -> false

let is_reflexive_equality_atom atom =
  match equality_sides atom with
  | Some (left, right) -> left = right
  | None -> false

let is_equality_atom atom =
  match equality_sides atom with
  | Some _ -> true
  | None -> false

let is_equality_literal = function
  | Pos atom -> is_equality_atom atom
  | Neg _ -> false

let is_reflexive_equality_literal = function
  | Pos atom -> is_reflexive_equality_atom atom
  | Neg _ -> false

let step_is_equality_source = function
  | Input (_, _, [literal]) -> is_equality_literal literal
  | FormulaInput (_, _, literal) -> is_equality_literal literal
  | FormulaTermInput (_, _, formula) -> is_equality_atom formula
  | _ -> false

let step_is_reflexive_equality_source = function
  | Input (_, _, [literal]) -> is_reflexive_equality_literal literal
  | FormulaInput (_, _, literal) -> is_reflexive_equality_literal literal
  | FormulaTermInput (_, _, formula) -> is_reflexive_equality_atom formula
  | _ -> false

let validate_certificate_sources source_map cert =
  let table = Hashtbl.create 101 in
  List.iter
    (fun entry ->
      source_map_entry_well_formed entry;
      if Hashtbl.mem table entry.source_map_tptp_name then
        error ("duplicate Megalodon source-map entry for " ^ entry.source_map_tptp_name);
      Hashtbl.add table entry.source_map_tptp_name entry)
    source_map;
  let checked = ref 0 in
  List.iter
    (fun step ->
      match source_of_step step with
      | None -> ()
      | Some (id, source) ->
          let name = source_name source in
          let entry =
            try Hashtbl.find table name
            with Not_found ->
              error
                (id ^ ": certificate " ^ source_kind_name source
                 ^ " source " ^ name ^ " is not present in the Megalodon source map")
          in
          if not (source_map_kind_compatible source entry) then
            error
              (id ^ ": certificate " ^ source_kind_name source
               ^ " source " ^ name ^ " maps to incompatible source-map kind "
               ^ entry.source_map_kind);
          if source_map_entry_requires_equality entry
             && not (step_is_equality_source step) then
            error
              (id ^ ": certificate source " ^ name
               ^ " maps to " ^ entry.source_map_kind
               ^ " but is not an equality input");
          if source_map_entry_requires_reflexive_equality entry
             && not (step_is_reflexive_equality_source step) then
            error
              (id ^ ": certificate source " ^ name
               ^ " maps to " ^ entry.source_map_kind
               ^ " but is not a reflexive equality input");
          incr checked)
    cert.steps;
  !checked
