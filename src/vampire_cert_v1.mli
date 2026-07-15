(*** Native strict Vampire/Megalodon certificate v1 importer. ***)

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
  | Pos of Syntax.tm
  | Neg of Syntax.tm

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
  rewrite_from : Syntax.tm;
  rewrite_to : Syntax.tm;
}

type urr_trace = {
  urr_unit_parent : string;
  urr_selected : literal;
  urr_selected_substituted : literal;
  urr_unit_substituted : literal;
  urr_remaining : clause;
}

type rectify_renaming = {
  rectify_source : Syntax.tm;
  rectify_subst : (string * Syntax.tm) list;
  rectify_target : Syntax.tm;
}

type checked_item =
  | CheckedClause of clause
  | CheckedFormula of Syntax.tm
  | CheckedSatClauseRecord

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | FormulaTermInput of string * source * Syntax.tm
  | FormulaTermCopy of string * string * Syntax.tm
  | RectifyFormula of string * string * rectify_renaming list * Syntax.tm
  | FoolFormula of string * string * Syntax.tm
  | EnnfFormula of string * string * Syntax.tm
  | SkolemFormula of string * string * (string * Syntax.tm) list * Syntax.tm
  | SkolemFormulaComputed of string * string * (string * Syntax.tm) list
  | CnfFormulaClause of string * string * int * clause
  | FormulaCopy of string * string * literal
  | FoolBool of string * string * literal
  | CnfLiteral of string * string * clause
  | PredicateDefinition of string * string * Syntax.tm
  | PredicateDefinitionFold of string * string * string * Syntax.tm
  | PredicateDefinitionFoldChain of string * string * string list * Syntax.tm
  | DefinitionInput of string * clause
  | DefinitionRewriteChain of string * string * definition_rewrite list * clause
  | AvatarComponent of string * clause
  | AvatarSplit of string * string list * clause
  | AvatarContradiction of string * string list * clause
  | AvatarRefutation of string * string list * sat_clause list * sat_proof_step list option * clause
  | FoolExhaustiveness of string * clause
  | FoolDistinctness of string * clause
  | InequalityNameIntro of string * clause
  | InequalitySplit of string * string * inequality_split list * clause
  | Substitute of string * string * (string * Syntax.tm) list * clause
  | Condensation of string * string * (string * Syntax.tm) list * clause
  | UnitResultingResolution of string * string * urr_trace list * clause
  | Resolve of string * string * string * int * int * clause
  | SubsumptionResolution of string * string * string * literal * literal * (string * Syntax.tm) list * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | EqualityResolutionConstraints of string * string * int * literal * clause * clause
  | EqualityFactoring of string * string * int * int * (string * Syntax.tm) list * clause
  | EqualityFactoringConstraints of string * string * int * int * (string * Syntax.tm) list * clause * clause
  | TruthConflict of string * string * int * clause
  | EqualitySymmetry of string * string * int * clause
  | BoolSimplify of string * string * int * int list * Syntax.tm * Syntax.tm * clause
  | Paramodulate of string * string * string * int * int * int list * Syntax.tm * Syntax.tm * clause
  | Superposition of string * string * string * int * int * (string * Syntax.tm) list * (string * Syntax.tm) list * int list * Syntax.tm * Syntax.tm * clause
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

type core_native_proof = {
  core_native_proposition : Syntax.tm;
  core_native_proof : Syntax.pf;
  core_native_steps : int;
}

type source_map_entry = {
  source_map_kind : string;
  source_map_tptp_name : string;
  source_map_source_name : string;
  source_map_hash : string;
  source_map_decl_hash : string option;
  source_map_decl_formula : string option;
}

type source_origin = {
  source_origin_file : string;
  source_origin_line : int option;
  source_origin_char : int option;
  source_origin_kind : string;
}

val parse_sexpr : string -> sexpr
val parse_certificate : string -> certificate
val step_id : step -> string
val certificate_source_count : certificate -> int
val parse_source_map : string -> source_map_entry list
val parse_source_origin : string -> source_origin option
val validate_certificate_sources : ?require_formula_match:bool -> source_map_entry list -> certificate -> int
val check_certificate : certificate -> (string * checked_item) list
val check_certificate_strict : certificate -> (string * checked_item) list
val validate_certificate_core_fragment : certificate -> int
val elaborate_core_unit_refutation_native : certificate -> core_native_proof
val emit_simple_megalodon :
  ?theorem_name:string ->
  ?source_map:source_map_entry list ->
  ?source_origin:source_origin ->
  ?closed:bool ->
  certificate ->
  string
