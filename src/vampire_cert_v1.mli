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
  | AvatarRefutation of string * sat_clause list * sat_proof_step list option * clause
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

type certificate = {
  problem : string option;
  steps : step list;
}

type source_map_entry = {
  source_map_kind : string;
  source_map_tptp_name : string;
  source_map_source_name : string;
  source_map_hash : string;
  source_map_decl_hash : string option;
}

val parse_sexpr : string -> sexpr
val parse_certificate : string -> certificate
val step_id : step -> string
val certificate_source_count : certificate -> int
val parse_source_map : string -> source_map_entry list
val validate_certificate_sources : source_map_entry list -> certificate -> int
val check_certificate : certificate -> (string * checked_item) list
val check_certificate_strict : certificate -> (string * checked_item) list
val emit_simple_megalodon :
  ?theorem_name:string -> ?source_map:source_map_entry list -> certificate -> string
