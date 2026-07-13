(*** Native strict Vampire/Megalodon certificate v1 importer. ***)

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
  | Pos of Syntax.tm
  | Neg of Syntax.tm

type clause = literal list

type checked_item =
  | CheckedClause of clause
  | CheckedFormula of Syntax.tm

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | FormulaTermInput of string * source * Syntax.tm
  | FormulaTermCopy of string * string * Syntax.tm
  | FoolFormula of string * string * Syntax.tm
  | EnnfFormula of string * string * Syntax.tm
  | SkolemFormula of string * string * (string * Syntax.tm) list * Syntax.tm
  | CnfFormulaClause of string * string * int * clause
  | FormulaCopy of string * string * literal
  | FoolBool of string * string * literal
  | CnfLiteral of string * string * clause
  | DefinitionInput of string * clause
  | FoolExhaustiveness of string * clause
  | Substitute of string * string * (string * Syntax.tm) list * clause
  | Resolve of string * string * string * int * int * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | EqualityFactoring of string * string * int * int * (string * Syntax.tm) list * clause
  | TruthConflict of string * string * int * clause
  | EqualitySymmetry of string * string * int * clause
  | Paramodulate of string * string * string * int * int * int list * Syntax.tm * Syntax.tm * clause
  | Contradiction of string * string

type certificate = {
  problem : string option;
  steps : step list;
}

val parse_sexpr : string -> sexpr
val parse_certificate : string -> certificate
val step_id : step -> string
val check_certificate : certificate -> (string * checked_item) list
