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

type step =
  | Input of string * source * clause
  | FormulaInput of string * source * literal
  | CnfLiteral of string * string * clause
  | Substitute of string * string * (string * Syntax.tm) list * clause
  | Resolve of string * string * string * int * int * clause
  | Factor of string * string * int * int * clause
  | EqualityResolution of string * string * int * clause
  | Paramodulate of string * string * string * int * int * int list * Syntax.tm * Syntax.tm * clause
  | Contradiction of string * string

type certificate = {
  problem : string option;
  steps : step list;
}

val parse_sexpr : string -> sexpr
val parse_certificate : string -> certificate
val step_id : step -> string
val check_certificate : certificate -> (string * clause) list
