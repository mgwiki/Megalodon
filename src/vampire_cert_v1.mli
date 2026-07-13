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
  | Resolve of string * string * string * int * int * clause
  | Contradiction of string * string

type certificate = {
  problem : string option;
  steps : step list;
}

val parse_sexpr : string -> sexpr
val parse_certificate : string -> certificate
val step_id : step -> string
