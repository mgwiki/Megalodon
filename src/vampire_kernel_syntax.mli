(*** Shared vocabulary for the Vampire/Megalodon small-kernel certificate. ***)

type literal =
  | Pos of Syntax.tm
  | Neg of Syntax.tm

type clause = literal list

val schema : string

val supported_rules : string list

val is_supported_rule : string -> bool

val required_primitives_for_rule : string -> string list
