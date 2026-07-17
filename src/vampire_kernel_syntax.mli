(*** Shared vocabulary for the Vampire/Megalodon small-kernel certificate. ***)

val schema : string

val supported_rules : string list

val is_supported_rule : string -> bool

val required_primitives_for_rule : string -> string list
