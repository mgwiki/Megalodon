(*** Shared vocabulary for the Vampire/Megalodon small-kernel certificate. ***)

type literal =
  | Pos of Syntax.tm
  | Neg of Syntax.tm

type clause = literal list

type skolem_formula_child = {
  skolem_child_role : string;
  skolem_child_formula : Syntax.tm;
}

type skolem_introduced_witness = {
  skolem_witness_symbol : string;
  skolem_witness_replaced_var : string;
  skolem_witness_term : Syntax.tm option;
}

type skolem_contract = {
  skolem_source_children : skolem_formula_child list;
  skolem_result_children : skolem_formula_child list;
  skolem_introduced_witnesses : skolem_introduced_witness list;
}

val schema : string

val supported_rules : string list

val is_supported_rule : string -> bool

val required_primitives_for_rule : string -> string list

val is_skolem_transform_primitive : string -> bool
