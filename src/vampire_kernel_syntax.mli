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

type skolem_parent_instantiation = {
  skolem_parent_inst_index : int;
  skolem_parent_inst_variable : string;
  skolem_parent_inst_type : Syntax.tp;
  skolem_parent_inst_term : Syntax.tm;
  skolem_parent_inst_role : string;
}

type skolem_contract = {
  skolem_source_children : skolem_formula_child list;
  skolem_result_children : skolem_formula_child list;
  skolem_introduced_witnesses : skolem_introduced_witness list;
  skolem_macro_edge_count : int option;
  skolem_parent_step_variables : (string * Syntax.tp) list;
  skolem_parent_instantiations : skolem_parent_instantiation list;
}

type skolem_branch_contract = {
  skolem_branch_index : int;
  skolem_branch_parent_index : int option;
  skolem_branch_unit : string option;
  skolem_branch_binder_count : int option;
  skolem_branch_source_formula : Syntax.tm option;
  skolem_branch_target_formula : Syntax.tm option;
  skolem_branch_parent_step_variables : (string * Syntax.tp) list;
  skolem_branch_parent_instantiations : skolem_parent_instantiation list;
  skolem_branch_introduced_witnesses : skolem_introduced_witness list;
}

type skolem_proof_object = {
  skolem_proof_contract : skolem_contract;
  skolem_proof_branches : skolem_branch_contract list;
}

val schema : string

val supported_rules : string list

val is_supported_rule : string -> bool

val required_primitives_for_rule : string -> string list

val is_skolem_transform_primitive : string -> bool
