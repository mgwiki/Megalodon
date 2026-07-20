(*** Deterministic checks for the Vampire/Megalodon small clause kernel. ***)

exception Error of string

val literal_atom : Vampire_kernel_syntax.literal -> Syntax.tm

val complementary :
  Vampire_kernel_syntax.literal ->
  Vampire_kernel_syntax.literal ->
  bool

val remove_at : int -> 'a list -> string -> 'a list

val replace_at : int -> 'a -> 'a list -> string -> 'a list

val nth : int -> 'a list -> string -> 'a

val same_clause_multiset :
  Vampire_kernel_syntax.clause ->
  Vampire_kernel_syntax.clause ->
  bool

val subst_tm :
  (string * Syntax.tm) list ->
  Syntax.tm ->
  Syntax.tm

val subst_literal :
  (string * Syntax.tm) list ->
  Vampire_kernel_syntax.literal ->
  Vampire_kernel_syntax.literal

val subst_clause :
  (string * Syntax.tm) list ->
  Vampire_kernel_syntax.clause ->
  Vampire_kernel_syntax.clause

val unique_clause :
  Vampire_kernel_syntax.clause ->
  Vampire_kernel_syntax.clause

val tm_at_position :
  Syntax.tm ->
  int list ->
  string ->
  Syntax.tm

val replace_tm_at_position :
  Syntax.tm ->
  int list ->
  Syntax.tm ->
  string ->
  Syntax.tm

val try_tm_at_position :
  Syntax.tm ->
  int list ->
  Syntax.tm option

val replace_literal_atom :
  Vampire_kernel_syntax.literal ->
  Syntax.tm ->
  Vampire_kernel_syntax.literal

val application_spine :
  Syntax.tm ->
  Syntax.tm * Syntax.tm list

type definition_rewrite = {
  definition_parent : string;
  definition_literal : int;
  target_literal : int;
  rewrite_position : int list;
  rewrite_from : Syntax.tm;
  rewrite_to : Syntax.tm;
}

val check_substitute :
  id:string ->
  parent:Vampire_kernel_syntax.clause ->
  subst:(string * Syntax.tm) list ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_condensation :
  id:string ->
  parent:Vampire_kernel_syntax.clause ->
  subst:(string * Syntax.tm) list ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_factor :
  id:string ->
  parent:Vampire_kernel_syntax.clause ->
  left_index:int ->
  right_index:int ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_resolution :
  id:string ->
  left:Vampire_kernel_syntax.clause ->
  right:Vampire_kernel_syntax.clause ->
  left_index:int ->
  right_index:int ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_equality_resolution :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  parent:Vampire_kernel_syntax.clause ->
  literal_index:int ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_truth_conflict :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  true_tm:Syntax.tm ->
  false_tm:Syntax.tm ->
  parent:Vampire_kernel_syntax.clause ->
  literal_index:int ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_equality_symmetry :
  id:string ->
  swap_equality_literal:
    (Vampire_kernel_syntax.literal -> Vampire_kernel_syntax.literal option) ->
  parent:Vampire_kernel_syntax.clause ->
  literal_index:int ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_paramodulate :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  swap_equality_literal:
    (Vampire_kernel_syntax.literal -> Vampire_kernel_syntax.literal option) ->
  clause_matches:
    (Vampire_kernel_syntax.clause -> Vampire_kernel_syntax.clause -> bool) ->
  equality_clause:Vampire_kernel_syntax.clause ->
  target_clause:Vampire_kernel_syntax.clause ->
  equality_index:int ->
  target_index:int ->
  position_candidates:int list list ->
  from_tm:Syntax.tm ->
  to_tm:Syntax.tm ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_equality_factoring :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  diseq_literal_like:
    (Syntax.tm -> Syntax.tm -> Syntax.tm -> Vampire_kernel_syntax.literal) ->
  clause_matches:
    (Vampire_kernel_syntax.clause -> Vampire_kernel_syntax.clause -> bool) ->
  parent:Vampire_kernel_syntax.clause ->
  selected_index:int ->
  other_index:int ->
  explicit_sides:(Syntax.tm * Syntax.tm) option ->
  subst:(string * Syntax.tm) list ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_equality_factoring_constraints :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  diseq_literal_like:
    (Syntax.tm -> Syntax.tm -> Syntax.tm -> Vampire_kernel_syntax.literal) ->
  clause_matches:
    (Vampire_kernel_syntax.clause -> Vampire_kernel_syntax.clause -> bool) ->
  parent:Vampire_kernel_syntax.clause ->
  selected_index:int ->
  other_index:int ->
  explicit_sides:(Syntax.tm * Syntax.tm) option ->
  subst:(string * Syntax.tm) list ->
  constraints:Vampire_kernel_syntax.clause ->
  result:Vampire_kernel_syntax.clause ->
  unit

val check_definition_rewrite_chain :
  id:string ->
  equality_sides:(Syntax.tm -> (Syntax.tm * Syntax.tm) option) ->
  source:Vampire_kernel_syntax.clause ->
  definition_parent:(string -> Vampire_kernel_syntax.clause) ->
  rewrites:definition_rewrite list ->
  result:Vampire_kernel_syntax.clause ->
  unit
