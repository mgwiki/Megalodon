(*** Deterministic checks for the Vampire/Megalodon small clause kernel. ***)

exception Error of string

val literal_atom : Vampire_kernel_syntax.literal -> Syntax.tm

val complementary :
  Vampire_kernel_syntax.literal ->
  Vampire_kernel_syntax.literal ->
  bool

val remove_at : int -> 'a list -> string -> 'a list

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
