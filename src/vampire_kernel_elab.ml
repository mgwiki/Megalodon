(*** Deterministic proof-term boundary for the Vampire/Megalodon small kernel. ***)

open Syntax
open Vampire_kernel_syntax

type clause_formula_basis = {
  false_tm : tm;
  or_tm : tm -> tm -> tm;
  atom_tm : tm -> tm;
}

let identity_atom tm = tm

let literal_prop basis = function
  | Pos atom -> basis.atom_tm atom
  | Neg atom -> Imp (basis.atom_tm atom, basis.false_tm)

let rec clause_prop basis = function
  | [] -> basis.false_tm
  | [literal] -> literal_prop basis literal
  | literal :: rest -> basis.or_tm (literal_prop basis literal) (clause_prop basis rest)

type proof_step = {
  step_id : string;
  step_clause : clause;
  step_prop : tm;
  step_proof : pf;
}

let input_step basis ~id ~clause proof =
  {
    step_id = id;
    step_clause = clause;
    step_prop = clause_prop basis clause;
    step_proof = proof;
  }
