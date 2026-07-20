#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/kernel_elab_unit.XXXXXX")"}
ln -sfn "$WORK_DIR" "$TMPDIR/latest_kernel_elab_unit"

if [[ ! -x "$ROOT/bin/megalodon" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

cat >"$WORK_DIR/test_kernel_elab.ml" <<'EOF_OCAML'
open Syntax

let expect_equal label expected actual =
  if expected <> actual then begin
    prerr_endline ("kernel_elab unit failure: " ^ label);
    exit 1
  end

let expect_bool label actual =
  if not actual then begin
    prerr_endline ("kernel_elab unit failure: " ^ label);
    exit 1
  end

let () =
  let inner_choice = Ap (TmH "eps", TmH "inner") in
  let outer_after_inner = Ap (TmH "eps", TmH "s0") in
  let outer_before_inner = Ap (TmH "eps", inner_choice) in
  let proof = PTmAp (Known "k", outer_before_inner) in
  let rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_after_inner, TmH "s1"]
      proof
  in
  expect_equal
    "nested term replacement should revisit parent after rewriting children"
    (PTmAp (Known "k", TmH "s1"))
    rewritten;
  let outer_first_rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_before_inner, TmH "s1"]
      proof
  in
  expect_equal
    "outer exact replacement should fire before child rewrites change the match"
    (PTmAp (Known "k", TmH "s1"))
    outer_first_rewritten;
  let lambda_proof = PLam (outer_before_inner, Hyp 0) in
  let lambda_rewritten =
    Vampire_kernel_elab.replace_exact_terms_in_proof
      ~normalize:(fun tm -> tm)
      [inner_choice, TmH "s0"; outer_after_inner, TmH "s1"]
      lambda_proof
  in
  expect_equal
    "nested replacement should also rewrite proof propositions"
    (PLam (TmH "s1", Hyp 0))
    lambda_rewritten;
  let choice_symbols = ["eps"] in
  expect_bool
    "proof_contains_term_symbol should find witness symbols"
    (Vampire_kernel_elab.proof_contains_term_symbol choice_symbols proof);
  expect_bool
    "proof_contains_exact_term should find normalized exact witness terms"
    (Vampire_kernel_elab.proof_contains_exact_term
       ~normalize:(fun tm -> tm)
       outer_before_inner
       proof);
  expect_equal
    "first_enclosing_term_with_symbol should report the enclosing application"
    (Some ("root.term.left", outer_before_inner))
    (Vampire_kernel_elab.first_enclosing_term_with_symbol choice_symbols proof);
  expect_equal
    "enclosing_terms_with_symbol should collect normalized unique enclosing terms"
    [inner_choice; outer_before_inner]
    (Vampire_kernel_elab.enclosing_terms_with_symbol
       ~normalize:(fun tm -> tm)
       choice_symbols
       proof);
  let binder_witness = Ap (TmH "eps", DB 0) in
  let binder_proof = TLam (Prop, PTmAp (Known "k", binder_witness)) in
  expect_equal
    "enclosing_terms_with_symbol_depth should track term binders"
    [1, binder_witness]
    (Vampire_kernel_elab.enclosing_terms_with_symbol_depth
       ~normalize:(fun tm -> tm)
       choice_symbols
       binder_proof);
  expect_equal
    "registered_witness_term_replacements should map exact witnesses to introduced symbols"
    [outer_before_inner, TmH "#s0"]
    (Vampire_kernel_elab.registered_witness_term_replacements
       ~normalize:(fun tm -> tm)
       ~witness_symbols:choice_symbols
       ["#s0", outer_before_inner]
       proof);
  expect_equal
    "registered_witness_term_replacements should also use emitted witness-symbol contracts"
    [Ap (TmH "eps", TmH "other"), TmH "#s1"]
    (Vampire_kernel_elab.registered_witness_term_replacements
       ~normalize:(fun tm -> tm)
       ~witness_symbols:choice_symbols
       ["#s1", Ap (TmH "eps", TmH "other")]
       proof);
  expect_equal
    "substitute_named_term should preserve vLAM binder convention"
    (Ap (TmH "vLAM", Ap (DB 0, TmH "z")))
    (Vampire_kernel_elab.substitute_named_term
       "X"
       (Ap (TmH "vLAM", Ap (TmH "X", TmH "z"))));
  expect_equal
    "term_head should peel type and term applications"
    (TmH "sK")
    (Vampire_kernel_elab.term_head
       (Ap (TpAp (TmH "sK", Prop), TmH "arg")));
  let aliases = function
    | "#s0" -> ["#s0"; "s0"]
    | "s0" -> ["#s0"; "s0"]
    | name -> [name]
  in
  let alias_rewritten =
    Vampire_kernel_elab.rewrite_head_symbols_by_alias
      ~alias_names:aliases
      [TmH "#s0", TmH "eps0"]
      (Lam (Prop, Ap (TmH "s0", DB 0)))
  in
  expect_equal
    "rewrite_head_symbols_by_alias should shift replacements under binders"
    (Lam (Prop, Ap (TmH "eps0", DB 0)))
    alias_rewritten;
  let branch_choice =
    {
      Vampire_kernel_syntax.skolem_branch_choice_index = 0;
      skolem_branch_choice_symbol = "s0";
      skolem_branch_choice_replaced_variable = "X";
      skolem_branch_choice_type = Prop;
      skolem_branch_choice_predicate = TmH "pred";
      skolem_branch_choice_body = Ap (TmH "X", TmH "a");
      skolem_branch_choice_witness_term = Some (TmH "#s0");
    }
  in
  expect_bool
    "skolem_branch_choice_matches_witness should use exact witness terms"
    (Vampire_kernel_elab.skolem_branch_choice_matches_witness
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       (TmH "#s0")
       branch_choice);
  expect_bool
    "skolem_branch_choice_matches_witness should use symbol aliases"
    (Vampire_kernel_elab.skolem_branch_choice_matches_witness
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       (Ap (TmH "#s0", TmH "arg"))
       { branch_choice with
         Vampire_kernel_syntax.skolem_branch_choice_witness_term = None });
  expect_equal
    "skolem_branch_choice_body should select, rewrite aliases, and bind the replaced variable"
    (Some (Ap (DB 0, TmH "a")))
    (Vampire_kernel_elab.skolem_branch_choice_body
       ~normalize:(fun tm -> tm)
       ~alias_names:aliases
       ~replacements:[]
       ~substitution_name:(Some "X")
       ~target_witness:(TmH "#s0")
       ~witness_type:Prop
       [branch_choice])
EOF_OCAML

ocamlopt \
  -I +unix \
  unix.cmxa \
  -I "$ROOT/bin" \
  -o "$WORK_DIR/test_kernel_elab" \
  "$ROOT/bin/hashbtcstub.o" \
  "$ROOT/bin/hashbtc.cmx" \
  "$ROOT/bin/ser.cmx" \
  "$ROOT/bin/hashaux.cmx" \
  "$ROOT/bin/hash.cmx" \
  "$ROOT/bin/hashold.cmx" \
  "$ROOT/bin/mathdata.cmx" \
  "$ROOT/bin/mathdatapfg.cmx" \
  "$ROOT/bin/syntax.cmx" \
  "$ROOT/bin/vampire_kernel_syntax.cmx" \
  "$ROOT/bin/vampire_kernel_elab.cmx" \
  "$WORK_DIR/test_kernel_elab.ml"

"$WORK_DIR/test_kernel_elab"

echo "kernel_elab unit checks passed"
echo "kernel_elab unit artifacts: $WORK_DIR"
