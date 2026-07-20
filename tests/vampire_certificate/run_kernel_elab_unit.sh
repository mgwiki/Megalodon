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
    lambda_rewritten
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
