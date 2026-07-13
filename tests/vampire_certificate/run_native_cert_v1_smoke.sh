#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

dummy="$TMPDIR/native_cert_v1_dummy.mg"
: >"$dummy"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_valid.log"; then
  echo "native certificate v1 checker did not accept the valid fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factor_equality_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_factor_equality_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_factor_equality_valid.log"; then
  echo "native certificate v1 checker did not accept the valid factor/equality-resolution fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_copy_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_formula_copy_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$TMPDIR/native_cert_v1_formula_copy_valid.log"; then
  echo "native certificate v1 checker did not accept the valid formula-copy fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_truth_conflict_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_truth_conflict_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$TMPDIR/native_cert_v1_truth_conflict_valid.log"; then
  echo "native certificate v1 checker did not accept the valid truth-conflict fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_subst_paramod_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_subst_paramod_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$TMPDIR/native_cert_v1_subst_paramod_valid.log"; then
  echo "native certificate v1 checker did not accept the valid substitution/paramodulation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_paramod_equality_shape_position_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_paramod_equality_shape_position_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_paramod_equality_shape_position_valid.log"; then
  echo "native certificate v1 checker did not accept the equality-shaped paramodulation position fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_literal_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_cnf_literal_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_cnf_literal_valid.log"; then
  echo "native certificate v1 checker did not accept the valid literal-CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_bool_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_fool_bool_valid.log"

if ! rg -q 'Vampire certificate v1 checked 9 steps' "$TMPDIR/native_cert_v1_fool_bool_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL Boolean fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_definition_input_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_definition_input_valid.log"

if ! rg -q 'Vampire certificate v1 checked 4 steps' "$TMPDIR/native_cert_v1_definition_input_valid.log"; then
  echo "native certificate v1 checker did not accept the valid definition-input fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_component_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_avatar_component_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_avatar_component_valid.log"; then
  echo "native certificate v1 checker did not accept the valid AVATAR component fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_refutation_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_avatar_refutation_valid.log"

if ! rg -q 'Vampire certificate v1 checked 2 steps' "$TMPDIR/native_cert_v1_avatar_refutation_valid.log"; then
  echo "native certificate v1 checker did not accept the valid AVATAR refutation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_symmetry_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_equality_symmetry_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$TMPDIR/native_cert_v1_equality_symmetry_valid.log"; then
  echo "native certificate v1 checker did not accept the valid equality-symmetry fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_fool_exhaustiveness_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_fool_exhaustiveness_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL exhaustiveness fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_formula_cnf_valid.log"

if ! rg -q 'Vampire certificate v1 checked 9 steps' "$TMPDIR/native_cert_v1_formula_cnf_valid.log"; then
  echo "native certificate v1 checker did not accept the valid formula CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_vampire_order_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_formula_cnf_vampire_order_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$TMPDIR/native_cert_v1_formula_cnf_vampire_order_valid.log"; then
  echo "native certificate v1 checker did not accept the valid Vampire-order formula CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_formula_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_rectify_formula_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$TMPDIR/native_cert_v1_rectify_formula_valid.log"; then
  echo "native certificate v1 checker did not accept the valid rectify-formula fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_predicate_definition_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_predicate_definition_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$TMPDIR/native_cert_v1_predicate_definition_valid.log"; then
  echo "native certificate v1 checker did not accept the valid predicate-definition fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_predicate_definition_fold_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_predicate_definition_fold_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$TMPDIR/native_cert_v1_predicate_definition_fold_valid.log"; then
  echo "native certificate v1 checker did not accept the valid predicate-definition-fold fixture" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_pivot.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_pivot.out" \
  2>"$TMPDIR/native_cert_v1_invalid_pivot.err"; then
  echo "native certificate v1 checker accepted an invalid resolution pivot" >&2
  exit 1
fi

if ! rg -q 'resolution pivots are not complementary' "$TMPDIR/native_cert_v1_invalid_pivot.err"; then
  echo "native certificate v1 invalid-pivot failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_equality_resolution.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_equality_resolution.out" \
  2>"$TMPDIR/native_cert_v1_invalid_equality_resolution.err"; then
  echo "native certificate v1 checker accepted non-reflexive equality resolution" >&2
  exit 1
fi

if ! rg -q 'equality-resolution equality is not reflexive' "$TMPDIR/native_cert_v1_invalid_equality_resolution.err"; then
  echo "native certificate v1 invalid-equality failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_truth_conflict.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_truth_conflict.out" \
  2>"$TMPDIR/native_cert_v1_invalid_truth_conflict.err"; then
  echo "native certificate v1 checker accepted a non-conflicting truth equality" >&2
  exit 1
fi

if ! rg -q 'truth-conflict equality is not true = false' "$TMPDIR/native_cert_v1_invalid_truth_conflict.err"; then
  echo "native certificate v1 invalid-truth-conflict failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_paramod_position.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_paramod_position.out" \
  2>"$TMPDIR/native_cert_v1_invalid_paramod_position.err"; then
  echo "native certificate v1 checker accepted a paramodulation with a bad target position" >&2
  exit 1
fi

if ! rg -q 'paramodulation position does not contain from term' "$TMPDIR/native_cert_v1_invalid_paramod_position.err"; then
  echo "native certificate v1 invalid-paramodulation failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_rectify_formula.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_rectify_formula.out" \
  2>"$TMPDIR/native_cert_v1_invalid_rectify_formula.err"; then
  echo "native certificate v1 checker accepted an invalid formula rectification" >&2
  exit 1
fi

if ! rg -q 'rectify_formula result is not a bijective Vampire-variable renaming of parent' "$TMPDIR/native_cert_v1_invalid_rectify_formula.err"; then
  echo "native certificate v1 invalid-rectify failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_predicate_definition_recursive.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_predicate_definition_recursive.out" \
  2>"$TMPDIR/native_cert_v1_invalid_predicate_definition_recursive.err"; then
  echo "native certificate v1 checker accepted a recursive predicate definition" >&2
  exit 1
fi

if ! rg -q 'predicate_definition is not a non-recursive definitional disjunction' "$TMPDIR/native_cert_v1_invalid_predicate_definition_recursive.err"; then
  echo "native certificate v1 invalid-predicate-definition failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_predicate_definition_fold.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_predicate_definition_fold.out" \
  2>"$TMPDIR/native_cert_v1_invalid_predicate_definition_fold.err"; then
  echo "native certificate v1 checker accepted an invalid predicate definition fold" >&2
  exit 1
fi

if ! rg -q 'predicate_definition_fold result is not one definition-body replacement' "$TMPDIR/native_cert_v1_invalid_predicate_definition_fold.err"; then
  echo "native certificate v1 invalid-predicate-definition-fold failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_partial.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_invalid_partial.out" \
  2>"$TMPDIR/native_cert_v1_invalid_partial.err"; then
  echo "native certificate v1 checker accepted a partial non-refutation certificate" >&2
  exit 1
fi

if ! rg -q 'final certificate step is not the empty clause' "$TMPDIR/native_cert_v1_invalid_partial.err"; then
  echo "native certificate v1 invalid-partial failure did not explain the rejected final clause" >&2
  exit 1
fi

echo "native certificate v1 smoke test passed"
