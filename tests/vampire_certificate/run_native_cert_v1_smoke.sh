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
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_subst_paramod_valid.sexp \
  "$dummy" >"$TMPDIR/native_cert_v1_subst_paramod_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$TMPDIR/native_cert_v1_subst_paramod_valid.log"; then
  echo "native certificate v1 checker did not accept the valid substitution/paramodulation fixture" >&2
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
