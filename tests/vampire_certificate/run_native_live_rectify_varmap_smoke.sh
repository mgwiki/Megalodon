#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
DEFAULT_VAMPIRE=$(
  find /project/vampire-leancheck/vampire_rel_vampire \
    -maxdepth 1 \
    -type f \
    -executable \
    -name 'megalodon*_*' \
    -printf '%T@ %p\n' \
    2>/dev/null \
    | sort -n \
    | tail -n 1 \
    | cut -d' ' -f2-
)
VAMPIRE=${VAMPIRE:-"$DEFAULT_VAMPIRE"}
PROBLEM=${PROBLEM:-"$ROOT/tests/vampire_certificate/closed_cases/hammer.1007.43.th0.p"}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_live_rectify_varmap.XXXXXX")"}

if [[ -z "$VAMPIRE" || ! -x "$VAMPIRE" ]]; then
  echo "VAMPIRE must point to an executable Vampire binary" >&2
  exit 2
fi
if [[ ! -x "$MEGALODON" ]]; then
  echo "MEGALODON must point to an executable Megalodon binary" >&2
  exit 2
fi

rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_live_rectify_varmap"
: > "$WORK_DIR/dummy.mg"

"$VAMPIRE" \
  --input_syntax tptp \
  --mode casc \
  -t "$VAMPIRE_SECONDS" \
  --proof megalodon \
  --proof_extra lean \
  --skolemization syntactic \
  --shuffle_input off \
  --output_axiom_names on \
  "$PROBLEM" \
  > "$WORK_DIR/vampire.out" \
  2> "$WORK_DIR/vampire.err" || true

awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
  "$WORK_DIR/vampire.out" > "$WORK_DIR/native.sexp"

if [[ ! -s "$WORK_DIR/native.sexp" ]]; then
  echo "Vampire did not emit a native Megalodon certificate" >&2
  tail -40 "$WORK_DIR/vampire.out" >&2 || true
  tail -40 "$WORK_DIR/vampire.err" >&2 || true
  exit 1
fi

if ! rg -q 'rectify_variable_map=.*X3.*X4.*X4.*X3' \
    "$WORK_DIR/native.sexp"; then
  echo "live rectification certificate did not contain the expected Vampire variable map" >&2
  rg -n 'rectify_variable_map|step_extra "u98"|rectify_formula "u98"' "$WORK_DIR/native.sexp" >&2 || true
  exit 1
fi

if rg -q '\(ALL ' "$WORK_DIR/native.sexp"; then
  echo "live rectification certificate regressed to compact anonymous ALL binders" >&2
  exit 1
fi

"$MEGALODON" \
  -vampirecertv1preprocesspfcheck \
  -vampirecertv1 "$WORK_DIR/native.sexp" \
  -vampirecertv1source "$PROBLEM" \
  "$WORK_DIR/dummy.mg" \
  > "$WORK_DIR/check.out" \
  2> "$WORK_DIR/check.err"

if ! rg -q 'Vampire certificate v1 native preprocess proof term checked 68 steps' \
    "$WORK_DIR/check.out"; then
  echo "Megalodon did not replay the live rectification proof through the expected frontier" >&2
  cat "$WORK_DIR/check.out" >&2
  cat "$WORK_DIR/check.err" >&2
  exit 1
fi

if ! rg -q 'Everything looks good' "$WORK_DIR/check.out"; then
  echo "Megalodon live rectification proof check did not finish cleanly" >&2
  cat "$WORK_DIR/check.out" >&2
  cat "$WORK_DIR/check.err" >&2
  exit 1
fi

cat "$WORK_DIR/check.out"
