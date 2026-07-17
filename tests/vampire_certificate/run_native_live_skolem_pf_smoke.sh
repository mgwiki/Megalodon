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
PROBLEM=${PROBLEM:-"$ROOT/tests/vampire_certificate/closed_cases/hammer.10609.51.th0.p"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_live_skolem_pf_smoke.XXXXXX")"}

if [[ -z "$VAMPIRE" || ! -x "$VAMPIRE" ]]; then
  echo "VAMPIRE must point to an executable Vampire binary" >&2
  exit 2
fi
if [[ ! -x "$MEGALODON" ]]; then
  echo "MEGALODON must point to an executable Megalodon binary" >&2
  exit 2
fi
if [[ ! -s "$PROBLEM" ]]; then
  echo "PROBLEM must point to a THF problem" >&2
  exit 2
fi

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_live_skolem_pf_smoke"

"$VAMPIRE" \
  --input_syntax tptp \
  --mode casc \
  -t 10 \
  --proof megalodon \
  --output_axiom_names on \
  "$PROBLEM" > "$WORK_DIR/vampire.out" 2> "$WORK_DIR/vampire.err" || true

awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
  "$WORK_DIR/vampire.out" > "$WORK_DIR/native.sexp"

if [[ ! -s "$WORK_DIR/native.sexp" ]]; then
  echo "Vampire did not emit a native S-expression certificate block" >&2
  tail -80 "$WORK_DIR/vampire.out" >&2 || true
  tail -80 "$WORK_DIR/vampire.err" >&2 || true
  exit 1
fi

if ! rg -q 'skolem_formula' "$WORK_DIR/native.sexp"; then
  echo "live Skolem proof-term smoke did not exercise skolem_formula" >&2
  exit 1
fi
if ! rg -q 'VLAMV' "$WORK_DIR/native.sexp"; then
  echo "live Skolem proof-term smoke expected named VLAMV binders" >&2
  exit 1
fi

dummy="$WORK_DIR/dummy.mg"
: > "$dummy"

"$MEGALODON" \
  -vampirecertv1preprocesspfcheck \
  -vampirecertv1strict \
  -vampirecertv1 "$WORK_DIR/native.sexp" \
  -vampirecertv1source "$PROBLEM" \
  "$dummy" > "$WORK_DIR/megalodon.out" 2> "$WORK_DIR/megalodon.err"

if ! rg -q 'native preprocess proof term checked' "$WORK_DIR/megalodon.out"; then
  echo "Megalodon did not check the live Skolem native proof term" >&2
  cat "$WORK_DIR/megalodon.out" >&2
  cat "$WORK_DIR/megalodon.err" >&2
  exit 1
fi

echo "native live Skolem proof-term smoke passed"
echo "native live Skolem proof-term smoke artifacts: $WORK_DIR"
echo "native live Skolem proof-term smoke latest link: $TMPDIR/latest_native_live_skolem_pf_smoke"
