#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT"

TMPDIR=${TMPDIR:-/project/tmp}
mkdir -p "$TMPDIR"

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/vampire_skolem_metadata_smoke.XXXXXX")"}
ln -sfn "$WORK_DIR" "$TMPDIR/latest_vampire_skolem_metadata_smoke"

VAMPIRE_BIN=${VAMPIRE_BIN:-${VAMPIRE:-}}
if [[ -z "$VAMPIRE_BIN" ]]; then
  VAMPIRE_BIN="$(
    {
      find /project/tmp -path '*/vampire-build-*' -type f -name vampire -perm -111 2>/dev/null
      find /project/vampire-leancheck/vampire_rel_vampire -type f -name 'vampire*' -perm -111 2>/dev/null
      find /project/vampire-leancheck -maxdepth 1 -type f -name 'vampire*' -perm -111 2>/dev/null
    } | head -1
  )"
fi

if [[ -z "$VAMPIRE_BIN" || ! -x "$VAMPIRE_BIN" ]]; then
  echo "VAMPIRE_BIN must point to a Vampire binary with Megalodon certificate output" >&2
  exit 1
fi

problem=${PROBLEM:-"$ROOT/tests/vampire_certificate/closed_cases/hammer.1007.43.th0.p"}
native_sexpr="$WORK_DIR/native.sexp"

"$VAMPIRE_BIN" \
  --input_syntax tptp \
  --mode casc \
  --avatar off \
  -t 10 \
  --proof megalodon \
  --output_axiom_names on \
  "$problem" >"$WORK_DIR/vampire.out" 2>"$WORK_DIR/vampire.err" || true

awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
  "$WORK_DIR/vampire.out" >"$native_sexpr"

if [[ ! -s "$native_sexpr" ]]; then
  echo "Vampire did not emit a native S-expression certificate block" >&2
  tail -80 "$WORK_DIR/vampire.out" >&2 || true
  tail -80 "$WORK_DIR/vampire.err" >&2 || true
  exit 1
fi

require_field() {
  local pattern=$1
  local description=$2
  if ! rg -q "$pattern" "$native_sexpr"; then
    echo "Skolem metadata smoke missing $description" >&2
    exit 1
  fi
}

require_field 'rule=skolemize' 'skolemize kernel rule'
require_field 'introduced_0_witness_term=' 'witness term'
require_field 'introduced_0_replaced_var_sort_sexpr=' 'replaced-variable sort'
require_field 'introduced_0_witness_sort_sexpr=' 'witness sort'
require_field 'introduced_0_choice_principle=classical_choice' 'choice principle'
require_field 'introduced_0_dependency_count=0' 'nullary Skolem dependency count'
require_field 'introduced_0_dependency_count=3' 'dependent Skolem dependency count'
require_field 'introduced_0_dependency_0_var=X2' 'first dependent Skolem variable'
require_field 'introduced_0_dependency_1_var=X1' 'second dependent Skolem variable'
require_field 'introduced_0_dependency_2_var=X0' 'third dependent Skolem variable'

dummy="$WORK_DIR/dummy.mg"
: >"$dummy"

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 "$native_sexpr" \
  -vampirecertv1source "$problem" \
  "$dummy" >"$WORK_DIR/megalodon.out" 2>"$WORK_DIR/megalodon.err"

if ! rg -q 'Vampire certificate v1 strict checked ' "$WORK_DIR/megalodon.out"; then
  echo "Megalodon did not strictly accept the live Skolem metadata certificate" >&2
  cat "$WORK_DIR/megalodon.out" >&2
  cat "$WORK_DIR/megalodon.err" >&2
  exit 1
fi

echo "Vampire Skolem metadata smoke passed"
echo "Vampire Skolem metadata smoke artifacts: $WORK_DIR"
echo "Vampire Skolem metadata smoke latest link: $TMPDIR/latest_vampire_skolem_metadata_smoke"
