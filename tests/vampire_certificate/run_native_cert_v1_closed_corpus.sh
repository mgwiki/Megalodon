#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
JOBS=${JOBS:-7}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_closed_corpus.XXXXXX")"}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_closed_corpus"

run_one() {
  local native=$1
  local base
  base=$(basename "$native" .native.sexp)
  local source="$CASES_DIR/$base.th0.p"
  local case_dir="$WORK_DIR/cases/$base"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -s "$source" ]]; then
    printf '%s\tMISSING_SOURCE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi
  if ! rg -q '^% megalodon_origin ' "$source"; then
    printf '%s\tMISSING_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! "$MEGALODON" \
      -vampirecertv1closed \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      -vampirecertv1emit "$case_dir/out.mg" \
      "$case_dir/dummy.mg" > "$case_dir/emit.out" 2> "$case_dir/emit.err"; then
    local err
    err=$(tail -1 "$case_dir/emit.err" | tr '\t' ' ')
    printf '%s\tEMIT_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q '^// Vampire certificate source origin:' "$case_dir/out.mg"; then
    printf '%s\tMISSING_EMITTED_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q '^// vampire_source_assumption ' "$case_dir/out.mg"; then
    printf '%s\tMISSING_SOURCE_BINDINGS\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if awk '/^\/\/ vampire_source_assumption / && $0 !~ /source_formula_status "closed_formula_checked"/ {print FNR ":" $0}' \
      "$case_dir/out.mg" > "$case_dir/unchecked_sources.txt" \
      && [[ -s "$case_dir/unchecked_sources.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/unchecked_sources.txt" | tr '\t' ' ')
    printf '%s\tUNCHECKED_SOURCE\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if rg -n '\b(admit|aby)\b|-allowincompleteqed|bridge_|assume definition_input__|assume vampire_eq_prop_ext' \
      "$case_dir/out.mg" > "$case_dir/forbidden.txt"; then
    local first
    first=$(head -1 "$case_dir/forbidden.txt" | tr '\t' ' ')
    printf '%s\tFORBIDDEN_TOKEN\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  local proof_check_args=()
  if rg -q '^Axiom prop_ext :' "$case_dir/out.mg"; then
    proof_check_args+=(-hf)
  fi

  if ! "$MEGALODON" "${proof_check_args[@]}" "$case_dir/out.mg" \
      > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tCHECK_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  printf '%s\tCLOSED_PASS\n' "$base" > "$case_dir/result.tsv"
}

export MEGALODON CASES_DIR WORK_DIR
export -f run_one

find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f -print0 \
  | sort -z \
  | xargs -0 -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort > "$WORK_DIR/counts.txt"

awk -F '\t' '$2 != "CLOSED_PASS"' "$WORK_DIR/summary.tsv" > "$WORK_DIR/nonpass.tsv"

cat "$WORK_DIR/counts.txt"
echo "native certificate v1 closed corpus artifacts: $WORK_DIR"
echo "native certificate v1 closed corpus latest link: $TMPDIR/latest_native_cert_v1_closed_corpus"

if [[ -s "$WORK_DIR/nonpass.tsv" ]]; then
  echo "native certificate v1 closed corpus had failures" >&2
  sed -n '1,40p' "$WORK_DIR/nonpass.tsv" >&2
  exit 1
fi
