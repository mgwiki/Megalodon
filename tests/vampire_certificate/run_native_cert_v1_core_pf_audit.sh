#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_core_pf_audit.XXXXXX")"}
JOBS=${JOBS:-10}
MIN_CORE_PF=${MIN_CORE_PF:-10}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_core_pf_audit"

case_list="$WORK_DIR/core_pf_cases.list"
find "$CASES_DIR" -maxdepth 1 -type f -name 'core.cnf.*.native.sexp' | sort > "$case_list"

run_one() {
  local native=$1
  local base
  base=$(basename "$native" .native.sexp)
  local source="$CASES_DIR/$base.th0.p"
  local case_dir="$WORK_DIR/cases/$base"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if ! "$MEGALODON" \
      -vampirecertv1corepfcheck \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      "$case_dir/dummy.mg" > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tCORE_PF_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'native core proof term checked' "$case_dir/check.out"; then
    printf '%s\tCORE_PF_MISSING_CONFIRMATION\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'Vampire certificate v1 source origin ' "$case_dir/check.out"; then
    printf '%s\tCORE_PF_MISSING_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'Vampire certificate v1 native core source bindings checked ' "$case_dir/check.out"; then
    printf '%s\tCORE_PF_MISSING_SOURCE_BINDINGS\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  printf '%s\tCORE_PF_PASS\n' "$base" > "$case_dir/result.tsv"
}

export MEGALODON CASES_DIR WORK_DIR
export -f run_one

xargs -r -P "$JOBS" -n 1 bash -c 'run_one "$1"' bash < "$case_list"

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | sort -z \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" | sort | tee "$WORK_DIR/counts.txt"

pass_count=$(awk -F '\t' '$2 == "CORE_PF_PASS" {count++} END {print count + 0}' "$WORK_DIR/summary.tsv")
if (( pass_count < MIN_CORE_PF )); then
  echo "native certificate v1 core proof-term audit has fewer than $MIN_CORE_PF passes" >&2
  sed -n '1,40p' "$WORK_DIR/summary.tsv" >&2
  exit 1
fi

if awk -F '\t' '$2 != "CORE_PF_PASS" {bad=1} END {exit bad ? 0 : 1}' "$WORK_DIR/summary.tsv"; then
  echo "native certificate v1 core proof-term audit has failures" >&2
  sed -n '1,80p' "$WORK_DIR/summary.tsv" >&2
  exit 1
fi

echo "native certificate v1 core proof-term audit artifacts: $WORK_DIR"
echo "native certificate v1 core proof-term audit latest link: $TMPDIR/latest_native_cert_v1_core_pf_audit"
