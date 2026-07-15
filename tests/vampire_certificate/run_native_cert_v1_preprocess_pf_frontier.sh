#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_preprocess_pf_frontier.XXXXXX")"}
JOBS=${JOBS:-10}
MIN_PREPROCESS=${MIN_PREPROCESS:-10}
MIN_FRONTIER_CASES=${MIN_FRONTIER_CASES:-10}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_preprocess_pf_frontier"

preprocess_audit_dir="$WORK_DIR/preprocess_closed_audit"
RUN_PREPROCESS_CASES=0 \
WORK_DIR="$preprocess_audit_dir" \
MIN_PREPROCESS="$MIN_PREPROCESS" \
JOBS="$JOBS" \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_preprocess_closed_audit.sh" \
  > "$WORK_DIR/preprocess_closed_audit.out" \
  2> "$WORK_DIR/preprocess_closed_audit.err"

frontier_cases="$preprocess_audit_dir/preprocess_closed_cases.list"
if [[ ! -s "$frontier_cases" ]]; then
  echo "preprocess proof-term frontier has no preprocessing-closed cases" >&2
  exit 2
fi

case_count=$(wc -l < "$frontier_cases" | tr -d ' ')
if (( case_count < MIN_FRONTIER_CASES )); then
  echo "preprocess proof-term frontier has fewer than $MIN_FRONTIER_CASES cases" >&2
  exit 1
fi

classify_error() {
  local err_file=$1
  local msg
  msg=$(tail -1 "$err_file" | tr '\t' ' ')
  if [[ "$msg" =~ no\ proof-term\ rule\ for\ ([a-z_]+) ]]; then
    printf 'UNSUPPORTED_RULE_%s' "${BASH_REMATCH[1]}"
  elif [[ "$msg" =~ references\ unknown\ formula\ parent ]]; then
    printf 'UNKNOWN_FORMULA_PARENT'
  elif [[ "$msg" =~ formula_copy\ result\ is\ not\ the\ parent\ formula ]]; then
    printf 'FORMULA_COPY_MISMATCH'
  elif [[ "$msg" =~ currently\ supports\ only\ ([^\"]+) ]]; then
    printf 'UNSUPPORTED_SHAPE'
  elif [[ "$msg" =~ built\ a\ proof\ of\ the\ wrong\ proposition ]]; then
    printf 'WRONG_PROPOSITION'
  elif [[ "$msg" =~ ill-formed\ proof\ term ]]; then
    printf 'ILL_FORMED_PROOF_TERM'
  elif [[ "$msg" =~ check\ failed:\ ([^:]+): ]]; then
    printf 'CHECK_FAILED'
  else
    printf 'PF_FAIL'
  fi
}

run_one() {
  local base=$1
  local native="$CASES_DIR/$base.native.sexp"
  local source="$CASES_DIR/$base.th0.p"
  local case_dir="$WORK_DIR/cases/$base"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -s "$native" ]]; then
    printf '%s\tMISSING_NATIVE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi
  if [[ ! -s "$source" ]]; then
    printf '%s\tMISSING_SOURCE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if "$MEGALODON" \
      -vampirecertv1preprocesspfcheck \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      "$case_dir/dummy.mg" > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    if rg -q 'native preprocess proof term checked' "$case_dir/check.out"; then
      printf '%s\tPREPROCESS_PF_PASS\n' "$base" > "$case_dir/result.tsv"
    else
      printf '%s\tPREPROCESS_PF_MISSING_CONFIRMATION\n' "$base" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  local status err
  status=$(classify_error "$case_dir/check.err")
  err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
  printf '%s\t%s\t%s\n' "$base" "$status" "$err" > "$case_dir/result.tsv"
}

export MEGALODON CASES_DIR WORK_DIR
export -f classify_error run_one

xargs -r -P "$JOBS" -n 1 bash -c 'run_one "$1"' bash < "$frontier_cases"

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | sort -z \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" | sort > "$WORK_DIR/counts.txt"

awk -F '\t' '$2 != "PREPROCESS_PF_PASS"' "$WORK_DIR/summary.tsv" \
  > "$WORK_DIR/frontier_failures.tsv"

awk -F '\t' '$2 != "PREPROCESS_PF_PASS" {print $2}' "$WORK_DIR/summary.tsv" \
  | sort | uniq -c | sort -nr > "$WORK_DIR/frontier_failure_counts.txt"

cat "$WORK_DIR/counts.txt"
echo "native certificate v1 preprocess proof-term frontier artifacts: $WORK_DIR"
echo "native certificate v1 preprocess proof-term frontier latest link: $TMPDIR/latest_native_cert_v1_preprocess_pf_frontier"
echo "native certificate v1 preprocess proof-term frontier failures: $WORK_DIR/frontier_failures.tsv"
echo "native certificate v1 preprocess proof-term frontier failure counts: $WORK_DIR/frontier_failure_counts.txt"
