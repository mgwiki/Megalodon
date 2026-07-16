#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_real_core_frontier.XXXXXX")"}
MIN_REAL_CORE=${MIN_REAL_CORE:-0}
JOBS=${JOBS:-10}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_real_core_frontier"

audit_dir="$WORK_DIR/core_closed_audit"
RUN_CORE_CASES=0 \
RUN_CORE_PF_CASES=0 \
MIN_CORE=1 \
JOBS="$JOBS" \
WORK_DIR="$audit_dir" \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh" \
  > "$WORK_DIR/core_closed_audit.out" \
  2> "$WORK_DIR/core_closed_audit.err"

real_core_list="$WORK_DIR/real_core_closed_cases.list"
synthetic_core_list="$WORK_DIR/synthetic_core_closed_cases.list"
: > "$real_core_list"
: > "$synthetic_core_list"

while IFS= read -r case_name || [[ -n "$case_name" ]]; do
  [[ -z "$case_name" ]] && continue
  if [[ "$case_name" == core.cnf.* ]]; then
    printf '%s\n' "$case_name" >> "$synthetic_core_list"
  else
    printf '%s\n' "$case_name" >> "$real_core_list"
  fi
done < "$audit_dir/core_closed_cases.list"

real_core_count=$(wc -l < "$real_core_list" | tr -d ' ')
synthetic_core_count=$(wc -l < "$synthetic_core_list" | tr -d ' ')
excluded_count=$(awk '/^EXCLUDED / {print $2}' "$audit_dir/counts.txt")

{
  printf 'REAL_CORE_ELIGIBLE %s\n' "$real_core_count"
  printf 'SYNTHETIC_CORE_ELIGIBLE %s\n' "$synthetic_core_count"
  printf 'EXCLUDED %s\n' "${excluded_count:-0}"
  printf 'MIN_REAL_CORE %s\n' "$MIN_REAL_CORE"
} | tee "$WORK_DIR/counts.txt"

cp "$audit_dir/first_excluded_rule_counts.txt" "$WORK_DIR/first_excluded_rule_counts.txt"
cp "$audit_dir/excluded_rule_counts.txt" "$WORK_DIR/excluded_rule_counts.txt"
cp "$audit_dir/rule_counts.txt" "$WORK_DIR/rule_counts.txt"
cp "$audit_dir/eligible.tsv" "$WORK_DIR/eligible.tsv"
cp "$audit_dir/excluded.tsv" "$WORK_DIR/excluded.tsv"

echo "native certificate v1 real-core frontier artifacts: $WORK_DIR"
echo "native certificate v1 real-core frontier latest link: $TMPDIR/latest_native_cert_v1_real_core_frontier"
echo "native certificate v1 real-core frontier first excluded rule counts: $WORK_DIR/first_excluded_rule_counts.txt"
echo "native certificate v1 real-core frontier excluded rule counts: $WORK_DIR/excluded_rule_counts.txt"

if (( real_core_count < MIN_REAL_CORE )); then
  echo "real-core frontier has fewer than $MIN_REAL_CORE real non-synthetic cases" >&2
  echo "top first excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/first_excluded_rule_counts.txt" >&2
  echo "top excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/excluded_rule_counts.txt" >&2
  exit 1
fi
