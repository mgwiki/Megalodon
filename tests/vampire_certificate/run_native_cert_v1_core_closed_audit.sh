#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_core_closed_audit.XXXXXX")"}
MIN_CORE=${MIN_CORE:-10}
RUN_CORE_CASES=${RUN_CORE_CASES:-1}
JOBS=${JOBS:-7}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_core_closed_audit"

allowed_rules=$(
  cat <<'RULES'
input
formula_input
formula_term_input
formula_term_copy
formula_copy
substitute
condensation
resolve
factor
equality_resolution
equality_symmetry
paramodulate
contradiction
RULES
)

metadata_rules='^(problem|step_proposition|step_variable_sorts|step_extra|symbol_declaration|source_declaration)$'

allowed_file="$WORK_DIR/allowed_rules.txt"
printf '%s\n' "$allowed_rules" | sort > "$allowed_file"
: > "$WORK_DIR/eligible.tsv"
: > "$WORK_DIR/excluded.tsv"
: > "$WORK_DIR/core_closed_cases.list"

find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f | sort |
while IFS= read -r native; do
  base=$(basename "$native" .native.sexp)
  rules_file="$WORK_DIR/$base.rules"
  bad_file="$WORK_DIR/$base.bad_rules"
  awk '
    match($0, /^  \(([a-z_]+)/, m) {
      if (m[1] !~ metadata) print m[1]
    }
  ' metadata="$metadata_rules" "$native" | sort -u > "$rules_file"
  comm -23 "$rules_file" "$allowed_file" > "$bad_file"
  if [[ ! -s "$bad_file" ]]; then
    printf '%s\tCORE_ELIGIBLE\t%s\n' "$base" "$(paste -sd, "$rules_file")" \
      >> "$WORK_DIR/eligible.tsv"
    printf '%s\n' "$base" >> "$WORK_DIR/core_closed_cases.list"
  else
    printf '%s\tEXCLUDED\t%s\n' "$base" "$(paste -sd, "$bad_file")" \
      >> "$WORK_DIR/excluded.tsv"
  fi
done

eligible_count=$(wc -l < "$WORK_DIR/eligible.tsv" | tr -d ' ')
excluded_count=$(wc -l < "$WORK_DIR/excluded.tsv" | tr -d ' ')

{
  printf 'CORE_ELIGIBLE %s\n' "$eligible_count"
  printf 'EXCLUDED %s\n' "$excluded_count"
  printf 'MIN_CORE %s\n' "$MIN_CORE"
} | tee "$WORK_DIR/counts.txt"

echo "native certificate v1 core closed audit artifacts: $WORK_DIR"
echo "native certificate v1 core closed audit latest link: $TMPDIR/latest_native_cert_v1_core_closed_audit"

if (( eligible_count < MIN_CORE )); then
  echo "core closed audit has fewer than $MIN_CORE whitelist-only cases" >&2
  sed -n '1,40p' "$WORK_DIR/excluded.tsv" >&2
  exit 1
fi

if [[ "$RUN_CORE_CASES" == "1" ]]; then
  CASE_LIST="$WORK_DIR/core_closed_cases.list" \
  WORK_DIR="$WORK_DIR/closed_check" \
  JOBS="$JOBS" \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh"
fi
