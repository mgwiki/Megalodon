#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_core_closed_audit.XXXXXX")"}
MIN_CORE=${MIN_CORE:-10}
RUN_CORE_CASES=${RUN_CORE_CASES:-1}
RUN_CORE_PF_CASES=${RUN_CORE_PF_CASES:-1}
JOBS=${JOBS:-7}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_core_closed_audit"

# This is the audit/MVP qualifying fragment.  It deliberately excludes
# preprocessing and macro proof steps such as rectification, FOOL elimination,
# ENNF/CNF projection, Skolemization, definition inputs, AVATAR, and theory
# facts.  Those may still be useful closed-mode diagnostics, but they are not
# counted by this core gate.
allowed_rules=$(
  cat <<'RULES'
input
substitute
resolve
subsumption_resolution
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
: > "$WORK_DIR/first_excluded.tsv"
: > "$WORK_DIR/near_core_nonidentity_substitute.list"
: > "$WORK_DIR/core_closed_cases.list"
all_rules="$WORK_DIR/all_case_rules.tsv"
: > "$all_rules"
mkdir -p "$WORK_DIR/cases_by_rule"
mkdir -p "$WORK_DIR/cases_by_first_blocker"

find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f | sort |
while IFS= read -r native; do
  base=$(basename "$native" .native.sexp)
  rules_order_file="$WORK_DIR/$base.rules_order"
  rules_file="$WORK_DIR/$base.rules"
  bad_file="$WORK_DIR/$base.bad_rules"
  awk '
    match($0, /^  \(([a-z_]+)/, m) {
      if (m[1] !~ metadata) {
        if (m[1] == "substitute" && $0 !~ /\(subst\)/) print "nonidentity_substitute"
        else print m[1]
      }
    }
  ' metadata="$metadata_rules" "$native" > "$rules_order_file"
  sort -u "$rules_order_file" > "$rules_file"
  while IFS= read -r rule || [[ -n "$rule" ]]; do
    [[ -z "$rule" ]] && continue
    printf '%s\t%s\n' "$base" "$rule" >> "$all_rules"
    printf '%s\n' "$base" >> "$WORK_DIR/cases_by_rule/$rule.list"
  done < "$rules_file"
  comm -23 "$rules_file" "$allowed_file" > "$bad_file"
  if [[ ! -s "$bad_file" ]]; then
    printf '%s\tCORE_ELIGIBLE\t%s\n' "$base" "$(paste -sd, "$rules_file")" \
      >> "$WORK_DIR/eligible.tsv"
    printf '%s\n' "$base" >> "$WORK_DIR/core_closed_cases.list"
  else
    printf '%s\tEXCLUDED\t%s\n' "$base" "$(paste -sd, "$bad_file")" \
      >> "$WORK_DIR/excluded.tsv"
    first_blocker=""
    while IFS= read -r rule || [[ -n "$rule" ]]; do
      [[ -z "$rule" ]] && continue
      if ! grep -Fxq "$rule" "$allowed_file"; then
        first_blocker="$rule"
        break
      fi
    done < "$rules_order_file"
    if [[ -z "$first_blocker" ]]; then
      first_blocker="$(sed -n '1p' "$bad_file")"
    fi
    printf '%s\tFIRST_EXCLUDED\t%s\n' "$base" "$first_blocker" \
      >> "$WORK_DIR/first_excluded.tsv"
    printf '%s\n' "$base" >> "$WORK_DIR/cases_by_first_blocker/$first_blocker.list"
    if [[ "$(wc -l < "$bad_file" | tr -d ' ')" == "1" ]] \
        && [[ "$(sed -n '1p' "$bad_file")" == "nonidentity_substitute" ]]; then
      printf '%s\n' "$base" >> "$WORK_DIR/near_core_nonidentity_substitute.list"
    fi
  fi
done

eligible_count=$(wc -l < "$WORK_DIR/eligible.tsv" | tr -d ' ')
excluded_count=$(wc -l < "$WORK_DIR/excluded.tsv" | tr -d ' ')
if [[ -s "$all_rules" ]]; then
  cut -f2 "$all_rules" | sort | uniq -c | sort -nr > "$WORK_DIR/rule_counts.txt"
  awk -F '\t' '$2 == "EXCLUDED" {split($3, rules, ","); for (i in rules) if (rules[i] != "") print rules[i]}' \
    "$WORK_DIR/excluded.tsv" | sort | uniq -c | sort -nr > "$WORK_DIR/excluded_rule_counts.txt"
  awk -F '\t' '$2 == "FIRST_EXCLUDED" {print $3}' \
    "$WORK_DIR/first_excluded.tsv" | sort | uniq -c | sort -nr > "$WORK_DIR/first_excluded_rule_counts.txt"
  find "$WORK_DIR/cases_by_rule" -type f -name '*.list' -print0 \
    | xargs -0 -r -n1 sh -c 'sort -u "$1" -o "$1"' sh
  find "$WORK_DIR/cases_by_first_blocker" -type f -name '*.list' -print0 \
    | xargs -0 -r -n1 sh -c 'sort -u "$1" -o "$1"' sh
else
  : > "$WORK_DIR/rule_counts.txt"
  : > "$WORK_DIR/excluded_rule_counts.txt"
  : > "$WORK_DIR/first_excluded_rule_counts.txt"
fi
sort -u "$WORK_DIR/near_core_nonidentity_substitute.list" \
  -o "$WORK_DIR/near_core_nonidentity_substitute.list"

{
  printf 'CORE_ELIGIBLE %s\n' "$eligible_count"
  printf 'EXCLUDED %s\n' "$excluded_count"
  printf 'MIN_CORE %s\n' "$MIN_CORE"
} | tee "$WORK_DIR/counts.txt"

echo "native certificate v1 core closed audit artifacts: $WORK_DIR"
echo "native certificate v1 core closed audit latest link: $TMPDIR/latest_native_cert_v1_core_closed_audit"
echo "native certificate v1 core closed audit rule counts: $WORK_DIR/rule_counts.txt"
echo "native certificate v1 core closed audit excluded rule counts: $WORK_DIR/excluded_rule_counts.txt"
echo "native certificate v1 core closed audit first excluded rule counts: $WORK_DIR/first_excluded_rule_counts.txt"
echo "native certificate v1 core closed audit near-core nonidentity-substitute cases: $WORK_DIR/near_core_nonidentity_substitute.list"

if (( eligible_count < MIN_CORE )); then
  echo "core closed audit has fewer than $MIN_CORE whitelist-only cases" >&2
  echo "top excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/excluded_rule_counts.txt" >&2
  echo "top first excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/first_excluded_rule_counts.txt" >&2
  sed -n '1,40p' "$WORK_DIR/excluded.tsv" >&2
  exit 1
fi

if [[ "$RUN_CORE_CASES" == "1" ]]; then
  CASE_LIST="$WORK_DIR/core_closed_cases.list" \
  WORK_DIR="$WORK_DIR/closed_check" \
  JOBS="$JOBS" \
  CORE_CERT_V1=1 \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh"
  sed 's/\tCLOSED_PASS$/\tCORE_CLOSED_PASS/' \
    "$WORK_DIR/closed_check/summary.tsv" > "$WORK_DIR/core_summary.tsv"
  awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
    "$WORK_DIR/core_summary.tsv" \
    | sort > "$WORK_DIR/core_counts.txt"
  cat "$WORK_DIR/core_counts.txt"
fi

if [[ "$RUN_CORE_PF_CASES" == "1" ]]; then
  CASE_LIST="$WORK_DIR/core_closed_cases.list" \
  WORK_DIR="$WORK_DIR/core_pf_check" \
  JOBS="$JOBS" \
  MIN_CORE_PF="$MIN_CORE" \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh"
fi
