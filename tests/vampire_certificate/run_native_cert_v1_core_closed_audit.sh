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
# preprocessing and macro proof steps such as Skolemization, AVATAR, and theory
# facts.  Rectification, ENNF, definition inputs, and the currently checked
# FOOL Boolean-lifting/exhaustiveness subset are counted only because the native
# core path builds and immediately checks proof terms for them without
# certificate-derived Known propositions.
allowed_rules=$(
  cat <<'RULES'
input
formula_input
formula_term_input
formula_term_copy
rectify_formula
fool_atom_lift
fool_formula
fool_bool
ennf_formula
formula_copy
cnf_literal
cnf_formula_clause
definition_input
fool_exhaustiveness
inequality_name_intro
inequality_split
substitute
resolve
subsumption_resolution
factor
equality_resolution
equality_factoring
equality_symmetry
truth_conflict
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
  instantiation_steps_file="$WORK_DIR/$base.instantiation_steps"
  rules_order_file="$WORK_DIR/$base.rules_order"
  rules_file="$WORK_DIR/$base.rules"
  bad_file="$WORK_DIR/$base.bad_rules"
  awk -v metadata="$metadata_rules" -v instantiation_steps="$instantiation_steps_file" '
    /^  \(step_extra "[^"]+" "kernel_v1"/ && /"rule=instantiation"/ {
      step = $0
      sub(/^  \(step_extra "/, "", step)
      sub(/".*$/, "", step)
      print step
    }
  ' "$native" | sort -u > "$instantiation_steps_file"
  awk -v metadata="$metadata_rules" -v instantiation_steps="$instantiation_steps_file" '
    BEGIN {
      while ((getline step < instantiation_steps) > 0) {
        has_instantiation_metadata[step] = 1
      }
      close(instantiation_steps)
    }
    match($0, /^  \(([a-z_]+)/, m) {
      if (m[1] !~ metadata) {
        if (m[1] == "substitute" && $0 !~ /\(subst\)/) {
          step_id = $0
          sub(/^  \(substitute "/, "", step_id)
          sub(/".*$/, "", step_id)
          if (has_instantiation_metadata[step_id]) {
            print "substitute"
          } else {
            print "nonidentity_substitute"
          }
        } else print m[1]
      }
    }
  ' "$native" > "$rules_order_file"
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
  set +e
  CASE_LIST="$WORK_DIR/core_closed_cases.list" \
  WORK_DIR="$WORK_DIR/closed_check" \
  JOBS="$JOBS" \
  CORE_CERT_V1=1 \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh"
  closed_status=$?
  set -e
  if [[ -s "$WORK_DIR/closed_check/summary.tsv" ]]; then
    sed 's/\tCLOSED_PASS$/\tCORE_CLOSED_PASS/' \
      "$WORK_DIR/closed_check/summary.tsv" > "$WORK_DIR/core_summary.tsv"
    awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
      "$WORK_DIR/core_summary.tsv" \
      | sort > "$WORK_DIR/core_counts.txt"
    cat "$WORK_DIR/core_counts.txt"
  else
    : > "$WORK_DIR/core_summary.tsv"
    : > "$WORK_DIR/core_counts.txt"
  fi
  if (( closed_status != 0 )); then
    echo "core closed textual emission had diagnostic failures; native core proof-term audit remains authoritative" >&2
  fi
fi

if [[ "$RUN_CORE_PF_CASES" == "1" ]]; then
  CASE_LIST="$WORK_DIR/core_closed_cases.list" \
  WORK_DIR="$WORK_DIR/core_pf_check" \
  JOBS="$JOBS" \
  MIN_CORE_PF="$MIN_CORE" \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh"
fi
