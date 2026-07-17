#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_avatar_closed_audit.XXXXXX")"}
MIN_AVATAR=${MIN_AVATAR:-10}
RUN_AVATAR_CASES=${RUN_AVATAR_CASES:-1}
JOBS=${JOBS:-7}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_avatar_closed_audit"

# This gate tracks the AVATAR layer above definition inputs.  It permits the
# lower certified layers plus AVATAR component, split, contradiction, and
# refutation records that closed mode can validate without adding non-source
# premises.  It deliberately excludes inequality splitting, definition rewrite
# chains, and broader macros.
allowed_rules=$(
  cat <<'RULES'
input
formula_input
formula_term_input
formula_term_copy
formula_copy
rectify_formula
fool_formula
fool_atom_lift
fool_bool
fool_exhaustiveness
truth_conflict
ennf_formula
cnf_formula_clause
cnf_literal
skolem_formula
definition_input
avatar_definition
avatar_component
split_dependency
avatar_split
avatar_contradiction
avatar_refutation
substitute
resolve
subsumption_resolution
factor
equality_resolution
equality_symmetry
equality_factoring
paramodulate
contradiction
RULES
)

avatar_rules=$(
  cat <<'RULES'
avatar_component
avatar_definition
split_dependency
avatar_split
avatar_contradiction
avatar_refutation
RULES
)

metadata_rules='^(problem|step_proposition|step_variable_sorts|step_extra|symbol_declaration|source_declaration)$'

allowed_file="$WORK_DIR/allowed_rules.txt"
avatar_file="$WORK_DIR/avatar_rules.txt"
printf '%s\n' "$allowed_rules" | sort > "$allowed_file"
printf '%s\n' "$avatar_rules" | sort > "$avatar_file"
: > "$WORK_DIR/eligible.tsv"
: > "$WORK_DIR/excluded.tsv"
: > "$WORK_DIR/first_excluded.tsv"
: > "$WORK_DIR/avatar_closed_cases.list"
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
  avatar_hit_file="$WORK_DIR/$base.avatar_rules"
  awk '
    match($0, /^  \(([a-z_]+)/, m) {
      if (m[1] !~ metadata) print m[1]
    }
  ' metadata="$metadata_rules" "$native" > "$rules_order_file"
  sort -u "$rules_order_file" > "$rules_file"
  while IFS= read -r rule || [[ -n "$rule" ]]; do
    [[ -z "$rule" ]] && continue
    printf '%s\t%s\n' "$base" "$rule" >> "$all_rules"
    printf '%s\n' "$base" >> "$WORK_DIR/cases_by_rule/$rule.list"
  done < "$rules_file"
  comm -23 "$rules_file" "$allowed_file" > "$bad_file"
  comm -12 "$rules_file" "$avatar_file" > "$avatar_hit_file"
  if [[ ! -s "$bad_file" && -s "$avatar_hit_file" ]]; then
    printf '%s\tAVATAR_ELIGIBLE\t%s\n' "$base" "$(paste -sd, "$rules_file")" \
      >> "$WORK_DIR/eligible.tsv"
    printf '%s\n' "$base" >> "$WORK_DIR/avatar_closed_cases.list"
  elif [[ -s "$bad_file" ]]; then
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
  else
    printf '%s\tLOWER_LAYER_ONLY\t%s\n' "$base" "$(paste -sd, "$rules_file")" \
      >> "$WORK_DIR/excluded.tsv"
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

{
  printf 'AVATAR_ELIGIBLE %s\n' "$eligible_count"
  printf 'EXCLUDED_OR_LOWER_LAYER_ONLY %s\n' "$excluded_count"
  printf 'MIN_AVATAR %s\n' "$MIN_AVATAR"
} | tee "$WORK_DIR/counts.txt"

echo "native certificate v1 avatar closed audit artifacts: $WORK_DIR"
echo "native certificate v1 avatar closed audit latest link: $TMPDIR/latest_native_cert_v1_avatar_closed_audit"
echo "native certificate v1 avatar closed audit rule counts: $WORK_DIR/rule_counts.txt"
echo "native certificate v1 avatar closed audit excluded rule counts: $WORK_DIR/excluded_rule_counts.txt"
echo "native certificate v1 avatar closed audit first excluded rule counts: $WORK_DIR/first_excluded_rule_counts.txt"

if (( eligible_count < MIN_AVATAR )); then
  echo "avatar closed audit has fewer than $MIN_AVATAR AVATAR cases" >&2
  echo "top excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/excluded_rule_counts.txt" >&2
  echo "top first excluded native certificate rules:" >&2
  sed -n '1,20p' "$WORK_DIR/first_excluded_rule_counts.txt" >&2
  sed -n '1,40p' "$WORK_DIR/excluded.tsv" >&2
  exit 1
fi

if [[ "$RUN_AVATAR_CASES" == "1" ]]; then
  CASE_LIST="$WORK_DIR/avatar_closed_cases.list" \
  WORK_DIR="$WORK_DIR/closed_check" \
  JOBS="$JOBS" \
    "$ROOT/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh"
  sed 's/\tCLOSED_PASS$/\tAVATAR_CLOSED_PASS/' \
    "$WORK_DIR/closed_check/summary.tsv" > "$WORK_DIR/avatar_summary.tsv"
  awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
    "$WORK_DIR/avatar_summary.tsv" \
    | sort > "$WORK_DIR/avatar_counts.txt"
  cat "$WORK_DIR/avatar_counts.txt"
fi
