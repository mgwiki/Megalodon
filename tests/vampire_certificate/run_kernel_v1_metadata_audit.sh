#!/usr/bin/env bash
set -euo pipefail

TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/kernel_v1_metadata_audit.XXXXXX")"}
MIN_KERNEL_V1=${MIN_KERNEL_V1:-1}
MIN_REWRITE_POSITION=${MIN_REWRITE_POSITION:-1}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_kernel_v1_metadata_audit"

native_run_dirs=("$@")
if (( ${#native_run_dirs[@]} == 0 )); then
  native_run_dirs=("$TMPDIR/latest_megalodon_native_live")
fi

: > "$WORK_DIR/native_files.txt"
for dir in "${native_run_dirs[@]}"; do
  if [[ -d "$dir/cases" ]]; then
    find -L "$dir/cases" -maxdepth 2 -type f -name native.sexp -size +0 \
      >> "$WORK_DIR/native_files.txt"
  elif [[ -f "$dir" ]]; then
    printf '%s\n' "$dir" >> "$WORK_DIR/native_files.txt"
  else
    echo "warning: missing native run or certificate: $dir" >&2
  fi
done

sort -u -o "$WORK_DIR/native_files.txt" "$WORK_DIR/native_files.txt"
if [[ ! -s "$WORK_DIR/native_files.txt" ]]; then
  echo "no native.sexp files found for kernel_v1 metadata audit" >&2
  exit 2
fi

xargs -a "$WORK_DIR/native_files.txt" \
  rg -n 'step_extra "[^"]+" "kernel_v1"' \
  > "$WORK_DIR/kernel_v1.tsv" || true

kernel_count=$(wc -l < "$WORK_DIR/kernel_v1.tsv")
if (( kernel_count < MIN_KERNEL_V1 )); then
  echo "kernel_v1 metadata audit found $kernel_count steps, below MIN_KERNEL_V1=$MIN_KERNEL_V1" >&2
  sed -n '1,40p' "$WORK_DIR/native_files.txt" >&2
  exit 1
fi

required_patterns=(
  'schema=prover9-small-kernel-v1'
  'rule='
  'conclusion_unit='
  'parent_count='
)

: > "$WORK_DIR/missing_required.tsv"
for pattern in "${required_patterns[@]}"; do
  awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
    "$WORK_DIR/kernel_v1.tsv" >> "$WORK_DIR/missing_required.tsv"
done

if [[ -s "$WORK_DIR/missing_required.tsv" ]]; then
  echo "kernel_v1 metadata audit found records missing required fields" >&2
  sed -n '1,40p' "$WORK_DIR/missing_required.tsv" >&2
  exit 1
fi

awk '
  index($0, "conclusion_clause=") == 0 &&
  index($0, "result_clause=") == 0 &&
  index($0, "result_formula=") == 0 {
    print
  }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_result.tsv"
if [[ -s "$WORK_DIR/missing_result.tsv" ]]; then
  echo "kernel_v1 metadata audit found records without a clause or formula result" >&2
  sed -n '1,40p' "$WORK_DIR/missing_result.tsv" >&2
  exit 1
fi

awk 'index($0, "selected=") != 0 && index($0, "selected_substituted=") == 0 {print}' \
  "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_selected_substituted.tsv"
if [[ -s "$WORK_DIR/missing_selected_substituted.tsv" ]]; then
  echo "kernel_v1 metadata audit found selected literals without substituted forms" >&2
  sed -n '1,40p' "$WORK_DIR/missing_selected_substituted.tsv" >&2
  exit 1
fi

awk 'index($0, "other=") != 0 && index($0, "other_substituted=") == 0 {print}' \
  "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_other_substituted.tsv"
if [[ -s "$WORK_DIR/missing_other_substituted.tsv" ]]; then
  echo "kernel_v1 metadata audit found other literals without substituted forms" >&2
  sed -n '1,40p' "$WORK_DIR/missing_other_substituted.tsv" >&2
  exit 1
fi

awk '
  /rule=resolution/ || /rule=subsumption_resolution/ || /rule=factoring/ ||
  /rule=equality_resolution/ || /rule=superposition/ ||
  /rule=equality_factoring/ || /rule=rewrite/ ||
  /rule=unit_resulting_resolution/ || /rule=cnf_clause/ ||
  /rule=skolemize/ || /rule=rectify_formula/ {
    next
  }
  { print }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/unknown_rules.tsv"

if [[ -s "$WORK_DIR/unknown_rules.tsv" ]]; then
  echo "kernel_v1 metadata audit found unexpected rule names" >&2
  sed -n '1,40p' "$WORK_DIR/unknown_rules.tsv" >&2
  exit 1
fi

grep -F 'rule=unit_resulting_resolution' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/unit_resulting_resolution.tsv" || true

if [[ -s "$WORK_DIR/unit_resulting_resolution.tsv" ]]; then
  : > "$WORK_DIR/missing_urr_fields.tsv"
  for pattern in \
    'trace_main_parent_unit=' \
    'trace_step_count=' \
    'trace_step_0_unit_parent=' \
    'trace_step_0_selected=' \
    'trace_step_0_selected_substituted=' \
    'trace_step_0_unit_substituted=' \
    'trace_step_0_remaining_after=' \
    'trace_remaining='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/unit_resulting_resolution.tsv" >> "$WORK_DIR/missing_urr_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_urr_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found unit-resulting-resolution records missing trace fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_urr_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=skolemize' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/skolemize.tsv" || true

if [[ -s "$WORK_DIR/skolemize.tsv" ]]; then
  : > "$WORK_DIR/missing_skolemize_fields.tsv"
  for pattern in \
    'source_unit=' \
    'proof_parent_count=' \
    'source_formula=' \
    'result_formula=' \
    'introduced_count=' \
    'introduced_0_symbol='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/skolemize.tsv" >> "$WORK_DIR/missing_skolemize_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_skolemize_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found skolemization records missing transformation fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_skolemize_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=rectify_formula' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/rectify_formula.tsv" || true

if [[ -s "$WORK_DIR/rectify_formula.tsv" ]]; then
  : > "$WORK_DIR/missing_rectify_formula_fields.tsv"
  for pattern in \
    'source_unit=' \
    'proof_parent_count=' \
    'source_formula=' \
    'result_formula=' \
    'renaming_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/rectify_formula.tsv" >> "$WORK_DIR/missing_rectify_formula_fields.tsv"
  done

  awk 'index($0, "renaming_count=0") == 0 && index($0, "renaming_0_source=") == 0 {print "renaming_0_source=\t" $0}' \
    "$WORK_DIR/rectify_formula.tsv" >> "$WORK_DIR/missing_rectify_formula_fields.tsv"
  awk 'index($0, "renaming_count=0") == 0 && index($0, "renaming_0_target=") == 0 {print "renaming_0_target=\t" $0}' \
    "$WORK_DIR/rectify_formula.tsv" >> "$WORK_DIR/missing_rectify_formula_fields.tsv"
  awk 'index($0, "renaming_count=0") == 0 && index($0, "renaming_0_substitution=") == 0 {print "renaming_0_substitution=\t" $0}' \
    "$WORK_DIR/rectify_formula.tsv" >> "$WORK_DIR/missing_rectify_formula_fields.tsv"

  if [[ -s "$WORK_DIR/missing_rectify_formula_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found rectification records missing transformation fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_rectify_formula_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=cnf_clause' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/cnf_clause.tsv" || true

if [[ -s "$WORK_DIR/cnf_clause.tsv" ]]; then
  : > "$WORK_DIR/missing_cnf_clause_fields.tsv"
  for pattern in \
    'source_unit=' \
    'source_kind=' \
    'result_clause=' \
    'clause_parent_unit=' \
    'clause_index=' \
    'clause_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/cnf_clause.tsv" >> "$WORK_DIR/missing_cnf_clause_fields.tsv"
  done

  awk 'index($0, "source_formula=") == 0 && index($0, "source_clause=") == 0 {print "source_formula_or_clause=\t" $0}' \
    "$WORK_DIR/cnf_clause.tsv" >> "$WORK_DIR/missing_cnf_clause_fields.tsv"

  if [[ -s "$WORK_DIR/missing_cnf_clause_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found cnf-clause records missing source/result fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_cnf_clause_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rewrite_position=' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/rewrite_position.tsv" || true

rewrite_count=$(wc -l < "$WORK_DIR/rewrite_position.tsv")
if (( rewrite_count < MIN_REWRITE_POSITION )); then
  echo "kernel_v1 metadata audit found $rewrite_count rewrite-position steps, below MIN_REWRITE_POSITION=$MIN_REWRITE_POSITION" >&2
  exit 1
fi

: > "$WORK_DIR/missing_rewrite_fields.tsv"
for pattern in 'from=' 'to=' 'rewritten_target=' 'target_substituted=' 'equality_substituted='; do
  awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
    "$WORK_DIR/rewrite_position.tsv" >> "$WORK_DIR/missing_rewrite_fields.tsv"
done

if [[ -s "$WORK_DIR/missing_rewrite_fields.tsv" ]]; then
  echo "kernel_v1 metadata audit found rewrite-position records missing rewrite fields" >&2
  sed -n '1,40p' "$WORK_DIR/missing_rewrite_fields.tsv" >&2
  exit 1
fi

awk '
  {
    rule = "unknown"
    if (match($0, /rule=[^"]+/)) {
      rule = substr($0, RSTART + 5, RLENGTH - 5)
    }
    count[rule]++
  }
  END {
    for (rule in count) {
      print rule, count[rule]
    }
  }
' "$WORK_DIR/kernel_v1.tsv" | sort > "$WORK_DIR/rule_counts.txt"

echo "kernel_v1 records: $kernel_count"
echo "kernel_v1 rewrite-position records: $rewrite_count"
cat "$WORK_DIR/rule_counts.txt"
echo "kernel_v1 metadata audit artifacts: $WORK_DIR"
echo "kernel_v1 metadata audit latest link: $TMPDIR/latest_kernel_v1_metadata_audit"
