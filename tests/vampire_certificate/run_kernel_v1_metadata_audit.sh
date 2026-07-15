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

: > "$WORK_DIR/mismatched_conclusion_units.tsv"
while IFS= read -r native_file; do
  awk -v source="$native_file" '
    index($0, "\"kernel_v1\"") != 0 {
      owner = ""
      conclusion = ""
      if (match($0, /step_extra "([^"]+)"/, owner_match)) {
        owner = owner_match[1]
      }
      if (match($0, /conclusion_unit=(u[0-9][[:alnum:]_]*)/, conclusion_match)) {
        conclusion = conclusion_match[1]
      }
      if (owner == "" || conclusion == "" || owner != conclusion) {
        print source ":" FNR "\towner=" owner "\tconclusion_unit=" conclusion "\t" $0
      }
    }
  ' "$native_file" >> "$WORK_DIR/mismatched_conclusion_units.tsv"
done < "$WORK_DIR/native_files.txt"

if [[ -s "$WORK_DIR/mismatched_conclusion_units.tsv" ]]; then
  echo "kernel_v1 metadata audit found records attached to a different unit than their conclusion_unit" >&2
  sed -n '1,40p' "$WORK_DIR/mismatched_conclusion_units.tsv" >&2
  exit 1
fi

: > "$WORK_DIR/missing_unit_references.tsv"
while IFS= read -r native_file; do
  awk -v source="$native_file" '
    NR == FNR {
      if (match($0, /^  \([[:alnum:]_]+ "([^"]+)"/, step)) {
        ids[step[1]] = 1
      }
      next
    }
    index($0, "\"kernel_v1\"") != 0 {
      rest = $0
      while (match(rest, /[[:alnum:]_]+_unit=u[0-9][[:alnum:]_]*/)) {
        token = substr(rest, RSTART, RLENGTH)
        split(token, parts, "=")
        ref = parts[2]
        if (!(ref in ids)) {
          print source ":" FNR "\t" ref "\t" $0
        }
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
  ' "$native_file" "$native_file" >> "$WORK_DIR/missing_unit_references.tsv"
done < "$WORK_DIR/native_files.txt"

if [[ -s "$WORK_DIR/missing_unit_references.tsv" ]]; then
  echo "kernel_v1 metadata audit found unit references missing from their certificate" >&2
  sed -n '1,40p' "$WORK_DIR/missing_unit_references.tsv" >&2
  exit 1
fi

: > "$WORK_DIR/future_unit_references.tsv"
while IFS= read -r native_file; do
  awk -v source="$native_file" '
    function remember_line_id() {
      if (match($0, /^  \([[:alnum:]_]+ "([^"]+)"/, step)) {
        seen[step[1]] = FNR
      }
    }

    index($0, "\"kernel_v1\"") != 0 {
      rest = $0
      while (match(rest, /[[:alnum:]_]*unit[[:alnum:]_]*=u[0-9][[:alnum:]_]*/)) {
        token = substr(rest, RSTART, RLENGTH)
        split(token, parts, "=")
        field = parts[1]
        ref = parts[2]
        if (field != "conclusion_unit" && !(ref in seen)) {
          print source ":" FNR "\t" field "\t" ref "\t" $0
        }
        rest = substr(rest, RSTART + RLENGTH)
      }
    }

    {
      remember_line_id()
    }
  ' "$native_file" >> "$WORK_DIR/future_unit_references.tsv"
done < "$WORK_DIR/native_files.txt"

if [[ -s "$WORK_DIR/future_unit_references.tsv" ]]; then
  echo "kernel_v1 metadata audit found premise unit references that are not earlier certificate units" >&2
  sed -n '1,40p' "$WORK_DIR/future_unit_references.tsv" >&2
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
  /rule=skolemize/ || /rule=rectify_formula/ ||
  /rule=formula_copy/ || /rule=formula_normalize/ ||
  /rule=fool_formula/ || /rule=fool_exhaustiveness/ ||
  /rule=avatar_component/ || /rule=avatar_split/ ||
  /rule=avatar_refutation/ || /rule=truth_conflict/ ||
  /rule=predicate_definition/ || /rule=predicate_definition_fold/ ||
  /rule=predicate_definition_fold_chain/ ||
  /rule=avatar_definition/ || /rule=split_dependency/ {
    next
  }
  { print }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/unknown_rules.tsv"

if [[ -s "$WORK_DIR/unknown_rules.tsv" ]]; then
  echo "kernel_v1 metadata audit found unexpected rule names" >&2
  sed -n '1,40p' "$WORK_DIR/unknown_rules.tsv" >&2
  exit 1
fi

require_primitive_expansion_contract() {
  local rule=$1
  local primitive=$2
  local file="$WORK_DIR/${rule}_primitive_expansion.tsv"
  grep -F "\"rule=${rule}\"" "$WORK_DIR/kernel_v1.tsv" > "$file" || true
  if [[ ! -s "$file" ]]; then
    return 0
  fi

  local missing="$WORK_DIR/missing_${rule}_primitive_expansion.tsv"
  : > "$missing"
  for pattern in \
    'primitive_expansion=prefix' \
    'primitive_expansion_prefix=' \
    "primitive_expansion_requires=${primitive}"; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$file" >> "$missing"
  done

  if [[ -s "$missing" ]]; then
    echo "kernel_v1 metadata audit found ${rule} records missing primitive-expansion contract fields" >&2
    sed -n '1,40p' "$missing" >&2
    exit 1
  fi
}

require_primitive_expansion_contract superposition paramodulate
require_primitive_expansion_contract rewrite paramodulate
require_primitive_expansion_contract unit_resulting_resolution resolve
require_primitive_expansion_contract subsumption_resolution resolve
require_primitive_expansion_contract resolution resolve
require_primitive_expansion_contract factoring factor

grep -F 'rule=resolution' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/resolution.tsv" || true

if [[ -s "$WORK_DIR/resolution.tsv" ]]; then
  : > "$WORK_DIR/missing_resolution_fields.tsv"
  for pattern in \
    'selected=' \
    'selected_substituted=' \
    'selected_parent_index=' \
    'selected_literal_index=' \
    'selected_parent_unit=' \
    'other=' \
    'other_substituted=' \
    'other_parent_index=' \
    'other_literal_index=' \
    'other_parent_unit=' \
    'primitive_parent_0_substitution=' \
    'primitive_parent_1_substitution=' \
    'result_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/resolution.tsv" >> "$WORK_DIR/missing_resolution_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_resolution_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found resolution records missing primitive pivot fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_resolution_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=factoring' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/factoring.tsv" || true

if [[ -s "$WORK_DIR/factoring.tsv" ]]; then
  : > "$WORK_DIR/missing_factoring_fields.tsv"
  for pattern in \
    'selected=' \
    'selected_substituted=' \
    'selected_parent_index=' \
    'selected_literal_index=' \
    'selected_parent_unit=' \
    'other=' \
    'other_substituted=' \
    'other_parent_index=' \
    'other_literal_index=' \
    'other_parent_unit=' \
    'primitive_parent_0_substitution=' \
    'result_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/factoring.tsv" >> "$WORK_DIR/missing_factoring_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_factoring_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found factoring records missing primitive pivot fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_factoring_fields.tsv" >&2
    exit 1
  fi
fi

awk 'index($0, "conclusion_clause=") != 0 {print}' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/clausal_kernel.tsv"

if [[ -s "$WORK_DIR/clausal_kernel.tsv" ]]; then
  : > "$WORK_DIR/missing_clausal_kernel_fields.tsv"
  awk 'index($0, "result_clause=") == 0 {print "result_clause=\t" $0}' \
    "$WORK_DIR/clausal_kernel.tsv" >> "$WORK_DIR/missing_clausal_kernel_fields.tsv"
  awk 'index($0, "result_literal_count=") == 0 {print "result_literal_count=\t" $0}' \
    "$WORK_DIR/clausal_kernel.tsv" >> "$WORK_DIR/missing_clausal_kernel_fields.tsv"
  awk '
    {
      if (match($0, /result_literal_count=([0-9]+)/, count_match)) {
        literal_count = count_match[1] + 0
        for (literal_index = 0; literal_index < literal_count; ++literal_index) {
          literal_field = "result_literal_" literal_index "="
          if (index($0, literal_field) == 0) {
            print literal_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/clausal_kernel.tsv" >> "$WORK_DIR/missing_clausal_kernel_fields.tsv"
  awk 'index($0, "result_literal_count=0") == 0 && index($0, "result_literal_0=") == 0 {print "result_literal_0=\t" $0}' \
    "$WORK_DIR/clausal_kernel.tsv" >> "$WORK_DIR/missing_clausal_kernel_fields.tsv"
  awk 'index($0, "result_literal_count=0") != 0 && index($0, "conclusion_clause=(clause)") == 0 {print "nonempty_conclusion_literal_count\t" $0}' \
    "$WORK_DIR/clausal_kernel.tsv" >> "$WORK_DIR/missing_clausal_kernel_fields.tsv"

  if [[ -s "$WORK_DIR/missing_clausal_kernel_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found clausal primitive records missing result literal fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_clausal_kernel_fields.tsv" >&2
    exit 1
  fi
fi

awk 'index($0, "result_formula=") != 0 && index($0, "rule=avatar_split") == 0 {print}' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/formula_kernel.tsv"

if [[ -s "$WORK_DIR/formula_kernel.tsv" ]]; then
  awk 'index($0, "conclusion_formula=") == 0 {print "conclusion_formula=\t" $0}' \
    "$WORK_DIR/formula_kernel.tsv" > "$WORK_DIR/missing_formula_kernel_fields.tsv"

  if [[ -s "$WORK_DIR/missing_formula_kernel_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found formula primitive records missing conclusion formula fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_formula_kernel_fields.tsv" >&2
    exit 1
  fi
fi

awk '
  {
    if (match($0, /"parent_count=([0-9]+)/, parent_count_match)) {
      parent_count = parent_count_match[1] + 0
      for (parent_index = 0; parent_index < parent_count; ++parent_index) {
        clause_field = "parent_" parent_index "_clause="
        if (index($0, clause_field) == 0) {
          print clause_field "\t" $0
        }
        literal_count_field = "parent_" parent_index "_literal_count="
        if (index($0, literal_count_field) == 0) {
          print literal_count_field "\t" $0
          continue
        }
        if (match($0, literal_count_field "([0-9]+)", literal_count_match)) {
          literal_count = literal_count_match[1] + 0
          for (literal_index = 0; literal_index < literal_count; ++literal_index) {
            literal_field = "parent_" parent_index "_literal_" literal_index "="
            if (index($0, literal_field) == 0) {
              print literal_field "\t" $0
            }
          }
        }
      }
    }
  }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_parent_literal_fields.tsv"

if [[ -s "$WORK_DIR/missing_parent_literal_fields.tsv" ]]; then
  echo "kernel_v1 metadata audit found records missing parent literal fields" >&2
  sed -n '1,40p' "$WORK_DIR/missing_parent_literal_fields.tsv" >&2
  exit 1
fi

awk '
  {
    if (match($0, /"parent_count=([0-9]+)/, parent_count_match)) {
      parent_count = parent_count_match[1] + 0
      for (parent_index = 0; parent_index < parent_count; ++parent_index) {
        substitution_field = "parent_" parent_index "_substitution="
        if (index($0, substitution_field) == 0) {
          continue
        }
        literal_count_field = "parent_" parent_index "_substituted_literal_count="
        if (index($0, literal_count_field) == 0) {
          print literal_count_field "\t" $0
          continue
        }
        if (match($0, literal_count_field "([0-9]+)", literal_count_match)) {
          literal_count = literal_count_match[1] + 0
          for (literal_index = 0; literal_index < literal_count; ++literal_index) {
            literal_field = "parent_" parent_index "_substituted_literal_" literal_index "="
            if (index($0, literal_field) == 0) {
              print literal_field "\t" $0
            }
          }
        }
      }
    }
  }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_parent_substituted_literal_fields.tsv"

if [[ -s "$WORK_DIR/missing_parent_substituted_literal_fields.tsv" ]]; then
  echo "kernel_v1 metadata audit found records missing substituted parent literal fields" >&2
  sed -n '1,40p' "$WORK_DIR/missing_parent_substituted_literal_fields.tsv" >&2
  exit 1
fi

awk '
  {
    if (match($0, /proof_parent_count=([0-9]+)/, parent_count_match)) {
      if (index($0, "rule=cnf_clause") != 0) {
        next
      }
      parent_count = parent_count_match[1] + 0
      if (index($0, "source_unit=") == 0) {
        print "source_unit=\t" $0
      }
      if (index($0, "result_formula=") == 0) {
        print "result_formula=\t" $0
      }
      for (parent_index = 0; parent_index < parent_count; ++parent_index) {
        unit_field = "parent_" parent_index "_unit="
        formula_field = "parent_" parent_index "_formula="
        if (index($0, unit_field) == 0) {
          print unit_field "\t" $0
        }
        if (index($0, formula_field) == 0) {
          print formula_field "\t" $0
        }
      }
    }
  }
' "$WORK_DIR/kernel_v1.tsv" > "$WORK_DIR/missing_formula_parent_fields.tsv"

if [[ -s "$WORK_DIR/missing_formula_parent_fields.tsv" ]]; then
  echo "kernel_v1 metadata audit found formula transformation records missing parent formula fields" >&2
  sed -n '1,40p' "$WORK_DIR/missing_formula_parent_fields.tsv" >&2
  exit 1
fi

grep -F '"rule=superposition"' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/superposition.tsv" || true

if [[ -s "$WORK_DIR/superposition.tsv" ]]; then
  : > "$WORK_DIR/missing_superposition_fields.tsv"
  for pattern in \
    'selected=' \
    'selected_substituted=' \
    'selected_parent_index=' \
    'selected_literal_index=' \
    'selected_parent_unit=' \
    'other=' \
    'other_substituted=' \
    'other_parent_index=' \
    'other_literal_index=' \
    'other_parent_unit=' \
    'rewrite_lhs=' \
    'rewrite_redex=' \
    'target_substituted=' \
    'equality_substituted=' \
    'target_parent_index=' \
    'target_literal_index=' \
    'equality_parent_index=' \
    'equality_literal_index=' \
    'rewrite_direction=' \
    'rewrite_position=' \
    'from=' \
    'to=' \
    'rewritten_target=' \
    'primitive_parent_0_substitution=' \
    'primitive_parent_1_substitution=' \
    'result_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/superposition.tsv" >> "$WORK_DIR/missing_superposition_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_superposition_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found superposition records missing rewrite fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_superposition_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=subsumption_resolution' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/subsumption_resolution.tsv" || true

if [[ -s "$WORK_DIR/subsumption_resolution.tsv" ]]; then
  : > "$WORK_DIR/missing_subsumption_resolution_fields.tsv"
  for pattern in \
    'selected=' \
    'selected_substituted=' \
    'selected_parent_index=' \
    'selected_literal_index=' \
    'selected_parent_unit=' \
    'main_parent_index=' \
    'side_parent_index=' \
    'side_substitution=' \
    'side_pivot=' \
    'side_pivot_substituted=' \
    'side_pivot_parent_index=' \
    'side_pivot_literal_index=' \
    'side_pivot_parent_unit=' \
    'result_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/subsumption_resolution.tsv" >> "$WORK_DIR/missing_subsumption_resolution_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_subsumption_resolution_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found subsumption-resolution records missing side-pivot fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_subsumption_resolution_fields.tsv" >&2
    exit 1
  fi
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

  awk '
    {
      if (match($0, /introduced_count=([0-9]+)/, introduced_count_match)) {
        introduced_count = introduced_count_match[1] + 0
        for (introduced_index = 0; introduced_index < introduced_count; ++introduced_index) {
          prefix = "introduced_" introduced_index
          kind_field = prefix "_kind="
          raw_symbol_field = prefix "_raw_symbol="
          symbol_field = "introduced_" introduced_index "_symbol="
          replaced_var_field = prefix "_replaced_var="
          declaration_field = prefix "_declaration="
          if (index($0, kind_field) == 0) {
            print kind_field "\t" $0
          }
          if (index($0, raw_symbol_field) == 0) {
            print raw_symbol_field "\t" $0
          }
          if (index($0, symbol_field) == 0) {
            print symbol_field "\t" $0
          }
          if (index($0, replaced_var_field) == 0) {
            print replaced_var_field "\t" $0
          }
          if (index($0, declaration_field) == 0) {
            print declaration_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/skolemize.tsv" > "$WORK_DIR/missing_skolemize_map_fields.tsv"

  if [[ -s "$WORK_DIR/missing_skolemize_map_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found skolemization maps with missing indexed fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_skolemize_map_fields.tsv" >&2
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
  awk '
    {
      if (match($0, /renaming_count=([0-9]+)/, renaming_count_match)) {
        renaming_count = renaming_count_match[1] + 0
        for (renaming_index = 0; renaming_index < renaming_count; ++renaming_index) {
          source_field = "renaming_" renaming_index "_source="
          target_field = "renaming_" renaming_index "_target="
          substitution_field = "renaming_" renaming_index "_substitution="
          if (index($0, source_field) == 0) {
            print source_field "\t" $0
          }
          if (index($0, target_field) == 0) {
            print target_field "\t" $0
          }
          if (index($0, substitution_field) == 0) {
            print substitution_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/rectify_formula.tsv" >> "$WORK_DIR/missing_rectify_formula_fields.tsv"

  if [[ -s "$WORK_DIR/missing_rectify_formula_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found rectification records missing transformation fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_rectify_formula_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=formula_copy' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/formula_copy.tsv" || true

if [[ -s "$WORK_DIR/formula_copy.tsv" ]]; then
  : > "$WORK_DIR/missing_formula_copy_fields.tsv"
  for pattern in \
    'source_unit=' \
    'proof_parent_count=1' \
    'source_formula=' \
    'result_formula=' \
    'copy_kind=formula_term_identity'; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/formula_copy.tsv" >> "$WORK_DIR/missing_formula_copy_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_formula_copy_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found formula-copy records missing identity fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_formula_copy_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=formula_normalize' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/formula_normalize.tsv" || true

if [[ -s "$WORK_DIR/formula_normalize.tsv" ]]; then
  : > "$WORK_DIR/missing_formula_normalize_fields.tsv"
  for pattern in \
    'source_unit=' \
    'proof_parent_count=1' \
    'source_formula=' \
    'result_formula=' \
    'normal_form_rule=' \
    'transformation_pair_count=' \
    'pair_0_source=' \
    'pair_0_target=' \
    'pair_0_path='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/formula_normalize.tsv" >> "$WORK_DIR/missing_formula_normalize_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_formula_normalize_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found formula-normalization records missing transformation fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_formula_normalize_fields.tsv" >&2
    exit 1
  fi

  awk '
    {
      if (match($0, /transformation_pair_count=([0-9]+)/, pair_count_match)) {
        pair_count = pair_count_match[1] + 0
        for (pair_index = 0; pair_index < pair_count; ++pair_index) {
          source_field = "pair_" pair_index "_source="
          target_field = "pair_" pair_index "_target="
          path_field = "pair_" pair_index "_path="
          if (index($0, source_field) == 0) {
            print source_field "\t" $0
          }
          if (index($0, target_field) == 0) {
            print target_field "\t" $0
          }
          if (index($0, path_field) == 0) {
            print path_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/formula_normalize.tsv" > "$WORK_DIR/missing_formula_normalize_map_fields.tsv"

  if [[ -s "$WORK_DIR/missing_formula_normalize_map_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found formula-normalization maps with missing indexed fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_formula_normalize_map_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=fool_formula' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/fool_formula.tsv" || true

if [[ -s "$WORK_DIR/fool_formula.tsv" ]]; then
  : > "$WORK_DIR/missing_fool_formula_fields.tsv"
  for pattern in \
    'source_unit=' \
    'proof_parent_count=1' \
    'source_formula=' \
    'result_formula=' \
    'transformation_pair_count=' \
    'pair_0_source=' \
    'pair_0_target=' \
    'pair_0_path='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/fool_formula.tsv" >> "$WORK_DIR/missing_fool_formula_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_fool_formula_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found FOOL formula records missing transformation fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_fool_formula_fields.tsv" >&2
    exit 1
  fi

  awk '
    {
      if (match($0, /transformation_pair_count=([0-9]+)/, pair_count_match)) {
        pair_count = pair_count_match[1] + 0
        for (pair_index = 0; pair_index < pair_count; ++pair_index) {
          source_field = "pair_" pair_index "_source="
          target_field = "pair_" pair_index "_target="
          path_field = "pair_" pair_index "_path="
          if (index($0, source_field) == 0) {
            print source_field "\t" $0
          }
          if (index($0, target_field) == 0) {
            print target_field "\t" $0
          }
          if (index($0, path_field) == 0) {
            print path_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/fool_formula.tsv" > "$WORK_DIR/missing_fool_formula_map_fields.tsv"

  if [[ -s "$WORK_DIR/missing_fool_formula_map_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found FOOL formula maps with missing indexed fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_fool_formula_map_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=fool_exhaustiveness' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/fool_exhaustiveness.tsv" || true

if [[ -s "$WORK_DIR/fool_exhaustiveness.tsv" ]]; then
  : > "$WORK_DIR/missing_fool_exhaustiveness_fields.tsv"
  for pattern in \
    'axiom_kind=all_is_true_or_false' \
    'parent_count=0' \
    'conclusion_clause=' \
    'result_clause=' \
    'literal_count=2' \
    'literal_0=' \
    'literal_1='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/fool_exhaustiveness.tsv" >> "$WORK_DIR/missing_fool_exhaustiveness_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_fool_exhaustiveness_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found FOOL exhaustiveness records missing axiom fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_fool_exhaustiveness_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=avatar_component' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/avatar_component.tsv" || true

if [[ -s "$WORK_DIR/avatar_component.tsv" ]]; then
  : > "$WORK_DIR/missing_avatar_component_fields.tsv"
  for pattern in \
    'conclusion_clause=' \
    'result_clause=' \
    'literal_count=' \
    'literal_0=' \
    'split_count=' \
    'split_0_level=' \
    'split_0_var=' \
    'split_0_positive='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/avatar_component.tsv" >> "$WORK_DIR/missing_avatar_component_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_avatar_component_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR component records missing split fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_avatar_component_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=avatar_split' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/avatar_split.tsv" || true

if [[ -s "$WORK_DIR/avatar_split.tsv" ]]; then
  : > "$WORK_DIR/missing_avatar_split_fields.tsv"
  for pattern in \
    'source_unit=' \
    'source_clause=' \
    'previous_split_count=' \
    'sat_literal_count=' \
    'sat_literal_0_var=' \
    'sat_literal_0_positive=' \
    'component_parent_count=' \
    'component_parent_ref_count=' \
    'literal_class_count=' \
    'parent_var_binding_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/avatar_split.tsv" >> "$WORK_DIR/missing_avatar_split_fields.tsv"
  done

  awk '
    {
      if (match($0, /component_parent_ref_count=([0-9]+)/, ref_count_match)) {
        ref_count = ref_count_match[1] + 0
        for (ref_index = 0; ref_index < ref_count; ++ref_index) {
          prefix = "component_parent_ref_" ref_index
          unit_field = prefix "_unit=u"
          split_level_field = prefix "_split_level="
          split_var_field = prefix "_split_var="
          split_positive_field = prefix "_split_positive="
          clause_field = prefix "_clause="
          if (index($0, unit_field) == 0) {
            print unit_field "\t" $0
          }
          if (index($0, split_level_field) == 0) {
            print split_level_field "\t" $0
          }
          if (index($0, split_var_field) == 0) {
            print split_var_field "\t" $0
          }
          if (index($0, split_positive_field) == 0) {
            print split_positive_field "\t" $0
          }
          if (index($0, clause_field) == 0) {
            print clause_field "\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/avatar_split.tsv" >> "$WORK_DIR/missing_avatar_split_fields.tsv"

  awk '
    {
      if (match($0, /literal_class_count=([0-9]+)/, class_count_match)) {
        class_count = class_count_match[1] + 0
        for (class_index = 0; class_index < class_count; ++class_index) {
          class_prefix = "literal_class_" class_index
          literal_count_field = class_prefix "_literal_count="
          if (!match($0, class_prefix "_literal_count=([0-9]+)", literal_count_match)) {
            print literal_count_field "\t" $0
            continue
          }
          literal_count = literal_count_match[1] + 0
          for (literal_index = 0; literal_index < literal_count; ++literal_index) {
            literal_field = class_prefix "_literal_" literal_index "="
            if (index($0, literal_field) == 0) {
              print literal_field "\t" $0
            }
          }
        }
      }
      if (match($0, /parent_var_binding_count=([0-9]+)/, binding_count_match)) {
        binding_count = binding_count_match[1] + 0
        for (binding_index = 0; binding_index < binding_count; ++binding_index) {
          binding_prefix = "parent_var_binding_" binding_index
          parent_var_field = binding_prefix "_parent_var="
          if (index($0, parent_var_field) == 0) {
            print parent_var_field "\t" $0
          }
          if (index($0, binding_prefix "_component_var=") == 0 &&
              index($0, binding_prefix "_split_var=") == 0) {
            print binding_prefix "_component_var|split_var=\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/avatar_split.tsv" >> "$WORK_DIR/missing_avatar_split_fields.tsv"

  awk '
    index($0, "result_clause=") == 0 &&
    index($0, "result_formula=") == 0 {
      print "result_clause|result_formula\t" $0
    }
  ' "$WORK_DIR/avatar_split.tsv" >> "$WORK_DIR/missing_avatar_split_fields.tsv"

  if [[ -s "$WORK_DIR/missing_avatar_split_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR split records missing split fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_avatar_split_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=avatar_refutation' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/avatar_refutation.tsv" || true

if [[ -s "$WORK_DIR/avatar_refutation.tsv" ]]; then
  : > "$WORK_DIR/missing_avatar_refutation_fields.tsv"
  for pattern in \
    'result_clause=' \
    'sat_input_count=' \
    'sat_input_0_clause=' \
    'sat_input_0_origin_unit=' \
    'sat_proof_step_count=' \
    'sat_proof_step_0_id=' \
    'sat_proof_step_0_kind=' \
    'sat_proof_step_0_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/avatar_refutation.tsv" >> "$WORK_DIR/missing_avatar_refutation_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_avatar_refutation_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR refutation records missing SAT proof fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_avatar_refutation_fields.tsv" >&2
    exit 1
  fi

  awk '
    {
      if (match($0, /sat_input_count=([0-9]+)/, input_count_match)) {
        input_count = input_count_match[1] + 0
        for (input_index = 0; input_index < input_count; ++input_index) {
          input_prefix = "sat_input_" input_index
          if (index($0, input_prefix "_clause=") == 0) {
            print input_prefix "_clause=\t" $0
          }
          if (index($0, input_prefix "_origin_unit=") == 0) {
            print input_prefix "_origin_unit=\t" $0
          }
        }
      }
      if (match($0, /sat_proof_step_count=([0-9]+)/, step_count_match)) {
        step_count = step_count_match[1] + 0
        for (step_index = 0; step_index < step_count; ++step_index) {
          step_prefix = "sat_proof_step_" step_index
          if (index($0, step_prefix "_id=") == 0) {
            print step_prefix "_id=\t" $0
          }
          if (index($0, step_prefix "_kind=") == 0) {
            print step_prefix "_kind=\t" $0
          }
          if (index($0, step_prefix "_clause=") == 0) {
            print step_prefix "_clause=\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/avatar_refutation.tsv" > "$WORK_DIR/missing_sat_map_fields.tsv"

  if [[ -s "$WORK_DIR/missing_sat_map_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR SAT maps with missing indexed fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_sat_map_fields.tsv" >&2
    exit 1
  fi

  awk '
    {
      delete proof_ids
      if (!match($0, /sat_proof_step_count=([0-9]+)/, step_count_match)) {
        next
      }
      step_count = step_count_match[1] + 0
      for (step_index = 0; step_index < step_count; ++step_index) {
        step_prefix = "sat_proof_step_" step_index
        if (match($0, step_prefix "_id=([0-9]+)", step_id_match)) {
          proof_ids[step_id_match[1]] = step_index
        }
      }
      for (step_index = 0; step_index < step_count; ++step_index) {
        step_prefix = "sat_proof_step_" step_index
        if (index($0, step_prefix "_kind=rup") == 0) {
          continue
        }
        if (!match($0, step_prefix "_parent_count=([0-9]+)", parent_count_match)) {
          print step_prefix "_parent_count=\t" $0
          continue
        }
        parent_count = parent_count_match[1] + 0
        for (parent_index = 0; parent_index < parent_count; ++parent_index) {
          parent_prefix = step_prefix "_parent_" parent_index
          if (!match($0, parent_prefix "_id=([0-9]+)", parent_id_match)) {
            print parent_prefix "_id=\t" $0
            continue
          }
          if (!(parent_id_match[1] in proof_ids)) {
            print parent_prefix "_id_unknown\t" parent_id_match[1] "\t" $0
          } else if (proof_ids[parent_id_match[1]] >= step_index) {
            print parent_prefix "_id_not_earlier\t" parent_id_match[1] "\t" $0
          }
          if (index($0, parent_prefix "_clause=") == 0) {
            print parent_prefix "_clause=\t" $0
          }
        }
      }
    }
  ' "$WORK_DIR/avatar_refutation.tsv" > "$WORK_DIR/missing_sat_proof_parent_fields.tsv"

  if [[ -s "$WORK_DIR/missing_sat_proof_parent_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR SAT proof records missing parent proof fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_sat_proof_parent_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=truth_conflict' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/truth_conflict.tsv" || true

if [[ -s "$WORK_DIR/truth_conflict.tsv" ]]; then
  : > "$WORK_DIR/missing_truth_conflict_fields.tsv"
  for pattern in \
    'parent_0_clause=' \
    'selected=' \
    'selected_substituted=' \
    'selected_parent_index=0' \
    'selected_literal_index=' \
    'result_clause='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/truth_conflict.tsv" >> "$WORK_DIR/missing_truth_conflict_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_truth_conflict_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found truth-conflict records missing selected/result fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_truth_conflict_fields.tsv" >&2
    exit 1
  fi
fi

grep -F '"rule=predicate_definition"' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/predicate_definition.tsv" || true

if [[ -s "$WORK_DIR/predicate_definition.tsv" ]]; then
  : > "$WORK_DIR/missing_predicate_definition_fields.tsv"
  for pattern in \
    'introduced_symbol=' \
    'definiendum_symbol=' \
    'result_formula=' \
    'body_variable_sort_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/predicate_definition.tsv" >> "$WORK_DIR/missing_predicate_definition_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_predicate_definition_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found predicate-definition records missing symbol/formula fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_predicate_definition_fields.tsv" >&2
    exit 1
  fi
fi

grep -E '"rule=predicate_definition_fold(_chain)?"' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/predicate_definition_fold.tsv" || true

if [[ -s "$WORK_DIR/predicate_definition_fold.tsv" ]]; then
  : > "$WORK_DIR/missing_predicate_definition_fold_fields.tsv"
  for pattern in \
    'source_unit=' \
    'source_formula=' \
    'definition_count=' \
    'definition_0_unit=' \
    'definition_0_formula=' \
    'definition_0_symbol=' \
    'result_formula='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/predicate_definition_fold.tsv" >> "$WORK_DIR/missing_predicate_definition_fold_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_predicate_definition_fold_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found predicate-definition fold records missing source/definition/result fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_predicate_definition_fold_fields.tsv" >&2
    exit 1
  fi
fi

grep -F '"rule=avatar_definition"' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/avatar_definition.tsv" || true

if [[ -s "$WORK_DIR/avatar_definition.tsv" ]]; then
  : > "$WORK_DIR/missing_avatar_definition_fields.tsv"
  for pattern in \
    'result_clause=' \
    'component_split_level=' \
    'component_split_var=' \
    'component_split_positive=' \
    'component_clause_sexpr=' \
    'component_clause_variable_sort_count=' \
    'component_clause_db_sort_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/avatar_definition.tsv" >> "$WORK_DIR/missing_avatar_definition_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_avatar_definition_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found AVATAR definition records missing component fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_avatar_definition_fields.tsv" >&2
    exit 1
  fi
fi

grep -F '"rule=split_dependency"' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/split_dependency.tsv" || true

if [[ -s "$WORK_DIR/split_dependency.tsv" ]]; then
  : > "$WORK_DIR/missing_split_dependency_fields.tsv"
  for pattern in \
    'result_clause=' \
    'dependency_count=' \
    'dependency_0_split_level=' \
    'dependency_0_split_var=' \
    'dependency_0_split_positive=' \
    'dependency_0_component_clause_sexpr=' \
    'dependency_0_component_clause_variable_sort_count=' \
    'dependency_0_component_clause_db_sort_count='; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$WORK_DIR/split_dependency.tsv" >> "$WORK_DIR/missing_split_dependency_fields.tsv"
  done

  if [[ -s "$WORK_DIR/missing_split_dependency_fields.tsv" ]]; then
    echo "kernel_v1 metadata audit found split-dependency records missing component/result fields" >&2
    sed -n '1,40p' "$WORK_DIR/missing_split_dependency_fields.tsv" >&2
    exit 1
  fi
fi

grep -F 'rule=cnf_clause' "$WORK_DIR/kernel_v1.tsv" \
  > "$WORK_DIR/cnf_clause.tsv" || true

if [[ -s "$WORK_DIR/cnf_clause.tsv" ]]; then
  : > "$WORK_DIR/missing_cnf_clause_fields.tsv"
  for pattern in \
    'source_unit=' \
    'parent_0_unit=' \
    'proof_parent_count=1' \
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
  awk 'index($0, "parent_0_formula=") == 0 && index($0, "parent_0_clause=") == 0 {print "parent_0_formula_or_clause=\t" $0}' \
    "$WORK_DIR/cnf_clause.tsv" >> "$WORK_DIR/missing_cnf_clause_fields.tsv"
  awk 'index($0, "source_kind=formula") != 0 && index($0, "parent_0_formula=") == 0 {print "parent_0_formula=\t" $0}' \
    "$WORK_DIR/cnf_clause.tsv" >> "$WORK_DIR/missing_cnf_clause_fields.tsv"
  awk 'index($0, "source_kind=clause") != 0 && index($0, "parent_0_clause=") == 0 {print "parent_0_clause=\t" $0}' \
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
