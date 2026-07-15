#!/usr/bin/env bash
set -euo pipefail

TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_primitive_audit.XXXXXX")"}
MIN_SUBSTITUTE=${MIN_SUBSTITUTE:-1}
MIN_PARAMODULATE=${MIN_PARAMODULATE:-1}
MIN_EQUALITY_SYMMETRY=${MIN_EQUALITY_SYMMETRY:-1}
MIN_EQUALITY_RESOLUTION=${MIN_EQUALITY_RESOLUTION:-1}
MIN_RESOLVE=${MIN_RESOLVE:-1}
MIN_FACTOR=${MIN_FACTOR:-1}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_primitive_audit"

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
  echo "no native.sexp files found for native primitive audit" >&2
  exit 2
fi

collect_rule() {
  local rule=$1
  local out=$2
  xargs -a "$WORK_DIR/native_files.txt" \
    rg -n "^  \\(${rule} " \
    > "$out" || true
}

require_min() {
  local label=$1
  local file=$2
  local min_count=$3
  local count
  count=$(wc -l < "$file")
  if (( count < min_count )); then
    echo "native primitive audit found $count $label records, below minimum $min_count" >&2
    sed -n '1,40p' "$WORK_DIR/native_files.txt" >&2
    exit 1
  fi
  printf '%s %s\n' "$label" "$count" >> "$WORK_DIR/rule_counts.txt"
}

require_fields() {
  local label=$1
  local file=$2
  shift 2
  local missing="$WORK_DIR/missing_${label}_fields.tsv"
  : > "$missing"

  local pattern
  for pattern in "$@"; do
    awk -v pat="$pattern" 'index($0, pat) == 0 {print pat "\t" $0}' \
      "$file" >> "$missing"
  done

  if [[ -s "$missing" ]]; then
    echo "native primitive audit found $label records missing required fields" >&2
    sed -n '1,40p' "$missing" >&2
    exit 1
  fi
}

: > "$WORK_DIR/rule_counts.txt"

collect_rule substitute "$WORK_DIR/substitute.tsv"
collect_rule paramodulate "$WORK_DIR/paramodulate.tsv"
collect_rule equality_symmetry "$WORK_DIR/equality_symmetry.tsv"
collect_rule equality_resolution "$WORK_DIR/equality_resolution.tsv"
collect_rule resolve "$WORK_DIR/resolve.tsv"
collect_rule factor "$WORK_DIR/factor.tsv"

require_min substitute "$WORK_DIR/substitute.tsv" "$MIN_SUBSTITUTE"
require_fields substitute "$WORK_DIR/substitute.tsv" \
  '(parent "' \
  '(subst' \
  '(result (clause'

require_min paramodulate "$WORK_DIR/paramodulate.tsv" "$MIN_PARAMODULATE"
require_fields paramodulate "$WORK_DIR/paramodulate.tsv" \
  '(equality "' \
  '(target "' \
  '(position' \
  '(from ' \
  '(to ' \
  '(result (clause'

require_min equality_symmetry "$WORK_DIR/equality_symmetry.tsv" "$MIN_EQUALITY_SYMMETRY"
require_fields equality_symmetry "$WORK_DIR/equality_symmetry.tsv" \
  '(parent "' \
  '(literal ' \
  '(result (clause'

require_min equality_resolution "$WORK_DIR/equality_resolution.tsv" "$MIN_EQUALITY_RESOLUTION"
require_fields equality_resolution "$WORK_DIR/equality_resolution.tsv" \
  '(parent "' \
  '(literal ' \
  '(result (clause'

require_min resolve "$WORK_DIR/resolve.tsv" "$MIN_RESOLVE"
require_fields resolve "$WORK_DIR/resolve.tsv" \
  '(parents "' \
  '(pivot ' \
  '(result (clause'

require_min factor "$WORK_DIR/factor.tsv" "$MIN_FACTOR"
require_fields factor "$WORK_DIR/factor.tsv" \
  '(parent "' \
  '(literals ' \
  '(result (clause'

parent_errors="$WORK_DIR/primitive_parent_reference_errors.tsv"
: > "$parent_errors"
while IFS= read -r native_file; do
  awk -v source="$native_file" '
    function report(kind, ref, line) {
      if (!(ref in seen)) {
        print source ":" FNR "\t" kind "\t" ref "\t" line
      }
    }

    /^  \([[:alnum:]_]+ "[^"]+"/ {
      line = $0
      if (match(line, /^  \(([[:alnum:]_]+) "([^"]+)"/, step)) {
        rule = step[1]
        id = step[2]

        if (rule == "substitute" ||
            rule == "paramodulate" ||
            rule == "equality_symmetry" ||
            rule == "equality_resolution" ||
            rule == "resolve" ||
            rule == "factor") {
          if (match(line, /\(parent "([^"]+)"/, ref)) {
            report("parent", ref[1], line)
          }
          if (match(line, /\(parents "([^"]+)" "([^"]+)"/, ref)) {
            report("parents", ref[1], line)
            report("parents", ref[2], line)
          }
          if (match(line, /\(equality "([^"]+)"/, ref)) {
            report("equality", ref[1], line)
          }
          if (match(line, /\(target "([^"]+)"/, ref)) {
            report("target", ref[1], line)
          }
        }

        seen[id] = 1
        if (rule != "step_proposition" &&
            rule != "step_variable_sorts" &&
            rule != "step_extra") {
          if (id in proof_step) {
            print source ":" FNR "\tduplicate-proof-step-id\t" id "\t" line
          }
          proof_step[id] = rule
        }
      }
    }
  ' "$native_file" >> "$parent_errors"
done < "$WORK_DIR/native_files.txt"

if [[ -s "$parent_errors" ]]; then
  echo "native primitive audit found dangling, duplicate, or forward primitive parent references" >&2
  sed -n '1,40p' "$parent_errors" >&2
  exit 1
fi

sort -k1,1 "$WORK_DIR/rule_counts.txt" -o "$WORK_DIR/rule_counts.txt"

echo "native primitive records:"
cat "$WORK_DIR/rule_counts.txt"
echo "native primitive audit artifacts: $WORK_DIR"
echo "native primitive audit latest link: $TMPDIR/latest_native_primitive_audit"
