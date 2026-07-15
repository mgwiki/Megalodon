#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_substitution_frontier_audit.XXXXXX")"}
MIN_NONIDENTITY_SUBSTITUTE=${MIN_NONIDENTITY_SUBSTITUTE:-1}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_substitution_frontier_audit"

native_inputs=("$@")
: > "$WORK_DIR/native_files.txt"
if (( ${#native_inputs[@]} == 0 )); then
  find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f >> "$WORK_DIR/native_files.txt"
else
  for input in "${native_inputs[@]}"; do
    if [[ -d "$input/cases" ]]; then
      find -L "$input/cases" -maxdepth 2 -type f -name native.sexp -size +0 \
        >> "$WORK_DIR/native_files.txt"
    elif [[ -d "$input" ]]; then
      find -L "$input" -type f \( -name native.sexp -o -name '*.native.sexp' \) -size +0 \
        >> "$WORK_DIR/native_files.txt"
    elif [[ -f "$input" ]]; then
      printf '%s\n' "$input" >> "$WORK_DIR/native_files.txt"
    else
      echo "warning: missing native substitution audit input: $input" >&2
    fi
  done
fi

sort -u -o "$WORK_DIR/native_files.txt" "$WORK_DIR/native_files.txt"
if [[ ! -s "$WORK_DIR/native_files.txt" ]]; then
  echo "no native certificate files found for substitution frontier audit" >&2
  exit 2
fi

: > "$WORK_DIR/nonidentity_substitutes.tsv"
: > "$WORK_DIR/missing_parent_variable_sorts.tsv"
: > "$WORK_DIR/vacuous_substitution_bindings.tsv"

while IFS= read -r native_file; do
  awk -v source="$native_file" \
      -v out="$WORK_DIR/nonidentity_substitutes.tsv" \
      -v missing="$WORK_DIR/missing_parent_variable_sorts.tsv" \
      -v vacuous="$WORK_DIR/vacuous_substitution_bindings.tsv" '
    function remember_step_variables(line, step_id, rest, var_name) {
      if (match(line, /^  \([A-Za-z_]+ "([^"]+)"/, step)) {
        step_id = step[1]
        rest = line
        while (match(rest, /\(TMH "X[0-9]+"/)) {
          var_name = substr(rest, RSTART + 6, RLENGTH - 7)
          occurs_in_step[step_id, var_name] = 1
          rest = substr(rest, RSTART + RLENGTH)
        }
      }
    }

    /^  \([A-Za-z_]+ "/ && /\(result / {
      remember_step_variables($0)
    }

    /^  \(step_variable_sorts "/ {
      if (match($0, /^  \(step_variable_sorts "([^"]+)"/, step)) {
        parent = step[1]
        rest = $0
        while (match(rest, /"[^":]+:[^"]+"/)) {
          item = substr(rest, RSTART + 1, RLENGTH - 2)
          split(item, parts, ":")
          sort_of[parent, parts[1]] = parts[2]
          rest = substr(rest, RSTART + RLENGTH)
        }
      }
    }

    /^  \(substitute "/ && $0 !~ /\(subst\)/ {
      id = ""
      parent = ""
      if (match($0, /^  \(substitute "([^"]+)"/, step)) {
        id = step[1]
      }
      if (match($0, /\(parent "([^"]+)"/, par)) {
        parent = par[1]
      }
      print source ":" FNR "\t" id "\t" parent "\t" $0 >> out

      subst_part = $0
      sub(/^.*\(subst[[:space:]]*/, "", subst_part)
      sub(/[[:space:]]*\(result[[:space:]].*$/, "", subst_part)
      while (match(subst_part, /\("[^"]+"[[:space:]]/)) {
        binding = substr(subst_part, RSTART + 2, RLENGTH - 4)
        if (parent == "" || ((parent, binding) in occurs_in_step && !((parent, binding) in sort_of))) {
          print source ":" FNR "\t" id "\t" parent "\t" binding "\t" $0 >> missing
        } else if (parent != "" && !((parent, binding) in occurs_in_step)) {
          print source ":" FNR "\t" id "\t" parent "\t" binding "\t" $0 >> vacuous
        }
        subst_part = substr(subst_part, RSTART + RLENGTH)
      }
    }
  ' "$native_file"
done < "$WORK_DIR/native_files.txt"

nonidentity_count=$(wc -l < "$WORK_DIR/nonidentity_substitutes.tsv" | tr -d ' ')
missing_count=$(wc -l < "$WORK_DIR/missing_parent_variable_sorts.tsv" | tr -d ' ')
vacuous_count=$(wc -l < "$WORK_DIR/vacuous_substitution_bindings.tsv" | tr -d ' ')

{
  printf 'NONIDENTITY_SUBSTITUTE %s\n' "$nonidentity_count"
  printf 'MISSING_PARENT_VARIABLE_SORTS %s\n' "$missing_count"
  printf 'VACUOUS_SUBSTITUTION_BINDINGS %s\n' "$vacuous_count"
  printf 'MIN_NONIDENTITY_SUBSTITUTE %s\n' "$MIN_NONIDENTITY_SUBSTITUTE"
} | tee "$WORK_DIR/counts.txt"

echo "native substitution frontier audit artifacts: $WORK_DIR"
echo "native substitution frontier audit latest link: $TMPDIR/latest_native_substitution_frontier_audit"

if (( nonidentity_count < MIN_NONIDENTITY_SUBSTITUTE )); then
  echo "substitution frontier audit found too few non-identity substitutions" >&2
  sed -n '1,40p' "$WORK_DIR/native_files.txt" >&2
  exit 1
fi

if (( missing_count > 0 )); then
  echo "substitution frontier audit found non-identity substitutions without parent variable sorts" >&2
  sed -n '1,40p' "$WORK_DIR/missing_parent_variable_sorts.tsv" >&2
  exit 1
fi
