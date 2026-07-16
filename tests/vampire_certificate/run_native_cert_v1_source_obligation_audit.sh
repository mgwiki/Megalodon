#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
CASE_LIST=${CASE_LIST:-}
DEFAULT_CASE_LIST=${DEFAULT_CASE_LIST:-"$ROOT/tests/vampire_certificate/closed_textual_pass_cases.list"}
JOBS=${JOBS:-10}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_source_obligations.XXXXXX")"}
STRICT=${STRICT:-0}
MIN_AUDIT_PASS=${MIN_AUDIT_PASS:-1}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_source_obligations"

selected_cases="$WORK_DIR/selected_native_cases.list"
: > "$selected_cases"
if [[ -z "$CASE_LIST" && -s "$DEFAULT_CASE_LIST" ]]; then
  CASE_LIST="$DEFAULT_CASE_LIST"
fi

if [[ -n "$CASE_LIST" ]]; then
  while IFS= read -r raw || [[ -n "$raw" ]]; do
    raw="${raw%%#*}"
    raw="${raw#"${raw%%[![:space:]]*}"}"
    raw="${raw%"${raw##*[![:space:]]}"}"
    [[ -z "$raw" ]] && continue
    if [[ "$raw" = /* ]]; then
      native="$raw"
    elif [[ "$raw" == *.native.sexp ]]; then
      native="$CASES_DIR/$raw"
    elif [[ "$raw" == *.th0.p ]]; then
      native="$CASES_DIR/${raw%.th0.p}.native.sexp"
    else
      native="$CASES_DIR/$raw.native.sexp"
    fi
    if [[ ! -s "$native" ]]; then
      echo "listed source-obligation certificate does not exist: $raw" >&2
      exit 2
    fi
    printf '%s\n' "$native" >> "$selected_cases"
  done < "$CASE_LIST"
else
  find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f \
    | sort > "$selected_cases"
fi

if [[ ! -s "$selected_cases" ]]; then
  echo "no source-obligation certificate cases selected" >&2
  exit 2
fi

run_one() {
  local native=$1
  local base
  base=$(basename "$native" .native.sexp)
  local source="$CASES_DIR/$base.th0.p"
  local case_dir="$WORK_DIR/cases/$base"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -s "$source" ]]; then
    printf '%s\tMISSING_SOURCE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  local args=(-vampirecertv1sourceaudit -vampirecertv1 "$native" -vampirecertv1source "$source")
  if [[ "$STRICT" == "1" ]]; then
    args=(-vampirecertv1strict "${args[@]}")
  fi

  if ! "$MEGALODON" "${args[@]}" "$case_dir/dummy.mg" \
      > "$case_dir/audit.out" 2> "$case_dir/audit.err"; then
    local err
    err=$(tail -1 "$case_dir/audit.err" | tr '\t' ' ')
    printf '%s\tAUDIT_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  local line
  line=$(rg 'Vampire certificate v1 source obligations audited ' "$case_dir/audit.out" || true)
  if [[ -z "$line" ]]; then
    printf '%s\tAUDIT_MISSING_OUTPUT\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  local total formula_checked formula_unsupported formula_missing equality_checked set_reflexivity_checked true_checked
  total=$(sed -n 's/.*total=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  formula_checked=$(sed -n 's/.*formula_checked=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  formula_unsupported=$(sed -n 's/.*formula_unsupported=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  formula_missing=$(sed -n 's/.*formula_missing=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  equality_checked=$(sed -n 's/.*equality_checked=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  set_reflexivity_checked=$(sed -n 's/.*set_reflexivity_checked=\([0-9][0-9]*\).*/\1/p' <<< "$line")
  true_checked=$(sed -n 's/.*true_checked=\([0-9][0-9]*\).*/\1/p' <<< "$line")

  if [[ -z "$total" || -z "$formula_checked" || -z "$formula_unsupported" || -z "$formula_missing" ||
        -z "$equality_checked" || -z "$set_reflexivity_checked" || -z "$true_checked" ]]; then
    printf '%s\tAUDIT_PARSE_FAIL\t%s\n' "$base" "$line" > "$case_dir/result.tsv"
    return 0
  fi

  printf '%s\tAUDIT_PASS\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$base" \
    "$total" \
    "$formula_checked" \
    "$formula_unsupported" \
    "$formula_missing" \
    "$equality_checked" \
    "$set_reflexivity_checked" \
    "$true_checked" > "$case_dir/result.tsv"
}

export MEGALODON CASES_DIR WORK_DIR STRICT
export -f run_one

xargs -a "$selected_cases" -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort > "$WORK_DIR/counts.txt"

awk -F '\t' '
  $2 == "AUDIT_PASS" {
    cases++;
    total += $3;
    formula_checked += $4;
    formula_unsupported += $5;
    formula_missing += $6;
    equality_checked += $7;
    set_reflexivity_checked += $8;
    true_checked += $9;
  }
  END {
    printf "cases %d\n", cases + 0;
    printf "total %d\n", total + 0;
    printf "formula_checked %d\n", formula_checked + 0;
    printf "formula_unsupported %d\n", formula_unsupported + 0;
    printf "formula_missing %d\n", formula_missing + 0;
    printf "equality_checked %d\n", equality_checked + 0;
    printf "set_reflexivity_checked %d\n", set_reflexivity_checked + 0;
    printf "true_checked %d\n", true_checked + 0;
  }
' "$WORK_DIR/summary.tsv" > "$WORK_DIR/totals.txt"

cat "$WORK_DIR/counts.txt"
cat "$WORK_DIR/totals.txt"
echo "native certificate v1 source-obligation selected cases: $selected_cases"
echo "native certificate v1 source-obligation artifacts: $WORK_DIR"
echo "native certificate v1 source-obligation latest link: $TMPDIR/latest_native_cert_v1_source_obligations"

pass_count=$(awk -F '\t' '$2 == "AUDIT_PASS" {count++} END {print count + 0}' "$WORK_DIR/summary.tsv")
if (( pass_count < MIN_AUDIT_PASS )); then
  echo "native certificate v1 source-obligation audit has fewer than $MIN_AUDIT_PASS passes" >&2
  sed -n '1,40p' "$WORK_DIR/summary.tsv" >&2
  exit 1
fi

