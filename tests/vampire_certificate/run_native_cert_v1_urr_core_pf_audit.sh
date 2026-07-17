#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
CASE_LIST=${CASE_LIST:-}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_urr_core_pf_audit.XXXXXX")"}
JOBS=${JOBS:-10}
MIN_URR_CORE_PF=${MIN_URR_CORE_PF:-1}
ORIGIN_CONTEXT_CASES=${ORIGIN_CONTEXT_CASES:-hammer.11453.77}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_urr_core_pf_audit"

case_list="$WORK_DIR/urr_core_pf_cases.list"
: > "$case_list"
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
      echo "listed URR native core proof-term certificate does not exist: $raw" >&2
      exit 2
    fi
    printf '%s\n' "$native" >> "$case_list"
  done < "$CASE_LIST"
else
  find "$CASES_DIR" -maxdepth 1 -type f -name '*.native.sexp' -size +0 -print0 \
    | xargs -0 -r rg -l 'rule=unit_resulting_resolution' \
    | sort > "$case_list"
fi

if [[ ! -s "$case_list" ]]; then
  echo "no URR native core proof-term cases selected" >&2
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
    printf '%s\tURR_CORE_PF_MISSING_SOURCE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'primitive_expansion_step_[0-9]+_rule=resolve' "$native"; then
    printf '%s\tURR_CORE_PF_MISSING_PRIMITIVE_RESOLVE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! "$MEGALODON" \
      -vampirecertv1sourcecontext \
      -vampirecertv1corepfcheck \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      "$case_dir/dummy.mg" > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tURR_CORE_PF_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'native core proof term checked' "$case_dir/check.out"; then
    printf '%s\tURR_CORE_PF_MISSING_CONFIRMATION\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'Vampire certificate v1 source origin ' "$case_dir/check.out"; then
    printf '%s\tURR_CORE_PF_MISSING_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q 'Vampire certificate v1 native core source bindings checked ' "$case_dir/check.out"; then
    printf '%s\tURR_CORE_PF_MISSING_SOURCE_BINDINGS\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  local remaining_by_kind
  remaining_by_kind=$(sed -n 's/^Vampire certificate v1 native core source assumptions remaining by kind //p' "$case_dir/check.out" | tail -1)
  if [[ -z "$remaining_by_kind" ]]; then
    remaining_by_kind="unknown"
  fi
  local source_issues
  source_issues=$(sed -n 's/^Vampire certificate v1 source context issues //p' "$case_dir/check.out" | tail -1)
  if [[ -z "$source_issues" ]]; then
    source_issues="not-audited"
  fi

  printf '%s\tURR_CORE_PF_PASS\t%s\t%s\n' "$base" "$remaining_by_kind" "$source_issues" > "$case_dir/result.tsv"
}

export MEGALODON CASES_DIR WORK_DIR
export -f run_one

xargs -r -P "$JOBS" -n 1 bash -c 'run_one "$1"' bash < "$case_list"

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | sort -z \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" | sort | tee "$WORK_DIR/counts.txt"

pass_count=$(awk -F '\t' '$2 == "URR_CORE_PF_PASS" {count++} END {print count + 0}' "$WORK_DIR/summary.tsv")
if (( pass_count < MIN_URR_CORE_PF )); then
  echo "native certificate v1 URR core proof-term audit has fewer than $MIN_URR_CORE_PF passes" >&2
  sed -n '1,80p' "$WORK_DIR/summary.tsv" >&2
  exit 1
fi

if awk -F '\t' '$2 != "URR_CORE_PF_PASS" {bad=1} END {exit bad ? 0 : 1}' "$WORK_DIR/summary.tsv"; then
  echo "native certificate v1 URR core proof-term audit has failures" >&2
  sed -n '1,80p' "$WORK_DIR/summary.tsv" >&2
  exit 1
fi

origin_loaded_dir="$WORK_DIR/origin_loaded"
mkdir -p "$origin_loaded_dir"
: > "$origin_loaded_dir/summary.tsv"
for base in $ORIGIN_CONTEXT_CASES; do
  native="$CASES_DIR/$base.native.sexp"
  source="$CASES_DIR/$base.th0.p"
  origin="$ROOT/examples/hammer/100thms_12_h.mg"
  case_dir="$origin_loaded_dir/$base"
  mkdir -p "$case_dir"
  if [[ ! -s "$native" || ! -s "$source" || ! -s "$origin" ]]; then
    printf '%s\tORIGIN_CORE_PF_MISSING_INPUT\n' "$base" >> "$origin_loaded_dir/summary.tsv"
    continue
  fi
  if ! "$MEGALODON" \
      -allowincompleteqed \
      -vampirecertv1sourcecontext \
      -vampirecertv1corepfcheck \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      "$origin" > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tORIGIN_CORE_PF_FAIL\t%s\n' "$base" "$err" >> "$origin_loaded_dir/summary.tsv"
    continue
  fi
  if ! rg -q 'Vampire certificate v1 native core proof term checked ' "$case_dir/check.out"; then
    printf '%s\tORIGIN_CORE_PF_MISSING_CONFIRMATION\n' "$base" >> "$origin_loaded_dir/summary.tsv"
    continue
  fi
  if ! rg -q 'Vampire certificate v1 native core source assumptions remaining by kind known=0 local=0 definition=0 generated=0 conjecture=1 unresolved=0' "$case_dir/check.out"; then
    printf '%s\tORIGIN_CORE_PF_UNEXPECTED_SOURCE_SUMMARY\n' "$base" >> "$origin_loaded_dir/summary.tsv"
    continue
  fi
  printf '%s\tORIGIN_CORE_PF_PASS\n' "$base" >> "$origin_loaded_dir/summary.tsv"
done

cat "$origin_loaded_dir/summary.tsv" | sort | tee "$origin_loaded_dir/counts.txt"
if awk -F '\t' '$2 != "ORIGIN_CORE_PF_PASS" {bad=1} END {exit bad ? 0 : 1}' "$origin_loaded_dir/summary.tsv"; then
  echo "native certificate v1 origin-loaded core proof-term regression has failures" >&2
  sed -n '1,80p' "$origin_loaded_dir/summary.tsv" >&2
  exit 1
fi

echo "native certificate v1 URR core proof-term audit artifacts: $WORK_DIR"
echo "native certificate v1 URR core proof-term audit latest link: $TMPDIR/latest_native_cert_v1_urr_core_pf_audit"
