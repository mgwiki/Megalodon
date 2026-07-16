#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
CASE_LIST=${CASE_LIST:-}
DEFAULT_CASE_LIST=${DEFAULT_CASE_LIST:-"$ROOT/tests/vampire_certificate/closed_textual_pass_cases.list"}
JOBS=${JOBS:-7}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_closed_corpus.XXXXXX")"}
CORE_CERT_V1=${CORE_CERT_V1:-0}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_closed_corpus"

resolve_origin_file() {
  local origin_file=$1
  if [[ "$origin_file" = /* ]]; then
    printf '%s\n' "$origin_file"
  else
    printf '%s/%s\n' "$ROOT" "$origin_file"
  fi
}

read_origin_field() {
  local field=$1
  local source=$2
  sed -n "s/^% megalodon_origin .*${field} \"\\([^\"]*\\)\".*/\\1/p" "$source" | head -1
}

check_origin_consistency() {
  local source=$1
  local emitted=$2
  local report=$3
  local origin_file origin_line origin_char origin_kind resolved_file
  origin_file=$(read_origin_field file "$source")
  origin_line=$(read_origin_field line "$source")
  origin_char=$(read_origin_field char "$source")
  origin_kind=$(read_origin_field kind "$source")

  if [[ -z "$origin_file" || -z "$origin_line" || -z "$origin_char" || -z "$origin_kind" ]]; then
    printf 'source origin is missing one or more fields\n' > "$report"
    return 1
  fi

  case "$origin_kind" in
    generated_*|manual_*)
      ;;
    *)
      resolved_file=$(resolve_origin_file "$origin_file")
      if [[ ! -f "$resolved_file" ]]; then
        printf 'origin file does not exist: %s\n' "$resolved_file" > "$report"
        return 1
      fi
      ;;
  esac

  awk \
      -v file="$origin_file" \
      -v line="$origin_line" \
      -v chr="$origin_char" \
      -v kind="$origin_kind" '
    /^\/\/ Vampire certificate source origin:/ {
      ok = index($0, ": " file " line " line " char " chr " ")
      if (!ok) print FNR ":" $0
    }
    /^\/\/ vampire_source_assumption / {
      ok = index($0, "(origin_file \"" file "\")") &&
           index($0, "(origin_line \"" line "\")") &&
           index($0, "(origin_char \"" chr "\")") &&
           index($0, "(origin_kind \"" kind "\")")
      if (!ok) print FNR ":" $0
    }
  ' "$emitted" > "$report"

  [[ ! -s "$report" ]]
}

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
  if ! rg -q '^% megalodon_origin ' "$source"; then
    printf '%s\tMISSING_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  local cert_mode_arg=-vampirecertv1closed
  if [[ "$CORE_CERT_V1" == "1" ]]; then
    cert_mode_arg=-vampirecertv1coreclosed
  fi

  if ! "$MEGALODON" \
      "$cert_mode_arg" \
      -vampirecertv1 "$native" \
      -vampirecertv1source "$source" \
      -vampirecertv1emit "$case_dir/out.mg" \
      "$case_dir/dummy.mg" > "$case_dir/emit.out" 2> "$case_dir/emit.err"; then
    local err
    err=$(tail -1 "$case_dir/emit.err" | tr '\t' ' ')
    printf '%s\tEMIT_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q '^// Vampire certificate source origin:' "$case_dir/out.mg"; then
    printf '%s\tMISSING_EMITTED_ORIGIN\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if ! rg -q '^// vampire_source_assumption ' "$case_dir/out.mg"; then
    printf '%s\tMISSING_SOURCE_BINDINGS\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if awk '/^\/\/ vampire_source_assumption / && $0 !~ /origin_file "[^"]+".*origin_line "[^"]*".*origin_char "[^"]*".*origin_kind "[^"]+"/ {print FNR ":" $0}' \
      "$case_dir/out.mg" > "$case_dir/source_bindings_without_origin.txt" \
      && [[ -s "$case_dir/source_bindings_without_origin.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/source_bindings_without_origin.txt" | tr '\t' ' ')
    printf '%s\tSOURCE_BINDING_WITHOUT_ORIGIN\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if ! check_origin_consistency "$source" "$case_dir/out.mg" "$case_dir/source_origin_mismatch.txt"; then
    local first
    first=$(head -1 "$case_dir/source_origin_mismatch.txt" | tr '\t' ' ')
    printf '%s\tSOURCE_ORIGIN_MISMATCH\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if awk '/^\/\/ vampire_source_assumption / && $0 !~ /source_formula_status "closed_formula_checked"/ {print FNR ":" $0}' \
      "$case_dir/out.mg" > "$case_dir/unchecked_sources.txt" \
      && [[ -s "$case_dir/unchecked_sources.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/unchecked_sources.txt" | tr '\t' ' ')
    printf '%s\tUNCHECKED_SOURCE\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)/) {print FNR ":" $0}' \
      "$case_dir/out.mg" > "$case_dir/forbidden.txt" \
      && [[ -s "$case_dir/forbidden.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/forbidden.txt" | tr '\t' ' ')
    printf '%s\tFORBIDDEN_TOKEN\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  local proof_check_args=()
  if rg -q '^Axiom ' "$case_dir/out.mg"; then
    proof_check_args+=(-hf)
  fi

  if ! "$MEGALODON" "${proof_check_args[@]}" "$case_dir/out.mg" \
      > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tCHECK_FAIL\t%s\n' "$base" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if rg -n 'WARNING: The id .*not indexed as previously known' \
      "$case_dir/check.out" "$case_dir/check.err" > "$case_dir/unindexed_axioms.txt"; then
    local first
    first=$(head -1 "$case_dir/unindexed_axioms.txt" | tr '\t' ' ')
    printf '%s\tUNINDEXED_AXIOM\t%s\n' "$base" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  printf '%s\tCLOSED_PASS\n' "$base" > "$case_dir/result.tsv"
}

export ROOT MEGALODON CASES_DIR WORK_DIR CORE_CERT_V1
export -f resolve_origin_file read_origin_field check_origin_consistency run_one

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
      echo "listed closed native certificate does not exist: $raw" >&2
      exit 2
    fi
    printf '%s\n' "$native" >> "$selected_cases"
  done < "$CASE_LIST"
else
  find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f \
    | sort > "$selected_cases"
fi

if [[ ! -s "$selected_cases" ]]; then
  echo "no closed native certificate cases selected" >&2
  exit 2
fi

xargs -a "$selected_cases" -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort > "$WORK_DIR/counts.txt"

awk -F '\t' '$2 != "CLOSED_PASS"' "$WORK_DIR/summary.tsv" > "$WORK_DIR/nonpass.tsv"

cat "$WORK_DIR/counts.txt"
echo "native certificate v1 closed corpus selected cases: $selected_cases"
echo "native certificate v1 closed corpus artifacts: $WORK_DIR"
echo "native certificate v1 closed corpus latest link: $TMPDIR/latest_native_cert_v1_closed_corpus"

if [[ -s "$WORK_DIR/nonpass.tsv" ]]; then
  echo "native certificate v1 closed corpus had failures" >&2
  sed -n '1,40p' "$WORK_DIR/nonpass.tsv" >&2
  exit 1
fi
