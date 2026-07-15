#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
PROBLEM_DIR=${PROBLEM_DIR:-"$ROOT/examples/hammer"}
JOBS=${JOBS:-20}
CHECK_SOURCE_MAP=${CHECK_SOURCE_MAP:-1}
REQUIRE_SOURCE_ORIGIN=${REQUIRE_SOURCE_ORIGIN:-0}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}
CLOSED_CERT_V1=${CLOSED_CERT_V1:-0}
EMIT_TIMEOUT=${EMIT_TIMEOUT:-30}
CHECK_TIMEOUT=${CHECK_TIMEOUT:-30}
MIN_PASS=${MIN_PASS:-1}
WORK_DIR=${WORK_DIR:-"$TMPDIR/megalodon_native_emit_cached"}
NATIVE_RUN_DIRS=${NATIVE_RUN_DIRS:-}

if [[ ! -x "$MEGALODON" ]]; then
  echo "MEGALODON must point to an executable Megalodon binary" >&2
  exit 2
fi

native_dirs=()
if (( $# > 0 )); then
  native_dirs=("$@")
elif [[ -n "$NATIVE_RUN_DIRS" ]]; then
  read -r -a native_dirs <<< "$NATIVE_RUN_DIRS"
else
  native_dirs=("$TMPDIR/latest_megalodon_native_live")
fi

rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_megalodon_native_emit_cached"

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

: > "$WORK_DIR/pass_cases.tsv"
for dir in "${native_dirs[@]}"; do
  if [[ ! -f "$dir/summary.tsv" ]]; then
    echo "native run directory lacks summary.tsv: $dir" >&2
    exit 2
  fi
  awk -F '\t' -v dir="$dir" '$2 == "PASS" {print dir "\t" $1}' \
    "$dir/summary.tsv" >> "$WORK_DIR/pass_cases.tsv"
done

if [[ ! -s "$WORK_DIR/pass_cases.tsv" ]]; then
  echo "no PASS native certificates found in selected run directories" >&2
  exit 2
fi

run_one() {
  local native_run_dir=$1
  local name=$2
  local case_id="${name%.p}"
  local native="$native_run_dir/cases/$case_id/native.sexp"
  local source="$PROBLEM_DIR/$name"
  local case_dir="$WORK_DIR/cases/$case_id"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -s "$native" ]]; then
    printf '%s\tMISSING_NATIVE\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi
  if [[ "$CHECK_SOURCE_MAP" == "1" && ! -f "$source" ]]; then
    printf '%s\tMISSING_SOURCE\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi
  if [[ "$REQUIRE_SOURCE_ORIGIN" == "1" ]] \
      && ! rg -q '^% megalodon_origin ' "$source"; then
    printf '%s\tMISSING_ORIGIN\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi

  local check_args=()
  if [[ "$CLOSED_CERT_V1" == "1" ]]; then
    check_args+=(-vampirecertv1closed)
  elif [[ "$STRICT_CERT_V1" == "1" ]]; then
    check_args+=(-vampirecertv1strict)
  fi
  check_args+=(-vampirecertv1 "$native")
  if [[ "$CHECK_SOURCE_MAP" == "1" ]]; then
    check_args+=(-vampirecertv1source "$source")
  fi
  check_args+=(-vampirecertv1emit "$case_dir/out.mg")

  if ! timeout "$EMIT_TIMEOUT" "$MEGALODON" "${check_args[@]}" "$case_dir/dummy.mg" \
      > "$case_dir/emit.out" 2> "$case_dir/emit.err"; then
    local err
    err=$(tail -1 "$case_dir/emit.err" | tr '\t' ' ')
    printf '%s\tEMIT_FAIL\t%s\n' "$name" "$err" > "$case_dir/result.tsv"
    return 0
  fi

  if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed/) {print FNR ":" $0}' \
      "$case_dir/out.mg" > "$case_dir/forbidden.txt" \
      && [[ -s "$case_dir/forbidden.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/forbidden.txt" | tr '\t' ' ')
    printf '%s\tFORBIDDEN_TOKEN\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if [[ "$CLOSED_CERT_V1" == "1" ]] \
      && rg -n '^assume (bridge_|definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
          "$case_dir/out.mg" > "$case_dir/forbidden.txt"; then
    local first
    first=$(head -1 "$case_dir/forbidden.txt" | tr '\t' ' ')
    printf '%s\tFORBIDDEN_NON_SOURCE_PREMISE\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if [[ "$CLOSED_CERT_V1" == "1" ]] \
      && awk '/^\/\/ vampire_source_assumption / && $0 !~ /source_formula_status "closed_formula_checked"/ {print FNR ":" $0}' \
          "$case_dir/out.mg" > "$case_dir/unchecked_sources.txt" \
      && [[ -s "$case_dir/unchecked_sources.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/unchecked_sources.txt" | tr '\t' ' ')
    printf '%s\tUNCHECKED_SOURCE\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if [[ "$REQUIRE_SOURCE_ORIGIN" == "1" ]] \
      && awk '/^\/\/ vampire_source_assumption / && $0 !~ /origin_file "[^"]+".*origin_line "[^"]*".*origin_char "[^"]*".*origin_kind "[^"]+"/ {print FNR ":" $0}' \
          "$case_dir/out.mg" > "$case_dir/source_bindings_without_origin.txt" \
      && [[ -s "$case_dir/source_bindings_without_origin.txt" ]]; then
    local first
    first=$(head -1 "$case_dir/source_bindings_without_origin.txt" | tr '\t' ' ')
    printf '%s\tSOURCE_BINDING_WITHOUT_ORIGIN\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if [[ "$REQUIRE_SOURCE_ORIGIN" == "1" ]] \
      && ! check_origin_consistency "$source" "$case_dir/out.mg" "$case_dir/source_origin_mismatch.txt"; then
    local first
    first=$(head -1 "$case_dir/source_origin_mismatch.txt" | tr '\t' ' ')
    printf '%s\tSOURCE_ORIGIN_MISMATCH\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  local proof_check_args=()
  if rg -q '^Axiom ' "$case_dir/out.mg"; then
    proof_check_args+=(-hf)
  fi

  set +e
  timeout "$CHECK_TIMEOUT" "$MEGALODON" "${proof_check_args[@]}" "$case_dir/out.mg" \
      > "$case_dir/check.out" 2> "$case_dir/check.err"
  local check_status=$?
  set -e
  if (( check_status != 0 )); then
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    if (( check_status == 124 )); then
      printf '%s\tCHECK_TIMEOUT\t%s seconds\n' "$name" "$CHECK_TIMEOUT" > "$case_dir/result.tsv"
    else
      printf '%s\tCHECK_FAIL\t%s\n' "$name" "$err" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  if [[ "$CLOSED_CERT_V1" == "1" ]] \
      && rg -n 'WARNING: The id .*not indexed as previously known' \
          "$case_dir/check.out" "$case_dir/check.err" > "$case_dir/unindexed_axioms.txt"; then
    local first
    first=$(head -1 "$case_dir/unindexed_axioms.txt" | tr '\t' ' ')
    printf '%s\tUNINDEXED_AXIOM\t%s\n' "$name" "$first" > "$case_dir/result.tsv"
    return 0
  fi

  if [[ "$CLOSED_CERT_V1" == "1" ]]; then
    printf '%s\tCLOSED_PASS\n' "$name" > "$case_dir/result.tsv"
  else
    printf '%s\tPASS\n' "$name" > "$case_dir/result.tsv"
  fi
}

export ROOT MEGALODON PROBLEM_DIR WORK_DIR CHECK_SOURCE_MAP REQUIRE_SOURCE_ORIGIN STRICT_CERT_V1 CLOSED_CERT_V1 EMIT_TIMEOUT CHECK_TIMEOUT
export -f resolve_origin_file read_origin_field check_origin_consistency run_one

xargs -a "$WORK_DIR/pass_cases.tsv" -n2 -P "$JOBS" bash -c 'run_one "$0" "$1"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort > "$WORK_DIR/counts.txt"

if [[ "$CLOSED_CERT_V1" == "1" ]]; then
  awk -F '\t' '$2 != "CLOSED_PASS"' "$WORK_DIR/summary.tsv" > "$WORK_DIR/nonpass.tsv"
else
  awk -F '\t' '$2 != "PASS"' "$WORK_DIR/summary.tsv" > "$WORK_DIR/nonpass.tsv"
fi

{
  printf 'Latest Vampire/Megalodon artifacts as of %s UTC\n\n' "$(date -u +%Y-%m-%dT%H:%M:%S)"
  printf '/project/tmp is a symlink to %s.\n' "$(readlink -f "$TMPDIR" 2>/dev/null || printf '%s' "$TMPDIR")"
  printf 'Use a trailing slash (`ls -la /project/tmp/`), `cd /project/tmp`, or `find -L` when inspecting it recursively.\n\n'
  printf 'Current cached native emit/check run:\n'
  printf '  %s\n' "$WORK_DIR"
  printf '  %s/latest_megalodon_native_emit_cached -> %s\n' "$TMPDIR" "$WORK_DIR"
  printf '  %s/counts.txt\n' "$WORK_DIR"
  printf '  %s/summary.tsv\n' "$WORK_DIR"
  printf '  %s/nonpass.tsv\n' "$WORK_DIR"
  printf '  %s/cases/*/out.mg\n' "$WORK_DIR"
  printf '  %s/cases/*/check.out\n\n' "$WORK_DIR"
  printf 'Native certificate input directories:\n'
  for dir in "${native_dirs[@]}"; do
    printf '  %s\n' "$dir"
    printf '  %s/cases/*/native.sexp\n' "$dir"
  done
  printf '\nUseful inspection commands:\n'
  printf '  cat %s/counts.txt\n' "$WORK_DIR"
  printf '  sed -n '\''1,40p'\'' %s/nonpass.tsv\n' "$WORK_DIR"
  printf '  find -L %s/latest_megalodon_native_emit_cached/cases -maxdepth 2 -name out.mg | head\n' "$TMPDIR"
} > "$TMPDIR/LATEST_ARTIFACTS.txt"

cat "$WORK_DIR/counts.txt"
echo "native emit cached artifacts: $WORK_DIR"
echo "native emit cached latest link: $TMPDIR/latest_megalodon_native_emit_cached"
echo "artifact manifest: $TMPDIR/LATEST_ARTIFACTS.txt"

if [[ "$CLOSED_CERT_V1" == "1" ]]; then
  passes=$(awk -F '\t' '$2 == "CLOSED_PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
else
  passes=$(awk -F '\t' '$2 == "PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
fi
failures=$(awk -F '\t' '$2 != "PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
if [[ "$CLOSED_CERT_V1" == "1" ]]; then
  failures=$(awk -F '\t' '$2 != "CLOSED_PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
fi

if (( failures != 0 )); then
  echo "native emit cached validation had $failures failures" >&2
  sed -n '1,40p' "$WORK_DIR/nonpass.tsv" >&2
  exit 1
fi
if (( passes < MIN_PASS )); then
  echo "native emit cached validation passed $passes proofs, below MIN_PASS=$MIN_PASS" >&2
  exit 1
fi
