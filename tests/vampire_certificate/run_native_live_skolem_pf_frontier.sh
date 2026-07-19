#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
DEFAULT_VAMPIRE=$(
  find /project/vampire-leancheck/vampire_rel_vampire \
    -maxdepth 1 \
    -type f \
    -executable \
    -name 'megalodon*_*' \
    -printf '%T@ %p\n' \
    2>/dev/null \
    | sort -n \
    | tail -n 1 \
    | cut -d' ' -f2-
)
VAMPIRE=${VAMPIRE:-"$DEFAULT_VAMPIRE"}
CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_live_skolem_pf_frontier.XXXXXX")"}
JOBS=${JOBS:-10}
MIN_SKOLEM=${MIN_SKOLEM:-10}
MIN_PASS=${MIN_PASS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-13}
CHECK_TIMEOUT=${CHECK_TIMEOUT:-30}
VAMPIRE_PROOF_ARGS=${VAMPIRE_PROOF_ARGS:-"--proof_extra lean --skolemization standard --shuffle_input off"}

if [[ -z "$VAMPIRE" || ! -x "$VAMPIRE" ]]; then
  echo "VAMPIRE must point to an executable Vampire binary" >&2
  exit 2
fi
if [[ ! -x "$MEGALODON" ]]; then
  echo "MEGALODON must point to an executable Megalodon binary" >&2
  exit 2
fi

rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_live_skolem_pf_frontier"

skolem_audit_dir="$WORK_DIR/skolem_closed_audit"
RUN_SKOLEM_CASES=0 \
WORK_DIR="$skolem_audit_dir" \
MIN_SKOLEM="$MIN_SKOLEM" \
JOBS="$JOBS" \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_skolem_closed_audit.sh" \
  > "$WORK_DIR/skolem_closed_audit.out" \
  2> "$WORK_DIR/skolem_closed_audit.err"

frontier_cases="$skolem_audit_dir/skolem_closed_cases.list"
if [[ ! -s "$frontier_cases" ]]; then
  echo "live skolem proof-term frontier has no selected Skolem cases" >&2
  exit 2
fi

classify_error() {
  local err_file=$1
  local msg
  msg=$(tail -1 "$err_file" | tr '\t' ' ')
  if [[ "$msg" =~ refuses\ certificate-derived\ Known\ primitive\ ([^[:space:]\;]+) ]]; then
    printf 'TRANSITIONAL_%s' "${BASH_REMATCH[1]}"
  elif [[ "$msg" =~ skolemization\ needs\ an\ explicit\ source\ formula ]]; then
    printf 'STALE_SKOLEM_NO_SOURCE'
  elif [[ "$msg" =~ skolemization\ result\ does\ not\ match\ source\ body ]]; then
    printf 'SKOLEM_SOURCE_BODY_MISMATCH'
  elif [[ "$msg" =~ formula\ orientation\ supports\ only ]]; then
    printf 'FORMULA_ORIENTATION_UNSUPPORTED'
  elif [[ "$msg" =~ rectify_formula ]]; then
    printf 'RECTIFY_UNSUPPORTED'
  elif [[ "$msg" =~ cannot\ instantiate\ (dropped\ )?parent\ variable ]]; then
    printf 'CNF_PARENT_INSTANTIATION_UNSUPPORTED'
  elif [[ "$msg" =~ no\ proof-term\ rule\ for\ ([a-z_]+) ]]; then
    printf 'UNSUPPORTED_RULE_%s' "${BASH_REMATCH[1]}"
  elif [[ "$msg" =~ built\ a\ proof\ of\ the\ wrong\ proposition ]]; then
    printf 'WRONG_PROPOSITION'
  elif [[ "$msg" =~ ill-formed\ proof\ term ]]; then
    printf 'ILL_FORMED_PROOF_TERM'
  elif [[ "$msg" =~ timed\ out ]]; then
    printf 'CHECK_TIMEOUT'
  else
    printf 'PF_FAIL'
  fi
}

run_one() {
  local base=$1
  local problem="$CASES_DIR/$base.th0.p"
  local case_dir="$WORK_DIR/cases/$base"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -s "$problem" ]]; then
    printf '%s\tMISSING_SOURCE\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  local proof_args=()
  if [[ -n "$VAMPIRE_PROOF_ARGS" ]]; then
    read -r -a proof_args <<< "$VAMPIRE_PROOF_ARGS"
  fi

  timeout "$WALL_SECONDS"s "$VAMPIRE" \
    --input_syntax tptp \
    --mode casc \
    -t "$VAMPIRE_SECONDS" \
    --proof megalodon \
    --output_axiom_names on \
    "${proof_args[@]}" \
    "$problem" > "$case_dir/vampire.out" 2> "$case_dir/vampire.err" || true

  awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
    "$case_dir/vampire.out" > "$case_dir/native.sexp"

  if [[ ! -s "$case_dir/native.sexp" ]]; then
    if rg -q 'Exception at run slice level|User error:' \
        "$case_dir/vampire.out" "$case_dir/vampire.err"; then
      printf '%s\tVAMPIRE_EXCEPTION\n' "$base" > "$case_dir/result.tsv"
    elif rg -q -- '-- Time limit reached!' "$case_dir/vampire.out"; then
      printf '%s\tTIMEOUT\n' "$base" > "$case_dir/result.tsv"
    else
      printf '%s\tNO_CERT\n' "$base" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  if ! rg -q 'skolem_formula' "$case_dir/native.sexp"; then
    printf '%s\tNO_SKOLEM_CERT\n' "$base" > "$case_dir/result.tsv"
    return 0
  fi

  if timeout "$CHECK_TIMEOUT"s "$MEGALODON" \
      -vampirecertv1preprocesspfcheck \
      -vampirecertv1strict \
      -vampirecertv1 "$case_dir/native.sexp" \
      -vampirecertv1source "$problem" \
      "$case_dir/dummy.mg" > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    if rg -q 'native preprocess proof term checked' "$case_dir/check.out"; then
      printf '%s\tSKOLEM_PF_PASS\n' "$base" > "$case_dir/result.tsv"
    else
      printf '%s\tSKOLEM_PF_MISSING_CONFIRMATION\n' "$base" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  local rc=$?
  local status err
  if [[ "$rc" -eq 124 ]]; then
    status=CHECK_TIMEOUT
    err="checker timed out after ${CHECK_TIMEOUT}s"
  else
    status=$(classify_error "$case_dir/check.err")
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
  fi
  printf '%s\t%s\t%s\n' "$base" "$status" "$err" > "$case_dir/result.tsv"
}

export ROOT TMPDIR MEGALODON VAMPIRE CASES_DIR WORK_DIR VAMPIRE_SECONDS WALL_SECONDS CHECK_TIMEOUT VAMPIRE_PROOF_ARGS
export -f classify_error run_one

xargs -r -P "$JOBS" -n 1 bash -c 'run_one "$1"' bash < "$frontier_cases"

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | sort -z \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" | sort | tee "$WORK_DIR/counts.txt"

awk -F '\t' '$2 != "SKOLEM_PF_PASS"' "$WORK_DIR/summary.tsv" \
  > "$WORK_DIR/frontier_failures.tsv"

awk -F '\t' '$2 != "SKOLEM_PF_PASS" {print $2}' "$WORK_DIR/summary.tsv" \
  | sort | uniq -c | sort -nr > "$WORK_DIR/frontier_failure_counts.txt"

echo "native live Skolem proof-term frontier artifacts: $WORK_DIR"
echo "native live Skolem proof-term frontier latest link: $TMPDIR/latest_native_live_skolem_pf_frontier"
echo "native live Skolem proof-term frontier failures: $WORK_DIR/frontier_failures.tsv"
echo "native live Skolem proof-term frontier failure counts: $WORK_DIR/frontier_failure_counts.txt"

passes=$(awk -F '\t' '$2 == "SKOLEM_PF_PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
if (( passes < MIN_PASS )); then
  echo "live Skolem proof-term frontier passed $passes cases, below MIN_PASS=$MIN_PASS" >&2
  sed -n '1,40p' "$WORK_DIR/frontier_failure_counts.txt" >&2
  exit 1
fi
