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
PROBLEM_DIR=${PROBLEM_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
PROBLEMS_FILE=${PROBLEMS_FILE:-}
LIMIT=${LIMIT:-100}
JOBS=${JOBS:-10}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-12}
MIN_CERT=${MIN_CERT:-1}
REQUIRE_SOURCE_ORIGIN=${REQUIRE_SOURCE_ORIGIN:-1}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}
VAMPIRE_PROOF_ARGS=${VAMPIRE_PROOF_ARGS:-"--proof_extra lean --skolemization syntactic --shuffle_input off"}
VAMPIRE_OUTPUT_AXIOM_NAMES=${VAMPIRE_OUTPUT_AXIOM_NAMES:-on}
VAMPIRE_EXTRA_ARGS=${VAMPIRE_EXTRA_ARGS:-}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_live_preprocess_pf_frontier.XXXXXX")"}

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
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_live_preprocess_pf_frontier"

if [[ -n "$PROBLEMS_FILE" ]]; then
  sed -n "1,${LIMIT}p" "$PROBLEMS_FILE" > "$WORK_DIR/problems.txt"
else
  find "$PROBLEM_DIR" -maxdepth 1 -type f -name '*.th0.p' \
    | sed 's#.*/##' \
    | sort \
    | sed -n "1,${LIMIT}p" \
    > "$WORK_DIR/problems.txt"
fi

run_with_wall_timeout() {
  local case_dir=$1
  shift
  setsid "$@" > "$case_dir/out.txt" 2> "$case_dir/vampire.err" &
  local pid=$!
  local elapsed=0
  while kill -0 "$pid" 2>/dev/null; do
    if (( elapsed >= WALL_SECONDS )); then
      kill -TERM "-$pid" 2>/dev/null || true
      sleep 1
      kill -KILL "-$pid" 2>/dev/null || true
      wait "$pid" 2>/dev/null || true
      return 124
    fi
    sleep 1
    elapsed=$((elapsed + 1))
  done
  wait "$pid" || true
  return 0
}

classify_error() {
  local err_file=$1
  local msg
  msg=$(tail -1 "$err_file" | tr '\t' ' ')
  if [[ "$msg" =~ no\ proof-term\ rule\ for\ ([a-z_]+) ]]; then
    printf 'UNSUPPORTED_RULE_%s' "${BASH_REMATCH[1]}"
  elif [[ "$msg" =~ built\ a\ proof\ of\ the\ wrong\ proposition ]]; then
    printf 'WRONG_PROPOSITION'
  elif [[ "$msg" =~ ill-formed\ proof\ term ]]; then
    printf 'ILL_FORMED_PROOF_TERM'
  elif [[ "$msg" =~ requires\ a\ final\ certificate\ step ]]; then
    printf 'STRICT_FINAL_STEP'
  elif [[ "$msg" =~ final\ certificate\ step\ is\ not\ the\ empty\ clause ]]; then
    printf 'STRICT_FINAL_NOT_EMPTY'
  elif [[ "$msg" =~ source\ map ]]; then
    printf 'SOURCE_MAP_FAIL'
  elif [[ "$msg" =~ check\ failed:\ ([^:]+): ]]; then
    printf 'CHECK_FAILED'
  else
    printf 'PF_FAIL'
  fi
}

run_one() {
  local name=$1
  local case_id="${name%.p}"
  local case_dir="$WORK_DIR/cases/$case_id"
  local problem="$PROBLEM_DIR/$name"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -f "$problem" ]]; then
    printf '%s\tMISSING_PROBLEM\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi
  if [[ "$REQUIRE_SOURCE_ORIGIN" == "1" ]] \
      && ! rg -q '^% megalodon_origin ' "$problem"; then
    printf '%s\tMISSING_ORIGIN\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi

  local proof_args=()
  local extra_args=()
  if [[ -n "$VAMPIRE_PROOF_ARGS" ]]; then
    read -r -a proof_args <<< "$VAMPIRE_PROOF_ARGS"
  fi
  if [[ -n "$VAMPIRE_EXTRA_ARGS" ]]; then
    read -r -a extra_args <<< "$VAMPIRE_EXTRA_ARGS"
  fi
  local axiom_name_args=()
  if [[ -n "$VAMPIRE_OUTPUT_AXIOM_NAMES" ]]; then
    axiom_name_args=(--output_axiom_names "$VAMPIRE_OUTPUT_AXIOM_NAMES")
  fi

  local timed_out=0
  if ! run_with_wall_timeout "$case_dir" \
      "$VAMPIRE" \
      --input_syntax tptp \
      --mode casc \
      -t "$VAMPIRE_SECONDS" \
      --proof megalodon \
      "${axiom_name_args[@]}" \
      "${proof_args[@]}" \
      "${extra_args[@]}" \
      "$problem"; then
    timed_out=1
  fi

  awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
    "$case_dir/out.txt" > "$case_dir/native.sexp"

  if [[ ! -s "$case_dir/native.sexp" ]]; then
    if (( timed_out )) || rg -q -- '-- Time limit reached!' "$case_dir/out.txt"; then
      printf '%s\tTIMEOUT\n' "$name" > "$case_dir/result.tsv"
    else
      printf '%s\tNO_CERT\n' "$name" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  local check_args=(-vampirecertv1preprocesspfcheck)
  if [[ "$STRICT_CERT_V1" == "1" ]]; then
    check_args+=(-vampirecertv1strict)
  fi
  check_args+=(-vampirecertv1 "$case_dir/native.sexp" -vampirecertv1source "$problem")

  if MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1 \
      "$MEGALODON" "${check_args[@]}" "$case_dir/dummy.mg" \
      > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    if rg -q 'native preprocess proof term checked' "$case_dir/check.out"; then
      printf '%s\tPREPROCESS_STRUCTURAL_PASS\n' "$name" > "$case_dir/result.tsv"
    else
      printf '%s\tPREPROCESS_STRUCTURAL_MISSING_CONFIRMATION\n' "$name" > "$case_dir/result.tsv"
    fi
    return 0
  fi

  local status err
  status=$(classify_error "$case_dir/check.err")
  err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
  printf '%s\t%s\t%s\n' "$name" "$status" "$err" > "$case_dir/result.tsv"
}

export ROOT TMPDIR MEGALODON VAMPIRE PROBLEM_DIR WORK_DIR VAMPIRE_SECONDS WALL_SECONDS REQUIRE_SOURCE_ORIGIN STRICT_CERT_V1 VAMPIRE_PROOF_ARGS VAMPIRE_OUTPUT_AXIOM_NAMES VAMPIRE_EXTRA_ARGS
export -f run_with_wall_timeout classify_error run_one

xargs -a "$WORK_DIR/problems.txt" -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | sort -z \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" | sort > "$WORK_DIR/counts.txt"

awk -F '\t' '$2 != "PREPROCESS_STRUCTURAL_PASS"' "$WORK_DIR/summary.tsv" \
  > "$WORK_DIR/frontier_failures.tsv"

awk -F '\t' '$2 != "PREPROCESS_STRUCTURAL_PASS" {print $2}' "$WORK_DIR/summary.tsv" \
  | sort | uniq -c | sort -nr > "$WORK_DIR/frontier_failure_counts.txt"

find "$WORK_DIR/cases" -name native.sexp -type f -size +0 -print0 \
  | xargs -0 -r cat \
  | awk '
      /^[[:space:]]+\([[:alpha:]_][[:alnum:]_]*/ {
        line = $0
        sub(/^[[:space:]]+\(/, "", line)
        split(line, parts, /[[:space:])]/)
        if (parts[1] != "problem") {
          count[parts[1]]++
        }
      }
      END {
        for (rule in count) {
          print rule, count[rule]
        }
      }' \
  | sort > "$WORK_DIR/rule_counts.txt"

cat "$WORK_DIR/counts.txt"
echo "native live preprocess structural frontier artifacts: $WORK_DIR"
echo "native live preprocess structural frontier latest link: $TMPDIR/latest_native_live_preprocess_pf_frontier"
echo "native live preprocess structural frontier failures: $WORK_DIR/frontier_failures.tsv"
echo "native live preprocess structural frontier failure counts: $WORK_DIR/frontier_failure_counts.txt"
echo "native live preprocess structural frontier rule counts: $WORK_DIR/rule_counts.txt"

certs=$(find "$WORK_DIR/cases" -name native.sexp -type f -size +0 | wc -l | tr -d ' ')
if (( certs < MIN_CERT )); then
  echo "native live preprocess structural frontier produced $certs certificates, below MIN_CERT=$MIN_CERT" >&2
  exit 1
fi
