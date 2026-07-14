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
    -name 'megalodon2_*' \
    2>/dev/null \
    | sort -V \
    | tail -n 1
)
VAMPIRE=${VAMPIRE:-"$DEFAULT_VAMPIRE"}
PROBLEM_DIR=${PROBLEM_DIR:-"$ROOT/examples/hammer"}
SOLVED_DIR=${SOLVED_DIR:-"$PROBLEM_DIR/out1"}
PROBLEMS_FILE=${PROBLEMS_FILE:-}
LIMIT=${LIMIT:-200}
JOBS=${JOBS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-15}
MIN_PASS=${MIN_PASS:-100}
CHECK_SOURCE_MAP=${CHECK_SOURCE_MAP:-0}
STRICT_CERT_V1=${STRICT_CERT_V1:-0}
VAMPIRE_PROOF_ARGS=${VAMPIRE_PROOF_ARGS:-"--proof_extra lean --skolemization syntactic --shuffle_input off"}
VAMPIRE_EXTRA_ARGS=${VAMPIRE_EXTRA_ARGS:-}
WORK_DIR=${WORK_DIR:-"$TMPDIR/megalodon_native_live_${LIMIT}"}

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

if [[ -n "$PROBLEMS_FILE" ]]; then
  sed -n "1,${LIMIT}p" "$PROBLEMS_FILE" > "$WORK_DIR/problems.txt"
elif [[ -d "$SOLVED_DIR" ]]; then
  find "$SOLVED_DIR" -maxdepth 1 -type f -name '*.th0.p' \
    | sed 's#.*/##' \
    | sort \
    | sed -n "1,${LIMIT}p" \
    > "$WORK_DIR/problems.txt"
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

run_one() {
  local name=$1
  local case_dir="$WORK_DIR/cases/${name%.p}"
  local problem="$PROBLEM_DIR/$name"
  mkdir -p "$case_dir"
  : > "$case_dir/dummy.mg"

  if [[ ! -f "$problem" ]]; then
    printf '%s\tMISSING_PROBLEM\n' "$name" > "$case_dir/result.tsv"
    return 0
  fi

  local timed_out=0
  local proof_args=()
  local extra_args=()
  if [[ -n "$VAMPIRE_PROOF_ARGS" ]]; then
    read -r -a proof_args <<< "$VAMPIRE_PROOF_ARGS"
  fi
  if [[ -n "$VAMPIRE_EXTRA_ARGS" ]]; then
    read -r -a extra_args <<< "$VAMPIRE_EXTRA_ARGS"
  fi
  if ! run_with_wall_timeout "$case_dir" \
      "$VAMPIRE" \
      --input_syntax tptp \
      --mode casc \
      -t "$VAMPIRE_SECONDS" \
      --proof megalodon \
      --output_axiom_names on \
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

  if rg -q 'source vampire_' "$case_dir/native.sexp"; then
    printf '%s\tFAIL\tnative certificate contains a Vampire-derived source assumption\n' \
      "$name" > "$case_dir/result.tsv"
    return 0
  fi

  local check_args=(-vampirecertv1 "$case_dir/native.sexp")
  if [[ "$STRICT_CERT_V1" == "1" ]]; then
    check_args=(-vampirecertv1strict "${check_args[@]}")
  fi
  if [[ "$CHECK_SOURCE_MAP" == "1" ]]; then
    check_args+=(-vampirecertv1source "$problem")
  fi

  if "$MEGALODON" "${check_args[@]}" "$case_dir/dummy.mg" \
      > "$case_dir/check.out" 2> "$case_dir/check.err"; then
    printf '%s\tPASS\n' "$name" > "$case_dir/result.tsv"
  else
    local err
    err=$(tail -1 "$case_dir/check.err" | tr '\t' ' ')
    printf '%s\tFAIL\t%s\n' "$name" "$err" > "$case_dir/result.tsv"
  fi
}

export ROOT TMPDIR MEGALODON VAMPIRE PROBLEM_DIR WORK_DIR VAMPIRE_SECONDS WALL_SECONDS CHECK_SOURCE_MAP STRICT_CERT_V1 VAMPIRE_PROOF_ARGS VAMPIRE_EXTRA_ARGS
export -f run_with_wall_timeout run_one

xargs -a "$WORK_DIR/problems.txt" -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort > "$WORK_DIR/summary.tsv"

cat "$WORK_DIR/summary.tsv"
awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort > "$WORK_DIR/counts.txt"
cat "$WORK_DIR/counts.txt"

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
cat "$WORK_DIR/rule_counts.txt"

passes=$(awk -F '\t' '$2 == "PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
failures=$(awk -F '\t' '$2 == "FAIL" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")

if (( failures != 0 )); then
  echo "native live validation had $failures certificate failures" >&2
  exit 1
fi
if (( passes < MIN_PASS )); then
  echo "native live validation passed $passes certificates, below MIN_PASS=$MIN_PASS" >&2
  exit 1
fi
