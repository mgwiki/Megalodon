#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASE_LIST=${CASE_LIST:-"$ROOT/tests/vampire_certificate/source_linked_strict_100.list"}
PROBLEM_DIR=${PROBLEM_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
JOBS=${JOBS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-15}
VAMPIRE_OUTPUT_AXIOM_NAMES=${VAMPIRE_OUTPUT_AXIOM_NAMES:-off}
CHECK_SOURCE_MAP=${CHECK_SOURCE_MAP:-1}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}
REQUIRE_SOURCE_ORIGIN=${REQUIRE_SOURCE_ORIGIN:-1}
WORK_DIR=${WORK_DIR:-"$TMPDIR/source_linked_live_no_axiom_names_100"}

if [[ ! -f "$CASE_LIST" ]]; then
  echo "CASE_LIST does not exist: $CASE_LIST" >&2
  exit 2
fi
if [[ ! -d "$PROBLEM_DIR" ]]; then
  echo "PROBLEM_DIR does not exist: $PROBLEM_DIR" >&2
  exit 2
fi

LIMIT=$(wc -l < "$CASE_LIST")
if (( LIMIT == 0 )); then
  echo "CASE_LIST is empty: $CASE_LIST" >&2
  exit 2
fi
MIN_PASS=${MIN_PASS:-$LIMIT}

ln -sfn "$WORK_DIR" "$TMPDIR/latest_source_linked_live_no_axiom_names_100"

PROBLEM_DIR="$PROBLEM_DIR" \
PROBLEMS_FILE="$CASE_LIST" \
CHECK_SOURCE_MAP="$CHECK_SOURCE_MAP" \
STRICT_CERT_V1="$STRICT_CERT_V1" \
REQUIRE_SOURCE_ORIGIN="$REQUIRE_SOURCE_ORIGIN" \
LIMIT="$LIMIT" \
JOBS="$JOBS" \
VAMPIRE_SECONDS="$VAMPIRE_SECONDS" \
VAMPIRE_OUTPUT_AXIOM_NAMES="$VAMPIRE_OUTPUT_AXIOM_NAMES" \
WALL_SECONDS="$WALL_SECONDS" \
MIN_PASS="$MIN_PASS" \
WORK_DIR="$WORK_DIR" \
  "$ROOT/tests/vampire_certificate/run_native_live_parallel.sh"
