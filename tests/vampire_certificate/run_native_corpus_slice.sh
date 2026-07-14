#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

PROBLEM_DIR=${PROBLEM_DIR:-"$TMPDIR/native_source_linked_corpus_1000"}
SLICE_START=${SLICE_START:-1}
SLICE_SIZE=${SLICE_SIZE:-400}
SLICE_END=${SLICE_END:-$((SLICE_START + SLICE_SIZE - 1))}
JOBS=${JOBS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-15}
CHECK_SOURCE_MAP=${CHECK_SOURCE_MAP:-1}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}
VAMPIRE_EXTRA_ARGS=${VAMPIRE_EXTRA_ARGS:-}

if [[ ! -d "$PROBLEM_DIR" ]]; then
  echo "PROBLEM_DIR does not exist: $PROBLEM_DIR" >&2
  exit 2
fi
if (( SLICE_START < 1 || SLICE_END < SLICE_START )); then
  echo "invalid slice: SLICE_START=$SLICE_START SLICE_END=$SLICE_END" >&2
  exit 2
fi

PROBLEMS_FILE=${PROBLEMS_FILE:-"$TMPDIR/native_slice_${SLICE_START}_${SLICE_END}.list"}
find -L "$PROBLEM_DIR" -maxdepth 1 -type f -name '*.th0.p' -printf '%f\n' \
  | sort \
  | sed -n "${SLICE_START},${SLICE_END}p" \
  > "$PROBLEMS_FILE"

LIMIT=$(wc -l < "$PROBLEMS_FILE")
if (( LIMIT == 0 )); then
  echo "selected slice is empty: $SLICE_START-$SLICE_END from $PROBLEM_DIR" >&2
  exit 2
fi

MIN_PASS=${MIN_PASS:-$(((LIMIT + 4) / 5))}
WORK_DIR=${WORK_DIR:-"$TMPDIR/native_source_linked_${SLICE_START}_${SLICE_END}"}

PROBLEM_DIR="$PROBLEM_DIR" \
PROBLEMS_FILE="$PROBLEMS_FILE" \
CHECK_SOURCE_MAP="$CHECK_SOURCE_MAP" \
STRICT_CERT_V1="$STRICT_CERT_V1" \
VAMPIRE_EXTRA_ARGS="$VAMPIRE_EXTRA_ARGS" \
LIMIT="$LIMIT" \
JOBS="$JOBS" \
VAMPIRE_SECONDS="$VAMPIRE_SECONDS" \
WALL_SECONDS="$WALL_SECONDS" \
MIN_PASS="$MIN_PASS" \
WORK_DIR="$WORK_DIR" \
  "$ROOT/tests/vampire_certificate/run_native_live_parallel.sh"
