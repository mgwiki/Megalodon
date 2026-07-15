#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASE_LIST=${CASE_LIST:-"$ROOT/tests/vampire_certificate/source_linked_strict_100.list"}
CORPUS_DIR=${CORPUS_DIR:-"$TMPDIR/source_linked_export_no_axiom_names_100_corpus"}
WORK_DIR=${WORK_DIR:-"$TMPDIR/source_linked_export_no_axiom_names_100_run"}
JOBS=${JOBS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-15}
VAMPIRE_OUTPUT_AXIOM_NAMES=${VAMPIRE_OUTPUT_AXIOM_NAMES:-off}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}

if [[ ! -f "$CASE_LIST" ]]; then
  echo "CASE_LIST does not exist: $CASE_LIST" >&2
  exit 2
fi

LIMIT=$(wc -l < "$CASE_LIST")
if (( LIMIT == 0 )); then
  echo "CASE_LIST is empty: $CASE_LIST" >&2
  exit 2
fi
MIN_PASS=${MIN_PASS:-$LIMIT}

ln -sfn "$WORK_DIR" "$TMPDIR/latest_source_linked_export_no_axiom_names_100"

PROBLEMS_FILE="$CASE_LIST" \
CORPUS_DIR="$CORPUS_DIR" \
WORK_DIR="$WORK_DIR" \
LIMIT="$LIMIT" \
MIN_PASS="$MIN_PASS" \
JOBS="$JOBS" \
VAMPIRE_SECONDS="$VAMPIRE_SECONDS" \
WALL_SECONDS="$WALL_SECONDS" \
VAMPIRE_OUTPUT_AXIOM_NAMES="$VAMPIRE_OUTPUT_AXIOM_NAMES" \
STRICT_CERT_V1="$STRICT_CERT_V1" \
  "$ROOT/tests/vampire_certificate/run_source_linked_corpus_parallel.sh"
