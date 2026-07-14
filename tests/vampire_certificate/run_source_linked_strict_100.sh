#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR
export PROBLEMS_FILE="${PROBLEMS_FILE:-"$ROOT/tests/vampire_certificate/source_linked_strict_100.list"}"
export LIMIT="${LIMIT:-100}"
export MIN_PASS="${MIN_PASS:-100}"
export JOBS="${JOBS:-20}"
export VAMPIRE_SECONDS="${VAMPIRE_SECONDS:-10}"
export WALL_SECONDS="${WALL_SECONDS:-15}"
export WORK_DIR="${WORK_DIR:-"$TMPDIR/source_linked_strict_100"}"
export CORPUS_DIR="${CORPUS_DIR:-"$TMPDIR/source_linked_strict_100_corpus"}"

exec "$ROOT/tests/vampire_certificate/run_source_linked_corpus_parallel.sh"
