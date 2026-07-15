#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR
export CASE_LIST="${CASE_LIST:-"$ROOT/tests/vampire_certificate/source_linked_strict_100.list"}"
export JOBS="${JOBS:-20}"
export WORK_DIR="${WORK_DIR:-"$TMPDIR/source_linked_strict_100"}"
export CASES_DIR="${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_source_linked_strict_100"

exec "$ROOT/tests/vampire_certificate/run_native_cert_v1_closed_corpus.sh"
