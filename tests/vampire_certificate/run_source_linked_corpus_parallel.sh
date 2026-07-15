#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
MEGALODON_FILE=${MEGALODON_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
CORPUS_DIR=${CORPUS_DIR:-"$TMPDIR/megalodon_source_linked_corpus"}
PREFIX=${PREFIX:-hammer}
LIMIT=${LIMIT:-300}
JOBS=${JOBS:-20}
VAMPIRE_SECONDS=${VAMPIRE_SECONDS:-10}
WALL_SECONDS=${WALL_SECONDS:-15}
MIN_PASS=${MIN_PASS:-100}
STRICT_CERT_V1=${STRICT_CERT_V1:-1}
VAMPIRE_OUTPUT_AXIOM_NAMES=${VAMPIRE_OUTPUT_AXIOM_NAMES:-on}
WORK_DIR=${WORK_DIR:-"$TMPDIR/megalodon_source_linked_live_${LIMIT}"}
PROBLEMS_FILE=${PROBLEMS_FILE:-}

if [[ ! -x "$MEGALODON" ]]; then
  echo "MEGALODON must point to an executable Megalodon binary" >&2
  exit 2
fi
if [[ ! -f "$MEGALODON_FILE" ]]; then
  echo "MEGALODON_FILE does not exist: $MEGALODON_FILE" >&2
  exit 2
fi

rm -rf "$CORPUS_DIR"
mkdir -p "$CORPUS_DIR"
ln -sfn "$CORPUS_DIR" "$TMPDIR/latest_megalodon_source_linked_corpus"

"$MEGALODON" \
  -allowincompleteqed \
  -createabyprobs "$CORPUS_DIR/$PREFIX" \
  "$MEGALODON_FILE" \
  > "$CORPUS_DIR/export.out" \
  2> "$CORPUS_DIR/export.err"
echo "source-linked corpus artifacts: $CORPUS_DIR"
echo "source-linked corpus latest link: $TMPDIR/latest_megalodon_source_linked_corpus"

PROBLEM_DIR="$CORPUS_DIR" \
CHECK_SOURCE_MAP=1 \
STRICT_CERT_V1="$STRICT_CERT_V1" \
PROBLEMS_FILE="$PROBLEMS_FILE" \
REQUIRE_SOURCE_ORIGIN=1 \
LIMIT="$LIMIT" \
JOBS="$JOBS" \
VAMPIRE_SECONDS="$VAMPIRE_SECONDS" \
VAMPIRE_OUTPUT_AXIOM_NAMES="$VAMPIRE_OUTPUT_AXIOM_NAMES" \
WALL_SECONDS="$WALL_SECONDS" \
MIN_PASS="$MIN_PASS" \
WORK_DIR="$WORK_DIR" \
  "$ROOT/tests/vampire_certificate/run_native_live_parallel.sh"
