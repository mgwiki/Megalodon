#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/vampireaby_qualifying_guards.XXXXXX")"}
mkdir -p "$WORK_DIR"

cd "$ROOT"

if [ ! -x bin/megalodon ]; then
  TMPDIR="$TMPDIR" ./makeopt
fi

if MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1 \
    bin/megalodon \
      -vampireabyqualifying \
      examples/egal/PfgENov2021Preambles.mg \
      >"$WORK_DIR/transitional_known_allowed.out" \
      2>"$WORK_DIR/transitional_known_allowed.err"; then
  echo "qualifying mode accepted transitional certificate Known escape hatch" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying cannot be combined with MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1' \
    "$WORK_DIR/transitional_known_allowed.err"; then
  echo "qualifying mode failed for the wrong reason when transitional Known escape hatch was set" >&2
  cat "$WORK_DIR/transitional_known_allowed.err" >&2
  exit 1
fi

echo "vampireaby qualifying guard checks passed"
