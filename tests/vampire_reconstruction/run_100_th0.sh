#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

export TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

python3 scripts/vampire_reconstruct_megalodon.py \
  --limit "${MEGALODON_VAMPIRE_LIMIT:-100}" \
  --timeout "${MEGALODON_VAMPIRE_TIMEOUT:-60}" \
  --jobs "${MEGALODON_VAMPIRE_JOBS:-10}" \
  "$@"
