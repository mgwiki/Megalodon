#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

export TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

extra_args=()
if [ "${MEGALODON_VAMPIRE_CHECK_SOURCES:-0}" != "0" ]; then
  extra_args+=(--check-megalodon-sources)
fi
if [ "${MEGALODON_VAMPIRE_REQUIRE_SOURCES:-0}" != "0" ]; then
  extra_args+=(--require-megalodon-sources)
fi
if [ -n "${MEGALODON_VAMPIRE_FROM_MANIFEST:-}" ]; then
  extra_args+=(--from-manifest "$MEGALODON_VAMPIRE_FROM_MANIFEST")
fi

python3 scripts/vampire_reconstruct_megalodon.py \
  --limit "${MEGALODON_VAMPIRE_LIMIT:-100}" \
  --timeout "${MEGALODON_VAMPIRE_TIMEOUT:-60}" \
  --jobs "${MEGALODON_VAMPIRE_JOBS:-10}" \
  --proof-mode "${MEGALODON_VAMPIRE_PROOF_MODE:-tptp}" \
  "${extra_args[@]}" \
  "$@"
