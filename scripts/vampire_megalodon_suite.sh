#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
VAMPIRE=${VAMPIRE:-/project/vampire-leancheck/vampire_rel_vampire/megalodon_10780}
SOURCE=${SOURCE:-examples/hammer/100thms_12_h.mg}
EXPORT_MODE=${EXPORT_MODE:-aby}
LIMIT=${LIMIT:-1000}
JOBS=${JOBS:-10}
TIMEOUT=${TIMEOUT:-10}
WORK_DIR=${WORK_DIR:-"$TMPDIR/megalodon_vampire_suite_${LIMIT}"}
SKELETON_DIR=${SKELETON_DIR:-"$WORK_DIR/claim_skeletons"}

cd "$ROOT"

if [[ -n "${MANIFEST:-}" ]]; then
  manifest="$MANIFEST"
else
  python3 scripts/vampire_reconstruct_megalodon.py \
    --repo "$ROOT" \
    --megalodon "$MEGALODON" \
    --source "$SOURCE" \
    --export-mode "$EXPORT_MODE" \
    --work-dir "$WORK_DIR" \
    --limit "$LIMIT" \
    --timeout "$TIMEOUT" \
    --jobs "$JOBS" \
    --progress 50 \
    --proof-mode megalodon \
    --vampire "$VAMPIRE" \
    --collect-successes \
    --reuse-existing-proofs \
    --select-all-generated
  manifest="$WORK_DIR/manifest.jsonl"
fi

rm -rf "$SKELETON_DIR"
python3 scripts/vampire_reconstruct_megalodon.py \
  --repo "$ROOT" \
  --megalodon "$MEGALODON" \
  --source "$SOURCE" \
  --check-existing "$manifest" \
  --jobs "$JOBS" \
  --progress 50 \
  --check-claim-skeletons \
  --require-claim-skeletons \
  --claim-skeleton-dir "$SKELETON_DIR"

cat "$SKELETON_DIR/index.summary.json"
