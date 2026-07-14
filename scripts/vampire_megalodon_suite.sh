#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
if [[ -x /project/tmp/vampire-megalodon-build/vampire ]]; then
  DEFAULT_VAMPIRE=/project/tmp/vampire-megalodon-build/vampire
else
  DEFAULT_VAMPIRE=$(
    find /project/vampire-leancheck/vampire_rel_vampire \
      -maxdepth 1 \
      -type f \
      -executable \
      -name 'megalodon*_*' \
      2>/dev/null \
      | sort -V \
      | tail -n 1
  )
fi
VAMPIRE=${VAMPIRE:-"$DEFAULT_VAMPIRE"}
SOURCE=${SOURCE:-examples/hammer/100thms_12_h.mg}
EXPORT_MODE=${EXPORT_MODE:-admit}
LIMIT=${LIMIT:-1000}
JOBS=${JOBS:-10}
TIMEOUT=${TIMEOUT:-10}
WORK_DIR=${WORK_DIR:-"$TMPDIR/megalodon_vampire_suite_${LIMIT}"}
SKELETON_DIR=${SKELETON_DIR:-"$WORK_DIR/claim_skeletons"}
CHECK_CLAIM_SKELETONS=${CHECK_CLAIM_SKELETONS:-1}
CHECK_RAW_TPTP=${CHECK_RAW_TPTP:-1}
RAW_TPTP_REPLAY_SECONDS=${RAW_TPTP_REPLAY_SECONDS:-1.0}
RAW_TPTP_SKELETON_SECONDS=${RAW_TPTP_SKELETON_SECONDS:-10}
RAW_TPTP_SKELETON_DIR=${RAW_TPTP_SKELETON_DIR:-"$WORK_DIR/raw_tptp_skeletons"}
RAW_TPTP_CHECK_DIR=${RAW_TPTP_CHECK_DIR:-"$WORK_DIR/raw_tptp_checks"}
RAW_TPTP_PROOF_LIST=${RAW_TPTP_PROOF_LIST:-}
RAW_TPTP_PROOF_DIR=${RAW_TPTP_PROOF_DIR:-}
RAW_TPTP_CHECK_MODE=${RAW_TPTP_CHECK_MODE:-noadmit}
RAW_TPTP_CHECK_TIMEOUT=${RAW_TPTP_CHECK_TIMEOUT:-30}
RAW_TPTP_MIN_OK=${RAW_TPTP_MIN_OK:-0}
RAW_TPTP_MIN_SOURCE_BRIDGES=${RAW_TPTP_MIN_SOURCE_BRIDGES:-0}

cd "$ROOT"

if [[ -n "$RAW_TPTP_PROOF_LIST" || -n "$RAW_TPTP_PROOF_DIR" ]]; then
  manifest=""
elif [[ -n "${MANIFEST:-}" ]]; then
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
    --require-claim-skeletons \
    --reuse-existing-proofs \
    --select-all-generated
  manifest="$WORK_DIR/manifest.jsonl"
fi

if [[ "$CHECK_CLAIM_SKELETONS" != 0 && -n "$manifest" ]]; then
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
fi

if [[ "$CHECK_RAW_TPTP" != 0 ]]; then
  mkdir -p "$WORK_DIR"
  proof_list="$WORK_DIR/raw_tptp_proofs.txt"
  if [[ -n "$RAW_TPTP_PROOF_LIST" ]]; then
    cp "$RAW_TPTP_PROOF_LIST" "$proof_list"
  elif [[ -n "$RAW_TPTP_PROOF_DIR" ]]; then
    find "$RAW_TPTP_PROOF_DIR" -maxdepth 1 -type f \( -name '*.out' -o -name '*.th0.p' \) | sort -V > "$proof_list"
  else
    python3 - "$manifest" "$proof_list" <<'PY'
import json
import sys
from pathlib import Path

manifest = Path(sys.argv[1])
proof_list = Path(sys.argv[2])
proofs = []
for row in manifest.read_text(encoding="utf-8").splitlines():
    if not row.strip():
        continue
    proof = json.loads(row).get("proof")
    if proof:
        proofs.append(proof)
proof_list.write_text("\n".join(proofs) + ("\n" if proofs else ""), encoding="utf-8")
PY
  fi

  proof_args=()
  while IFS= read -r proof; do
    proof=${proof%%#*}
    proof=${proof%"${proof##*[![:space:]]}"}
    proof=${proof#"${proof%%[![:space:]]*}"}
    [[ -n "$proof" ]] || continue
    proof_args+=(--raw-tptp-proof "$proof")
  done < "$proof_list"
  raw_selected=$(printf '%s\n' "${proof_args[@]}" | rg -c '^--raw-tptp-proof$' || true)

  rm -rf "$RAW_TPTP_SKELETON_DIR" "$RAW_TPTP_CHECK_DIR"
  raw_admit_pattern='^\s*(\{\s*)?admit\.\s*(\})?\s*$'
  mkdir -p "$RAW_TPTP_CHECK_DIR"

  raw_check_args=()
  if [[ "$RAW_TPTP_CHECK_MODE" == noadmit ]]; then
    raw_check_args+=(
      --check-raw-tptp-skeletons
      --raw-tptp-check-dir "$RAW_TPTP_CHECK_DIR"
      --raw-tptp-check-timeout "$RAW_TPTP_CHECK_TIMEOUT"
    )
  fi

  case "$RAW_TPTP_CHECK_MODE" in
    noadmit)
      MEGALODON_RAW_TPTP_REPLAY_SECONDS="$RAW_TPTP_REPLAY_SECONDS" \
      MEGALODON_RAW_TPTP_SKELETON_SECONDS="$RAW_TPTP_SKELETON_SECONDS" \
      python3 scripts/vampire_reconstruct_megalodon.py \
        --repo "$ROOT" \
        --megalodon "$MEGALODON" \
        --source "$SOURCE" \
        "${proof_args[@]}" \
        --raw-tptp-skeleton-dir "$RAW_TPTP_SKELETON_DIR" \
        --jobs "$JOBS" \
        "${raw_check_args[@]}" \
        | tee "$RAW_TPTP_CHECK_DIR/status.txt"
      raw_checked=$(find "$RAW_TPTP_CHECK_DIR" -maxdepth 1 -name '*.source_context.log' | wc -l)
      raw_check_failures=$({ rg -n 'raw TPTP source-context check fail:' "$RAW_TPTP_CHECK_DIR/status.txt" || true; } | wc -l)
      ;;
    allow_admits)
      MEGALODON_RAW_TPTP_REPLAY_SECONDS="$RAW_TPTP_REPLAY_SECONDS" \
      MEGALODON_RAW_TPTP_SKELETON_SECONDS="$RAW_TPTP_SKELETON_SECONDS" \
      python3 scripts/vampire_reconstruct_megalodon.py \
        --repo "$ROOT" \
        --megalodon "$MEGALODON" \
        --source "$SOURCE" \
        "${proof_args[@]}" \
        --raw-tptp-skeleton-dir "$RAW_TPTP_SKELETON_DIR" \
        --check-raw-tptp-skeletons \
        --allow-raw-tptp-admits \
        --raw-tptp-check-dir "$RAW_TPTP_CHECK_DIR" \
        --raw-tptp-check-timeout "$RAW_TPTP_CHECK_TIMEOUT" \
        --jobs "$JOBS" \
        | tee "$RAW_TPTP_CHECK_DIR/status.txt"
      raw_checked=$(find "$RAW_TPTP_CHECK_DIR" -maxdepth 1 -name '*.source_context.log' | wc -l)
      raw_check_failures=0
      ;;
    none)
      MEGALODON_RAW_TPTP_REPLAY_SECONDS="$RAW_TPTP_REPLAY_SECONDS" \
      MEGALODON_RAW_TPTP_SKELETON_SECONDS="$RAW_TPTP_SKELETON_SECONDS" \
      python3 scripts/vampire_reconstruct_megalodon.py \
        --repo "$ROOT" \
        --megalodon "$MEGALODON" \
        --source "$SOURCE" \
        "${proof_args[@]}" \
        --raw-tptp-skeleton-dir "$RAW_TPTP_SKELETON_DIR" \
        --jobs "$JOBS" \
        | tee "$RAW_TPTP_CHECK_DIR/status.txt"
      raw_checked=0
      raw_check_failures=0
      ;;
    *)
      echo "unknown RAW_TPTP_CHECK_MODE=$RAW_TPTP_CHECK_MODE" >&2
      exit 2
      ;;
  esac

  raw_admits=$({ rg -n "$raw_admit_pattern" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_aby=$({ rg -n "\baby\b" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_timeouts=$(find "$RAW_TPTP_SKELETON_DIR" -maxdepth 1 -name '*.timeout' | wc -l)
  raw_written=$(find "$RAW_TPTP_SKELETON_DIR" -maxdepth 1 -name '*.mg' | wc -l)
  raw_source_bridges=$({ rg -l "source-shaped theorem reconstructed" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_local_claim_bridges=$({ rg -l "original Megalodon local claim" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_local_prove_bridges=$({ rg -l "original Megalodon local prove" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_skipped=$(
    awk -F': ' '/raw TPTP skeletons skipped without reconstructable proof content:/ {sum += $NF} END {print sum + 0}' \
      "$RAW_TPTP_CHECK_DIR/status.txt"
  )

  printf '{"raw_tptp_selected":%s,"raw_tptp_written":%s,"raw_tptp_checked":%s,"raw_tptp_check_failures":%s,"raw_tptp_skipped":%s,"raw_tptp_timeouts":%s}\n' \
    "$raw_selected" "$raw_written" "$raw_checked" "$raw_check_failures" "$raw_skipped" "$raw_timeouts"
  printf '{"raw_tptp_skeleton_dir":"%s","raw_tptp_check_dir":"%s","raw_tptp_admits":%s,"raw_tptp_aby":%s,"raw_tptp_source_bridges":%s,"raw_tptp_local_claim_bridges":%s,"raw_tptp_local_prove_bridges":%s}\n' \
    "$RAW_TPTP_SKELETON_DIR" "$RAW_TPTP_CHECK_DIR" "$raw_admits" "$raw_aby" "$raw_source_bridges" "$raw_local_claim_bridges" "$raw_local_prove_bridges"
  if (( raw_checked < RAW_TPTP_MIN_OK )); then
    echo "raw TPTP checked $raw_checked skeletons, below RAW_TPTP_MIN_OK=$RAW_TPTP_MIN_OK" >&2
    exit 1
  fi
  if (( raw_source_bridges < RAW_TPTP_MIN_SOURCE_BRIDGES )); then
    echo "raw TPTP source bridges $raw_source_bridges, below RAW_TPTP_MIN_SOURCE_BRIDGES=$RAW_TPTP_MIN_SOURCE_BRIDGES" >&2
    exit 1
  fi
  if [[ "$raw_aby" != 0 || "$raw_check_failures" != 0 ]]; then
    exit 1
  fi
fi
