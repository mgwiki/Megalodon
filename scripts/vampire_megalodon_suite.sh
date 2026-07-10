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
      -name 'megalodon_*' \
      2>/dev/null \
      | sort -V \
      | tail -n 1
  )
  DEFAULT_VAMPIRE=${DEFAULT_VAMPIRE:-/project/vampire-leancheck/vampire_rel_vampire/megalodon_10780}
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
RAW_TPTP_SKELETON_DIR=${RAW_TPTP_SKELETON_DIR:-"$WORK_DIR/raw_tptp_skeletons"}
RAW_TPTP_CHECK_DIR=${RAW_TPTP_CHECK_DIR:-"$WORK_DIR/raw_tptp_checks"}
RAW_TPTP_PROOF_DIR=${RAW_TPTP_PROOF_DIR:-}
RAW_TPTP_CHECK_MODE=${RAW_TPTP_CHECK_MODE:-noadmit}

cd "$ROOT"

if [[ -n "$RAW_TPTP_PROOF_DIR" ]]; then
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
  if [[ -n "$RAW_TPTP_PROOF_DIR" ]]; then
    find "$RAW_TPTP_PROOF_DIR" -maxdepth 1 -type f -name '*.out' | sort > "$proof_list"
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
    [[ -n "$proof" ]] || continue
    proof_args+=(--raw-tptp-proof "$proof")
  done < "$proof_list"

  rm -rf "$RAW_TPTP_SKELETON_DIR" "$RAW_TPTP_CHECK_DIR"
  MEGALODON_RAW_TPTP_REPLAY_SECONDS="$RAW_TPTP_REPLAY_SECONDS" \
  python3 scripts/vampire_reconstruct_megalodon.py \
    --repo "$ROOT" \
    --megalodon "$MEGALODON" \
    --source "$SOURCE" \
    "${proof_args[@]}" \
    --raw-tptp-skeleton-dir "$RAW_TPTP_SKELETON_DIR" \
    --jobs "$JOBS"

  raw_admit_pattern='^\s*(\{\s*)?admit\.\s*(\})?\s*$'
  raw_admits=$({ rg -n "$raw_admit_pattern" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  raw_aby=$({ rg -n "\baby\b" "$RAW_TPTP_SKELETON_DIR" -g '*.mg' || true; } | wc -l)
  mkdir -p "$RAW_TPTP_CHECK_DIR"

  case "$RAW_TPTP_CHECK_MODE" in
    noadmit)
      noadmit_list="$WORK_DIR/raw_tptp_noadmit_skeletons.txt"
      find "$RAW_TPTP_SKELETON_DIR" -maxdepth 1 -name '*.mg' | sort | while IFS= read -r skeleton; do
        if ! rg -q "$raw_admit_pattern" "$skeleton"; then
          printf '%s\n' "$skeleton"
        fi
      done > "$noadmit_list"
      check_one_raw_tptp_skeleton() {
        local skeleton="$1"
        local base context log status
        base=$(basename "$skeleton" .mg)
        context="$RAW_TPTP_CHECK_DIR/${base}.source_context.mg"
        log="$RAW_TPTP_CHECK_DIR/${base}.source_context.log"
        { cat "$SOURCE"; printf '\n'; cat "$skeleton"; } > "$context"
        if timeout 30 "$MEGALODON" -allowincompleteqed "$context" > "$log" 2>&1; then
          printf 'ok %s\n' "$base"
        else
          status=$?
          printf 'fail %s %s log=%s\n' "$status" "$base" "$log"
        fi
      }
      export SOURCE RAW_TPTP_CHECK_DIR MEGALODON
      export -f check_one_raw_tptp_skeleton
      if [[ -s "$noadmit_list" ]]; then
        xargs -a "$noadmit_list" -P "$JOBS" -n 1 bash -lc 'check_one_raw_tptp_skeleton "$0"' \
          | tee "$RAW_TPTP_CHECK_DIR/status.txt"
      else
        : > "$RAW_TPTP_CHECK_DIR/status.txt"
      fi
      raw_checked=$(wc -l < "$noadmit_list")
      raw_check_failures=$({ rg -n '^fail ' "$RAW_TPTP_CHECK_DIR/status.txt" || true; } | wc -l)
      ;;
    allow_admits)
      MEGALODON_RAW_TPTP_REPLAY_SECONDS="$RAW_TPTP_REPLAY_SECONDS" \
      python3 scripts/vampire_reconstruct_megalodon.py \
        --repo "$ROOT" \
        --megalodon "$MEGALODON" \
        --source "$SOURCE" \
        "${proof_args[@]}" \
        --raw-tptp-skeleton-dir "$RAW_TPTP_SKELETON_DIR" \
        --check-raw-tptp-skeletons \
        --allow-raw-tptp-admits \
        --raw-tptp-check-dir "$RAW_TPTP_CHECK_DIR" \
        --raw-tptp-check-timeout 30 \
        --jobs "$JOBS"
      raw_checked=$(find "$RAW_TPTP_SKELETON_DIR" -maxdepth 1 -name '*.mg' | wc -l)
      raw_check_failures=0
      ;;
    none)
      raw_checked=0
      raw_check_failures=0
      ;;
    *)
      echo "unknown RAW_TPTP_CHECK_MODE=$RAW_TPTP_CHECK_MODE" >&2
      exit 2
      ;;
  esac

  printf '{"raw_tptp_skeleton_dir":"%s","raw_tptp_check_dir":"%s","raw_tptp_admits":%s,"raw_tptp_aby":%s}\n' \
    "$RAW_TPTP_SKELETON_DIR" "$RAW_TPTP_CHECK_DIR" "$raw_admits" "$raw_aby"
  printf '{"raw_tptp_check_mode":"%s","raw_tptp_checked":%s,"raw_tptp_check_failures":%s}\n' \
    "$RAW_TPTP_CHECK_MODE" "$raw_checked" "$raw_check_failures"
  if [[ "$raw_aby" != 0 || "$raw_check_failures" != 0 ]]; then
    exit 1
  fi
fi
