#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

JOBS=${JOBS:-4}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/real_vampire_targets.XXXXXX")"}
RUN_ONE="$ROOT/tests/vampire_certificate/run_real_vampire_11703_target_smoke.sh"

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_real_vampire_targets"

if [[ ! -x "$RUN_ONE" ]]; then
  echo "missing target smoke runner: $RUN_ONE" >&2
  exit 2
fi

run_one_target() {
  local row=$1
  local label line char expected_steps expected_sources expected_context
  IFS=$'\t' read -r label line char expected_steps expected_sources expected_context <<<"$row"

  local case_dir="$WORK_DIR/cases/$label"
  mkdir -p "$case_dir"

  if TARGET_LINE="$line" \
    TARGET_CHAR="$char" \
    TARGET_LABEL="$label" \
    EXPECTED_STEPS="$expected_steps" \
    EXPECTED_SOURCES="$expected_sources" \
    EXPECTED_CONTEXT="$expected_context" \
    WORK_DIR="$case_dir" \
    ROOT="$ROOT" \
    TMPDIR="$TMPDIR" \
    VAMPIRE="${VAMPIRE:-}" \
    MEGALODON="${MEGALODON:-}" \
    SOURCE_FILE="${SOURCE_FILE:-}" \
    MEGALODON_VAMPIRE_TIMEOUT="${MEGALODON_VAMPIRE_TIMEOUT:-10}" \
    "$RUN_ONE" >"$case_dir/batch.out" 2>"$case_dir/batch.err"
  then
    printf '%s\tPASS\tline=%s\tchar=%s\tsteps=%s\tsources=%s\t%s\n' \
      "$label" "$line" "$char" "$expected_steps" "$expected_sources" \
      "$expected_context" >"$case_dir/result.tsv"
  else
    local status=$?
    local msg
    msg=$((rg -n 'did not resolve|did not reconstruct|did not report|did not stop|expected exactly|failed|Failure|Error|Vampire native certificate checked|source_context|target smoke passed' "$case_dir/batch.out" "$case_dir/batch.err" 2>/dev/null || true) | tail -10 | tr '\n\t' ' ')
    printf '%s\tFAIL_%s\tline=%s\tchar=%s\t%s\n' \
      "$label" "$status" "$line" "$char" "$msg" >"$case_dir/result.tsv"
  fi
}

export ROOT TMPDIR WORK_DIR RUN_ONE VAMPIRE MEGALODON SOURCE_FILE MEGALODON_VAMPIRE_TIMEOUT
export -f run_one_target

cat <<'TARGETS' | xargs -P "$JOBS" -I{} bash -c 'run_one_target "$1"' bash "{}"
10809	10809	92	11	3	known=0 local=1 local_definition=0 conjecture=2 unresolved=0
10823	10823	92	9	3	known=0 local=1 local_definition=0 conjecture=2 unresolved=0
11203	11203	25	22	3	known=1 local=0 local_definition=0 conjecture=2 unresolved=0
11453	11453	77	65	8	known=6 local=0 local_definition=0 conjecture=2 unresolved=0
11555	11555	42	11	3	known=1 local=0 local_definition=0 conjecture=2 unresolved=0
11560	11560	31	5	2	known=0 local=0 local_definition=0 conjecture=2 unresolved=0
11572	11572	88	11	3	known=0 local=1 local_definition=0 conjecture=2 unresolved=0
11578	11578	57	15	4	known=0 local=2 local_definition=0 conjecture=2 unresolved=0
11696	11696	239	11	3	known=0 local=1 local_definition=0 conjecture=2 unresolved=0
11703	11703	242	44	7	known=1 local=4 local_definition=0 conjecture=2 unresolved=0
11706	11706	270	13	3	known=0 local=1 local_definition=0 conjecture=2 unresolved=0
TARGETS

find "$WORK_DIR/cases" -name result.tsv -print0 | sort -z | xargs -0 cat \
  | tee "$WORK_DIR/summary.tsv"

if rg -q $'\tFAIL_' "$WORK_DIR/summary.tsv"; then
  echo "real Vampire target batch had failures: $WORK_DIR" >&2
  exit 1
fi

pass_count=$(rg -c $'\tPASS\t' "$WORK_DIR/summary.tsv")
if [[ "$pass_count" != "11" ]]; then
  echo "real Vampire target batch expected 11 passes, got $pass_count" >&2
  exit 1
fi

echo "real Vampire target batch smoke passed"
echo "real Vampire target batch artifacts: $WORK_DIR"
echo "real Vampire target batch latest link: $TMPDIR/latest_real_vampire_targets"
