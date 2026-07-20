#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
TARGETS=${TARGETS:-"172:4 183:4 233:4 10978:17 11106:19"}
EXPECT_FAIL_TARGETS=${EXPECT_FAIL_TARGETS:-}
JOBS=${JOBS:-10}
MEGALODON_VAMPIRE_TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}
WALL_SECONDS=${WALL_SECONDS:-90}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_aby_targets.XXXXXX")"}

mkdir -p "$WORK_DIR/cases"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_aby_targets"

if [[ ! -x "$MEGALODON" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

supports_megalodon_proof() {
  local candidate=$1
  [[ -x "$candidate" ]] || return 1
  local options
  options=$("$candidate" --show_options on 2>/dev/null) || return 1
  rg -q 'megalodon produces a Megalodon proof-reconstruction outline|^[[:space:]]+megalodon[[:space:]]*$' <<<"$options"
}

if [[ -z "${VAMPIRE:-}" ]]; then
  for candidate in \
    /project/tmp/vampire-megalodon5-build/vampire \
    /project/tmp/vampire-build-megalodon5/vampire \
    "$ROOT/../vampire-leancheck/vampire_rel_vampire/vampire" \
    "$ROOT/../vampire-leancheck/vampire_rel_detached_10761" \
    "$ROOT/../vampire-leancheck/vampire_rel_vampire"/megalodon*_*
  do
    if supports_megalodon_proof "$candidate"; then
      VAMPIRE=$candidate
      break
    fi
  done
fi

if [[ -z "${VAMPIRE:-}" || ! -x "$VAMPIRE" ]]; then
  echo "Set VAMPIRE=/path/to/vampire with --proof megalodon support" >&2
  exit 2
fi
if ! supports_megalodon_proof "$VAMPIRE"; then
  echo "VAMPIRE=$VAMPIRE does not advertise --proof megalodon support" >&2
  exit 2
fi

is_expected_fail() {
  local target=$1
  for expected in $EXPECT_FAIL_TARGETS; do
    if [[ "$target" == "$expected" ]]; then
      return 0
    fi
  done
  return 1
}

run_one() {
  local target=$1
  local line=${target%%:*}
  local char=${target#*:}
  local safe=${target/:/_}
  local case_dir="$WORK_DIR/cases/$safe"
  mkdir -p "$case_dir/out"

  set +e
  timeout "$WALL_SECONDS" "$MEGALODON" \
    -v 4 \
    -allowincompleteqed \
    -vampireaby "$VAMPIRE" \
    -vampireabytimeout "$MEGALODON_VAMPIRE_TIMEOUT" \
    -vampireabyproof megalodon \
    -vampireabynative \
    -vampireabynativestrict \
    -vampireabytarget "$line" "$char" \
    -vampireabytargetstop \
    -vampireabyoutdir "$case_dir/out" \
    "$SOURCE_FILE" \
    >"$case_dir/run.out" \
    2>"$case_dir/run.err"
  local rc=$?
  set -e

  local status=FAIL
  local detail=
  if (( rc == 0 )) \
      && rg -q "Vampire native certificate built local aby proof candidate at line $line char $char\\." "$case_dir/run.out" \
      && rg -q "Vampire certified aby at line $line char $char\\." "$case_dir/run.out" \
      && rg -q "Vampire target stop after reconstructed aby proof term at line $line char $char\\." "$case_dir/run.out"; then
    status=PASS
  else
    detail=$(tail -1 "$case_dir/run.err" | tr '\t' ' ')
    if [[ -z "$detail" ]]; then
      detail=$(tail -1 "$case_dir/run.out" | tr '\t' ' ')
    fi
    if [[ -z "$detail" ]]; then
      detail="exit $rc"
    else
      detail="exit $rc: $detail"
    fi
  fi

  if is_expected_fail "$target"; then
    if [[ "$status" == "PASS" ]]; then
      printf '%s\tUNEXPECTED_PASS\t%s\n' "$target" "$case_dir" >"$case_dir/result.tsv"
    else
      printf '%s\tEXPECTED_FAIL\t%s\t%s\n' "$target" "$case_dir" "$detail" >"$case_dir/result.tsv"
    fi
  else
    printf '%s\t%s\t%s\t%s\n' "$target" "$status" "$case_dir" "$detail" >"$case_dir/result.tsv"
  fi
}

export ROOT TMPDIR MEGALODON SOURCE_FILE VAMPIRE MEGALODON_VAMPIRE_TIMEOUT WALL_SECONDS WORK_DIR EXPECT_FAIL_TARGETS
export -f supports_megalodon_proof is_expected_fail run_one

printf '%s\n' $TARGETS >"$WORK_DIR/targets.txt"
xargs -a "$WORK_DIR/targets.txt" -n1 -P "$JOBS" bash -c 'run_one "$0"'

find "$WORK_DIR/cases" -name result.tsv -type f -print0 \
  | xargs -0 cat \
  | sort >"$WORK_DIR/summary.tsv"
cat "$WORK_DIR/summary.tsv"

awk -F '\t' '{count[$2]++} END {for (status in count) print status, count[status]}' \
  "$WORK_DIR/summary.tsv" \
  | sort >"$WORK_DIR/counts.txt"
cat "$WORK_DIR/counts.txt"

failures=$(awk -F '\t' '$2 == "FAIL" || $2 == "UNEXPECTED_PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")
passes=$(awk -F '\t' '$2 == "PASS" {n++} END {print n + 0}' "$WORK_DIR/summary.tsv")

echo "native aby target artifacts: $WORK_DIR"
echo "native aby target latest link: $TMPDIR/latest_native_aby_targets"
echo "native aby target vampire: $VAMPIRE"

if (( passes == 0 )); then
  echo "native aby target replay did not pass any selected target" >&2
  exit 1
fi
if (( failures != 0 )); then
  echo "native aby target replay had $failures unexpected failures" >&2
  exit 1
fi
