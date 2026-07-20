#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
MEGALODON_VAMPIRE_TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}
WALL_SECONDS=${WALL_SECONDS:-120}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/live_hammer_falsee_qualifying.XXXXXX")"}

mkdir -p "$WORK_DIR/out"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_live_hammer_falsee_qualifying"

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
    /project/tmp/vampire-cmake-megalodon5/vampire \
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

prefix_file="$WORK_DIR/hammer_falsee_qualifying.mg"
awk 'NR<=170 {print}' "$SOURCE_FILE" |
  sed -E 's/^aby(.*)\.$/vampire\1./' >"$prefix_file"

expected_reconstructed=1
actual_vampire_commands=$(rg -c '^vampire( .*)?\.$' "$prefix_file" || true)
if [[ "$actual_vampire_commands" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed generated vampire command, got $actual_vampire_commands" >&2
  exit 1
fi
if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed/) {print FNR ":" $0}' \
    "$prefix_file" |
    rg . >&2; then
  echo "hammer FalseE qualifying fixture contains an admission-shaped token" >&2
  exit 1
fi

set +e
timeout "$WALL_SECONDS" "$MEGALODON" \
  -v 4 \
  -trustdeclaredaxioms \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "$MEGALODON_VAMPIRE_TIMEOUT" \
  -vampireabyproof megalodon \
  -vampireabyqualifying \
  -vampireabyoutdir "$WORK_DIR/out" \
  "$prefix_file" \
  >"$WORK_DIR/run.out" \
  2>"$WORK_DIR/run.err"
rc=$?
set -e
if (( rc != 0 )); then
  echo "hammer FalseE qualifying run failed with exit $rc" >&2
  tail -100 "$WORK_DIR/run.out" >&2 || true
  tail -100 "$WORK_DIR/run.err" >&2 || true
  exit "$rc"
fi

actual_reconstructed=$(
  rg -c 'Vampire proof command reconstructed proof term at line ' "$WORK_DIR/run.out" || true
)
if [[ "$actual_reconstructed" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed reconstructed vampire proof command, got $actual_reconstructed" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' "$WORK_DIR/run.out"; then
  echo "hammer FalseE qualifying fixture did not close" >&2
  exit 1
fi
if rg -q '\b(admit|aby)\b|-allowincompleteqed|depends on non-proved FalseE|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "hammer FalseE qualifying log contains forbidden proof artifact" >&2
  exit 1
fi

problem_count=$(find "$WORK_DIR/out" -name 'vampire.*.thf.p' | wc -l | tr -d ' ')
proof_count=$(find "$WORK_DIR/out" -name 'vampire.*.megalodon.out' | wc -l | tr -d ' ')
if [[ "$problem_count" != "$expected_reconstructed" || "$proof_count" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed THF/proof artifact, got THF=$problem_count proof=$proof_count" >&2
  exit 1
fi

echo "LIVE_HAMMER_FALSEE_QUALIFYING_PASS $expected_reconstructed"
echo "live hammer FalseE qualifying artifacts: $WORK_DIR"
echo "live hammer FalseE qualifying latest link: $TMPDIR/latest_live_hammer_falsee_qualifying"
echo "live hammer FalseE qualifying vampire: $VAMPIRE"
