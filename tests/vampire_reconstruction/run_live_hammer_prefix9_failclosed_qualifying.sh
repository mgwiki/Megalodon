#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
MEGALODON_VAMPIRE_TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}
WALL_SECONDS=${WALL_SECONDS:-120}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/live_hammer_prefix9_failclosed_qualifying.XXXXXX")"}

mkdir -p "$WORK_DIR/out"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_live_hammer_prefix9_failclosed_qualifying"

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
    /project/tmp/vampire-cmake-megalodon6/vampire \
    /project/tmp/vampire-megalodon6-build/vampire \
    /project/tmp/vampire-build-megalodon6/vampire \
    "$ROOT/../vampire-leancheck/vampire_rel_vampire/vampire" \
    "$ROOT/../vampire-leancheck/vampire_rel_detached_10761"
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

vampire_wrapper="$WORK_DIR/vampire-noavatar"
cat >"$vampire_wrapper" <<EOF
#!/usr/bin/env bash
exec "$VAMPIRE" --avatar off "\$@"
EOF
chmod +x "$vampire_wrapper"

prefix_file="$WORK_DIR/hammer_prefix9_failclosed_qualifying.mg"
awk 'NR<=204 {print}' "$SOURCE_FILE" |
  sed -E 's/^aby(.*)\.$/vampire\1./' >"$prefix_file"

expected_successes_before_frontier=8
actual_vampire_commands=$(rg -c '^vampire( .*)?\.$' "$prefix_file" || true)
if [[ "$actual_vampire_commands" != "9" ]]; then
  echo "expected 9 generated vampire commands, got $actual_vampire_commands" >&2
  exit 1
fi
if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed/) {print FNR ":" $0}' \
    "$prefix_file" |
    rg . >&2; then
  echo "prefix9 fail-closed fixture contains an admission-shaped token" >&2
  exit 1
fi

set +e
MEGALODON_CERT_DEBUG_TIMING=1 \
timeout "$WALL_SECONDS" "$MEGALODON" \
  -v 4 \
  -trustdeclaredaxioms \
  -vampireaby "$vampire_wrapper" \
  -vampireabytimeout "$MEGALODON_VAMPIRE_TIMEOUT" \
  -vampireabyproof megalodon \
  -vampireabyqualifying \
  -vampireabyoutdir "$WORK_DIR/out" \
  "$prefix_file" \
  >"$WORK_DIR/run.out" \
  2>"$WORK_DIR/run.err"
rc=$?
set -e
if (( rc == 0 )); then
  echo "prefix9 unexpectedly passed; update this guard only after or3E has a small-kernel reconstruction" >&2
  exit 1
fi

actual_reconstructed=$(
  rg -c 'Vampire proof command reconstructed proof term at line ' "$WORK_DIR/run.out" || true
)
if [[ "$actual_reconstructed" != "$expected_successes_before_frontier" ]]; then
  echo "expected $expected_successes_before_frontier reconstructed vampire commands before frontier, got $actual_reconstructed" >&2
  exit 1
fi
signature_invariant_count=$(
  rg -c 'Qualifying Vampire reconstruction kept global signature unchanged after ' \
    "$WORK_DIR/run.out" || true
)
if (( signature_invariant_count < actual_reconstructed + 1 )); then
  echo "expected qualifying signature invariant checks for the reconstructed prefix and failing frontier, got $signature_invariant_count" >&2
  exit 1
fi
if rg -q 'Qualifying Vampire reconstruction (changed global signature|leaked certificate-local Qed state)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "qualifying prefix9 leaked certificate reconstruction state" >&2
  exit 1
fi
if ! rg -q \
    'candidate_refutation_fallback:disabled_by_qualifying_mode|native preprocess proof-term predicate fold does not support this formula context' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "qualifying prefix9 did not stop at a known deterministic fail-closed guard" >&2
  tail -100 "$WORK_DIR/run.out" >&2 || true
  tail -100 "$WORK_DIR/run.err" >&2 || true
  exit 1
fi
if rg -q 'candidate_refutation_fallback:start' "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "qualifying prefix9 entered candidate-refutation fallback search" >&2
  exit 1
fi
if rg -q 'Vampire native supplied-refutation timing .* depth=([2-9]|[1-9][0-9]+)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "qualifying prefix9 used supplied-refutation search deeper than depth 1" >&2
  exit 1
fi
if ! rg -q 'Vampire native certificate did not reconstruct current proof goal' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "qualifying prefix9 failed for an unexpected reason" >&2
  tail -100 "$WORK_DIR/run.out" >&2 || true
  tail -100 "$WORK_DIR/run.err" >&2 || true
  exit 1
fi

echo "LIVE_HAMMER_PREFIX9_FAILCLOSED_QUALIFYING_PASS"
echo "live hammer prefix9 fail-closed qualifying artifacts: $WORK_DIR"
echo "live hammer prefix9 fail-closed qualifying latest link: $TMPDIR/latest_live_hammer_prefix9_failclosed_qualifying"
echo "live hammer prefix9 fail-closed qualifying vampire: $VAMPIRE"
