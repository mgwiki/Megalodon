#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
MEGALODON_VAMPIRE_TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}
WALL_SECONDS=${WALL_SECONDS:-120}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/live_hammer_and_prefix_qualifying.XXXXXX")"}

mkdir -p "$WORK_DIR/out"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_live_hammer_and_prefix_qualifying"

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

prefix_file="$WORK_DIR/hammer_and_prefix_qualifying.mg"
awk 'NR<=177 {print}' "$SOURCE_FILE" |
  sed -E 's/^aby(.*)\.$/vampire\1./' >"$prefix_file"

expected_reconstructed=3
actual_vampire_commands=$(rg -c '^vampire( .*)?\.$' "$prefix_file" || true)
if [[ "$actual_vampire_commands" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed generated vampire commands, got $actual_vampire_commands" >&2
  exit 1
fi
if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed/) {print FNR ":" $0}' \
    "$prefix_file" |
    rg . >&2; then
  echo "hammer and-prefix qualifying fixture contains an admission-shaped token" >&2
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
if (( rc != 0 )); then
  echo "hammer and-prefix qualifying run failed with exit $rc" >&2
  tail -100 "$WORK_DIR/run.out" >&2 || true
  tail -100 "$WORK_DIR/run.err" >&2 || true
  exit "$rc"
fi

actual_reconstructed=$(
  rg -c 'Vampire proof command reconstructed proof term at line ' "$WORK_DIR/run.out" || true
)
if [[ "$actual_reconstructed" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed reconstructed vampire proof commands, got $actual_reconstructed" >&2
  exit 1
fi
signature_invariant_count=$(
  rg -c 'Qualifying Vampire reconstruction kept global signature unchanged after Vampire certificate reconstruction' \
    "$WORK_DIR/run.out" || true
)
if [[ "$signature_invariant_count" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed qualifying signature invariant checks, got $signature_invariant_count" >&2
  exit 1
fi
if rg -q 'Qualifying Vampire reconstruction (changed global signature|leaked certificate-local Qed state)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "hammer and-prefix qualifying leaked certificate reconstruction state" >&2
  exit 1
fi
if rg -q 'checked only with certificate delta|candidate checked only with certificate delta' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "hammer and-prefix qualifying relied on certificate-delta-only proof checking" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' "$WORK_DIR/run.out"; then
  echo "hammer and-prefix qualifying fixture did not close" >&2
  exit 1
fi
if rg -q '\b(admit|aby)\b|-allowincompleteqed|depends on non-proved|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "hammer and-prefix qualifying log contains forbidden proof artifact" >&2
  exit 1
fi

problem_count=$(find "$WORK_DIR/out" -name 'vampire.*.thf.p' | wc -l | tr -d ' ')
proof_count=$(find "$WORK_DIR/out" -name 'vampire.*.megalodon.out' | wc -l | tr -d ' ')
if [[ "$problem_count" != "$expected_reconstructed" || "$proof_count" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed THF/proof artifacts, got THF=$problem_count proof=$proof_count" >&2
  exit 1
fi

echo "LIVE_HAMMER_AND_PREFIX_QUALIFYING_PASS $expected_reconstructed"
echo "live hammer and-prefix qualifying artifacts: $WORK_DIR"
echo "live hammer and-prefix qualifying latest link: $TMPDIR/latest_live_hammer_and_prefix_qualifying"
echo "live hammer and-prefix qualifying vampire: $VAMPIRE"
