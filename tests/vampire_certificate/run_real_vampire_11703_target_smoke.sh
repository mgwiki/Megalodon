#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
TARGET_LINE=${TARGET_LINE:-11703}
TARGET_CHAR=${TARGET_CHAR:-242}
TARGET_LABEL=${TARGET_LABEL:-11703}
SOURCE_COMMAND=${SOURCE_COMMAND:-aby}
EXPECTED_STEPS=${EXPECTED_STEPS:-44}
EXPECTED_SOURCES=${EXPECTED_SOURCES:-7}
EXPECTED_CONTEXT=${EXPECTED_CONTEXT:-"known=1 local=4 local_definition=0 conjecture=2 unresolved=0"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/real_vampire_${TARGET_LABEL}_target.XXXXXX")"}
TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_real_vampire_${TARGET_LABEL}_target"

if [[ ! -x "$MEGALODON" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

case "$SOURCE_COMMAND" in
  aby)
    EFFECTIVE_SOURCE_FILE=$SOURCE_FILE
    EXPECTED_CHAR=${EXPECTED_CHAR:-$TARGET_CHAR}
    EXPECTED_TARGET_STOP="Vampire target stop after reconstructed aby proof term at line $TARGET_LINE char $EXPECTED_CHAR\\."
    ;;
  vampire)
    EFFECTIVE_SOURCE_FILE="$WORK_DIR/source_vampire_command.mg"
    awk -v line="$TARGET_LINE" '
      NR == line {
        if ($0 !~ /(^|[^[:alnum:]_])aby[[:space:]]/) {
          printf("target line %d does not contain an aby command: %s\n", line, $0) > "/dev/stderr";
          exit 42;
        }
        sub(/aby[[:space:]]/, "vampire ");
      }
      { print }
    ' "$SOURCE_FILE" >"$EFFECTIVE_SOURCE_FILE"
    EXPECTED_CHAR=${EXPECTED_CHAR:-$((TARGET_CHAR + 4))}
    EXPECTED_TARGET_STOP="Vampire target stop after reconstructed proof term at line $TARGET_LINE char $EXPECTED_CHAR\\."
    ;;
  *)
    echo "SOURCE_COMMAND must be aby or vampire, got $SOURCE_COMMAND" >&2
    exit 2
    ;;
esac

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

"$MEGALODON" \
  -v 9 \
  -allowincompleteqed \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "$TIMEOUT" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabynativestrict \
  -vampireabytarget "$TARGET_LINE" "$TARGET_CHAR" \
  -vampireabytargetstop \
  -vampireabyoutdir "$WORK_DIR/out" \
  "$EFFECTIVE_SOURCE_FILE" \
  >"$WORK_DIR/run.out" \
  2>"$WORK_DIR/run.err"

if ! rg -q "Vampire native certificate checked $EXPECTED_STEPS steps and $EXPECTED_SOURCES sources at line $TARGET_LINE char $EXPECTED_CHAR; source_context $EXPECTED_CONTEXT\\." "$WORK_DIR/run.out"; then
  echo "real Vampire $TARGET_LABEL target did not resolve the live source context" >&2
  exit 1
fi
if ! rg -q "Vampire native certificate reconstructed $SOURCE_COMMAND proof term at line $TARGET_LINE char $EXPECTED_CHAR\\." "$WORK_DIR/run.out"; then
  echo "real Vampire $TARGET_LABEL target did not reconstruct the selected proof term" >&2
  exit 1
fi
if ! rg -q "Vampire certified $SOURCE_COMMAND at line $TARGET_LINE char $EXPECTED_CHAR" "$WORK_DIR/run.out"; then
  echo "real Vampire $TARGET_LABEL target did not report the selected certification" >&2
  exit 1
fi
if ! rg -q "$EXPECTED_TARGET_STOP" "$WORK_DIR/run.out"; then
  echo "real Vampire $TARGET_LABEL target did not stop after reconstructing the selected proof term" >&2
  exit 1
fi
if rg -q 'Everything looks good\.' "$WORK_DIR/run.out"; then
  echo "real Vampire $TARGET_LABEL target unexpectedly checked the rest of the source file" >&2
  exit 1
fi

proof_count=$(find "$WORK_DIR/out" -maxdepth 1 -name '*.megalodon.out' | wc -l | tr -d ' ')
problem_count=$(find "$WORK_DIR/out" -maxdepth 1 -name '*.thf.p' | wc -l | tr -d ' ')
if [[ "$proof_count" != "1" || "$problem_count" != "1" ]]; then
  echo "real Vampire $TARGET_LABEL target expected exactly one problem/proof pair, got problems=$problem_count proofs=$proof_count" >&2
  exit 1
fi

if ! rg -q 'megalodon_certificate_native_sexpr_start\.' "$WORK_DIR/out"/*.megalodon.out; then
  echo "real Vampire $TARGET_LABEL target proof output did not contain a native certificate block" >&2
  exit 1
fi
if ! find "$WORK_DIR/out" -maxdepth 1 -name "$SOURCE_COMMAND.*.thf.p" | rg -q .; then
  echo "real Vampire $TARGET_LABEL target did not write a $SOURCE_COMMAND-named THF artifact" >&2
  exit 1
fi
if ! rg -q "^% megalodon_origin .* \\(kind \"$SOURCE_COMMAND\"\\)" "$WORK_DIR/out"/*.thf.p; then
  echo "real Vampire $TARGET_LABEL target did not export origin kind $SOURCE_COMMAND" >&2
  exit 1
fi

echo "real Vampire $TARGET_LABEL $SOURCE_COMMAND target smoke passed"
echo "real Vampire $TARGET_LABEL target vampire: $VAMPIRE"
echo "real Vampire $TARGET_LABEL target artifacts: $WORK_DIR"
echo "real Vampire $TARGET_LABEL target latest link: $TMPDIR/latest_real_vampire_${TARGET_LABEL}_target"
