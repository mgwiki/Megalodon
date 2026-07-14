#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

if [ -z "${VAMPIRE:-}" ]; then
  echo "Set VAMPIRE=/path/to/vampire" >&2
  exit 2
fi

export TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

WORK_DIR="${WORK_DIR:-$(mktemp -d "$TMPDIR/live_aby_smoke.XXXXXX")}"
mkdir -p "$WORK_DIR"
tmp_mg="$WORK_DIR/100thms_12_h_slice.mg"
tmp_out="$WORK_DIR/out"
rm -rf "$tmp_out"
mkdir -p "$tmp_out"
if [ "${CLEANUP:-0}" = "1" ]; then
  trap 'rm -rf "$WORK_DIR"' EXIT
fi
proof_mode="${MEGALODON_VAMPIRE_PROOF:-tptp}"

sed -n '1,169p' examples/hammer/100thms_12_h.mg > "$tmp_mg"

./bin/megalodon \
  -allowincompleteqed \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "${MEGALODON_VAMPIRE_TIMEOUT:-10}" \
  -vampireabyoutdir "$tmp_out" \
  -vampireabyproof "$proof_mode" \
  "$tmp_mg"

if [ "$proof_mode" = "megalodon" ]; then
  grep -q 'megalodon_certificate_native_sexpr_start' "$tmp_out"/*.out
  grep -q 'megalodon_reconstruction_start' "$tmp_out"/*.out
  grep -q 'megalodon_step(' "$tmp_out"/*.out
  grep -q 'megalodon_reconstruction_end' "$tmp_out"/*.out
  grep -q 'megalodon_certificate_native_sexpr_end' "$tmp_out"/*.out
  ! grep -q 'megalodon_certificate_json_start' "$tmp_out"/*.out
  ! grep -q 'megalodon_certificate_step' "$tmp_out"/*.out
  ! grep -q 'megalodon_certificate_clause' "$tmp_out"/*.out
else
  grep -q 'SZS status \(Theorem\|Unsatisfiable\|ContradictoryAxioms\)' "$tmp_out"/*.out
  grep -q 'SZS output start\|inference(' "$tmp_out"/*.out
fi

echo "live aby smoke artifacts: $WORK_DIR"
