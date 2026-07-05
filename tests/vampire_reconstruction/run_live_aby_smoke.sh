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

tmp_mg="$(mktemp)"
tmp_out="$(mktemp -d)"
trap 'rm -f "$tmp_mg"; rm -rf "$tmp_out"' EXIT

sed -n '1,169p' examples/hammer/100thms_12_h.mg > "$tmp_mg"

./bin/megalodon \
  -allowincompleteqed \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "${MEGALODON_VAMPIRE_TIMEOUT:-10}" \
  -vampireabyoutdir "$tmp_out" \
  "$tmp_mg"

grep -q 'SZS status \(Theorem\|Unsatisfiable\|ContradictoryAxioms\)' "$tmp_out"/*.out
grep -q 'SZS output start\|inference(' "$tmp_out"/*.out
