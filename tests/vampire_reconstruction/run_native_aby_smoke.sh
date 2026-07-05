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
log="$(mktemp)"
trap 'rm -f "$tmp_mg" "$log"; rm -rf "$tmp_out"' EXIT

sed -n '1,177p' examples/hammer/100thms_12_h.mg > "$tmp_mg"

./bin/megalodon \
  -allowincompleteqed \
  -v 10 \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "${MEGALODON_VAMPIRE_TIMEOUT:-10}" \
  -vampireabyoutdir "$tmp_out" \
  -vampireabynativestrict \
  "$tmp_mg" > "$log" 2>&1

grep -q "Vampire certified aby at line 168 char 4" "$log"
grep -q "Vampire certified aby at line 172 char 4" "$log"
grep -q "Vampire certified aby at line 176 char 4" "$log"
grep -q "Proof (fun _:False" "$log"
grep -q " of FalseE was assigned id" "$log"
grep -q " of andEL was assigned id" "$log"
grep -q " of andER was assigned id" "$log"
! grep -q "Theorem FalseE admitted" "$log"
! grep -q "Theorem andEL admitted" "$log"
! grep -q "Theorem andER admitted" "$log"
