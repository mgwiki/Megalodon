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

sed -n '1,286p' examples/hammer/100thms_12_h.mg > "$tmp_mg"

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
grep -q "Vampire certified aby at line 183 char 4" "$log"
grep -q "Vampire certified aby at line 187 char 4" "$log"
grep -q "Vampire certified aby at line 191 char 4" "$log"
grep -q "Vampire certified aby at line 195 char 4" "$log"
grep -q "Vampire certified aby at line 199 char 4" "$log"
grep -q "Vampire certified aby at line 203 char 4" "$log"
grep -q "Vampire certified aby at line 209 char 10" "$log"
grep -q "Vampire certified aby at line 215 char 10" "$log"
grep -q "Vampire certified aby at line 221 char 10" "$log"
grep -q "Vampire certified aby at line 227 char 10" "$log"
grep -q "Vampire certified aby at line 233 char 4" "$log"
grep -q "Vampire certified aby at line 237 char 4" "$log"
grep -q "Vampire certified aby at line 241 char 4" "$log"
grep -q "Vampire certified aby at line 245 char 4" "$log"
grep -q "Vampire certified aby at line 249 char 4" "$log"
grep -q "Vampire certified aby at line 253 char 4" "$log"
grep -q "Vampire certified aby at line 257 char 4" "$log"
grep -q "Vampire certified aby at line 261 char 4" "$log"
grep -q "Vampire certified aby at line 265 char 4" "$log"
grep -q "Vampire certified aby at line 269 char 13" "$log"
grep -q "Vampire certified aby at line 273 char 13" "$log"
grep -q "Vampire certified aby at line 277 char 4" "$log"
grep -q "Vampire certified aby at line 281 char 4" "$log"
grep -q "Vampire certified aby at line 285 char 23" "$log"
grep -q "Proof (fun _:False" "$log"
grep -q " of FalseE was assigned id" "$log"
grep -q " of andEL was assigned id" "$log"
grep -q " of andER was assigned id" "$log"
grep -q " of and3I was assigned id" "$log"
grep -q " of and3E was assigned id" "$log"
grep -q " of or3I1 was assigned id" "$log"
grep -q " of or3I2 was assigned id" "$log"
grep -q " of or3I3 was assigned id" "$log"
grep -q " of or3E was assigned id" "$log"
grep -q " of and4I was assigned id" "$log"
grep -q " of and5I was assigned id" "$log"
grep -q " of and6I was assigned id" "$log"
grep -q " of and7I was assigned id" "$log"
grep -q " of not_or_and_demorgan was assigned id" "$log"
grep -q " of not_ex_all_demorgan_i was assigned id" "$log"
grep -q " of iffEL was assigned id" "$log"
grep -q " of iffER was assigned id" "$log"
grep -q " of iff_refl was assigned id" "$log"
grep -q " of iff_sym was assigned id" "$log"
grep -q " of iff_trans was assigned id" "$log"
grep -q " of eq_i_tra was assigned id" "$log"
grep -q " of neq_i_sym was assigned id" "$log"
grep -q " of Eps_i_ex was assigned id" "$log"
grep -q " of prop_ext_2 was assigned id" "$log"
grep -q " of Subq_ref was assigned id" "$log"
grep -q " of Subq_tra was assigned id" "$log"
grep -q " of Empty_Subq_eq was assigned id" "$log"
! grep -q "Theorem FalseE admitted" "$log"
! grep -q "Theorem andEL admitted" "$log"
! grep -q "Theorem andER admitted" "$log"
! grep -q "Theorem and3I admitted" "$log"
! grep -q "Theorem and3E admitted" "$log"
! grep -q "Theorem or3I1 admitted" "$log"
! grep -q "Theorem or3I2 admitted" "$log"
! grep -q "Theorem or3I3 admitted" "$log"
! grep -q "Theorem or3E admitted" "$log"
! grep -q "Theorem and4I admitted" "$log"
! grep -q "Theorem and5I admitted" "$log"
! grep -q "Theorem and6I admitted" "$log"
! grep -q "Theorem and7I admitted" "$log"
! grep -q "Theorem not_or_and_demorgan admitted" "$log"
! grep -q "Theorem not_ex_all_demorgan_i admitted" "$log"
! grep -q "Theorem iffEL admitted" "$log"
! grep -q "Theorem iffER admitted" "$log"
! grep -q "Theorem iff_refl admitted" "$log"
! grep -q "Theorem iff_sym admitted" "$log"
! grep -q "Theorem iff_trans admitted" "$log"
! grep -q "Theorem eq_i_tra admitted" "$log"
! grep -q "Theorem neq_i_sym admitted" "$log"
! grep -q "Theorem Eps_i_ex admitted" "$log"
! grep -q "Theorem prop_ext_2 admitted" "$log"
! grep -q "Theorem Subq_ref admitted" "$log"
! grep -q "Theorem Subq_tra admitted" "$log"
! grep -q "Theorem Empty_Subq_eq admitted" "$log"
