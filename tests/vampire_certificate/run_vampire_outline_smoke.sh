#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

if [[ -z "${VAMPIRE_BIN:-}" ]]; then
  VAMPIRE_BIN="$(find /project/vampire-leancheck/vampire_rel_vampire -maxdepth 1 -type f -perm -111 -name 'megalodon1_*' 2>/dev/null | sort | tail -n 1 || true)"
fi

if [[ -z "${VAMPIRE_BIN:-}" ]]; then
  VAMPIRE_BIN="$(find /project/vampire-leancheck/vampire_rel_vampire -maxdepth 1 -type f -perm -111 2>/dev/null | sort | tail -n 1 || true)"
fi

if [[ -z "$VAMPIRE_BIN" || ! -x "$VAMPIRE_BIN" ]]; then
  echo "VAMPIRE_BIN must point to a Vampire binary with megalodon_certificate_clause output" >&2
  exit 1
fi

problem="$TMPDIR/vampire_outline_smoke.p"
outline="$TMPDIR/vampire_outline_smoke.out"
certificate="$TMPDIR/vampire_outline_smoke.json"
megalodon="$TMPDIR/vampire_outline_smoke.mg"

cat >"$problem" <<'PROBLEM'
fof(a1, axiom, p(a)).
fof(c, conjecture, p(a)).
PROBLEM

"$VAMPIRE_BIN" \
  --input_syntax tptp \
  --mode casc \
  -t 10 \
  --proof megalodon \
  --output_axiom_names on \
  "$problem" >"$outline"

python3 scripts/vampire_certificate.py \
  "$outline" \
  --from-vampire-outline \
  --summary \
  --write-certificate "$certificate" \
  --emit-megalodon "$megalodon"

if rg -n '\badmit\b|\baby\b|-allowincompleteqed' "$megalodon"; then
  echo "generated Megalodon proof contains an admission marker" >&2
  exit 1
fi

./bin/megalodon "$megalodon" >"$TMPDIR/vampire_outline_smoke.check.log"

echo "vampire outline smoke test passed"
