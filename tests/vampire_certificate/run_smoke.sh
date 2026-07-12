#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_substituted_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation_refutation.json --summary
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_resolution.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_resolution.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_substituted_resolution.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_substituted_resolution.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_equality_resolution_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_paramodulation_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
  "$TMPDIR/vampire_certificate_valid_resolution.mg" \
  "$TMPDIR/vampire_certificate_valid_substituted_resolution.mg" \
  "$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg"; then
  echo "generated Megalodon certificate proof contains an admission marker" >&2
  exit 1
fi
./bin/megalodon "$TMPDIR/vampire_certificate_valid_resolution.mg" >"$TMPDIR/vampire_certificate_valid_resolution.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_substituted_resolution.mg" >"$TMPDIR/vampire_certificate_valid_substituted_resolution.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.mg" >"$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg" >"$TMPDIR/vampire_certificate_valid_paramodulation_refutation.check.log"

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_pivot.json >"$TMPDIR/vampire_certificate_invalid_pivot.out" 2>"$TMPDIR/vampire_certificate_invalid_pivot.err"; then
  echo "invalid pivot certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/malformed_substitution.json >"$TMPDIR/vampire_certificate_malformed_substitution.out" 2>"$TMPDIR/vampire_certificate_malformed_substitution.err"; then
  echo "malformed substitution certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_substitution_result.json >"$TMPDIR/vampire_certificate_invalid_substitution_result.out" 2>"$TMPDIR/vampire_certificate_invalid_substitution_result.err"; then
  echo "invalid substitution-result certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_equality_resolution_positive.json >"$TMPDIR/vampire_certificate_invalid_equality_resolution_positive.out" 2>"$TMPDIR/vampire_certificate_invalid_equality_resolution_positive.err"; then
  echo "positive equality-resolution certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_equality_resolution_nonreflexive.json >"$TMPDIR/vampire_certificate_invalid_equality_resolution_nonreflexive.out" 2>"$TMPDIR/vampire_certificate_invalid_equality_resolution_nonreflexive.err"; then
  echo "non-reflexive equality-resolution certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_paramodulation_position.json >"$TMPDIR/vampire_certificate_invalid_paramodulation_position.out" 2>"$TMPDIR/vampire_certificate_invalid_paramodulation_position.err"; then
  echo "invalid-position paramodulation certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_paramodulation_orientation.json >"$TMPDIR/vampire_certificate_invalid_paramodulation_orientation.out" 2>"$TMPDIR/vampire_certificate_invalid_paramodulation_orientation.err"; then
  echo "wrong-orientation paramodulation certificate unexpectedly passed" >&2
  exit 1
fi

echo "vampire certificate smoke tests passed"
