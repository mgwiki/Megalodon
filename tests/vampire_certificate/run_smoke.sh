#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_resolution.json --summary

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_pivot.json >"$TMPDIR/vampire_certificate_invalid_pivot.out" 2>"$TMPDIR/vampire_certificate_invalid_pivot.err"; then
  echo "invalid pivot certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/malformed_substitution.json >"$TMPDIR/vampire_certificate_malformed_substitution.out" 2>"$TMPDIR/vampire_certificate_malformed_substitution.err"; then
  echo "malformed substitution certificate unexpectedly passed" >&2
  exit 1
fi

echo "vampire certificate smoke tests passed"
