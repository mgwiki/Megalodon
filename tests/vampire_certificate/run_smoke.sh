#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

tests/vampire_certificate/run_native_cert_v1_smoke.sh

echo "native Vampire certificate smoke tests passed"
