#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)

SOURCE_CONTEXT_ONLY=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_smoke.sh"
