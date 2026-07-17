#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}

TARGET_LINE=11453 \
TARGET_CHAR=77 \
TARGET_LABEL=11453 \
EXPECTED_STEPS=65 \
EXPECTED_SOURCES=8 \
EXPECTED_CONTEXT="known=6 local=0 local_definition=0 conjecture=2 unresolved=0" \
ROOT="$ROOT" \
"$ROOT/tests/vampire_certificate/run_real_vampire_11703_target_smoke.sh"
