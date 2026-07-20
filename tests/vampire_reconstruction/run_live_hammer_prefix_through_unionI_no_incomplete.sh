#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export ROOT TMPDIR

PREFIX_END_LINE=${PREFIX_END_LINE:-294}
EXPECTED_RECONSTRUCTED=${EXPECTED_RECONSTRUCTED:-29}
WALL_SECONDS=${WALL_SECONDS:-360}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/live_hammer_prefix_through_unionI_no_incomplete.XXXXXX")"}
export PREFIX_END_LINE EXPECTED_RECONSTRUCTED WALL_SECONDS WORK_DIR

"$ROOT/tests/vampire_reconstruction/run_live_hammer_prefix_no_incomplete.sh"
