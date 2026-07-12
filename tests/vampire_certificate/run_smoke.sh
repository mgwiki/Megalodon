#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_substituted_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_truth_conflict_resolution_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_subsumption_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation_negative_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation_side_literals_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_prop_paramodulation_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_paramodulation_all.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_prop_equality_symmetry_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_prop_equality_factoring.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_definition_input_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_definition_input_function_sort.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_lambda_hint_refutation.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_higher_order_lambda_paramodulation.json --summary
avatar_outline="$TMPDIR/vampire_certificate_avatar_refutation.out"
avatar_certificate="$TMPDIR/vampire_certificate_avatar_refutation.json"
cat >"$avatar_outline" <<'OUTLINE'
megalodon_step(1,"input","clause",[],false,0,"cnf(u1,plain,$true).\n").
megalodon_certificate_clause(1,[{"polarity":true,"atom":{"pred":"p","args":[]}}]).
megalodon_step_replay_kind(1,"").
megalodon_step(2,"avatar sat refutation","clause",[1],false,0,"cnf(u2,plain,$true).\n").
megalodon_certificate_clause(2,[]).
megalodon_step_replay_kind(2,"avatar_refutation").
megalodon_final_step(2).
OUTLINE
python3 scripts/vampire_certificate.py \
  "$avatar_outline" \
  --from-vampire-outline \
  --write-certificate "$avatar_certificate" \
  --summary
python3 - "$avatar_certificate" <<'PY'
import json
import sys
from pathlib import Path

certificate = json.loads(Path(sys.argv[1]).read_text())
avatar_steps = [
    step for step in certificate["steps"]
    if (step.get("source") or {}).get("replay_kind") == "avatar_refutation"
]
if len(avatar_steps) != 1:
    raise SystemExit("avatar_refutation outline step was not preserved as an auditable source")
if avatar_steps[0]["rule"] != "input" or avatar_steps[0]["source"]["kind"] != "vampire_derived_clause":
    raise SystemExit("avatar_refutation fallback should be an explicit derived skeleton assumption")
PY
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
  tests/vampire_certificate/valid_truth_conflict_resolution_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_truth_conflict_resolution_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_paramodulation_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_paramodulation_negative_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_negative_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_paramodulation_side_literals_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_side_literals_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_prop_paramodulation_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_prop_paramodulation_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_prop_equality_symmetry_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_prop_equality_symmetry_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_prop_equality_factoring.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_prop_equality_factoring.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_definition_input_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_definition_input_refutation.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_definition_input_function_sort.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_definition_input_function_sort.mg"
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_lambda_hint_refutation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_lambda_hint_refutation.mg"
if rg -n '\bvLAM\b|^Variable db0:' "$TMPDIR/vampire_certificate_valid_lambda_hint_refutation.mg"; then
  echo "lambda-hint Megalodon output leaked raw vLAM or db0 declaration" >&2
  exit 1
fi
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_higher_order_lambda_paramodulation.json \
  --emit-megalodon "$TMPDIR/vampire_certificate_valid_higher_order_lambda_paramodulation.mg"
if rg -n '\bvLAM\b|^Variable db[0-9]+:' "$TMPDIR/vampire_certificate_valid_higher_order_lambda_paramodulation.mg"; then
  echo "higher-order lambda Megalodon output leaked raw vLAM or db declaration" >&2
  exit 1
fi
if rg -n '\badmit\b|\baby\b|-allowincompleteqed|^Axiom xm\b' \
  "$TMPDIR/vampire_certificate_valid_resolution.mg" \
  "$TMPDIR/vampire_certificate_valid_substituted_resolution.mg" \
  "$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_truth_conflict_resolution_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_paramodulation_negative_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_paramodulation_side_literals_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_prop_paramodulation_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_prop_equality_symmetry_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_prop_equality_factoring.mg" \
  "$TMPDIR/vampire_certificate_valid_definition_input_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_definition_input_function_sort.mg" \
  "$TMPDIR/vampire_certificate_valid_lambda_hint_refutation.mg" \
  "$TMPDIR/vampire_certificate_valid_higher_order_lambda_paramodulation.mg"; then
  echo "generated Megalodon certificate proof contains an admission marker" >&2
  exit 1
fi
./bin/megalodon "$TMPDIR/vampire_certificate_valid_resolution.mg" >"$TMPDIR/vampire_certificate_valid_resolution.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_substituted_resolution.mg" >"$TMPDIR/vampire_certificate_valid_substituted_resolution.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.mg" >"$TMPDIR/vampire_certificate_valid_equality_resolution_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_truth_conflict_resolution_refutation.mg" >"$TMPDIR/vampire_certificate_valid_truth_conflict_resolution_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_refutation.mg" >"$TMPDIR/vampire_certificate_valid_paramodulation_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_negative_refutation.mg" >"$TMPDIR/vampire_certificate_valid_paramodulation_negative_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_paramodulation_side_literals_refutation.mg" >"$TMPDIR/vampire_certificate_valid_paramodulation_side_literals_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_prop_paramodulation_refutation.mg" >"$TMPDIR/vampire_certificate_valid_prop_paramodulation_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_prop_equality_symmetry_refutation.mg" >"$TMPDIR/vampire_certificate_valid_prop_equality_symmetry_refutation.check.log"
./bin/megalodon -allowincompleteqed "$TMPDIR/vampire_certificate_valid_prop_equality_factoring.mg" >"$TMPDIR/vampire_certificate_valid_prop_equality_factoring.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_definition_input_refutation.mg" >"$TMPDIR/vampire_certificate_valid_definition_input_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_definition_input_function_sort.mg" >"$TMPDIR/vampire_certificate_valid_definition_input_function_sort.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_lambda_hint_refutation.mg" >"$TMPDIR/vampire_certificate_valid_lambda_hint_refutation.check.log"
./bin/megalodon "$TMPDIR/vampire_certificate_valid_higher_order_lambda_paramodulation.mg" >"$TMPDIR/vampire_certificate_valid_higher_order_lambda_paramodulation.check.log"

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

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_truth_conflict_nonconflict.json >"$TMPDIR/vampire_certificate_invalid_truth_conflict_nonconflict.out" 2>"$TMPDIR/vampire_certificate_invalid_truth_conflict_nonconflict.err"; then
  echo "non-conflicting truth-conflict certificate unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_subsumption_resolution_uncovered.json >"$TMPDIR/vampire_certificate_invalid_subsumption_resolution_uncovered.out" 2>"$TMPDIR/vampire_certificate_invalid_subsumption_resolution_uncovered.err"; then
  echo "uncovered subsumption-resolution side literal unexpectedly passed" >&2
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

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_paramodulation_all_positions.json >"$TMPDIR/vampire_certificate_invalid_paramodulation_all_positions.out" 2>"$TMPDIR/vampire_certificate_invalid_paramodulation_all_positions.err"; then
  echo "incomplete simultaneous-paramodulation positions unexpectedly passed" >&2
  exit 1
fi

if python3 scripts/vampire_certificate.py tests/vampire_certificate/invalid_definition_input_sort.json >"$TMPDIR/vampire_certificate_invalid_definition_input_sort.out" 2>"$TMPDIR/vampire_certificate_invalid_definition_input_sort.err"; then
  echo "invalid definition-input sort unexpectedly passed" >&2
  exit 1
fi

echo "vampire certificate smoke tests passed"
