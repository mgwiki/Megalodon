#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

tests/vampire_certificate/run_native_cert_v1_smoke.sh

python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_resolution.json --strict-certificate-v1 --summary
python3 scripts/vampire_certificate.py \
  tests/vampire_certificate/valid_resolution.json \
  --strict-certificate-v1 \
  --emit-native-sexpr "$TMPDIR/vampire_certificate_valid_resolution.sexp"
./bin/megalodon \
  -vampirecertv1 "$TMPDIR/vampire_certificate_valid_resolution.sexp" \
  "$TMPDIR/native_cert_v1_dummy.mg" >"$TMPDIR/vampire_certificate_valid_resolution.native.log"
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_substituted_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_substituted_resolution.json --strict-certificate-v1 --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution.json --summary
python3 scripts/vampire_certificate.py tests/vampire_certificate/valid_equality_resolution.json --strict-certificate-v1 --summary
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
if python3 scripts/vampire_certificate.py \
  "$avatar_outline" \
  --from-vampire-outline \
  --strict-certificate-v1 \
  >"$TMPDIR/vampire_certificate_avatar_refutation.strict.out" \
  2>"$TMPDIR/vampire_certificate_avatar_refutation.strict.err"; then
  echo "strict certificate v1 accepted an AVATAR-derived fallback assumption" >&2
  exit 1
fi
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
cnf_conjunct_outline="$TMPDIR/vampire_certificate_cnf_conjunct.out"
cnf_conjunct_certificate="$TMPDIR/vampire_certificate_cnf_conjunct.json"
cnf_conjunct_megalodon="$TMPDIR/vampire_certificate_cnf_conjunct.mg"
cat >"$cnf_conjunct_outline" <<'OUTLINE'
megalodon_symbol_declaration("Variable p:prop.").
megalodon_symbol_declaration("Variable q:prop.").
megalodon_step(1,"input","formula",[],false,0,"tff(u1,plain,$true).\n").
megalodon_step(2,"cnf transformation","clause",[1],false,0,"cnf(u2,plain,$true).\n").
megalodon_certificate_clause(2,[{"polarity":true,"atom":{"pred":"q","args":[]}}]).
megalodon_step_extra(2,"cnf",["rule=cnf transformation","parent_unit=1","parent_kind=formula","source=vampire_and (p) (q)","source_proposition=vampire_and (p) (q)","target=q","target_proposition=q","target_clause=[{\"polarity\":true,\"atom\":{\"pred\":\"q\",\"args\":[]}}]","target_literal_count=1","target_literal_0=q","parent_clause_count=2","clause_parent_unit=1","clause_index=1","clause_count=2"]).
megalodon_step_replay_kind(2,"cnf").
megalodon_step(3,"input","clause",[],false,0,"cnf(u3,plain,$true).\n").
megalodon_certificate_clause(3,[{"polarity":false,"atom":{"pred":"q","args":[]}}]).
megalodon_step_replay_kind(3,"").
megalodon_step(4,"resolution","clause",[2,3],false,0,"cnf(u4,plain,$true).\n").
megalodon_certificate_clause(4,[]).
megalodon_certificate_step(4,{"rule":"resolve","parents":["u2","u3"],"pivot":{"polarity":true,"atom":{"pred":"q","args":[]}}}).
megalodon_step_replay_kind(4,"resolution").
megalodon_final_step(4).
OUTLINE
python3 scripts/vampire_certificate.py \
  "$cnf_conjunct_outline" \
  --from-vampire-outline \
  --write-certificate "$cnf_conjunct_certificate" \
  --emit-megalodon "$cnf_conjunct_megalodon" \
  --theorem-name vampire_certificate_cnf_conjunct \
  --summary
python3 - "$cnf_conjunct_certificate" <<'PY'
import json
import sys
from pathlib import Path

certificate = json.loads(Path(sys.argv[1]).read_text())
rules = [step["rule"] for step in certificate["steps"]]
if "cnf_formula_conjunct" not in rules:
    raise SystemExit("CNF conjunction projection was not reconstructed explicitly")
PY
./bin/megalodon "$cnf_conjunct_megalodon" >"$TMPDIR/vampire_certificate_cnf_conjunct.check.log"
cnf_projection_outline="$TMPDIR/vampire_certificate_cnf_projection.out"
cnf_projection_certificate="$TMPDIR/vampire_certificate_cnf_projection.json"
cnf_projection_megalodon="$TMPDIR/vampire_certificate_cnf_projection.mg"
cat >"$cnf_projection_outline" <<'OUTLINE'
megalodon_symbol_declaration("Variable p:prop.").
megalodon_symbol_declaration("Variable q:prop.").
megalodon_symbol_declaration("Variable r:prop.").
megalodon_step(1,"input","formula",[],false,0,"tff(u1,plain,$true).\n").
megalodon_step(2,"cnf transformation","clause",[1],false,0,"cnf(u2,plain,$true).\n").
megalodon_certificate_clause(2,[{"polarity":true,"atom":{"pred":"p","args":[]}},{"polarity":true,"atom":{"pred":"q","args":[]}}]).
megalodon_step_extra(2,"cnf",["rule=cnf transformation","parent_unit=1","parent_kind=formula","source=vampire_or (p) (vampire_and (q) (r))","source_proposition=vampire_or (p) (vampire_and (q) (r))","target=vampire_or (p) (q)","target_proposition=vampire_or (p) (q)","target_clause=[{\"polarity\":true,\"atom\":{\"pred\":\"p\",\"args\":[]}},{\"polarity\":true,\"atom\":{\"pred\":\"q\",\"args\":[]}}]","target_literal_count=2","target_literal_0=p","target_literal_1=q","parent_clause_count=2","clause_parent_unit=1","clause_index=0","clause_count=2"]).
megalodon_step_replay_kind(2,"cnf").
megalodon_step(3,"input","clause",[],false,0,"cnf(u3,plain,$true).\n").
megalodon_certificate_clause(3,[{"polarity":false,"atom":{"pred":"p","args":[]}}]).
megalodon_step_replay_kind(3,"").
megalodon_step(4,"resolution","clause",[2,3],false,0,"cnf(u4,plain,$true).\n").
megalodon_certificate_clause(4,[{"polarity":true,"atom":{"pred":"q","args":[]}}]).
megalodon_certificate_step(4,{"rule":"resolve","parents":["u2","u3"],"pivot":{"polarity":true,"atom":{"pred":"p","args":[]}}}).
megalodon_step_replay_kind(4,"resolution").
megalodon_step(5,"input","clause",[],false,0,"cnf(u5,plain,$true).\n").
megalodon_certificate_clause(5,[{"polarity":false,"atom":{"pred":"q","args":[]}}]).
megalodon_step_replay_kind(5,"").
megalodon_step(6,"resolution","clause",[4,5],false,0,"cnf(u6,plain,$true).\n").
megalodon_certificate_clause(6,[]).
megalodon_certificate_step(6,{"rule":"resolve","parents":["u4","u5"],"pivot":{"polarity":true,"atom":{"pred":"q","args":[]}}}).
megalodon_step_replay_kind(6,"resolution").
megalodon_final_step(6).
OUTLINE
python3 scripts/vampire_certificate.py \
  "$cnf_projection_outline" \
  --from-vampire-outline \
  --write-certificate "$cnf_projection_certificate" \
  --emit-megalodon "$cnf_projection_megalodon" \
  --theorem-name vampire_certificate_cnf_projection \
  --summary
python3 - "$cnf_projection_certificate" <<'PY'
import json
import sys
from pathlib import Path

certificate = json.loads(Path(sys.argv[1]).read_text())
rules = [step["rule"] for step in certificate["steps"]]
if "cnf_formula_projection" not in rules:
    raise SystemExit("CNF formula projection was not reconstructed explicitly")
PY
./bin/megalodon "$cnf_projection_megalodon" >"$TMPDIR/vampire_certificate_cnf_projection.check.log"
cnf_quant_projection_outline="$TMPDIR/vampire_certificate_cnf_quant_projection.out"
cnf_quant_projection_certificate="$TMPDIR/vampire_certificate_cnf_quant_projection.json"
cnf_quant_projection_megalodon="$TMPDIR/vampire_certificate_cnf_quant_projection.mg"
cat >"$cnf_quant_projection_outline" <<'OUTLINE'
megalodon_symbol_declaration("Variable p:set->prop.").
megalodon_symbol_declaration("Variable q:set->set->prop.").
megalodon_step(1,"input","formula",[],false,0,"tff(u1,plain,$true).\n").
megalodon_step(2,"cnf transformation","clause",[1],false,0,"cnf(u2,plain,$true).\n").
megalodon_certificate_clause(2,[{"polarity":true,"atom":{"pred":"p","args":[{"var":"X0"}]}},{"polarity":true,"atom":{"pred":"q","args":[{"var":"X0"},{"var":"X1"}]}}]).
megalodon_step_variable_sorts(2,["X0:set","X1:set"]).
megalodon_step_extra(2,"cnf",["rule=cnf transformation","parent_unit=1","parent_kind=formula","source=forall X0:set, vampire_or (p X0) (forall X1:set, q X0 X1)","source_proposition=forall X0:set, vampire_or (p X0) (forall X1:set, q X0 X1)","target=forall X0:set, forall X1:set, vampire_or (p X0) (q X0 X1)","target_proposition=forall X0:set, forall X1:set, vampire_or (p X0) (q X0 X1)","target_clause=[{\"polarity\":true,\"atom\":{\"pred\":\"p\",\"args\":[{\"var\":\"X0\"}]}},{\"polarity\":true,\"atom\":{\"pred\":\"q\",\"args\":[{\"var\":\"X0\"},{\"var\":\"X1\"}]}}]","target_literal_count=2","target_literal_0=p X0","target_literal_1=q X0 X1","parent_clause_count=1","clause_parent_unit=1","clause_index=0","clause_count=1"]).
megalodon_step_replay_kind(2,"cnf").
megalodon_step(3,"input","clause",[],false,0,"cnf(u3,plain,$true).\n").
megalodon_certificate_clause(3,[]).
megalodon_step_replay_kind(3,"").
megalodon_final_step(3).
OUTLINE
python3 scripts/vampire_certificate.py \
  "$cnf_quant_projection_outline" \
  --from-vampire-outline \
  --write-certificate "$cnf_quant_projection_certificate" \
  --emit-megalodon "$cnf_quant_projection_megalodon" \
  --theorem-name vampire_certificate_cnf_quant_projection \
  --summary
python3 - "$cnf_quant_projection_certificate" <<'PY'
import json
import sys
from pathlib import Path

certificate = json.loads(Path(sys.argv[1]).read_text())
rules = [step["rule"] for step in certificate["steps"]]
if "cnf_formula_projection" not in rules:
    raise SystemExit("quantified CNF formula projection was not reconstructed explicitly")
PY
./bin/megalodon "$cnf_quant_projection_megalodon" >"$TMPDIR/vampire_certificate_cnf_quant_projection.check.log"
cnf_lambda_projection_outline="$TMPDIR/vampire_certificate_cnf_lambda_projection.out"
cnf_lambda_projection_certificate="$TMPDIR/vampire_certificate_cnf_lambda_projection.json"
cnf_lambda_projection_megalodon="$TMPDIR/vampire_certificate_cnf_lambda_projection.mg"
cat >"$cnf_lambda_projection_outline" <<'OUTLINE'
megalodon_symbol_declaration("Variable F:(set->prop)->prop.").
megalodon_symbol_declaration("Variable p:set->prop.").
megalodon_symbol_declaration("Variable r:prop.").
megalodon_step(1,"input","formula",[],false,0,"tff(u1,plain,$true).\n").
megalodon_step(2,"cnf transformation","clause",[1],false,0,"cnf(u2,plain,$true).\n").
megalodon_certificate_clause(2,[{"polarity":true,"atom":{"eq":[{"const":"f__true"},{"apply":[{"const":"F"},{"app":"vLAM","args":[{"apply":[{"const":"p"},{"const":"db0"}]}]}]}],"sort":"prop"}}]).
megalodon_step_extra(2,"lambda_sorts",["step_lambda_count=1","step_lambda_0_body=p db0","step_lambda_0_binder_db=db0","step_lambda_0_binder_sort=set"]).
megalodon_step_extra(2,"cnf",["rule=cnf transformation","parent_unit=1","parent_kind=formula","source=vampire_and (vampire_eq_prop (vampire_true) (F (vLAM (p db0)))) (r)","source_proposition=vampire_and (vampire_eq_prop (vampire_true) (F (vLAM (p db0)))) (r)","target=vampire_eq_prop (vampire_true) (F (vLAM (p db0)))","target_proposition=vampire_eq_prop (vampire_true) (F (vLAM (p db0)))","target_clause=[{\"polarity\":true,\"atom\":{\"eq\":[{\"const\":\"f__true\"},{\"apply\":[{\"const\":\"F\"},{\"app\":\"vLAM\",\"args\":[{\"apply\":[{\"const\":\"p\"},{\"const\":\"db0\"}]}]}]}],\"sort\":\"prop\"}}]","target_literal_count=1","target_literal_0=vampire_eq_prop (vampire_true) (F (vLAM (p db0)))","parent_clause_count=2","clause_parent_unit=1","clause_index=0","clause_count=2"]).
megalodon_step_replay_kind(2,"cnf").
megalodon_step(3,"input","clause",[],false,0,"cnf(u3,plain,$true).\n").
megalodon_certificate_clause(3,[]).
megalodon_step_replay_kind(3,"").
megalodon_final_step(3).
OUTLINE
python3 scripts/vampire_certificate.py \
  "$cnf_lambda_projection_outline" \
  --from-vampire-outline \
  --write-certificate "$cnf_lambda_projection_certificate" \
  --emit-megalodon "$cnf_lambda_projection_megalodon" \
  --theorem-name vampire_certificate_cnf_lambda_projection \
  --summary
python3 - "$cnf_lambda_projection_certificate" <<'PY'
import json
import sys
from pathlib import Path

certificate = json.loads(Path(sys.argv[1]).read_text())
rules = [step["rule"] for step in certificate["steps"]]
if "cnf_formula_conjunct" not in rules:
    raise SystemExit("lambda CNF conjunction projection was not reconstructed explicitly")
PY
if rg -n '\bvLAM\b|^Variable db[0-9]+:' "$cnf_lambda_projection_megalodon"; then
  echo "lambda CNF projection leaked raw vLAM or db declaration" >&2
  exit 1
fi
./bin/megalodon "$cnf_lambda_projection_megalodon" >"$TMPDIR/vampire_certificate_cnf_lambda_projection.check.log"
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
