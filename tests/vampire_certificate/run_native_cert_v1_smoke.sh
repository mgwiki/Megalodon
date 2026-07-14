#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

BASE_TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$BASE_TMPDIR"
WORK_DIR="${WORK_DIR:-$(mktemp -d "$BASE_TMPDIR/native_cert_v1.XXXXXX")}"
mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$BASE_TMPDIR/latest_native_cert_v1"

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

dummy="$WORK_DIR/native_cert_v1_dummy.mg"
: >"$dummy"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_valid.log"; then
  echo "native certificate v1 checker did not accept the valid fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_metadata_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_metadata_valid.log"

if ! rg -q 'Vampire certificate v1 checked 4 steps' "$WORK_DIR/native_cert_v1_metadata_valid.log"; then
  echo "native certificate v1 checker did not accept metadata-bearing certificates" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_valid_emit.log"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' "$WORK_DIR/native_cert_v1_valid_emit.mg"; then
  echo "native certificate v1 simple emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_valid_emit.check.log"
if ! rg -q 'assume src_axiom_a1__c1:' "$WORK_DIR/native_cert_v1_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not preserve source axiom a1 in the proof script" >&2
  exit 1
fi
if ! rg -q 'assume src_axiom_a2__c2:' "$WORK_DIR/native_cert_v1_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not preserve source axiom a2 in the proof script" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_name_mangled_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_name_mangled_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.log"
if ! rg -q 'Vampire certificate v1 source map checked 2 sources' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.log"; then
  echo "native certificate v1 checker did not validate the source-name map fixture" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 source origin examples/hammer/100thms_12_h\.mg line 123 char 45 \(aby\)' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.log"; then
  echo "native certificate v1 checker did not report source-origin metadata" >&2
  exit 1
fi
if ! rg -q '// Vampire certificate source origin: examples/hammer/100thms_12_h\.mg line 123 char 45 \(aby\)\.' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not preserve source-origin metadata" >&2
  exit 1
fi
if ! rg -q 'assume src_axiom_Foo_bar__c1:' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not use the original Foo_bar source name" >&2
  exit 1
fi
if ! rg -q 'assume src_axiom_Not_x2Fp__c2:' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not sanitize the original Not/p source name" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_resolution_mirrored_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.log"
if ! rg -q 'Vampire certificate v1 checked 6 steps' \
    "$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.log"; then
  echo "native certificate v1 checker did not accept the mirrored resolution fixture" >&2
  exit 1
fi
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.mg"; then
  echo "native certificate v1 mirrored resolution emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factor_prop_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_factor_prop_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_factor_prop_valid_emit.log"
if ! rg -q 'Vampire certificate v1 checked 5 steps' \
    "$WORK_DIR/native_cert_v1_factor_prop_valid_emit.log"; then
  echo "native certificate v1 checker did not accept the propositional factor fixture" >&2
  exit 1
fi
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_factor_prop_valid_emit.mg"; then
  echo "native certificate v1 propositional factor emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_factor_prop_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_factor_prop_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_substitute_prop_noop_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.log"
if ! rg -q 'Vampire certificate v1 checked 5 steps' \
    "$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.log"; then
  echo "native certificate v1 checker did not accept the no-op substitute fixture" >&2
  exit 1
fi
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.mg"; then
  echo "native certificate v1 no-op substitute emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_condensation_prop_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.log"
if ! rg -q 'Vampire certificate v1 checked 5 steps' \
    "$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.log"; then
  echo "native certificate v1 checker did not accept the propositional condensation fixture" >&2
  exit 1
fi
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.mg"; then
  echo "native certificate v1 propositional condensation emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.log"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.mg"; then
  echo "native certificate v1 term-changing substitution emitter generated an admission marker" >&2
  exit 1
fi
if ! rg -q 'bridge_substitute__' \
    "$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.mg"; then
  echo "native certificate v1 term-changing substitution emitter did not expose a bridge obligation" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.mg" \
  >"$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.check.log"

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_substitute_prop_changed_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_substitute_prop_changed_closed.out" \
  2>"$WORK_DIR/native_cert_v1_substitute_prop_changed_closed.err"; then
  echo "closed native certificate v1 emitter accepted a substitution bridge premise" >&2
  exit 1
fi
if ! rg -q 'zero non-source premises.*bridge:bridge_substitute__c2' \
    "$WORK_DIR/native_cert_v1_substitute_prop_changed_closed.err"; then
  echo "closed native certificate v1 substitution failure did not report the bridge premise" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factor_equality_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_factor_equality_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_factor_equality_valid_emit.log"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_factor_equality_valid_emit.mg"; then
  echo "native certificate v1 factor/equality emitter generated an admission marker" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_factor_equality_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_factor_equality_valid_emit.check.log"

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_strict_missing_source.out" \
  2>"$WORK_DIR/native_cert_v1_strict_missing_source.err"; then
  echo "strict native certificate v1 checker accepted source-backed inputs without a source map" >&2
  exit 1
fi

if ! rg -q 'strict certificate v1 requires -vampirecertv1source' "$WORK_DIR/native_cert_v1_strict_missing_source.err"; then
  echo "strict native certificate v1 missing-source failure did not explain the source-map requirement" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 3 sources' "$WORK_DIR/native_cert_v1_source_map_valid.log"; then
  echo "native certificate v1 source-map checker did not accept mapped inputs" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_hash_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_hash_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 3 sources' "$WORK_DIR/native_cert_v1_source_map_hash_valid.log"; then
  echo "native certificate v1 source-map hash validation did not report all mapped inputs" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_true_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_true_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_true_mismatch_bad.err"; then
  echo "native certificate v1 source-map checker accepted a non-true certificate input for THF true" >&2
  exit 1
fi

if ! rg -Fq 'maps to THF $true but the certificate input is not true' \
    "$WORK_DIR/native_cert_v1_source_map_true_mismatch_bad.err"; then
  echo "native certificate v1 source-map true-mismatch failure did not explain the semantic mismatch" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_formula_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad.err"; then
  echo "native certificate v1 source-map checker accepted a mismatched THF formula" >&2
  exit 1
fi

if ! rg -q 'does not match the THF declaration formula' \
    "$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad.err"; then
  echo "native certificate v1 source-map formula-mismatch failure did not explain the semantic mismatch" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_cnf_known_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_known_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 3 sources' \
    "$WORK_DIR/native_cert_v1_formula_cnf_known_valid.log"; then
  echo "native certificate v1 source-map checker did not accept formula-backed known inputs" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_cnf_quantifier_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_quantifier_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_formula_cnf_quantifier_mismatch_bad.err"; then
  echo "native certificate v1 source-map checker accepted a quantified formula mismatch" >&2
  exit 1
fi

if ! rg -q 'does not match the THF declaration formula' \
    "$WORK_DIR/native_cert_v1_formula_cnf_quantifier_mismatch_bad.err"; then
  echo "native certificate v1 source-map quantified formula-mismatch failure did not explain the mismatch" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_hash_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_hash_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_hash_mismatch_bad.err"; then
  echo "native certificate v1 source-map validation accepted a stale source hash" >&2
  exit 1
fi

if ! rg -q 'has source hash .* but the THF declaration is tagged' \
    "$WORK_DIR/native_cert_v1_source_map_hash_mismatch_bad.err"; then
  echo "native certificate v1 source-map hash mismatch failure did not explain the stale hash" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_strict_source_map_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' "$WORK_DIR/native_cert_v1_strict_source_map_valid.log"; then
  echo "strict native certificate v1 checker did not accept mapped inputs" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_closed_source_map_valid.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_closed_source_map_valid.log"

if ! rg -q 'Vampire certificate v1 closed checked 6 steps' "$WORK_DIR/native_cert_v1_closed_source_map_valid.log"; then
  echo "closed native certificate v1 checker did not accept the closed mapped fixture" >&2
  exit 1
fi
if rg -q 'bridge_' "$WORK_DIR/native_cert_v1_closed_source_map_valid.mg"; then
  echo "closed native certificate v1 emitter generated a bridge premise for a closed fixture" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_closed_source_map_valid.mg" \
  >"$WORK_DIR/native_cert_v1_closed_source_map_valid.check.log"

if bin/megalodon \
    -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_local_fact_negated.sexp \
    -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_local_fact_negated.th0.p \
    "$dummy" >"$WORK_DIR/native_cert_v1_source_map_local_fact_negated_bad.log" \
    2>"$WORK_DIR/native_cert_v1_source_map_local_fact_negated_bad.err"; then
  echo "native certificate v1 source-map checker accepted negated local_fact preprocessing" >&2
  exit 1
fi

if ! rg -q 'incompatible source-map kind' "$WORK_DIR/native_cert_v1_source_map_local_fact_negated_bad.err"; then
  echo "native certificate v1 source-map local_fact rejection did not explain the incompatible kind" >&2
  exit 1
fi

if bin/megalodon \
    -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_local_definition_negated.sexp \
    -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_local_definition_negated.th0.p \
    "$dummy" >"$WORK_DIR/native_cert_v1_source_map_local_definition_negated_bad.log" \
    2>"$WORK_DIR/native_cert_v1_source_map_local_definition_negated_bad.err"; then
  echo "native certificate v1 source-map checker accepted negated local_definition preprocessing" >&2
  exit 1
fi

if ! rg -q 'incompatible source-map kind' "$WORK_DIR/native_cert_v1_source_map_local_definition_negated_bad.err"; then
  echo "native certificate v1 source-map local_definition rejection did not explain the incompatible kind" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_definition_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_definition_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_definition_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 2 sources' "$WORK_DIR/native_cert_v1_source_map_definition_valid.log"; then
  echo "native certificate v1 source-map checker did not accept mapped definition inputs" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_conjecture_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_conjecture_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_conjecture_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 2 sources' "$WORK_DIR/native_cert_v1_source_map_conjecture_valid.log"; then
  echo "native certificate v1 source-map checker did not accept mapped conjecture inputs" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_axiom_conjecture_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_axiom_conjecture_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_axiom_conjecture_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_axiom_conjecture_bad.err"; then
  echo "native certificate v1 source-map checker accepted an axiom source mapped to conjecture" >&2
  exit 1
fi

if ! rg -q 'source goal maps to incompatible source-map kind conjecture' "$WORK_DIR/native_cert_v1_source_map_axiom_conjecture_bad.err"; then
  echo "native certificate v1 source-map incompatibility failure did not explain the bad conjecture mapping" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_axiom_definition_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_axiom_definition_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_axiom_definition_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_axiom_definition_bad.err"; then
  echo "native certificate v1 source-map checker accepted an axiom source mapped to definition" >&2
  exit 1
fi

if ! rg -q 'source d1 maps to incompatible source-map kind definition' "$WORK_DIR/native_cert_v1_source_map_axiom_definition_bad.err"; then
  echo "native certificate v1 source-map incompatibility failure did not explain the bad definition mapping" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_definition_non_equality_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_definition_non_equality_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_definition_non_equality_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_definition_non_equality_bad.err"; then
  echo "native certificate v1 source-map checker accepted a non-equality local definition input" >&2
  exit 1
fi

if ! rg -q 'maps to local_definition but is not an equality input' "$WORK_DIR/native_cert_v1_source_map_definition_non_equality_bad.err"; then
  echo "native certificate v1 source-map definition-shape failure did not explain the side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_missing.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_missing.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_missing.err"; then
  echo "native certificate v1 source-map checker accepted an unmapped input" >&2
  exit 1
fi

if ! rg -q 'source a3 is not present in the Megalodon source map' "$WORK_DIR/native_cert_v1_source_map_missing.err"; then
  echo "native certificate v1 source-map failure did not explain the unmapped input" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_duplicate.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_duplicate.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_duplicate.err"; then
  echo "native certificate v1 source-map checker accepted a duplicate source-map key" >&2
  exit 1
fi

if ! rg -q 'duplicate Megalodon source-map entry for a1' "$WORK_DIR/native_cert_v1_source_map_duplicate.err"; then
  echo "native certificate v1 duplicate source-map failure did not explain the duplicate key" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_known_empty_hash_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_known_empty_hash_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_known_empty_hash_bad.err"; then
  echo "native certificate v1 source-map checker accepted a global known entry without a hash" >&2
  exit 1
fi

if ! rg -q 'global known but has an empty source hash' "$WORK_DIR/native_cert_v1_source_map_known_empty_hash_bad.err"; then
  echo "native certificate v1 source-map hash failure did not explain the missing known hash" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 2 sources' "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_valid.log"; then
  echo "native certificate v1 source-map checker did not accept a reflexive set source" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_bad.err"; then
  echo "native certificate v1 source-map checker accepted a non-reflexive set-reflexivity source" >&2
  exit 1
fi

if ! rg -q 'maps to set_reflexivity but is not a reflexive equality input' "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_bad.err"; then
  echo "native certificate v1 source-map set-reflexivity failure did not explain the side condition" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factor_equality_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_factor_equality_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_factor_equality_valid.log"; then
  echo "native certificate v1 checker did not accept the valid factor/equality-resolution fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_copy_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_copy_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_formula_copy_valid.log"; then
  echo "native certificate v1 checker did not accept the valid formula-copy fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_truth_conflict_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_truth_conflict_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_truth_conflict_valid.log"; then
  echo "native certificate v1 checker did not accept the valid truth-conflict fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_subst_paramod_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_subst_paramod_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$WORK_DIR/native_cert_v1_subst_paramod_valid.log"; then
  echo "native certificate v1 checker did not accept the valid substitution/paramodulation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_condensation_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_condensation_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_condensation_valid.log"; then
  echo "native certificate v1 checker did not accept the valid condensation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_paramod_equality_shape_position_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_paramod_equality_shape_position_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_paramod_equality_shape_position_valid.log"; then
  echo "native certificate v1 checker did not accept the equality-shaped paramodulation position fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_paramod_equality_right_spine_position_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_paramod_equality_right_spine_position_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_paramod_equality_right_spine_position_valid.log"; then
  echo "native certificate v1 checker did not accept the equality right-spine paramodulation position fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_superposition_equality_subst_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_superposition_equality_subst_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$WORK_DIR/native_cert_v1_superposition_equality_subst_valid.log"; then
  echo "native certificate v1 checker did not accept the equality-substitution superposition fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_superposition_simultaneous_selected_literal_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_superposition_simultaneous_selected_literal_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_superposition_simultaneous_selected_literal_valid.log"; then
  echo "native certificate v1 checker did not accept the simultaneous selected-literal superposition fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_bool_simplify_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_bool_simplify_valid.log"

if ! rg -q 'Vampire certificate v1 checked 4 steps' "$WORK_DIR/native_cert_v1_bool_simplify_valid.log"; then
  echo "native certificate v1 checker did not accept the Boolean simplification fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_literal_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_cnf_literal_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_cnf_literal_valid.log"; then
  echo "native certificate v1 checker did not accept the valid literal-CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_bool_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_bool_valid.log"

if ! rg -q 'Vampire certificate v1 checked 9 steps' "$WORK_DIR/native_cert_v1_fool_bool_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL Boolean fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_lambda_not_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_lambda_not_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_fool_lambda_not_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL lambda/not fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_formula_equality_orientation_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_formula_equality_orientation_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_fool_formula_equality_orientation_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL equality-orientation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_term_bool_constant_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_term_bool_constant_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_fool_term_bool_constant_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL term Boolean-constant fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_definition_input_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_definition_input_valid.log"

if ! rg -q 'Vampire certificate v1 checked 4 steps' "$WORK_DIR/native_cert_v1_definition_input_valid.log"; then
  echo "native certificate v1 checker did not accept the valid definition-input fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_component_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_component_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_avatar_component_valid.log"; then
  echo "native certificate v1 checker did not accept the valid AVATAR component fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_component_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_avatar_component_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_component_strict.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' "$WORK_DIR/native_cert_v1_avatar_component_strict.log"; then
  echo "strict native certificate v1 checker did not accept the valid AVATAR component fixture" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_component_multiple_splits_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_component_multiple_splits_bad.out" \
  2>"$WORK_DIR/native_cert_v1_avatar_component_multiple_splits_bad.err"; then
  echo "strict native certificate v1 checker accepted an AVATAR component with multiple split literals" >&2
  exit 1
fi

if ! rg -q 'strict avatar_component must contain exactly one split literal' \
  "$WORK_DIR/native_cert_v1_avatar_component_multiple_splits_bad.err"; then
  echo "strict native certificate v1 multiple-split AVATAR component failure did not explain the rejected shape" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_refutation_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_refutation_valid.log"

if ! rg -q 'Vampire certificate v1 checked 2 steps' "$WORK_DIR/native_cert_v1_avatar_refutation_valid.log"; then
  echo "native certificate v1 checker did not accept the valid AVATAR refutation fixture" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_refutation_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_refutation_strict.log" 2>&1; then
  echo "strict native certificate v1 checker accepted an AVATAR refutation without a SAT proof trace" >&2
  exit 1
fi

if ! rg -q 'strict certificate v1 requires SAT proof traces for AVATAR refutations' \
  "$WORK_DIR/native_cert_v1_avatar_refutation_strict.log"; then
  echo "strict native certificate v1 checker rejected untraced AVATAR refutation with the wrong error" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_refutation_traced_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_refutation_traced_strict.log"

if ! rg -q 'Vampire certificate v1 strict checked 2 steps' "$WORK_DIR/native_cert_v1_avatar_refutation_traced_strict.log"; then
  echo "strict native certificate v1 checker did not accept traced AVATAR refutation" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_symmetry_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_symmetry_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_equality_symmetry_valid.log"; then
  echo "native certificate v1 checker did not accept the valid equality-symmetry fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_symmetry_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.log"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg"; then
  echo "native certificate v1 equality-symmetry emitter generated an admission marker" >&2
  exit 1
fi
if rg -q 'bridge_equality_symmetry__' \
    "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg"; then
  echo "native certificate v1 equality-symmetry emitter still exposed a bridge proof" >&2
  exit 1
fi
if ! rg -Fq 'exact (vampire_eq_set_sym (a) (b) src_axiom_eq_forward__p1).' \
    "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg"; then
  echo "native certificate v1 equality-symmetry emitter did not replay symmetry directly" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_exhaustiveness_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_fool_exhaustiveness_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL exhaustiveness fixture" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.out" \
  2>"$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.err"; then
  echo "closed native certificate v1 emitter accepted a FOOL theory premise" >&2
  exit 1
fi
if ! rg -q 'zero non-source premises.*derived:theory_fool_exhaustiveness__b1' \
    "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.err"; then
  echo "closed native certificate v1 FOOL-exhaustiveness failure did not report the derived premise" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_valid.log"

if ! rg -q 'Vampire certificate v1 checked 9 steps' "$WORK_DIR/native_cert_v1_formula_cnf_valid.log"; then
  echo "native certificate v1 checker did not accept the valid formula CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.log"
if rg -n '\badmit\b|\baby\b|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg"; then
  echo "native certificate v1 formula-CNF emitter generated an admission marker" >&2
  exit 1
fi
if rg -q 'bridge_fool__f1' "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg"; then
  echo "native certificate v1 formula-CNF emitter still exposed the replayed FOOL obligation" >&2
  exit 1
fi
if ! rg -q 'bridge_normal_form__f2' "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg"; then
  echo "native certificate v1 formula-CNF emitter did not expose the normal-form bridge obligation" >&2
  exit 1
fi
bin/megalodon "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.check.log"

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_cnf_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_formula_cnf_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_closed.out" \
  2>"$WORK_DIR/native_cert_v1_formula_cnf_closed.err"; then
  echo "closed native certificate v1 emitter accepted formula/CNF bridge premises" >&2
  exit 1
fi
if ! rg -q 'zero non-source premises.*bridge:bridge_' \
    "$WORK_DIR/native_cert_v1_formula_cnf_closed.err"; then
  echo "closed native certificate v1 formula-CNF failure did not report bridge premises" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_vampire_order_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_vampire_order_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$WORK_DIR/native_cert_v1_formula_cnf_vampire_order_valid.log"; then
  echo "native certificate v1 checker did not accept the valid Vampire-order formula CNF fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_formula_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_rectify_formula_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_rectify_formula_valid.log"; then
  echo "native certificate v1 checker did not accept the valid rectify-formula fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_scoped_equality_symmetry_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_valid.log"; then
  echo "native certificate v1 checker did not accept scoped equality-symmetry rectification" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_scoped_equality_symmetry_valid.sexp \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_unsupported.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_unsupported.out" \
  2>"$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_unsupported.err"; then
  echo "native certificate v1 simple emitter accepted unsupported formula transformation" >&2
  exit 1
fi
if ! rg -q 'unsupported identifier =' \
    "$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_unsupported.err"; then
  echo "native certificate v1 simple emitter did not report the unsupported equality identifier" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_equality_orientation_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_equality_orientation_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_skolem_equality_orientation_valid.log"; then
  echo "native certificate v1 checker did not accept the valid skolem equality-orientation fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_application_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_application_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_skolem_application_valid.log"; then
  echo "native certificate v1 checker did not accept Skolem substitution under application" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_bogus_shape_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_bogus_shape_bad.out" \
  2>"$WORK_DIR/native_cert_v1_skolem_bogus_shape_bad.err"; then
  echo "native certificate v1 checker accepted a bogus skolem result" >&2
  exit 1
fi

if ! rg -q 'skolem_formula result does not match explicit skolem substitution' "$WORK_DIR/native_cert_v1_skolem_bogus_shape_bad.err"; then
  echo "native certificate v1 checker did not explain bogus skolem rejection" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_duplicate_subst_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_duplicate_subst_bad.out" \
  2>"$WORK_DIR/native_cert_v1_skolem_duplicate_subst_bad.err"; then
  echo "native certificate v1 checker accepted duplicate Skolem substitution bindings" >&2
  exit 1
fi

if ! rg -q 'duplicate substitution binding for X0' "$WORK_DIR/native_cert_v1_skolem_duplicate_subst_bad.err"; then
  echo "native certificate v1 duplicate Skolem substitution failure did not explain the duplicate binding" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_computed_strict_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_computed_strict_bad.out" \
  2>"$WORK_DIR/native_cert_v1_skolem_computed_strict_bad.err"; then
  echo "strict native certificate v1 checker accepted a computed skolem formula" >&2
  exit 1
fi

if ! rg -q 'strict certificate v1 rejects computed skolem formulas without explicit Vampire results' \
  "$WORK_DIR/native_cert_v1_skolem_computed_strict_bad.err"; then
  echo "strict native certificate v1 computed-skolem failure did not explain the rejected missing result" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_predicate_definition_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_predicate_definition_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_predicate_definition_valid.log"; then
  echo "native certificate v1 checker did not accept the valid predicate-definition fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_predicate_definition_fold_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_predicate_definition_fold_valid.log"

if ! rg -q 'Vampire certificate v1 checked 7 steps' "$WORK_DIR/native_cert_v1_predicate_definition_fold_valid.log"; then
  echo "native certificate v1 checker did not accept the valid predicate-definition-fold fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_predicate_definition_fold_chain_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_predicate_definition_fold_chain_valid.log"

if ! rg -q 'Vampire certificate v1 checked 8 steps' "$WORK_DIR/native_cert_v1_predicate_definition_fold_chain_valid.log"; then
  echo "native certificate v1 checker did not accept the valid predicate-definition-fold-chain fixture" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_pivot.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_pivot.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_pivot.err"; then
  echo "native certificate v1 checker accepted an invalid resolution pivot" >&2
  exit 1
fi

if ! rg -q 'resolution pivots are not complementary' "$WORK_DIR/native_cert_v1_invalid_pivot.err"; then
  echo "native certificate v1 invalid-pivot failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_equality_resolution.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_equality_resolution.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_equality_resolution.err"; then
  echo "native certificate v1 checker accepted non-reflexive equality resolution" >&2
  exit 1
fi

if ! rg -q 'equality-resolution equality is not reflexive' "$WORK_DIR/native_cert_v1_invalid_equality_resolution.err"; then
  echo "native certificate v1 invalid-equality failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_truth_conflict.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_truth_conflict.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_truth_conflict.err"; then
  echo "native certificate v1 checker accepted a non-conflicting truth equality" >&2
  exit 1
fi

if ! rg -q 'truth-conflict equality is not true = false' "$WORK_DIR/native_cert_v1_invalid_truth_conflict.err"; then
  echo "native certificate v1 invalid-truth-conflict failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_paramod_position.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_paramod_position.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_paramod_position.err"; then
  echo "native certificate v1 checker accepted a paramodulation with a bad target position" >&2
  exit 1
fi

if ! rg -q 'paramodulation position does not contain from term' "$WORK_DIR/native_cert_v1_invalid_paramod_position.err"; then
  echo "native certificate v1 invalid-paramodulation failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_rectify_formula.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_rectify_formula.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_rectify_formula.err"; then
  echo "native certificate v1 checker accepted an invalid formula rectification" >&2
  exit 1
fi

if ! rg -q 'rectify_formula result is not a bijective Vampire-variable renaming of parent' "$WORK_DIR/native_cert_v1_invalid_rectify_formula.err"; then
  echo "native certificate v1 invalid-rectify failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_predicate_definition_recursive.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_predicate_definition_recursive.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_predicate_definition_recursive.err"; then
  echo "native certificate v1 checker accepted a recursive predicate definition" >&2
  exit 1
fi

if ! rg -q 'predicate_definition is not a non-recursive definitional disjunction' "$WORK_DIR/native_cert_v1_invalid_predicate_definition_recursive.err"; then
  echo "native certificate v1 invalid-predicate-definition failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_predicate_definition_symbol.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_predicate_definition_symbol.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_predicate_definition_symbol.err"; then
  echo "native certificate v1 checker accepted a predicate definition with the wrong symbol" >&2
  exit 1
fi

if ! rg -q 'predicate_definition symbol wrong does not match definiendum pdef' "$WORK_DIR/native_cert_v1_invalid_predicate_definition_symbol.err"; then
  echo "native certificate v1 invalid-predicate-definition-symbol failure did not explain the rejected symbol" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_predicate_definition_fold.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_predicate_definition_fold.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_predicate_definition_fold.err"; then
  echo "native certificate v1 checker accepted an invalid predicate definition fold" >&2
  exit 1
fi

if ! rg -q 'predicate_definition_fold result is not one definition-body replacement' "$WORK_DIR/native_cert_v1_invalid_predicate_definition_fold.err"; then
  echo "native certificate v1 invalid-predicate-definition-fold failure did not explain the rejected side condition" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_invalid_partial.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_invalid_partial.out" \
  2>"$WORK_DIR/native_cert_v1_invalid_partial.err"; then
  echo "native certificate v1 checker accepted a partial non-refutation certificate" >&2
  exit 1
fi

if ! rg -q 'final certificate step is not the empty clause' "$WORK_DIR/native_cert_v1_invalid_partial.err"; then
  echo "native certificate v1 invalid-partial failure did not explain the rejected final clause" >&2
  exit 1
fi

echo "native certificate v1 smoke test passed"
echo "native certificate v1 artifacts: $WORK_DIR"
echo "native certificate v1 latest link: $BASE_TMPDIR/latest_native_cert_v1"
