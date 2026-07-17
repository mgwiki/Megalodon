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

check_no_unindexed_axioms() {
  local log=$1
  if rg -n 'WARNING: The id .*not indexed as previously known' "$log"; then
    echo "Megalodon accepted an unindexed axiom in $log" >&2
    exit 1
  fi
}

run_focused_primitive_audit() {
  MIN_SUBSTITUTE=0 \
  MIN_PARAMODULATE=0 \
  MIN_EQUALITY_SYMMETRY=0 \
  MIN_EQUALITY_RESOLUTION=0 \
  MIN_EQUALITY_RESOLUTION_CONSTRAINTS=0 \
  MIN_EQUALITY_FACTORING=${MIN_EQUALITY_FACTORING:-0} \
  MIN_EQUALITY_FACTORING_CONSTRAINTS=${MIN_EQUALITY_FACTORING_CONSTRAINTS:-0} \
  MIN_RESOLVE=0 \
  MIN_FACTOR=0 \
  MIN_FOOL_ATOM_LIFT=0 \
  MIN_ENNF_FORMULA=0 \
  MIN_SKOLEM_FORMULA=0 \
  MIN_CNF_LITERAL=0 \
  MIN_CNF_FORMULA_CLAUSE=0 \
  MIN_FORMULA_COPY=0 \
  MIN_FORMULA_TERM_COPY=0 \
  MIN_RECTIFY_FORMULA=0 \
  MIN_FOOL_EXHAUSTIVENESS=0 \
  MIN_TRUTH_CONFLICT=0 \
  MIN_AVATAR_COMPONENT=0 \
  MIN_AVATAR_DEFINITION=0 \
  MIN_AVATAR_SPLIT=0 \
  MIN_AVATAR_REFUTATION=0 \
  MIN_SPLIT_DEPENDENCY=0 \
  tests/vampire_certificate/run_native_primitive_audit.sh "$@"
}

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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_valid_emit.mg" \
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
if ! rg -q '// Vampire certificate source origin: examples/hammer/100thms_12_h\.mg line 123 char 45 \(source obligation\)\.' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not preserve source-origin metadata" >&2
  exit 1
fi
if ! rg -q '// vampire_source_assumption \(\(parameter "src_axiom_Foo_bar__c1"\) \(step "c1"\) \(certificate_source_kind "axiom"\) \(tptp_name "c_Foo_5Fbar"\) \(source_name "Foo_bar"\) \(source_map_kind "local_fact"\)' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not preserve source-assumption binding metadata" >&2
  exit 1
fi
if ! rg -q 'source_formula_status "decl_formula_present_unhashed"' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not classify local source-assumption binding metadata" >&2
  exit 1
fi
if ! rg -q 'vampire_source_assumption .*origin_file "examples/hammer/100thms_12_h\.mg".*origin_line "123".*origin_char "45".*origin_kind "aby"' \
    "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg"; then
  echo "native certificate v1 simple emitter did not attach origin metadata to source-assumption bindings" >&2
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_source_name_mangled_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_copied_conjecture_alias_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_copied_conjecture_alias_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.log"
if ! rg -q 'Vampire certificate v1 closed checked 5 steps' \
    "$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.log"; then
  echo "closed native certificate v1 checker did not accept copied-corpus conjecture aliases" >&2
  exit 1
fi
if ! rg -q 'source_formula_status "closed_formula_checked"' \
    "$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.mg"; then
  echo "copied-corpus conjecture alias was not semantically checked against the stable THF source" >&2
  exit 1
fi
if ! rg -q 'assume src_conjecture_hammer_10656_24__c1:' \
    "$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.mg"; then
  echo "copied-corpus conjecture alias did not recover the stable source name" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_copied_conjecture_alias_valid_emit.check.log"

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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_resolution_mirrored_valid_emit.mg" \
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_factor_prop_valid_emit.mg" \
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_substitute_prop_noop_valid_emit.mg" \
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_condensation_prop_valid_emit.mg" \
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_substitute_prop_changed_bridge.mg" \
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_factor_equality_valid_emit.mg" \
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
  -vampirecertv1sourcecontextstrict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_hash_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_context_missing.out" \
  2>"$WORK_DIR/native_cert_v1_source_context_missing.err"; then
  echo "native certificate v1 strict source-context audit accepted missing hash-backed knowns" >&2
  exit 1
fi

if ! rg -q 'strict source-context audit failed' "$WORK_DIR/native_cert_v1_source_context_missing.err"; then
  echo "native certificate v1 strict source-context audit did not explain missing hash-backed knowns" >&2
  exit 1
fi

source_context_mg="$WORK_DIR/native_cert_v1_source_context.mg"
source_context_th0="$WORK_DIR/native_cert_v1_source_context.th0.p"
source_context_cert="$WORK_DIR/native_cert_v1_source_context.sexp"
cat > "$source_context_mg" <<'EOF_SOURCE_CONTEXT_MG'
Variable p:prop.
Axiom original_a1 : forall r:prop, r -> r.
EOF_SOURCE_CONTEXT_MG
source_context_hash=$(bin/megalodon -pfgsummary2 "$source_context_mg" \
  | sed -n 's/^Known:\([0-9a-f][0-9a-f]*\)$/\1/p' \
  | head -1)
if [[ -z "$source_context_hash" ]]; then
  echo "native certificate v1 source-context smoke could not obtain the generated axiom hash" >&2
  exit 1
fi
cat > "$source_context_th0" <<EOF_SOURCE_CONTEXT_TH0
% megalodon_origin ((file "$source_context_mg") (line "1") (char "1") (kind "generated_source_context_smoke"))
% megalodon_source_map (type "p" "p" "")
thf(p,type,(p : \$o)).
% megalodon_source_map (known "a1" "original_a1" "$source_context_hash")
thf(a1,axiom,(! [R:\$o,S:\$o] : (S => S))). % $source_context_hash
% megalodon_source_map (local_fact "a2" "local_not_p" "")
thf(a2,axiom,~p).
% megalodon_source_map (local_fact "a3" "local_p" "")
thf(a3,axiom,p).
EOF_SOURCE_CONTEXT_TH0
cat > "$source_context_cert" <<'EOF_SOURCE_CONTEXT_CERT'
(certificate vampire-megalodon 1
  (problem "source-context")
  (symbol_declaration "Variable p:prop.")
  (input "u0" (source axiom "a1") (clause (pos (ALL (PROP) (ALL (PROP) (IMP (DB 0) (DB 0)))))))
  (input "u2" (source axiom "a2") (clause (neg (TMH "p"))))
  (input "u3" (source axiom "a3") (clause (pos (TMH "p"))))
  (resolve "u4" (parents "u2" "u3") (pivot 0 0) (result (clause)))
)
EOF_SOURCE_CONTEXT_CERT

bin/megalodon \
  -vampirecertv1sourcecontextstrict \
  -vampirecertv1 "$source_context_cert" \
  -vampirecertv1source "$source_context_th0" \
  "$source_context_mg" >"$WORK_DIR/native_cert_v1_source_context_checked.log"

if ! rg -q 'source context audited total=3 known_checked=1 known_missing=0 known_mismatch=0 .*local_or_unhashed=2' \
    "$WORK_DIR/native_cert_v1_source_context_checked.log"; then
  echo "native certificate v1 source-context audit did not resolve a real hash-backed known" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1sourcecontextstrict \
  -vampirecertv1corepfcheck \
  -vampirecertv1 "$source_context_cert" \
  -vampirecertv1source "$source_context_th0" \
  "$source_context_mg" >"$WORK_DIR/native_cert_v1_source_context_core_pf.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 4 steps' \
    "$WORK_DIR/native_cert_v1_source_context_core_pf.log"; then
  echo "native certificate v1 core checker did not accept a context-resolved source proof" >&2
  exit 1
fi

local_source_live_dir="$WORK_DIR/local_source_live"
mkdir -p "$local_source_live_dir"
cat >"$local_source_live_dir/fake_vampire" <<'EOF_LOCAL_SOURCE_FAKE_VAMPIRE'
#!/usr/bin/env bash
problem="${@: -1}"
conj=$(sed -n 's/^% megalodon_source_map (conjecture "\([^"]*\)" .*/\1/p' "$problem" | head -1)
cat <<CERT
% SZS status Theorem
% SZS output start Proof
megalodon_certificate_native_sexpr_start.
(certificate vampire-megalodon 1
  (problem "local-source-live")
  (symbol_declaration "Variable p:prop.")
  (input "u0" (source axiom "c_Hp") (clause (pos (TMH "p"))))
  (input "u1" (source negated_conjecture "$conj") (clause (neg (TMH "p"))))
  (resolve "u2" (parents "u0" "u1") (pivot 0 0) (result (clause)))
)
megalodon_certificate_native_sexpr_end.
% SZS output end Proof
CERT
EOF_LOCAL_SOURCE_FAKE_VAMPIRE
chmod +x "$local_source_live_dir/fake_vampire"
cat >"$local_source_live_dir/local_source_live.mg" <<'EOF_LOCAL_SOURCE_LIVE_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Axiom xm : forall P:prop, P \/ ~P.
Variable p:prop.
Theorem local_source_live:p -> p.
assume Hp:p.
aby Hp.
Qed.
EOF_LOCAL_SOURCE_LIVE_MG
bin/megalodon \
  -v 9 \
  -vampireaby "$local_source_live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabyoutdir "$local_source_live_dir/out" \
  "$local_source_live_dir/local_source_live.mg" \
  >"$WORK_DIR/native_cert_v1_live_local_source_context.log" \
  2>"$WORK_DIR/native_cert_v1_live_local_source_context.err"

if ! rg -q 'source_context known=0 local=1 local_definition=0 unresolved=1' \
    "$WORK_DIR/native_cert_v1_live_local_source_context.log"; then
  echo "live vampireaby source-context resolver did not bind the local Hp hypothesis" >&2
  exit 1
fi
if ! rg -q 'Vampire native certificate reconstructed aby proof term' \
    "$WORK_DIR/native_cert_v1_live_local_source_context.log"; then
  echo "live vampireaby did not compose the native certificate proof into the current Megalodon goal" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' \
    "$WORK_DIR/native_cert_v1_live_local_source_context.log"; then
  echo "live vampireaby source-context fixture did not close after composing the native certificate proof" >&2
  exit 1
fi

local_definition_live_dir="$WORK_DIR/local_definition_live"
mkdir -p "$local_definition_live_dir"
cat >"$local_definition_live_dir/fake_vampire" <<'EOF_LOCAL_DEFINITION_FAKE_VAMPIRE'
#!/usr/bin/env bash
problem="${@: -1}"
def=$(sed -n 's/^% megalodon_source_map (local_definition "\([^"]*\)" .*/\1/p' "$problem" | head -1)
conj=$(sed -n 's/^% megalodon_source_map (conjecture "\([^"]*\)" .*/\1/p' "$problem" | head -1)
cat <<CERT
% SZS status Theorem
% SZS output start Proof
megalodon_certificate_native_sexpr_start.
(certificate vampire-megalodon 1
  (problem "local-definition-source-live")
  (symbol_declaration "Variable p:prop.")
  (symbol_declaration "Variable r:prop.")
  (input "d0" (source definition "$def") (clause (pos (AP (AP (TMH "=") (TMH "r")) (TMH "p")))))
  (input "u0" (source axiom "c_Hp") (clause (pos (TMH "p"))))
  (input "u1" (source negated_conjecture "$conj") (clause (neg (TMH "p"))))
  (resolve "u2" (parents "u0" "u1") (pivot 0 0) (result (clause)))
)
megalodon_certificate_native_sexpr_end.
% SZS output end Proof
CERT
EOF_LOCAL_DEFINITION_FAKE_VAMPIRE
chmod +x "$local_definition_live_dir/fake_vampire"
cat >"$local_definition_live_dir/local_definition_live.mg" <<'EOF_LOCAL_DEFINITION_LIVE_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Axiom xm : forall P:prop, P \/ ~P.
Variable p:prop.
Theorem local_definition_live:p -> p.
assume Hp:p.
set r := p.
aby Hp.
Qed.
EOF_LOCAL_DEFINITION_LIVE_MG
bin/megalodon \
  -v 9 \
  -vampireaby "$local_definition_live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabyoutdir "$local_definition_live_dir/out" \
  "$local_definition_live_dir/local_definition_live.mg" \
  >"$WORK_DIR/native_cert_v1_live_local_definition_source_context.log" \
  2>"$WORK_DIR/native_cert_v1_live_local_definition_source_context.err"
if ! rg -q 'source_context known=0 local=1 local_definition=1 unresolved=1' \
    "$WORK_DIR/native_cert_v1_live_local_definition_source_context.log"; then
  echo "live vampireaby source-context resolver did not identify the local set definition" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' \
    "$WORK_DIR/native_cert_v1_live_local_definition_source_context.log"; then
  echo "live vampireaby local-definition fixture did not close via non-strict fallback" >&2
  exit 1
fi
bin/megalodon \
  -v 9 \
  -vampireaby "$local_definition_live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabynativestrict \
  -vampireabyoutdir "$local_definition_live_dir/strict_out" \
  "$local_definition_live_dir/local_definition_live.mg" \
  >"$WORK_DIR/native_cert_v1_live_local_definition_strict.log" \
  2>"$WORK_DIR/native_cert_v1_live_local_definition_strict.err"
if ! rg -q 'source_context known=0 local=1 local_definition=1 unresolved=1' \
    "$WORK_DIR/native_cert_v1_live_local_definition_strict.log"; then
  echo "strict live vampireaby did not preserve the local-definition source-context audit" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' \
    "$WORK_DIR/native_cert_v1_live_local_definition_strict.log"; then
  echo "strict live vampireaby did not close when the matched local definition was unused by the refutation" >&2
  exit 1
fi

strict_no_fallback_dir="$WORK_DIR/strict_no_fallback"
mkdir -p "$strict_no_fallback_dir"
cat >"$strict_no_fallback_dir/fake_vampire_no_certificate" <<'EOF_STRICT_NO_FALLBACK_FAKE'
#!/usr/bin/env bash
cat <<'CERT'
% SZS status Theorem
% SZS output start Proof
% no Megalodon native certificate block
% SZS output end Proof
CERT
EOF_STRICT_NO_FALLBACK_FAKE
chmod +x "$strict_no_fallback_dir/fake_vampire_no_certificate"
cat >"$strict_no_fallback_dir/strict_no_fallback.mg" <<'EOF_STRICT_NO_FALLBACK_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Axiom xm : forall P:prop, P \/ ~P.
Variable p:prop.
Theorem strict_no_fallback:p -> p.
assume Hp:p.
aby Hp.
Qed.
EOF_STRICT_NO_FALLBACK_MG
if bin/megalodon \
    -vampireaby "$strict_no_fallback_dir/fake_vampire_no_certificate" \
    -vampireabyproof megalodon \
    -vampireabynative \
    -vampireabynativestrict \
    -vampireabyoutdir "$strict_no_fallback_dir/out" \
    "$strict_no_fallback_dir/strict_no_fallback.mg" \
    >"$WORK_DIR/native_cert_v1_strict_no_fallback.out" \
    2>"$WORK_DIR/native_cert_v1_strict_no_fallback.err"; then
  echo "strict live vampireaby accepted direct native reconstruction after Vampire produced no native certificate" >&2
  exit 1
fi
if ! rg -q 'has no native certificate block|did not reconstruct current aby goal' \
    "$WORK_DIR/native_cert_v1_strict_no_fallback.out" \
    "$WORK_DIR/native_cert_v1_strict_no_fallback.err"; then
  echo "strict live vampireaby failure did not explain the missing certificate-derived proof" >&2
  exit 1
fi

cat >"$WORK_DIR/native_cert_v1_bad_xm_shape.mg" <<'EOF_BAD_XM_SHAPE'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Axiom xm : forall P:prop, P.
Variable p:prop.
Theorem bad_xm_shape:p.
exact (xm p).
Qed.
EOF_BAD_XM_SHAPE
if bin/megalodon "$WORK_DIR/native_cert_v1_bad_xm_shape.mg" \
    >"$WORK_DIR/native_cert_v1_bad_xm_shape.out" \
    2>"$WORK_DIR/native_cert_v1_bad_xm_shape.err"; then
  echo "Megalodon trusted an xm axiom with the wrong proposition shape" >&2
  exit 1
fi

library_source_live_dir="$WORK_DIR/library_source_live"
mkdir -p "$library_source_live_dir"
awk '{print} /^Axiom xm /{exit}' examples/UpToOctonions/Part2.mg \
  >"$library_source_live_dir/prefix.mg"
cp "$local_source_live_dir/fake_vampire" "$library_source_live_dir/fake_vampire"
cat "$library_source_live_dir/prefix.mg" >"$library_source_live_dir/library_source_live.mg"
cat >>"$library_source_live_dir/library_source_live.mg" <<'EOF_LIBRARY_SOURCE_LIVE_MG'

Variable p:prop.
Theorem live_source_after_library_xm:p -> p.
assume Hp:p.
aby Hp.
Qed.
EOF_LIBRARY_SOURCE_LIVE_MG
bin/megalodon \
  -v 9 \
  -vampireaby "$library_source_live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabyoutdir "$library_source_live_dir/out" \
  "$library_source_live_dir/library_source_live.mg" \
  >"$WORK_DIR/native_cert_v1_live_library_source_context.log" \
  2>"$WORK_DIR/native_cert_v1_live_library_source_context.err"
if ! rg -q 'Vampire native certificate reconstructed aby proof term' \
    "$WORK_DIR/native_cert_v1_live_library_source_context.log"; then
  echo "live vampireaby did not compose a native certificate proof in the larger library context" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' \
    "$WORK_DIR/native_cert_v1_live_library_source_context.log"; then
  echo "live vampireaby larger library-context fixture did not close" >&2
  exit 1
fi

multi_local_source_live_dir="$WORK_DIR/multi_local_source_live"
mkdir -p "$multi_local_source_live_dir"
cat >"$multi_local_source_live_dir/fake_vampire" <<'EOF_MULTI_LOCAL_FAKE_VAMPIRE'
#!/usr/bin/env bash
problem="${@: -1}"
conj=$(sed -n 's/^% megalodon_source_map (conjecture "\([^"]*\)" .*/\1/p' "$problem" | head -1)
cat <<CERT
% SZS status Theorem
% SZS output start Proof
megalodon_certificate_native_sexpr_start.
(certificate vampire-megalodon 1
  (problem "multi-local-source-live")
  (symbol_declaration "Variable p:prop.")
  (symbol_declaration "Variable q:prop.")
  (input "u0" (source axiom "c_Hp") (clause (pos (TMH "p"))))
  (input "u1" (source axiom "c_Hq") (clause (pos (TMH "q"))))
  (input "u2" (source negated_conjecture "$conj") (clause (neg (TMH "p"))))
  (resolve "u3" (parents "u0" "u2") (pivot 0 0) (result (clause)))
)
megalodon_certificate_native_sexpr_end.
% SZS output end Proof
CERT
EOF_MULTI_LOCAL_FAKE_VAMPIRE
chmod +x "$multi_local_source_live_dir/fake_vampire"
cat >"$multi_local_source_live_dir/multi_local_source_live.mg" <<'EOF_MULTI_LOCAL_SOURCE_LIVE_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Axiom xm : forall P:prop, P \/ ~P.
Variable p q:prop.
Theorem live_multi_local:p -> q -> p.
assume Hp:p.
assume Hq:q.
aby Hp Hq.
Qed.
EOF_MULTI_LOCAL_SOURCE_LIVE_MG
bin/megalodon \
  -v 9 \
  -vampireaby "$multi_local_source_live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabyoutdir "$multi_local_source_live_dir/out" \
  "$multi_local_source_live_dir/multi_local_source_live.mg" \
  >"$WORK_DIR/native_cert_v1_live_multi_local_source_context.log" \
  2>"$WORK_DIR/native_cert_v1_live_multi_local_source_context.err"
if ! rg -q 'source_context known=0 local=2 local_definition=0 unresolved=1' \
    "$WORK_DIR/native_cert_v1_live_multi_local_source_context.log"; then
  echo "live vampireaby multi-local fixture did not bind both local hypotheses" >&2
  exit 1
fi
if ! rg -q 'Vampire native certificate reconstructed aby proof term' \
    "$WORK_DIR/native_cert_v1_live_multi_local_source_context.log"; then
  echo "live vampireaby did not compose the multi-local native certificate proof" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' \
    "$WORK_DIR/native_cert_v1_live_multi_local_source_context.log"; then
  echo "live vampireaby multi-local fixture did not close" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_synthetic_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_synthetic_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 3 sources' \
    "$WORK_DIR/native_cert_v1_source_map_synthetic_valid.log"; then
  echo "native certificate v1 source-map checker did not synthesize THF declaration mappings" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_multiline_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_map_multiline_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_multiline_closed.log"

if ! rg -q 'Vampire certificate v1 closed checked 6 steps' \
    "$WORK_DIR/native_cert_v1_source_map_multiline_closed.log"; then
  echo "closed native certificate v1 checker did not accept multiline THF source-map declarations" >&2
  exit 1
fi
if ! rg -q 'source_formula_status "closed_formula_checked"' \
    "$WORK_DIR/native_cert_v1_source_map_multiline_closed.mg"; then
  echo "closed native certificate v1 checker did not semantically check multiline THF source formulas" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_synthetic_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_map_synthetic_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_synthetic_closed.log"

if ! rg -q 'Vampire certificate v1 closed checked 6 steps' \
    "$WORK_DIR/native_cert_v1_source_map_synthetic_closed.log"; then
  echo "closed native certificate v1 checker did not accept synthesized THF declaration mappings" >&2
  exit 1
fi

if rg -q 'bridge_' "$WORK_DIR/native_cert_v1_source_map_synthetic_closed.mg"; then
  echo "closed native certificate v1 synthetic source-map fixture generated a bridge premise" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_closed_unapproved_axiom_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_synthetic_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_closed_unapproved_axiom_bad.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_closed_unapproved_axiom_bad.out" \
  2>"$WORK_DIR/native_cert_v1_closed_unapproved_axiom_bad.err"; then
  echo "closed native certificate v1 emitter accepted an unapproved generated axiom" >&2
  exit 1
fi

if ! rg -q 'closed axiom policy rejects unapproved axiom vampire_backdoor' \
    "$WORK_DIR/native_cert_v1_closed_unapproved_axiom_bad.err"; then
  echo "closed native certificate v1 unapproved-axiom failure did not explain the rejected axiom" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1coreclosed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_synthetic_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_map_synthetic_core_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_synthetic_core_closed.log"

if ! rg -q 'Vampire certificate v1 core fragment checked 6 steps' \
    "$WORK_DIR/native_cert_v1_source_map_synthetic_core_closed.log"; then
  echo "core closed native certificate v1 checker did not report the clausal core fragment" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.2.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.2.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_unit.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 3 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_unit.log"; then
  echo "native core proof-term checker did not validate the unit resolution seed" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source bindings checked 2 assumptions' \
    "$WORK_DIR/native_cert_v1_core_pf_unit.log"; then
  echo "native core proof-term checker did not bind source assumptions for the unit seed" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source propositions recorded 2 assumptions' \
    "$WORK_DIR/native_cert_v1_core_pf_unit.log"; then
  echo "native core proof-term checker did not retain source assumption propositions for the unit seed" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 source origin core_seed_core\.cnf\.2\.mg line 1 char 1 \(generated_core_seed\)' \
    "$WORK_DIR/native_cert_v1_core_pf_unit.log"; then
  echo "native core proof-term checker did not require/report original-origin metadata" >&2
  exit 1
fi

tail -n +2 tests/vampire_certificate/closed_cases/core.cnf.2.th0.p \
  >"$WORK_DIR/core.cnf.2.no_origin.th0.p"
if bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.2.native.sexp \
  -vampirecertv1source "$WORK_DIR/core.cnf.2.no_origin.th0.p" \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_no_origin.log" 2>"$WORK_DIR/native_cert_v1_core_pf_no_origin.err"; then
  echo "native core proof-term checker accepted a source file without Megalodon origin metadata" >&2
  exit 1
fi
if ! rg -q 'requires Megalodon origin metadata' \
    "$WORK_DIR/native_cert_v1_core_pf_no_origin.err"; then
  echo "native core proof-term missing-origin rejection did not explain the source-origin requirement" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.1.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.1.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_binary_unit.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_binary_unit.log"; then
  echo "native core proof-term checker did not validate the binary/unit resolution seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.9.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.9.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_factor.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 6 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_factor.log"; then
  echo "native core proof-term checker did not validate the factor seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.16.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.16.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_identity_substitute.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_identity_substitute.log"; then
  echo "native core proof-term checker did not validate the identity substitution seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_instantiation_refutation_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_kernel_instantiation_refutation_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_instantiation_substitute.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_instantiation_substitute.log"; then
  echo "native core proof-term checker did not validate the instantiation substitution seed" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1coreclosed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_closed_nonidentity_substitute_bad.out" \
  2>"$WORK_DIR/native_cert_v1_core_closed_nonidentity_substitute_bad.err"; then
  echo "core closed native certificate v1 checker accepted a non-identity substitution" >&2
  exit 1
fi

if ! rg -q 'c2:substitute' \
    "$WORK_DIR/native_cert_v1_core_closed_nonidentity_substitute_bad.err"; then
  echo "core closed native certificate v1 non-identity substitution rejection did not name the unsupported step" >&2
  exit 1
fi

{
  echo '% megalodon_origin ((file "native_cert_v1_substitute_prop_changed_unsupported.mg") (line "1") (char "1") (kind "synthetic_negative"))'
  cat tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.th0.p
} >"$WORK_DIR/native_cert_v1_substitute_prop_changed_unsupported_with_origin.th0.p"

if bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_substitute_prop_changed_unsupported.sexp \
  -vampirecertv1source "$WORK_DIR/native_cert_v1_substitute_prop_changed_unsupported_with_origin.th0.p" \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_nonidentity_substitute_bad.out" \
  2>"$WORK_DIR/native_cert_v1_core_pf_nonidentity_substitute_bad.err"; then
  echo "native core proof-term checker accepted a non-identity substitution without explicit proof data" >&2
  exit 1
fi

if ! rg -q 'c2:substitute' \
    "$WORK_DIR/native_cert_v1_core_pf_nonidentity_substitute_bad.err"; then
  echo "native core proof-term non-identity substitution rejection did not name the unsupported step" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.17.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.17.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_equality_resolution.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_equality_resolution.log"; then
  echo "native core proof-term checker did not validate the equality-resolution seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.23.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.23.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_equality_symmetry.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_equality_symmetry.log"; then
  echo "native core proof-term checker did not validate the equality-symmetry seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.18.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.18.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_paramodulation.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 6 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_paramodulation.log"; then
  echo "native core proof-term checker did not validate the paramodulation seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.19.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.19.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_paramodulation_negative.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 6 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_paramodulation_negative.log"; then
  echo "native core proof-term checker did not validate the negative-target paramodulation seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.20.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.20.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_subsumption_resolution.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 6 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_subsumption_resolution.log"; then
  echo "native core proof-term checker did not validate the subsumption-resolution seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.21.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.21.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_paramodulation_binary.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 8 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_paramodulation_binary.log"; then
  echo "native core proof-term checker did not validate the binary-target paramodulation seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/core.cnf.22.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/core.cnf.22.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_paramodulation_long.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 10 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_paramodulation_long.log"; then
  echo "native core proof-term checker did not validate the long-clause paramodulation seed" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.11560.31.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.11560.31.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_source_entry_hammer.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 5 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_source_entry_hammer.log"; then
  echo "native core proof-term checker did not validate the source-entry hammer fixture" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source bindings checked 1 assumption' \
    "$WORK_DIR/native_cert_v1_core_pf_source_entry_hammer.log"; then
  echo "native core proof-term checker did not retain source-entry assumptions" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/preprocess.formula.2.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/preprocess.formula.2.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_rectify_formula.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 7 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_rectify_formula.log"; then
  echo "native core proof-term checker did not validate the rectify_formula source-entry fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.12340.9.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.12340.9.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_fool_formula.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 11 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_fool_formula.log"; then
  echo "native core proof-term checker did not validate the fool_formula source-entry fixture" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source bindings checked 2 assumptions' \
    "$WORK_DIR/native_cert_v1_core_pf_fool_formula.log"; then
  echo "native core proof-term checker did not retain FOOL source-entry assumptions" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.10455.26.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.10455.26.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_core_pf_ennf_instantiation_hammer.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 40 steps' \
    "$WORK_DIR/native_cert_v1_core_pf_ennf_instantiation_hammer.log"; then
  echo "native core proof-term checker did not validate the ENNF/instantiation hammer fixture" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source bindings checked 4 assumptions' \
    "$WORK_DIR/native_cert_v1_core_pf_ennf_instantiation_hammer.log"; then
  echo "native core proof-term checker did not retain ENNF/instantiation source assumptions" >&2
  exit 1
fi

mkdir -p "$WORK_DIR/core_pf_missing_source_cases"
cp tests/vampire_certificate/closed_cases/core.cnf.2.native.sexp \
  "$WORK_DIR/core_pf_missing_source_cases/missing_source.native.sexp"
cat >"$WORK_DIR/core_pf_missing_source_cases.list" <<EOF
missing_source
EOF
if CASES_DIR="$WORK_DIR/core_pf_missing_source_cases" \
    CASE_LIST="$WORK_DIR/core_pf_missing_source_cases.list" \
    WORK_DIR="$WORK_DIR/core_pf_missing_source_audit" \
    MIN_CORE_PF=1 \
    tests/vampire_certificate/run_native_cert_v1_core_pf_audit.sh \
    >"$WORK_DIR/core_pf_missing_source_audit.out" \
    2>"$WORK_DIR/core_pf_missing_source_audit.err"; then
  echo "native core proof-term audit accepted a selected certificate without a source file" >&2
  exit 1
fi

if ! rg -q $'missing_source\tCORE_PF_MISSING_SOURCE' \
    "$WORK_DIR/core_pf_missing_source_audit/summary.tsv"; then
  echo "native core proof-term audit did not classify missing source files explicitly" >&2
  exit 1
fi

mkdir -p "$WORK_DIR/preprocess_pf_missing_source_cases"
cp tests/vampire_certificate/closed_cases/preprocess.formula.1.native.sexp \
  "$WORK_DIR/preprocess_pf_missing_source_cases/missing_preprocess_source.native.sexp"
cat >"$WORK_DIR/preprocess_pf_missing_source_cases.list" <<EOF
missing_preprocess_source
EOF
if CASES_DIR="$WORK_DIR/preprocess_pf_missing_source_cases" \
    CASE_LIST="$WORK_DIR/preprocess_pf_missing_source_cases.list" \
    WORK_DIR="$WORK_DIR/preprocess_pf_missing_source_audit" \
    MIN_PREPROCESS_STRUCTURAL=1 \
    tests/vampire_certificate/run_native_cert_v1_preprocess_pf_audit.sh \
    >"$WORK_DIR/preprocess_pf_missing_source_audit.out" \
    2>"$WORK_DIR/preprocess_pf_missing_source_audit.err"; then
  echo "native preprocess structural audit accepted a selected certificate without a source file" >&2
  exit 1
fi

if ! rg -q $'missing_preprocess_source\tPREPROCESS_STRUCTURAL_MISSING_SOURCE' \
    "$WORK_DIR/preprocess_pf_missing_source_audit/summary.tsv"; then
  echo "native preprocess structural audit did not classify missing source files explicitly" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1coreclosed \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.1007.43.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.1007.43.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_skolem_core_closed_bad.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_core_closed_bad.out" \
  2>"$WORK_DIR/native_cert_v1_skolem_core_closed_bad.err"; then
  echo "core closed native certificate v1 checker accepted an unsupported skolemization certificate" >&2
  exit 1
fi

if ! rg -q 'core closed certificate v1 permits only the proof-producing source-entry/core fragment' \
    "$WORK_DIR/native_cert_v1_skolem_core_closed_bad.err"; then
  echo "core closed native certificate v1 skolemization rejection did not explain the source-entry/core fragment boundary" >&2
  exit 1
fi
if ! rg -q 'skolem_formula' \
    "$WORK_DIR/native_cert_v1_skolem_core_closed_bad.err"; then
  echo "core closed native certificate v1 skolemization rejection did not name the unsupported step" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_factoring_core_pf_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_equality_factoring_core_pf_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_factoring_core_pf_valid.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 6 steps' \
    "$WORK_DIR/native_cert_v1_equality_factoring_core_pf_valid.log"; then
  echo "native core proof-term checker did not accept equality_factoring" >&2
  exit 1
fi

MIN_EQUALITY_FACTORING=1 \
WORK_DIR="$WORK_DIR/equality_factoring_primitive_audit_valid" \
run_focused_primitive_audit \
  tests/vampire_certificate/native_cert_v1_equality_factoring_primitive_valid.sexp \
  >"$WORK_DIR/equality_factoring_primitive_audit_valid.out"

if ! rg -q 'equality_factoring 1' \
    "$WORK_DIR/equality_factoring_primitive_audit_valid/rule_counts.txt"; then
  echo "native primitive audit did not count the equality_factoring primitive fixture" >&2
  exit 1
fi

if MIN_EQUALITY_FACTORING=1 \
    WORK_DIR="$WORK_DIR/equality_factoring_primitive_audit_missing_other_bad" \
    run_focused_primitive_audit \
      tests/vampire_certificate/native_cert_v1_equality_factoring_primitive_missing_other_bad.sexp \
      >"$WORK_DIR/equality_factoring_primitive_audit_missing_other_bad.out" \
      2>"$WORK_DIR/equality_factoring_primitive_audit_missing_other_bad.err"; then
  echo "native primitive audit accepted equality_factoring without an other literal" >&2
  exit 1
fi

if ! rg -q '\(other ' \
    "$WORK_DIR/equality_factoring_primitive_audit_missing_other_bad/missing_equality_factoring_fields.tsv"; then
  echo "native primitive audit did not explain the missing equality_factoring other literal" >&2
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

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_formula_mismatch_bad.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad_closed.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad_closed.err"; then
  echo "closed native certificate v1 source-map checker accepted a mismatched THF formula" >&2
  exit 1
fi

if ! rg -q 'does not match the THF declaration formula' \
    "$WORK_DIR/native_cert_v1_source_map_formula_mismatch_bad_closed.err"; then
  echo "closed native certificate v1 source-map formula-mismatch failure did not explain the semantic mismatch" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_local_fact_formula_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_local_fact_formula_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_local_fact_formula_mismatch_bad.err"; then
  echo "native certificate v1 source-map checker accepted a mismatched local fact formula" >&2
  exit 1
fi

if ! rg -q 'does not match the THF declaration formula' \
    "$WORK_DIR/native_cert_v1_source_map_local_fact_formula_mismatch_bad.err"; then
  echo "native certificate v1 source-map local-fact formula-mismatch failure did not explain the semantic mismatch" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_unsupported_formula.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_unsupported_formula.log"

if ! rg -q 'Vampire certificate v1 source map checked 3 sources' \
    "$WORK_DIR/native_cert_v1_source_map_unsupported_formula.log"; then
  echo "native certificate v1 ordinary source-map checker did not preserve unsupported-formula diagnostics" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_unsupported_formula.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_unsupported_formula_strict.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_unsupported_formula_strict.err"; then
  echo "strict native certificate v1 source-map checker accepted an unsupported THF source formula" >&2
  exit 1
fi

if ! rg -q 'outside the checked source-linking fragment' \
    "$WORK_DIR/native_cert_v1_source_map_unsupported_formula_strict.err"; then
  echo "strict native certificate v1 unsupported-formula failure did not explain the source-linking gap" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_unsupported_formula.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_source_map_unsupported_formula_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_unsupported_formula_closed.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_unsupported_formula_closed.err"; then
  echo "closed native certificate v1 source-map checker accepted an unsupported THF source formula" >&2
  exit 1
fi

if ! rg -q 'outside the checked source-linking fragment' \
    "$WORK_DIR/native_cert_v1_source_map_unsupported_formula_closed.err"; then
  echo "closed native certificate v1 unsupported-formula failure did not explain the source-linking gap" >&2
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

if ! rg -q 'has source hash .* but the TPTP declaration is tagged' \
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
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_primitive_expansion_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_primitive_expansion_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' \
    "$WORK_DIR/native_cert_v1_primitive_expansion_valid.log"; then
  echo "strict native certificate v1 checker did not accept primitive-expansion contract metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factoring_kernel_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_factoring_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_factoring_kernel_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 5 steps' \
    "$WORK_DIR/native_cert_v1_factoring_kernel_valid.log"; then
  echo "strict native certificate v1 checker did not accept factoring kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_factoring_kernel_missing_other_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_factoring_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_factoring_kernel_missing_other_bad.out" \
  2>"$WORK_DIR/native_cert_v1_factoring_kernel_missing_other_bad.err"; then
  echo "strict native certificate v1 checker accepted factoring metadata without an other literal" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata requires other' \
    "$WORK_DIR/native_cert_v1_factoring_kernel_missing_other_bad.err"; then
  echo "strict native certificate v1 factoring failure did not explain the missing other metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_subsumption_resolution_kernel_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_subsumption_resolution_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_subsumption_resolution_kernel_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 7 steps' \
    "$WORK_DIR/native_cert_v1_subsumption_resolution_kernel_valid.log"; then
  echo "strict native certificate v1 checker did not accept subsumption-resolution kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_subsumption_resolution_kernel_side_pivot_mismatch_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_subsumption_resolution_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_subsumption_resolution_kernel_side_pivot_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_subsumption_resolution_kernel_side_pivot_mismatch_bad.err"; then
  echo "strict native certificate v1 checker accepted mismatched subsumption-resolution side pivot metadata" >&2
  exit 1
fi

if ! rg -q 'field side_pivot_substituted does not match the certificate literal' \
    "$WORK_DIR/native_cert_v1_subsumption_resolution_kernel_side_pivot_mismatch_bad.err"; then
  echo "strict native certificate v1 subsumption-resolution failure did not explain the side-pivot mismatch" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_resolution_kernel_valid.log"

if ! rg -q 'Vampire certificate v1 checked 3 steps' \
    "$WORK_DIR/native_cert_v1_equality_resolution_kernel_valid.log"; then
  echo "native certificate v1 checker did not accept equality-resolution kernel metadata" >&2
  exit 1
fi

TMPDIR="$TMPDIR" \
WORK_DIR="$WORK_DIR/equality_resolution_kernel_metadata_audit" \
MIN_REWRITE_POSITION=0 \
  tests/vampire_certificate/run_kernel_v1_metadata_audit.sh \
    tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_valid.sexp \
  >"$WORK_DIR/native_cert_v1_equality_resolution_kernel_metadata_audit.log"

if ! rg -q '^equality_resolution 1$' \
    "$WORK_DIR/native_cert_v1_equality_resolution_kernel_metadata_audit.log"; then
  echo "kernel_v1 metadata audit did not accept equality-resolution primitive contract" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_resolution_kernel_strict_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 3 steps' \
    "$WORK_DIR/native_cert_v1_equality_resolution_kernel_strict_valid.log"; then
  echo "strict native certificate v1 checker did not accept equality-resolution kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_missing_selected_substituted_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_equality_resolution_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_resolution_kernel_missing_selected_substituted_bad.out" \
  2>"$WORK_DIR/native_cert_v1_equality_resolution_kernel_missing_selected_substituted_bad.err"; then
  echo "strict native certificate v1 checker accepted equality-resolution metadata without substituted selected literal" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata requires selected_substituted' \
    "$WORK_DIR/native_cert_v1_equality_resolution_kernel_missing_selected_substituted_bad.err"; then
  echo "strict native certificate v1 equality-resolution failure did not explain the missing selected_substituted metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_factoring_kernel_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_equality_factoring_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_factoring_kernel_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 7 steps' \
    "$WORK_DIR/native_cert_v1_equality_factoring_kernel_valid.log"; then
  echo "strict native certificate v1 checker did not accept equality-factoring kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_equality_factoring_kernel_missing_other_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_equality_factoring_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_equality_factoring_kernel_missing_other_bad.out" \
  2>"$WORK_DIR/native_cert_v1_equality_factoring_kernel_missing_other_bad.err"; then
  echo "strict native certificate v1 checker accepted equality-factoring metadata without an other literal" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata requires other' \
    "$WORK_DIR/native_cert_v1_equality_factoring_kernel_missing_other_bad.err"; then
  echo "strict native certificate v1 equality-factoring failure did not explain the missing other metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_primitive_expansion_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 7 steps' \
    "$WORK_DIR/native_cert_v1_fool_primitive_expansion_valid.log"; then
  echo "strict native certificate v1 checker did not accept FOOL primitive-expansion metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_typed_eq_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_primitive_expansion_typed_eq_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 7 steps' \
    "$WORK_DIR/native_cert_v1_fool_primitive_expansion_typed_eq_valid.log"; then
  echo "strict native certificate v1 checker did not accept typed-equality FOOL primitive-expansion metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_primitive_expansion_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_fool_primitive_expansion_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted FOOL primitive-expansion metadata without the primitive step" >&2
  exit 1
fi

if ! rg -q 'requires a fool_atom_lift primitive step with prefix f1' \
    "$WORK_DIR/native_cert_v1_fool_primitive_expansion_missing_bad.err"; then
  echo "strict native certificate v1 FOOL primitive-expansion failure did not explain the missing primitive" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_contract_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_primitive_contract_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_fool_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted FOOL formula metadata without a primitive-expansion contract" >&2
  exit 1
fi

if ! rg -q 'requires primitive_expansion=prefix for kernel rule fool_formula' \
    "$WORK_DIR/native_cert_v1_fool_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 FOOL primitive-contract failure did not explain the missing contract" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1preprocesspfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_origin_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_preprocess_dynamic_known_bad.out" \
  2>"$WORK_DIR/native_cert_v1_fool_preprocess_dynamic_known_bad.err"; then
  echo "native preprocess checker accepted a certificate-derived Known primitive without the structural opt-in" >&2
  exit 1
fi

if ! rg -q 'refuses certificate-derived Known primitive vampire_fool_formula_f1' \
    "$WORK_DIR/native_cert_v1_fool_preprocess_dynamic_known_bad.err"; then
  echo "native preprocess checker did not explain rejected certificate-derived Known primitive" >&2
  exit 1
fi

MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1 bin/megalodon \
  -vampirecertv1preprocesspfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_primitive_expansion_origin_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.out" \
  2>"$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.err"

if ! rg -q 'Vampire certificate v1 native preprocess proof term checked 7 steps' \
    "$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.out"; then
  echo "native preprocess structural checker did not accept the typed FOOL primitive fixture" >&2
  exit 1
fi

if ! rg -q 'Vampire certificate v1 native preprocess source bindings checked 2 assumptions' \
    "$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.out"; then
  echo "native preprocess structural checker did not validate FOOL primitive source bindings" >&2
  exit 1
fi

if rg -q 'admit|aby|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.out" \
    "$WORK_DIR/native_cert_v1_fool_preprocess_pf_frontier.err"; then
  echo "native preprocess structural checker reported an admission marker for the FOOL primitive fixture" >&2
  exit 1
fi

MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1 bin/megalodon \
  -vampirecertv1preprocesspfcheck \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.1032.16.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.1032.16.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_raw_prop_eq_fool_bool_frontier.out" \
  2>"$WORK_DIR/native_cert_v1_raw_prop_eq_fool_bool_frontier.err"

if ! rg -q 'Vampire certificate v1 native preprocess proof term checked 15 steps' \
    "$WORK_DIR/native_cert_v1_raw_prop_eq_fool_bool_frontier.out"; then
  echo "native preprocess structural checker did not accept the refreshed typed-equality hammer FOOL case" >&2
  exit 1
fi

if rg -q 'native preprocess proof-term fool_bool cannot lift positive atom|equality-symmetry requires typed Megalodon equality|admit|-allowincompleteqed' \
    "$WORK_DIR/native_cert_v1_raw_prop_eq_fool_bool_frontier.out" \
    "$WORK_DIR/native_cert_v1_raw_prop_eq_fool_bool_frontier.err"; then
  echo "native preprocess structural checker regressed on the refreshed typed-equality hammer FOOL case" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_normalize_primitive_contract_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_cnf_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_normalize_primitive_contract_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_formula_normalize_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted formula-normalize metadata without a primitive-expansion contract" >&2
  exit 1
fi

if ! rg -q 'requires primitive_expansion=prefix for kernel rule formula_normalize' \
    "$WORK_DIR/native_cert_v1_formula_normalize_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 formula-normalize primitive-contract failure did not explain the missing contract" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_clause_primitive_contract_missing_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_cnf_clause_primitive_contract_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_cnf_clause_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted CNF-clause metadata without a primitive-expansion contract" >&2
  exit 1
fi

if ! rg -q 'requires primitive_expansion=prefix for kernel rule cnf_clause' \
    "$WORK_DIR/native_cert_v1_cnf_clause_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 CNF-clause primitive-contract failure did not explain the missing contract" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_clause_kernel_count_mismatch_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_cnf_clause_kernel_count_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_cnf_clause_kernel_count_mismatch_bad.err"; then
  echo "strict native certificate v1 checker accepted CNF-clause metadata with a wrong deterministic clause count" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata field clause_count expected 1 but got 2' \
    "$WORK_DIR/native_cert_v1_cnf_clause_kernel_count_mismatch_bad.err"; then
  echo "strict native certificate v1 CNF-clause count mismatch did not explain the bad metadata" >&2
  exit 1
fi

cat >"$WORK_DIR/native_cert_v1_primitive_audit_cnf_clause_bad_requires.sexp" <<'EOF'
(certificate vampire-megalodon 1
  (problem "native-cert-v1-primitive-audit-cnf-clause-bad-requires")
  (step_extra "u1" "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=cnf_clause"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=u1"
     "primitive_expansion_requires=bogus_primitive"))
  (bogus_primitive "u1"
    (result
      (clause))))
EOF
if MIN_SUBSTITUTE=0 \
    MIN_PARAMODULATE=0 \
    MIN_EQUALITY_SYMMETRY=0 \
    MIN_EQUALITY_RESOLUTION=0 \
    MIN_RESOLVE=0 \
    MIN_FACTOR=0 \
    tests/vampire_certificate/run_native_primitive_audit.sh \
      "$WORK_DIR/native_cert_v1_primitive_audit_cnf_clause_bad_requires.sexp" \
      >"$WORK_DIR/native_cert_v1_primitive_audit_cnf_clause_bad_requires.out" \
      2>"$WORK_DIR/native_cert_v1_primitive_audit_cnf_clause_bad_requires.err"; then
  echo "native primitive audit accepted an unsupported CNF-clause primitive expansion" >&2
  exit 1
fi

if ! rg -q 'unsupported-expansion-primitive.*cnf_clause.*bogus_primitive' \
    "$WORK_DIR/native_cert_v1_primitive_audit_cnf_clause_bad_requires.err"; then
  echo "native primitive audit did not explain the unsupported CNF-clause primitive expansion" >&2
  exit 1
fi

cat >"$WORK_DIR/native_cert_v1_primitive_audit_avatar_bad_requires.sexp" <<'EOF'
(certificate vampire-megalodon 1
  (problem "native-cert-v1-primitive-audit-avatar-bad-requires")
  (step_extra "u1" "kernel_v1"
    ("schema=prover9-small-kernel-v1"
     "rule=avatar_component"
     "primitive_expansion=prefix"
     "primitive_expansion_prefix=u1"
     "primitive_expansion_requires=bogus_primitive"))
  (bogus_primitive "u1"
    (result
      (clause))))
EOF
if MIN_SUBSTITUTE=0 \
    MIN_PARAMODULATE=0 \
    MIN_EQUALITY_SYMMETRY=0 \
    MIN_EQUALITY_RESOLUTION=0 \
    MIN_RESOLVE=0 \
    MIN_FACTOR=0 \
    tests/vampire_certificate/run_native_primitive_audit.sh \
      "$WORK_DIR/native_cert_v1_primitive_audit_avatar_bad_requires.sexp" \
      >"$WORK_DIR/native_cert_v1_primitive_audit_avatar_bad_requires.out" \
      2>"$WORK_DIR/native_cert_v1_primitive_audit_avatar_bad_requires.err"; then
  echo "native primitive audit accepted an unsupported AVATAR-component primitive expansion" >&2
  exit 1
fi

if ! rg -q 'unsupported-expansion-primitive.*avatar_component.*bogus_primitive' \
    "$WORK_DIR/native_cert_v1_primitive_audit_avatar_bad_requires.err"; then
  echo "native primitive audit did not explain the unsupported AVATAR-component primitive expansion" >&2
  exit 1
fi

MIN_REWRITE_POSITION=0 \
  tests/vampire_certificate/run_kernel_v1_metadata_audit.sh \
  tests/vampire_certificate/native_cert_v1_kernel_instantiation_valid.sexp \
  >"$WORK_DIR/native_cert_v1_kernel_instantiation_valid.log"

if ! rg -q 'instantiation 1' "$WORK_DIR/native_cert_v1_kernel_instantiation_valid.log"; then
  echo "kernel_v1 metadata audit did not accept instantiation metadata" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_instantiation_refutation_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_kernel_instantiation_refutation_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_kernel_instantiation_strict_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 5 steps' \
    "$WORK_DIR/native_cert_v1_kernel_instantiation_strict_valid.log"; then
  echo "strict native certificate v1 checker did not accept instantiation metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_instantiation_missing_substitution_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_kernel_instantiation_refutation_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_kernel_instantiation_missing_substitution_bad.out" \
  2>"$WORK_DIR/native_cert_v1_kernel_instantiation_missing_substitution_bad.err"; then
  echo "strict native certificate v1 checker accepted instantiation metadata without a substitution" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata requires substitution' \
    "$WORK_DIR/native_cert_v1_kernel_instantiation_missing_substitution_bad.err"; then
  echo "strict native certificate v1 instantiation failure did not explain the missing substitution" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_primitive_expansion_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_primitive_expansion_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_primitive_expansion_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted kernel macro metadata without a primitive-expansion contract" >&2
  exit 1
fi

if ! rg -q 'requires primitive_expansion=prefix for kernel rule unit_resulting_resolution' \
    "$WORK_DIR/native_cert_v1_primitive_expansion_missing_bad.err"; then
  echo "strict native certificate v1 primitive-expansion failure did not explain the missing contract" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_future_unit_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_kernel_future_unit_bad.out" \
  2>"$WORK_DIR/native_cert_v1_kernel_future_unit_bad.err"; then
  echo "strict native certificate v1 checker accepted kernel metadata with a future premise unit" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata references non-earlier premise unit c4' \
    "$WORK_DIR/native_cert_v1_kernel_future_unit_bad.err"; then
  echo "strict native certificate v1 future-unit failure did not explain the non-earlier reference" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_resolution_metadata_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_resolution_metadata_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' \
    "$WORK_DIR/native_cert_v1_resolution_metadata_valid.log"; then
  echo "strict native certificate v1 checker did not accept resolution primitive metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_resolution_metadata_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_resolution_metadata_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_resolution_metadata_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted resolution metadata without both primitive parent substitutions" >&2
  exit 1
fi

if ! rg -q 'kernel_v1 metadata requires primitive_parent_1_substitution' \
    "$WORK_DIR/native_cert_v1_resolution_metadata_missing_bad.err"; then
  echo "strict native certificate v1 resolution-metadata failure did not explain the missing primitive parent substitution" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_resolution_metadata_pivot_mismatch_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_resolution_metadata_pivot_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_resolution_metadata_pivot_mismatch_bad.err"; then
  echo "strict native certificate v1 checker accepted resolution metadata with mismatched pivots" >&2
  exit 1
fi

if ! rg -q 'resolution parent/literal metadata does not match certificate pivots' \
    "$WORK_DIR/native_cert_v1_resolution_metadata_pivot_mismatch_bad.err"; then
  echo "strict native certificate v1 resolution-metadata failure did not explain the pivot mismatch" >&2
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
if ! rg -q 'source_hash "[0-9a-fA-F]{64}".*source_formula_status "closed_formula_checked"' \
    "$WORK_DIR/native_cert_v1_closed_source_map_valid.mg"; then
  echo "closed native certificate v1 emitter did not mark hash-backed source bindings as checked" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_closed_source_map_valid.mg" \
  >"$WORK_DIR/native_cert_v1_closed_source_map_valid.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_cnf_source_map_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_cnf_source_map_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_cnf_source_map_valid.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_cnf_source_map_valid.log"

if ! rg -q 'Vampire certificate v1 closed checked 5 steps' \
    "$WORK_DIR/native_cert_v1_cnf_source_map_valid.log"; then
  echo "closed native certificate v1 checker did not accept the CNF source-map fixture" >&2
  exit 1
fi

if ! rg -q 'source_hash "[0-9a-fA-F]{64}".*source_formula_status "closed_formula_checked"' \
    "$WORK_DIR/native_cert_v1_cnf_source_map_valid.mg"; then
  echo "closed native certificate v1 emitter did not mark CNF source bindings as checked" >&2
  exit 1
fi

bin/megalodon -hf "$WORK_DIR/native_cert_v1_cnf_source_map_valid.mg" \
  >"$WORK_DIR/native_cert_v1_cnf_source_map_valid.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.10208.46.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.10208.46.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_vlam_source_metadata_emit.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_vlam_source_metadata_emit.log"

if rg -q 'assume src_axiom_LxLy.*forall X0:set, \(\(In X0\) Lx -> forall X0:set' \
    "$WORK_DIR/native_cert_v1_vlam_source_metadata_emit.mg"; then
  echo "native certificate v1 emitter reused an ill-scoped vLAM source proposition" >&2
  exit 1
fi

if ! rg -q 'assume src_axiom_LxLy.*forall X0:set, .*In X0.*Lx.*forall X1:set, .*In X1.*Ly' \
    "$WORK_DIR/native_cert_v1_vlam_source_metadata_emit.mg"; then
  echo "native certificate v1 emitter did not render the vLAM source proposition with distinct binders" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.10208.46.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.10208.46.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_vlam_fool_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_vlam_fool_closed.log"

if rg -q 'bridge_fool__(u229|u231|u233)' "$WORK_DIR/native_cert_v1_vlam_fool_closed.mg"; then
  echo "closed native certificate v1 vLAM FOOL replay generated a bridge premise" >&2
  exit 1
fi

if rg -q 'claim u231: forall db0:set|claim u231: .*forall vLAM:' \
    "$WORK_DIR/native_cert_v1_vlam_fool_closed.mg"; then
  echo "closed native certificate v1 vLAM FOOL replay quantified an internal encoding name" >&2
  exit 1
fi

if ! rg -q 'claim u231: forall X0:set, .*forall X1:set' \
    "$WORK_DIR/native_cert_v1_vlam_fool_closed.mg"; then
  echo "closed native certificate v1 vLAM FOOL replay reused or lost nested binders" >&2
  exit 1
fi

bin/megalodon -hf "$WORK_DIR/native_cert_v1_vlam_fool_closed.mg" \
  >"$WORK_DIR/native_cert_v1_vlam_fool_closed.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.10783.22.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.10783.22.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.log"

if rg -q 'bridge_substitute__u364_subst0' \
    "$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.mg"; then
  echo "closed native certificate v1 metadata binder replay generated a substitution bridge" >&2
  exit 1
fi

if rg -q 'claim u222: forall X2:set' \
    "$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.mg"; then
  echo "closed native certificate v1 metadata binder replay kept an unused parent binder" >&2
  exit 1
fi

bin/megalodon -hf "$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.mg" \
  >"$WORK_DIR/native_cert_v1_metadata_binder_substitute_closed.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.10644.15.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.10644.15.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_vlam_metadata_sort_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_vlam_metadata_sort_closed.log"

if rg -q 'u203 \(Eps_i' "$WORK_DIR/native_cert_v1_vlam_metadata_sort_closed.mg"; then
  echo "closed native certificate v1 vLAM FOOL replay applied a stale metadata binder" >&2
  exit 1
fi

bin/megalodon -hf "$WORK_DIR/native_cert_v1_vlam_metadata_sort_closed.mg" \
  >"$WORK_DIR/native_cert_v1_vlam_metadata_sort_closed.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/closed_cases/hammer.11428.35.native.sexp \
  -vampirecertv1source tests/vampire_certificate/closed_cases/hammer.11428.35.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_paramod_annotation_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_paramod_annotation_closed.log"

if rg -q 'fun Hparamod_eq:eps_' "$WORK_DIR/native_cert_v1_paramod_annotation_closed.mg"; then
  echo "closed native certificate v1 paramodulation emitted an unparenthesized equality annotation" >&2
  exit 1
fi

bin/megalodon -hf "$WORK_DIR/native_cert_v1_paramod_annotation_closed.mg" \
  >"$WORK_DIR/native_cert_v1_paramod_annotation_closed.check.log"

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

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_negated_conjecture_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_negated_conjecture_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_negated_conjecture_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 5 steps' \
    "$WORK_DIR/native_cert_v1_source_map_negated_conjecture_valid.log"; then
  echo "strict native certificate v1 source-map checker did not accept already-negated conjecture declarations" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_negated_conjecture_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_negated_conjecture_mismatch_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_negated_conjecture_mismatch_bad.out" \
  2>"$WORK_DIR/native_cert_v1_source_map_negated_conjecture_mismatch_bad.err"; then
  echo "strict native certificate v1 source-map checker accepted mismatched already-negated conjecture declarations" >&2
  exit 1
fi

if ! rg -q 'source ng does not match the THF declaration formula' \
    "$WORK_DIR/native_cert_v1_source_map_negated_conjecture_mismatch_bad.err"; then
  echo "strict native certificate v1 negated-conjecture mismatch failure did not explain the semantic mismatch" >&2
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
  -vampirecertv1sourceaudit \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_valid.log"

if ! rg -q 'Vampire certificate v1 source map checked 2 sources' "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_valid.log"; then
  echo "native certificate v1 source-map checker did not accept a reflexive set source" >&2
  exit 1
fi

if ! rg -q 'source obligations audited total=2 .*set_reflexivity_checked=1' "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_valid.log"; then
  echo "native certificate v1 source-obligation audit did not classify a reflexive set source" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1sourcecontext \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_source_context.log"

if ! rg -q 'source context audited total=2 .*generated_checked=1' \
    "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_source_context.log"; then
  echo "native certificate v1 source-context resolver did not prove a generated set-reflexivity source" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1sourcecontext \
  -vampirecertv1corepfcheck \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_source_map_set_reflexivity_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_source_map_set_reflexivity_corepf.log"

if ! rg -q 'Vampire certificate v1 native core proof term checked 4 steps' "$WORK_DIR/native_cert_v1_source_map_set_reflexivity_corepf.log"; then
  echo "native certificate v1 core proof-term checker did not prove a reflexive set source" >&2
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
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_copy_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_copy_valid.log"

if ! rg -q 'Vampire certificate v1 checked 5 steps' "$WORK_DIR/native_cert_v1_formula_copy_valid.log"; then
  echo "native certificate v1 checker did not accept the valid formula-copy fixture" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 source map checked 2 sources' "$WORK_DIR/native_cert_v1_formula_copy_valid.log"; then
  echo "native certificate v1 source-map checker did not accept the negated conjecture formula-copy fixture" >&2
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

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_superposition_kernel_rewritten_target_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_superposition_kernel_rewritten_target_bad.out" \
  2>"$WORK_DIR/native_cert_v1_superposition_kernel_rewritten_target_bad.err"; then
  echo "strict native certificate v1 checker accepted superposition metadata with a wrong rewritten target" >&2
  exit 1
fi

if ! rg -q 'superposition rewritten_target does not match from/to rewrite' \
    "$WORK_DIR/native_cert_v1_superposition_kernel_rewritten_target_bad.err"; then
  echo "strict native certificate v1 superposition metadata failure did not explain the wrong rewritten target" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rewrite_kernel_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_rewrite_kernel_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_rewrite_kernel_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' \
    "$WORK_DIR/native_cert_v1_rewrite_kernel_valid.log"; then
  echo "strict native certificate v1 checker did not accept valid rewrite kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rewrite_kernel_rewritten_target_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_rewrite_kernel_rewritten_target_bad.out" \
  2>"$WORK_DIR/native_cert_v1_rewrite_kernel_rewritten_target_bad.err"; then
  echo "strict native certificate v1 checker accepted rewrite metadata with a wrong rewritten target" >&2
  exit 1
fi

if ! rg -q 'rewrite rewritten_target does not match from/to rewrite' \
    "$WORK_DIR/native_cert_v1_rewrite_kernel_rewritten_target_bad.err"; then
  echo "strict native certificate v1 rewrite metadata failure did not explain the wrong rewritten target" >&2
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
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_bool_typed_eq_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_bool_typed_eq_valid.log"

if ! rg -q 'Vampire certificate v1 checked 9 steps' "$WORK_DIR/native_cert_v1_fool_bool_typed_eq_valid.log"; then
  echo "native certificate v1 checker did not accept the typed-equality FOOL Boolean fixture" >&2
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
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_definition_input_function_closed.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_definition_input_function_closed.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_definition_input_function_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_definition_input_function_closed.log"

if ! rg -q 'Vampire certificate v1 closed checked 4 steps' \
    "$WORK_DIR/native_cert_v1_definition_input_function_closed.log"; then
  echo "closed native certificate v1 checker did not accept a function-definition input" >&2
  exit 1
fi
if rg -q 'assume definition_input__d1' \
    "$WORK_DIR/native_cert_v1_definition_input_function_closed.mg"; then
  echo "function-definition input was emitted as an assumption" >&2
  exit 1
fi
if ! rg -Fq 'Definition b : set := a.' \
    "$WORK_DIR/native_cert_v1_definition_input_function_closed.mg"; then
  echo "function-definition input did not define the introduced symbol" >&2
  exit 1
fi
if ! rg -Fq 'claim definition_input__d1: a = b.' \
    "$WORK_DIR/native_cert_v1_definition_input_function_closed.mg"; then
  echo "function-definition input did not emit a checked definition claim" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_definition_input_function_closed.mg" \
  >"$WORK_DIR/native_cert_v1_definition_input_function_closed.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_definition_input_arrow_function_closed.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_definition_input_arrow_function_closed.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.log"

if ! rg -q 'Vampire certificate v1 closed checked 5 steps' \
    "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.log"; then
  echo "closed native certificate v1 checker did not accept the arrow-valued function definition fixture" >&2
  exit 1
fi
if rg -q 'assume definition_input__d1' \
    "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.mg"; then
  echo "closed native certificate v1 arrow-valued definition input was still emitted as an assumption" >&2
  exit 1
fi
if ! rg -Fq 'Definition g : set->set := f.' \
    "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.mg"; then
  echo "closed native certificate v1 arrow-valued definition input did not emit a Megalodon definition" >&2
  exit 1
fi
if ! rg -Fq 'claim definition_input__d1: vampire_eq_set_to_set f g.' \
    "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.mg"; then
  echo "closed native certificate v1 arrow-valued definition input did not emit a checked claim" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.mg" \
  >"$WORK_DIR/native_cert_v1_definition_input_arrow_function_closed.check.log"

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

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_component_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_avatar_component_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_avatar_component_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_component_closed.out" \
  2>"$WORK_DIR/native_cert_v1_avatar_component_closed.err"
if rg -n '\b(admit|aby)\b|-allowincompleteqed|bridge_|derived:avatar_component' \
    "$WORK_DIR/native_cert_v1_avatar_component_closed.mg"; then
  echo "closed native certificate v1 AVATAR-component emitter left an admission or bridge" >&2
  exit 1
fi
if ! rg -q 'Definition split_1 : prop := p.' \
    "$WORK_DIR/native_cert_v1_avatar_component_closed.mg"; then
  echo "closed native certificate v1 AVATAR-component emitter did not define the split atom" >&2
  exit 1
fi
if ! rg -q 'claim avatar_component__c0:' \
    "$WORK_DIR/native_cert_v1_avatar_component_closed.mg"; then
  echo "closed native certificate v1 AVATAR-component emitter did not emit a replayed claim" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_avatar_component_closed.mg" \
  >"$WORK_DIR/native_cert_v1_avatar_component_closed.check.log"

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

if ! rg -q 'Vampire certificate v1 strict checked 4 steps' "$WORK_DIR/native_cert_v1_avatar_refutation_traced_strict.log"; then
  echo "strict native certificate v1 checker did not accept traced AVATAR refutation" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_refutation_traced_unparented_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_refutation_traced_unparented_bad.log" 2>&1; then
  echo "strict native certificate v1 checker accepted an AVATAR refutation without parent links" >&2
  exit 1
fi

if ! rg -q 'strict certificate v1 requires AVATAR refutation parent links' \
  "$WORK_DIR/native_cert_v1_avatar_refutation_traced_unparented_bad.log"; then
  echo "strict native certificate v1 checker rejected unparented AVATAR refutation with the wrong error" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_avatar_sat_clauses_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_avatar_sat_clauses_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 5 steps' "$WORK_DIR/native_cert_v1_avatar_sat_clauses_valid.log"; then
  echo "strict native certificate v1 checker did not accept AVATAR SAT clause parents" >&2
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
bin/megalodon -hf "$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_equality_symmetry_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_exhaustiveness_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_fool_exhaustiveness_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL exhaustiveness fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_exhaustiveness_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.out"
if ! rg -q 'Vampire certificate v1 closed checked 6 steps' \
    "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.out"; then
  echo "closed native certificate v1 checker did not accept replayed FOOL exhaustiveness" >&2
  exit 1
fi
if ! rg -q '^// vampire_approved_library_known .*prop_ext' \
    "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.mg"; then
  echo "closed native certificate v1 FOOL-exhaustiveness did not mark prop_ext as an approved library known" >&2
  exit 1
fi
if rg -n '\b(admit|aby)\b|-allowincompleteqed|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.mg"; then
  echo "closed native certificate v1 FOOL-exhaustiveness emitted a forbidden premise" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.mg" \
  >"$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.check.log"
check_no_unindexed_axioms "$WORK_DIR/native_cert_v1_fool_exhaustiveness_closed.check.log"

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_distinctness_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_distinctness_valid.log"

if ! rg -q 'Vampire certificate v1 checked 4 steps' "$WORK_DIR/native_cert_v1_fool_distinctness_valid.log"; then
  echo "native certificate v1 checker did not accept the valid FOOL distinctness fixture" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_fool_distinctness_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_fool_distinctness_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_fool_distinctness_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_fool_distinctness_closed.out"
if ! rg -q 'Vampire certificate v1 closed checked 4 steps' \
    "$WORK_DIR/native_cert_v1_fool_distinctness_closed.out"; then
  echo "closed native certificate v1 checker did not accept replayed FOOL distinctness" >&2
  exit 1
fi
if ! rg -q '^// vampire_approved_library_known .*prop_ext' \
    "$WORK_DIR/native_cert_v1_fool_distinctness_closed.mg"; then
  echo "closed native certificate v1 FOOL-distinctness did not mark prop_ext as an approved library known" >&2
  exit 1
fi
if rg -n '\b(admit|aby)\b|-allowincompleteqed|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/native_cert_v1_fool_distinctness_closed.mg"; then
  echo "closed native certificate v1 FOOL-distinctness emitted a forbidden premise" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_fool_distinctness_closed.mg" \
  >"$WORK_DIR/native_cert_v1_fool_distinctness_closed.check.log"
check_no_unindexed_axioms "$WORK_DIR/native_cert_v1_fool_distinctness_closed.check.log"

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
if rg -q 'bridge_normal_form__f2' "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg"; then
  echo "native certificate v1 formula-CNF emitter still exposed the replayed normal-form obligation" >&2
  exit 1
fi
if ! rg -q 'claim f2:' "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg"; then
  echo "native certificate v1 formula-CNF emitter did not emit the replayed normal-form claim" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.mg" \
  >"$WORK_DIR/native_cert_v1_formula_cnf_valid_emit.check.log"

bin/megalodon \
  -vampirecertv1closed \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_formula_cnf_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_formula_cnf_valid.th0.p \
  -vampirecertv1emit "$WORK_DIR/native_cert_v1_formula_cnf_closed.mg" \
  "$dummy" >"$WORK_DIR/native_cert_v1_formula_cnf_closed.out"
if ! rg -q 'Vampire certificate v1 closed checked 9 steps' \
    "$WORK_DIR/native_cert_v1_formula_cnf_closed.out"; then
  echo "closed native certificate v1 checker did not accept replayed formula-CNF" >&2
  exit 1
fi
if ! rg -q '^// vampire_approved_library_known .*prop_ext' \
    "$WORK_DIR/native_cert_v1_formula_cnf_closed.mg"; then
  echo "closed native certificate v1 formula-CNF did not mark prop_ext as an approved library known" >&2
  exit 1
fi
if rg -n '\b(admit|aby)\b|-allowincompleteqed|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/native_cert_v1_formula_cnf_closed.mg"; then
  echo "closed native certificate v1 formula-CNF emitted a forbidden premise" >&2
  exit 1
fi
bin/megalodon -hf "$WORK_DIR/native_cert_v1_formula_cnf_closed.mg" \
  >"$WORK_DIR/native_cert_v1_formula_cnf_closed.check.log"
check_no_unindexed_axioms "$WORK_DIR/native_cert_v1_formula_cnf_closed.check.log"

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

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_primitive_contract_missing_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_rectify_primitive_contract_missing_bad.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_rectify_primitive_contract_missing_bad.out" \
  2>"$WORK_DIR/native_cert_v1_rectify_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 checker accepted rectify-formula metadata without a primitive-expansion contract" >&2
  exit 1
fi

if ! rg -q 'requires primitive_expansion=prefix for kernel rule rectify_formula' \
    "$WORK_DIR/native_cert_v1_rectify_primitive_contract_missing_bad.err"; then
  echo "strict native certificate v1 rectify primitive-contract failure did not explain the missing contract" >&2
  exit 1
fi

bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_rectify_scoped_equality_symmetry_valid.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_valid.log"

if ! rg -q 'Vampire certificate v1 checked 6 steps' "$WORK_DIR/native_cert_v1_rectify_scoped_equality_symmetry_valid.log"; then
  echo "native certificate v1 checker did not accept scoped equality-symmetry rectification" >&2
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

bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_skolemize_valid.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_kernel_skolemize_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_kernel_skolemize_valid.log"

if ! rg -q 'Vampire certificate v1 strict checked 6 steps' "$WORK_DIR/native_cert_v1_kernel_skolemize_valid.log"; then
  echo "strict native certificate v1 checker did not accept Skolem kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1strict \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_kernel_skolemize_introduced_symbol_bad.sexp \
  -vampirecertv1source tests/vampire_certificate/native_cert_v1_kernel_skolemize_valid.th0.p \
  "$dummy" >"$WORK_DIR/native_cert_v1_kernel_skolemize_introduced_symbol_bad.out" \
  2>"$WORK_DIR/native_cert_v1_kernel_skolemize_introduced_symbol_bad.err"; then
  echo "strict native certificate v1 checker accepted mismatched Skolem kernel metadata" >&2
  exit 1
fi

if ! rg -q 'u1: strict certificate v1 kernel_v1 skolemize introduced symbol bad_sk is not present in skolem_formula metadata' \
    "$WORK_DIR/native_cert_v1_kernel_skolemize_introduced_symbol_bad.err"; then
  echo "strict native certificate v1 checker did not explain mismatched Skolem kernel metadata" >&2
  exit 1
fi

if bin/megalodon \
  -vampirecertv1 tests/vampire_certificate/native_cert_v1_skolem_introduced_symbol_bad.sexp \
  "$dummy" >"$WORK_DIR/native_cert_v1_skolem_introduced_symbol_bad.out" \
  2>"$WORK_DIR/native_cert_v1_skolem_introduced_symbol_bad.err"; then
  echo "native certificate v1 checker accepted mismatched Skolem introduced-symbol metadata" >&2
  exit 1
fi

if ! rg -q 'skolem introduced symbol bad_sk does not head substitution for X0' \
    "$WORK_DIR/native_cert_v1_skolem_introduced_symbol_bad.err"; then
  echo "native certificate v1 checker did not explain mismatched Skolem introduced-symbol metadata" >&2
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
