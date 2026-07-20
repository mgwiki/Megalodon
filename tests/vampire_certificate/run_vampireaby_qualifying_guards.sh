#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/vampireaby_qualifying_guards.XXXXXX")"}
mkdir -p "$WORK_DIR"

cd "$ROOT"

if [ ! -x bin/megalodon ]; then
  TMPDIR="$TMPDIR" ./makeopt
fi

if MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1 \
    bin/megalodon \
      -vampireabyqualifying \
      examples/egal/PfgENov2021Preambles.mg \
      >"$WORK_DIR/transitional_known_allowed.out" \
      2>"$WORK_DIR/transitional_known_allowed.err"; then
  echo "qualifying mode accepted transitional certificate Known escape hatch" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying cannot be combined with MEGALODON_CERT_ALLOW_TRANSITIONAL_PREPROCESS_KNOWN=1' \
    "$WORK_DIR/transitional_known_allowed.err"; then
  echo "qualifying mode failed for the wrong reason when transitional Known escape hatch was set" >&2
  cat "$WORK_DIR/transitional_known_allowed.err" >&2
  exit 1
fi

if MEGALODON_CERT_KEEP_QED_DELTA=1 \
    bin/megalodon \
      -vampireabyqualifying \
      examples/egal/PfgENov2021Preambles.mg \
      >"$WORK_DIR/keep_qed_delta_allowed.out" \
      2>"$WORK_DIR/keep_qed_delta_allowed.err"; then
  echo "qualifying mode accepted certificate-local Qed delta retention" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying cannot be combined with MEGALODON_CERT_KEEP_QED_DELTA=1' \
    "$WORK_DIR/keep_qed_delta_allowed.err"; then
  echo "qualifying mode failed for the wrong reason when Qed delta retention was requested" >&2
  cat "$WORK_DIR/keep_qed_delta_allowed.err" >&2
  exit 1
fi

if bin/megalodon \
    -allowincompleteqed \
    -vampireabyqualifying \
    examples/egal/PfgENov2021Preambles.mg \
    >"$WORK_DIR/allow_incomplete_allowed.out" \
    2>"$WORK_DIR/allow_incomplete_allowed.err"; then
  echo "qualifying mode accepted -allowincompleteqed" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying cannot be combined with -allowincompleteqed' \
    "$WORK_DIR/allow_incomplete_allowed.err"; then
  echo "qualifying mode failed for the wrong reason with -allowincompleteqed" >&2
  cat "$WORK_DIR/allow_incomplete_allowed.err" >&2
  exit 1
fi

if bin/megalodon \
    -vampireabyqualifying \
    -vampireabytarget 1 0 \
    -vampireabytargetstop \
    examples/egal/PfgENov2021Preambles.mg \
    >"$WORK_DIR/target_stop_allowed.out" \
    2>"$WORK_DIR/target_stop_allowed.err"; then
  echo "qualifying mode accepted -vampireabytargetstop" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying cannot be combined with -vampireabytargetstop' \
    "$WORK_DIR/target_stop_allowed.err"; then
  echo "qualifying mode failed for the wrong reason with -vampireabytargetstop" >&2
  cat "$WORK_DIR/target_stop_allowed.err" >&2
  exit 1
fi

if bin/megalodon \
    -vampireabyqualifying \
    -vampireabyproof tptp \
    examples/egal/PfgENov2021Preambles.mg \
    >"$WORK_DIR/proof_mode_override_allowed.out" \
    2>"$WORK_DIR/proof_mode_override_allowed.err"; then
  echo "qualifying mode accepted a non-Megalodon Vampire proof mode" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying requires -vampireabyproof megalodon' \
    "$WORK_DIR/proof_mode_override_allowed.err"; then
  echo "qualifying mode failed for the wrong reason with a proof-mode override" >&2
  cat "$WORK_DIR/proof_mode_override_allowed.err" >&2
  exit 1
fi

if bin/megalodon \
    -vampireabyqualifying \
    -vampireabytimeout 11 \
    examples/egal/PfgENov2021Preambles.mg \
    >"$WORK_DIR/timeout_override_allowed.out" \
    2>"$WORK_DIR/timeout_override_allowed.err"; then
  echo "qualifying mode accepted a Vampire timeout above 10 seconds" >&2
  exit 1
fi

if ! rg -q -- '-vampireabyqualifying requires -vampireabytimeout <= 10' \
    "$WORK_DIR/timeout_override_allowed.err"; then
  echo "qualifying mode failed for the wrong reason with a timeout override" >&2
  cat "$WORK_DIR/timeout_override_allowed.err" >&2
  exit 1
fi

strict_native_dir="$WORK_DIR/strict_native_required"
mkdir -p "$strict_native_dir"
cat >"$strict_native_dir/fake_vampire_no_certificate" <<'EOF_FAKE_VAMPIRE_NO_CERTIFICATE'
#!/usr/bin/env bash
cat <<'CERT'
% SZS status Theorem
% SZS output start Proof
% no Megalodon native certificate block
% SZS output end Proof
CERT
EOF_FAKE_VAMPIRE_NO_CERTIFICATE
chmod +x "$strict_native_dir/fake_vampire_no_certificate"

cat >"$strict_native_dir/strict_native_required.mg" <<'EOF_STRICT_NATIVE_REQUIRED_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Variable p:prop.
Theorem strict_native_required:p -> p.
assume Hp:p.
vampire Hp.
Qed.
EOF_STRICT_NATIVE_REQUIRED_MG

if bin/megalodon \
    -vampireaby "$strict_native_dir/fake_vampire_no_certificate" \
    -vampireabyqualifying \
    -vampireabyoutdir "$strict_native_dir/out" \
    "$strict_native_dir/strict_native_required.mg" \
    >"$WORK_DIR/strict_native_required.out" \
    2>"$WORK_DIR/strict_native_required.err"; then
  echo "qualifying mode accepted a Vampire proof without a native certificate block" >&2
  exit 1
fi

if ! rg -q 'has no native certificate block|did not reconstruct current vampire goal' \
    "$WORK_DIR/strict_native_required.out" \
    "$WORK_DIR/strict_native_required.err"; then
  echo "qualifying mode failure did not explain the missing native certificate" >&2
  cat "$WORK_DIR/strict_native_required.out" >&2
  cat "$WORK_DIR/strict_native_required.err" >&2
  exit 1
fi

echo "vampireaby qualifying guard checks passed"
