#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
MEGALODON_VAMPIRE_TIMEOUT=${MEGALODON_VAMPIRE_TIMEOUT:-10}
WALL_SECONDS=${WALL_SECONDS:-120}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/live_certified_vampire_no_incomplete.XXXXXX")"}

mkdir -p "$WORK_DIR/out"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_live_certified_vampire_no_incomplete"

if [[ ! -x "$MEGALODON" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

supports_megalodon_proof() {
  local candidate=$1
  [[ -x "$candidate" ]] || return 1
  local options
  options=$("$candidate" --show_options on 2>/dev/null) || return 1
  rg -q 'megalodon produces a Megalodon proof-reconstruction outline|^[[:space:]]+megalodon[[:space:]]*$' <<<"$options"
}

if [[ -z "${VAMPIRE:-}" ]]; then
  for candidate in \
    /project/tmp/vampire-cmake-megalodon5/vampire \
    /project/tmp/vampire-megalodon5-build/vampire \
    /project/tmp/vampire-build-megalodon5/vampire \
    "$ROOT/../vampire-leancheck/vampire_rel_vampire/vampire" \
    "$ROOT/../vampire-leancheck/vampire_rel_detached_10761" \
    "$ROOT/../vampire-leancheck/vampire_rel_vampire"/megalodon*_*
  do
    if supports_megalodon_proof "$candidate"; then
      VAMPIRE=$candidate
      break
    fi
  done
fi

if [[ -z "${VAMPIRE:-}" || ! -x "$VAMPIRE" ]]; then
  echo "Set VAMPIRE=/path/to/vampire with --proof megalodon support" >&2
  exit 2
fi
if ! supports_megalodon_proof "$VAMPIRE"; then
  echo "VAMPIRE=$VAMPIRE does not advertise --proof megalodon support" >&2
  exit 2
fi

source_file="$WORK_DIR/live_certified_vampire_no_incomplete.mg"
cat >"$source_file" <<'EOF_MG'
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Prefix ~ 700 := not.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 785 left := or.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 right := and.
Variable p:prop.
Theorem live_certified_vampire_no_incomplete_id:p -> p.
assume Hp:p.
vampire Hp.
Qed.
Theorem live_certified_vampire_no_incomplete_falseE:False -> forall q:prop, q.
vampire.
Qed.
Theorem live_certified_vampire_no_incomplete_andEL:forall A B:prop, A /\ B -> A.
vampire.
Qed.
Theorem live_certified_vampire_no_incomplete_andER:forall A B:prop, A /\ B -> B.
vampire.
Qed.
EOF_MG

if awk '$0 !~ /^\/\// && ($0 ~ /(^|[^[:alnum:]_])(admit|aby)([^[:alnum:]_]|$)/ || $0 ~ /-allowincompleteqed/) {print FNR ":" $0}' \
    "$source_file" |
    rg . >&2; then
  echo "live certified vampire no-incomplete fixture contains an admission-shaped token" >&2
  exit 1
fi

set +e
timeout "$WALL_SECONDS" "$MEGALODON" \
  -v 4 \
  -vampireaby "$VAMPIRE" \
  -vampireabytimeout "$MEGALODON_VAMPIRE_TIMEOUT" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabynativestrict \
  -vampireabyoutdir "$WORK_DIR/out" \
  "$source_file" \
  >"$WORK_DIR/run.out" \
  2>"$WORK_DIR/run.err"
rc=$?
set -e
if (( rc != 0 )); then
  echo "live certified vampire no-incomplete run failed with exit $rc" >&2
  tail -80 "$WORK_DIR/run.out" >&2 || true
  tail -80 "$WORK_DIR/run.err" >&2 || true
  exit "$rc"
fi

expected_reconstructed=4
actual_reconstructed=$(
  rg -c 'Vampire proof command reconstructed proof term at line ' "$WORK_DIR/run.out" || true
)
if [[ "$actual_reconstructed" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed reconstructed vampire proof commands, got $actual_reconstructed" >&2
  exit 1
fi
if ! rg -q 'Everything looks good' "$WORK_DIR/run.out"; then
  echo "live certified vampire no-incomplete fixture did not close" >&2
  exit 1
fi
if rg -q '\b(admit|aby)\b|-allowincompleteqed|bridge_|^assume (definition_input__|avatar_|theory_|predicate_definition__|vampire_eq_prop_ext\b)' \
    "$WORK_DIR/run.out" "$WORK_DIR/run.err"; then
  echo "live certified vampire no-incomplete log contains forbidden proof artifact" >&2
  exit 1
fi

problem_count=$(find "$WORK_DIR/out" -name 'vampire.*.thf.p' | wc -l | tr -d ' ')
proof_count=$(find "$WORK_DIR/out" -name 'vampire.*.megalodon.out' | wc -l | tr -d ' ')
if [[ "$problem_count" != "$expected_reconstructed" || "$proof_count" != "$expected_reconstructed" ]]; then
  echo "expected $expected_reconstructed THF/proof artifacts, got THF=$problem_count proof=$proof_count" >&2
  exit 1
fi
while IFS= read -r problem; do
  if ! rg -q '^% megalodon_origin .* \(kind "vampire"\)' "$problem"; then
    echo "problem $problem did not export vampire origin kind" >&2
    exit 1
  fi
done < <(find "$WORK_DIR/out" -name 'vampire.*.thf.p' | sort)

echo "LIVE_CERTIFIED_VAMPIRE_NO_INCOMPLETE_PASS $expected_reconstructed"
echo "live certified vampire no-incomplete artifacts: $WORK_DIR"
echo "live certified vampire no-incomplete latest link: $TMPDIR/latest_live_certified_vampire_no_incomplete"
echo "live certified vampire no-incomplete vampire: $VAMPIRE"
