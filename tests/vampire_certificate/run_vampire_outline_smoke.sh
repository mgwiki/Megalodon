#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

if [[ -z "${VAMPIRE_BIN:-}" ]]; then
  VAMPIRE_BIN="$(find /project/vampire-leancheck/vampire_rel_vampire -maxdepth 1 -type f -perm -111 -name 'megalodon1_*' 2>/dev/null | sort | tail -n 1 || true)"
fi

if [[ -z "${VAMPIRE_BIN:-}" ]]; then
  VAMPIRE_BIN="$(find /project/vampire-leancheck/vampire_rel_vampire -maxdepth 1 -type f -perm -111 2>/dev/null | sort | tail -n 1 || true)"
fi

if [[ -z "$VAMPIRE_BIN" || ! -x "$VAMPIRE_BIN" ]]; then
  echo "VAMPIRE_BIN must point to a Vampire binary with megalodon_certificate_clause output" >&2
  exit 1
fi

run_outline_case() {
  local label="$1"
  local problem="$2"
  local outline="$TMPDIR/${label}.out"
  local certificate="$TMPDIR/${label}.json"
  local megalodon="$TMPDIR/${label}.mg"

  "$VAMPIRE_BIN" \
    --input_syntax tptp \
    --mode casc \
    -t 10 \
    --proof megalodon \
    --output_axiom_names on \
    "$problem" >"$outline"

  if [[ "$label" == *"_thf" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"definition_input"' "$outline"; then
      echo "THF outline did not contain Vampire-side definition_input certificate step" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"paramodulate"' "$outline"; then
      echo "THF outline did not contain Vampire-side paramodulate certificate step" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_certificate_steps\([0-9]+,\[\{"id":"u[0-9]+_paramodulate","rule":"paramodulate"' "$outline"; then
      echo "THF outline did not contain Vampire-side paramodulate-plus-symmetry certificate steps" >&2
      exit 1
    fi
  fi
  if [[ "$label" != *"_substituted_resolution" ]] \
    && ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"resolve"' "$outline" \
    && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"resolve"' "$outline"; then
    echo "outline did not contain Vampire-side resolve certificate step" >&2
    exit 1
  fi
  if [[ "$label" == *"_equality_resolution" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"equality_resolution"' "$outline"; then
      echo "outline did not contain Vampire-side equality_resolution certificate step" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_factor" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"factor"' "$outline"; then
      echo "outline did not contain Vampire-side factor certificate step" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_substituted_resolution" ]]; then
    if ! rg -q 'megalodon_certificate_steps\([0-9]+,\[\{"id":"u[0-9]+_subst[0-9]+","rule":"substitute"' "$outline"; then
      echo "outline did not contain Vampire-side substitute-plus-resolution certificate steps" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_superposition" ]]; then
    if ! rg -q 'megalodon_step\([0-9]+,"superposition"' "$outline"; then
      echo "outline did not contain a Vampire superposition inference" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"paramodulate"' "$outline"; then
      echo "outline did not contain Vampire-side superposition certificate expansion" >&2
      exit 1
    fi
  fi

  python3 scripts/vampire_certificate.py \
    "$outline" \
    --from-vampire-outline \
    --summary \
    --write-certificate "$certificate" \
    --emit-megalodon "$megalodon" \
    --theorem-name "${label}_certificate_smoke"

  python3 - "$outline" <<'PY'
import importlib.util
import sys
from pathlib import Path

outline = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location(
    "vampire_reconstruct_megalodon",
    Path("scripts/vampire_reconstruct_megalodon.py"),
)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
text = outline.read_text(errors="replace")
steps = module.megalodon_replay_steps(text, outline)
certified = {
    name: module.megalodon_replay_step_certificate_rules(step)
    for name, step in steps.items()
    if step.certificate_steps
}
if "megalodon_certificate_step" in text and not certified:
    raise SystemExit("raw replay parser dropped Vampire certificate steps")
if '"rule":"paramodulate"' in text and not any("paramodulate" in rules for rules in certified.values()):
    raise SystemExit("raw replay parser dropped Vampire paramodulate certificate steps")
PY

  if rg -n '\badmit\b|\baby\b|-allowincompleteqed' "$megalodon"; then
    echo "generated Megalodon proof contains an admission marker" >&2
    exit 1
  fi

  ./bin/megalodon "$megalodon" >"$TMPDIR/${label}.check.log"
}

fof_problem="$TMPDIR/vampire_outline_smoke_fof.p"
thf_problem="$TMPDIR/vampire_outline_smoke_thf.p"
equality_resolution_problem="$TMPDIR/vampire_outline_smoke_equality_resolution.p"
factor_problem="$TMPDIR/vampire_outline_smoke_factor.p"
substituted_resolution_problem="$TMPDIR/vampire_outline_smoke_substituted_resolution.p"
superposition_problem="$TMPDIR/vampire_outline_smoke_superposition.p"

cat >"$fof_problem" <<'PROBLEM'
fof(a1, axiom, p(a)).
fof(c, conjecture, p(a)).
PROBLEM

cat >"$thf_problem" <<'PROBLEM'
thf(a_type,type,(a: $i)).
thf(p_type,type,(p: $i > $o)).
thf(a1,axiom,(p @ a)).
thf(c,conjecture,(p @ a)).
PROBLEM

cat >"$equality_resolution_problem" <<'PROBLEM'
fof(a1,axiom,((a != a) | p)).
fof(c,conjecture,p).
PROBLEM

cat >"$factor_problem" <<'PROBLEM'
fof(a1,axiom,(p | p)).
fof(c,conjecture,p).
PROBLEM

cat >"$substituted_resolution_problem" <<'PROBLEM'
fof(a1,axiom,![X] : p(X)).
fof(a2,axiom,~p(f(a))).
fof(c,conjecture,$false).
PROBLEM

cat >"$superposition_problem" <<'PROBLEM'
fof(eq,axiom,f(a)=b).
fof(pa,axiom,p(f(a))).
fof(c,conjecture,p(b)).
PROBLEM

run_outline_case vampire_outline_smoke_fof "$fof_problem"
run_outline_case vampire_outline_smoke_thf "$thf_problem"
run_outline_case vampire_outline_smoke_equality_resolution "$equality_resolution_problem"
run_outline_case vampire_outline_smoke_factor "$factor_problem"
run_outline_case vampire_outline_smoke_substituted_resolution "$substituted_resolution_problem"
run_outline_case vampire_outline_smoke_superposition "$superposition_problem"

echo "vampire outline smoke test passed"
