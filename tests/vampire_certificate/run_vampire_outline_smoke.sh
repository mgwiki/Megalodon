#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"
native_dummy="$TMPDIR/vampire_outline_native_dummy.mg"
: >"$native_dummy"

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
  local native_sexpr="$TMPDIR/${label}.sexp"

  "$VAMPIRE_BIN" \
    --input_syntax tptp \
    --mode casc \
    --avatar off \
    -t 10 \
    --proof megalodon \
    --output_axiom_names on \
    "$problem" >"$outline"

  awk '/megalodon_certificate_native_sexpr_start\./{flag=1;next}/megalodon_certificate_native_sexpr_end\./{flag=0}flag' \
    "$outline" >"$native_sexpr"
  if [[ ! -s "$native_sexpr" ]]; then
    echo "$label: Vampire did not emit a native S-expression certificate block" >&2
    exit 1
  fi
  ./bin/megalodon -vampirecertv1 "$native_sexpr" "$native_dummy" >"$TMPDIR/${label}.native.log"

  if rg -q '"rule":"paramodulate_clause_all"' "$outline"; then
    echo "outline contains an unlowered clause-wide paramodulation macro" >&2
    exit 1
  fi
  if rg -q 'megalodon_step_extra\([0-9]+,"cnf"' "$outline"; then
    if ! rg -q 'megalodon_step_extra\([0-9]+,"cnf".*"clause_parent_unit=' "$outline" \
      || ! rg -q 'megalodon_step_extra\([0-9]+,"cnf".*"clause_index=' "$outline" \
      || ! rg -q 'megalodon_step_extra\([0-9]+,"cnf".*"clause_count=' "$outline"; then
      echo "outline CNF extra did not contain Vampire-side clause index metadata" >&2
      exit 1
    fi
  fi

  if [[ "$label" == *"_thf" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"definition_input"' "$outline"; then
      echo "THF outline did not contain Vampire-side definition_input certificate step" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"paramodulate"' "$outline" \
      && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"paramodulate"' "$outline"; then
      echo "THF outline did not contain Vampire-side paramodulate certificate step" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"paramodulate".*"clause":' "$outline" \
      && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"paramodulate".*"clause":' "$outline"; then
      echo "THF outline did not contain Vampire-side paramodulate certificate conclusion detail" >&2
      exit 1
    fi
    python3 - "$outline" <<'PY'
import re
import sys
from pathlib import Path

text = Path(sys.argv[1]).read_text(errors="replace").splitlines()
cert_steps = {}
cert_step = {}
replay_kinds = {}
for line in text:
    m = re.match(r"megalodon_certificate_steps\((\d+),(.+)\)\.$", line)
    if m:
        cert_steps[int(m.group(1))] = m.group(2)
        continue
    m = re.match(r"megalodon_certificate_step\((\d+),(.+)\)\.$", line)
    if m:
        cert_step[int(m.group(1))] = m.group(2)
        continue
    m = re.match(r'megalodon_step_replay_kind\((\d+),"([^"]+)"\)\.$', line)
    if m:
        replay_kinds[int(m.group(1))] = m.group(2)

subsumption_steps = [
    step for step, kind in replay_kinds.items()
    if kind == "subsumption_resolution"
]
if not subsumption_steps:
    raise SystemExit("THF outline did not contain a subsumption_resolution replay step")
for step in subsumption_steps:
    if '"rule":"subsumption_resolution"' in cert_step.get(step, ""):
        raise SystemExit("THF subsumption_resolution was emitted as a macro certificate step")
    if '"rule":"resolve"' not in cert_steps.get(step, ""):
        raise SystemExit("THF subsumption_resolution was not expanded to primitive resolve certificate steps")
PY
  fi
  if [[ "$label" != *"_substituted_resolution" ]] \
    && [[ "$label" != *"_equality_resolution" ]] \
    && [[ "$label" != *"_bound_lambda_scope" ]] \
    && ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"resolve"' "$outline" \
    && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"resolve"' "$outline"; then
    echo "outline did not contain Vampire-side resolve certificate step" >&2
    exit 1
  fi
  if [[ "$label" == *"_equality_resolution" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"equality_resolution"' "$outline" \
      && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"equality_resolution"' "$outline"; then
      echo "outline did not contain Vampire-side equality_resolution certificate step" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_factor" ]]; then
    if ! rg -q 'megalodon_certificate_step\([0-9]+,\{"rule":"factor"' "$outline" \
      && ! rg -q 'megalodon_certificate_steps\([0-9]+,\[.*"rule":"factor"' "$outline"; then
      echo "outline did not contain Vampire-side factor certificate step" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_substituted_resolution" ]]; then
    if ! rg -q 'megalodon_certificate_steps\([0-9]+,\[\{"id":"u[0-9]+_subst[0-9]+","rule":"substitute"' "$outline"; then
      echo "outline did not contain Vampire-side substitute-plus-resolution certificate steps" >&2
      exit 1
    fi
    if rg -q 'source_proposition=.*\bp f a\b|target_proposition=.*\bp f a\b' "$outline"; then
      echo "outline contains ambiguous unparenthesized predicate application p f a" >&2
      exit 1
    fi
    if ! rg -q 'p \(f a\)' "$outline"; then
      echo "outline did not parenthesize compound predicate argument p (f a)" >&2
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
    if ! rg -q '"rewritten_target":' "$outline"; then
      echo "outline did not contain Vampire-side rewritten_target detail" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_superposition_substituted" ]]; then
    if ! rg -q 'megalodon_certificate_steps\([0-9]+,\[\{"id":"u[0-9]+_subst[0-9]+","rule":"substitute".*"rule":"paramodulate"' "$outline"; then
      echo "outline did not contain Vampire-side substitute-plus-paramodulate superposition expansion" >&2
      exit 1
    fi
  fi
  if [[ "$label" == *"_bound_lambda_scope" ]]; then
    if ! rg -q '"rewrite_scope":\{"kind":"bound_lambda_var"' "$outline"; then
      echo "outline did not contain Vampire-side bound-lambda rewrite_scope detail" >&2
      exit 1
    fi
    if ! rg -q 'megalodon_step_extra\([0-9]+,"normal_form_clause"' "$outline"; then
      echo "outline did not contain Vampire-side normal_form_clause detail" >&2
      exit 1
    fi
  fi

  if rg -q 'source vampire_' "$native_sexpr"; then
    echo "$label: native certificate contains a Vampire-derived source assumption" >&2
    exit 1
  fi
}

resolution_problem="$TMPDIR/vampire_outline_smoke_resolution.p"
equality_resolution_problem="$TMPDIR/vampire_outline_smoke_equality_resolution.p"
factor_problem="$TMPDIR/vampire_outline_smoke_factor.p"
substituted_resolution_problem="$TMPDIR/vampire_outline_smoke_substituted_resolution.p"
superposition_problem="$TMPDIR/vampire_outline_smoke_superposition.p"

cat >"$resolution_problem" <<'PROBLEM'
cnf(a1, axiom, p(a)).
cnf(a2, axiom, ~p(a)).
PROBLEM

cat >"$equality_resolution_problem" <<'PROBLEM'
cnf(a1, axiom, a != a).
PROBLEM

cat >"$factor_problem" <<'PROBLEM'
cnf(a1, axiom, p | p).
cnf(a2, axiom, ~p).
PROBLEM

cat >"$substituted_resolution_problem" <<'PROBLEM'
cnf(a1, axiom, p(X)).
cnf(a2, axiom, ~p(f(a))).
PROBLEM

cat >"$superposition_problem" <<'PROBLEM'
cnf(eq, axiom, f(a)=b).
cnf(pa, axiom, p(f(a))).
cnf(nb, axiom, ~p(b)).
PROBLEM

run_outline_case vampire_outline_smoke_resolution "$resolution_problem"
run_outline_case vampire_outline_smoke_equality_resolution "$equality_resolution_problem"
run_outline_case vampire_outline_smoke_factor "$factor_problem"
run_outline_case vampire_outline_smoke_substituted_resolution "$substituted_resolution_problem"
run_outline_case vampire_outline_smoke_superposition "$superposition_problem"

echo "vampire outline smoke test passed"
