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
  echo "VAMPIRE_BIN must point to a Vampire binary with native S-expression certificate output" >&2
  exit 1
fi

run_outline_case() {
  local label="$1"
  local problem="$2"
  local expected_axiom_name="${3:-}"
  local expected_negated_conjecture_name="${4:-}"
  local expected_native_rule="${5:-}"
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

  if rg -q 'source vampire_' "$native_sexpr"; then
    echo "$label: native certificate contains a Vampire-derived source assumption" >&2
    exit 1
  fi
  if [[ -n "$expected_native_rule" ]] \
    && ! rg -q "\\($expected_native_rule " "$native_sexpr"; then
    echo "$label: native certificate did not include expected $expected_native_rule step" >&2
    exit 1
  fi
  if [[ -n "$expected_axiom_name" ]] \
    && ! rg -q "\\(source axiom \"$expected_axiom_name\"\\)" "$native_sexpr"; then
    echo "$label: native certificate did not preserve source axiom name $expected_axiom_name" >&2
    exit 1
  fi
  if [[ -n "$expected_negated_conjecture_name" ]] \
    && ! rg -q "\\(source negated_conjecture \"$expected_negated_conjecture_name\"\\)" "$native_sexpr"; then
    echo "$label: native certificate did not preserve negated conjecture name $expected_negated_conjecture_name" >&2
    exit 1
  fi
  if [[ "$label" == *"_fof_source_names" ]]; then
    if ! rg -q '\(formula_input "u[0-9]+" \(source axiom "lemma_formula"\)' "$native_sexpr"; then
      echo "$label: native certificate did not include checked source formula input" >&2
      exit 1
    fi
    if ! rg -q '\(cnf_literal "u[0-9]+" \(parent "u[0-9]+"\)' "$native_sexpr"; then
      echo "$label: native certificate did not include checked literal-CNF preprocessing" >&2
      exit 1
    fi
  fi
}

resolution_problem="$TMPDIR/vampire_outline_smoke_resolution.p"
equality_resolution_problem="$TMPDIR/vampire_outline_smoke_equality_resolution.p"
factor_problem="$TMPDIR/vampire_outline_smoke_factor.p"
substituted_resolution_problem="$TMPDIR/vampire_outline_smoke_substituted_resolution.p"
superposition_problem="$TMPDIR/vampire_outline_smoke_superposition.p"
source_names_problem="$TMPDIR/vampire_outline_smoke_source_names.p"
fof_source_names_problem="$TMPDIR/vampire_outline_smoke_fof_source_names.p"

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

cat >"$source_names_problem" <<'PROBLEM'
cnf(lemma_source, axiom, p(a)).
cnf(goal_source, negated_conjecture, ~p(a)).
PROBLEM

cat >"$fof_source_names_problem" <<'PROBLEM'
fof(lemma_formula, axiom, p(a)).
fof(goal_formula, negated_conjecture, ~p(a)).
PROBLEM

run_outline_case vampire_outline_smoke_resolution "$resolution_problem" "" "" resolve
run_outline_case vampire_outline_smoke_equality_resolution "$equality_resolution_problem" "" "" equality_resolution
run_outline_case vampire_outline_smoke_factor "$factor_problem" "" "" factor
run_outline_case vampire_outline_smoke_substituted_resolution "$substituted_resolution_problem" "" "" substitute
run_outline_case vampire_outline_smoke_superposition "$superposition_problem" "" "" paramodulate
run_outline_case vampire_outline_smoke_source_names "$source_names_problem" lemma_source goal_source resolve
run_outline_case vampire_outline_smoke_fof_source_names "$fof_source_names_problem" lemma_formula goal_formula cnf_literal

echo "vampire native certificate live smoke test passed"
