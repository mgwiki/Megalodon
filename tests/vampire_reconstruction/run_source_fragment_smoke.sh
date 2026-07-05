#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

if [ ! -x bin/megalodon ]; then
  ./makeopt
fi

VAMPIRE="${VAMPIRE:-vampire}"
TMPDIR="${TMPDIR:-/project/tmp}"
mkdir -p "$TMPDIR"

work_dir="${MEGALODON_VAMPIRE_SOURCE_SMOKE_DIR:-$TMPDIR/megalodon_vampire_source_fragment_smoke}"
rm -rf "$work_dir"
mkdir -p "$work_dir"

run_case() {
  local name="$1"
  local problem="$work_dir/$name.th0.p"
  local output="$work_dir/$name.out"
  local source="$work_dir/$name.mg"

  "$VAMPIRE" \
    --input_syntax tptp \
    --mode portfolio \
    --schedule casc \
    -t "${MEGALODON_VAMPIRE_TIMEOUT:-10}" \
    --proof megalodon \
    --proof_extra lean \
    --skolemization syntactic \
    --shuffle_input off \
    "$problem" > "$output" 2>&1

  awk '
    /^megalodon_source_candidate_start\.$/ { inside = 1; next }
    /^megalodon_source_candidate_end\.$/ { inside = 0; next }
    inside {
      line = $0
      sub(/^megalodon_source_line[(]"/, "", line)
      sub(/"[)]\.$/, "", line)
      print line
    }
  ' "$output" > "$source"
  if [ ! -s "$source" ]; then
    sed -n '1,120p' "$output" >&2
    echo "missing Megalodon source candidate for $name" >&2
    return 1
  fi
  bin/megalodon "$source"
}

assert_contains() {
  local file="$1"
  local pattern="$2"
  if ! grep -Fq "$pattern" "$file"; then
    echo "expected $file to contain: $pattern" >&2
    return 1
  fi
}

cat > "$work_dir/conjunction_intro.th0.p" <<'EOF'
thf(p,type,(p : $o)).
thf(q,type,(q : $o)).
thf(hp,axiom,p).
thf(hq,axiom,q).
thf(conj,conjecture,(p & q)).
EOF

cat > "$work_dir/conjunction_projection.th0.p" <<'EOF'
thf(p,type,(p : $o)).
thf(q,type,(q : $o)).
thf(hpq,axiom,(p & q)).
thf(conj,conjecture,p).
EOF

cat > "$work_dir/equality_rewrite.th0.p" <<'EOF'
thf(a,type,(a : $i)).
thf(b,type,(b : $i)).
thf(p,type,(p : $i > $o)).
thf(hp,axiom,(p @ a)).
thf(heq,axiom,(a = b)).
thf(goal,conjecture,(p @ b)).
EOF

cat > "$work_dir/equality_normalization.th0.p" <<'EOF'
thf(e,type,(e : $i)).
thf(n,type,(n : $i)).
thf(m,type,(m : $i)).
thf(add,type,(add : $i > $i > $i)).
thf(add_empty,axiom,(! [X:$i] : ((add @ X @ e) = X))).
thf(goal,conjecture,((add @ (add @ n @ m) @ e) = (add @ n @ (add @ m @ e)))).
EOF

cat > "$work_dir/predicate_equality_rewrite.th0.p" <<'EOF'
thf(e,type,(e : $i)).
thf(n,type,(n : $i)).
thf(mul,type,(mul : $i > $i > $i)).
thf(mul_empty,axiom,(! [X:$i] : (e = (mul @ X @ e)))).
thf(goal,conjecture,(! [P:$i > $o] : ((P @ e) => (P @ (mul @ n @ e))))).
EOF

cat > "$work_dir/reverse_equality_normalization.th0.p" <<'EOF'
thf(e,type,(e : $i)).
thf(n,type,(n : $i)).
thf(m,type,(m : $i)).
thf(mul,type,(mul : $i > $i > $i)).
thf(mul_empty,axiom,(! [X:$i] : (e = (mul @ X @ e)))).
thf(goal,conjecture,((mul @ n @ e) = (mul @ m @ e))).
EOF

cat > "$work_dir/binary_predicate_simplification.th0.p" <<'EOF'
thf(e,type,(e : $i)).
thf(a,type,(a : $i)).
thf(b,type,(b : $i)).
thf(add,type,(add : $i > $i > $i)).
thf(r,type,(r : $i > $i > $o)).
thf(add_empty,axiom,(! [X:$i] : ((add @ X @ e) = X))).
thf(hr,axiom,((r @ a) @ b)).
thf(goal,conjecture,((r @ (add @ a @ e)) @ (add @ b @ e))).
EOF

run_case conjunction_intro
run_case conjunction_projection
run_case equality_rewrite
run_case equality_normalization
run_case predicate_equality_rewrite
run_case reverse_equality_normalization
run_case binary_predicate_simplification
assert_contains "$work_dir/equality_rewrite.mg" "claim L0:"
assert_contains "$work_dir/equality_rewrite.mg" "rewrite <- L0."
assert_contains "$work_dir/equality_normalization.mg" "claim L0:"
assert_contains "$work_dir/equality_normalization.mg" "claim L1:"
assert_contains "$work_dir/equality_normalization.mg" "rewrite L1."
assert_contains "$work_dir/predicate_equality_rewrite.mg" "fun Zeq:set"
assert_contains "$work_dir/reverse_equality_normalization.mg" "rewrite <- L0."
assert_contains "$work_dir/reverse_equality_normalization.mg" "rewrite <- L1."
assert_contains "$work_dir/binary_predicate_simplification.mg" "fun Zeq:set"
