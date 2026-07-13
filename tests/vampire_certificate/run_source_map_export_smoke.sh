#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

TMPDIR="${TMPDIR:-/project/tmp}"
WORK_DIR="${WORK_DIR:-"$TMPDIR/vampire_source_map_export"}"
MEGALODON="${MEGALODON:-bin/megalodon}"
VAMPIRE="${VAMPIRE:-/project/vampire-leancheck/vampire_rel_vampire/megalodon2_10940}"

rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"

if [ ! -x "$MEGALODON" ]; then
  ./makeopt
fi

"$MEGALODON" \
  -allowincompleteqed \
  -createabyprobs "$WORK_DIR/hammer" \
  examples/hammer/100thms_12_h.mg \
  >"$WORK_DIR/megalodon.log" \
  2>"$WORK_DIR/megalodon.err"

find "$WORK_DIR" -maxdepth 1 -name '*.th0.p' -type f | sort > "$WORK_DIR/problems.txt"
problem=$(sed -n '1p' "$WORK_DIR/problems.txt")
if [ -z "$problem" ]; then
  echo "source-map export smoke did not produce a TH0 problem" >&2
  exit 1
fi

if ! rg -q '^% megalodon_source_map ' "$problem"; then
  echo "TH0 problem does not contain Megalodon source-map comments" >&2
  exit 1
fi

if awk '/^% megalodon_source_map / {
    if (match($0, /"[^"]+"/)) {
      name = substr($0, RSTART + 1, RLENGTH - 2)
      seen[name]++
    }
  }
  END {
    for (name in seen) {
      if (seen[name] > 1) {
        print name
        bad = 1
      }
    }
    exit bad
  }' "$problem" >"$WORK_DIR/duplicate_source_map_names.txt"; then
  :
else
  echo "TH0 source-map contains duplicate TPTP names:" >&2
  cat "$WORK_DIR/duplicate_source_map_names.txt" >&2
  exit 1
fi

if rg '^% megalodon_source_map \(def "' "$problem" \
    | rg -vq '^% megalodon_source_map \(def "[^"]+_def"'; then
  echo "TH0 source-map definition entry does not point to the *_def formula name" >&2
  exit 1
fi

if rg -q '^thf\(conj_[^,/]*/' "$problem"; then
  echo "TH0 conjecture name contains an unsanitized slash" >&2
  exit 1
fi

if [ -x "$VAMPIRE" ]; then
  "$VAMPIRE" \
    --input_syntax tptp \
    --mode casc \
    -t 1 \
    --proof megalodon \
    --output_axiom_names on \
    "$problem" \
    >"$WORK_DIR/vampire.out" \
    2>"$WORK_DIR/vampire.err" || true
  if rg -qi 'parse error|bad character|syntax error' "$WORK_DIR/vampire.out" "$WORK_DIR/vampire.err"; then
    echo "Vampire rejected the source-mapped TH0 problem syntax" >&2
    exit 1
  fi
fi

echo "Megalodon TH0 source-map export smoke passed"
