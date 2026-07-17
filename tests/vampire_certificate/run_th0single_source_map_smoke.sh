#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON=${MEGALODON:-"$ROOT/bin/megalodon"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/th0single_source_map.XXXXXX")"}
SOURCE_FILE=${SOURCE_FILE:-"$ROOT/examples/hammer/100thms_12_h.mg"}
CASE_NATIVE=${CASE_NATIVE:-"$ROOT/tests/vampire_certificate/closed_cases/hammer.11703.242.native.sexp"}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_th0single_source_map"

if [[ ! -x "$MEGALODON" ]]; then
  (cd "$ROOT" && TMPDIR="$TMPDIR" ./makeopt)
fi

"$MEGALODON" \
  -allowincompleteqed \
  -th0single "$WORK_DIR/hammer_11703_242" 11703 242 \
  "$SOURCE_FILE" \
  >"$WORK_DIR/export.out" \
  2>"$WORK_DIR/export.err"

problem="$WORK_DIR/hammer_11703_242.th0.p"
if [[ ! -s "$problem" ]]; then
  echo "th0single source-map smoke did not produce the target problem" >&2
  exit 1
fi

if ! rg -q '^% megalodon_origin \(\(file "(/project/Megalodon/)?examples/hammer/100thms_12_h\.mg"\) \(line "11703"\) \(char "242"\) \(kind "aby"\)\)' "$problem"; then
  echo "th0single source-map smoke lost the original 11703 origin" >&2
  exit 1
fi

if ! rg -q '^% megalodon_source_map \(known "add_5FSNo_5Fcancel_5FL" "add_SNo_cancel_L" "3f9f0821c9c0345a8ac0542c7724549fd6f110a6c49b60b21e47a6f79ed69c2c"\)' "$problem"; then
  echo "th0single source-map smoke lost the add_SNo_cancel_L source link" >&2
  exit 1
fi

for local_name in Hguv Lfv3 Lfu3 L2n3; do
  if ! rg -q '^% megalodon_source_map \(local_fact "[^"]+" "'"$local_name"'" ""\)' "$problem"; then
    echo "th0single source-map smoke lost local fact $local_name" >&2
    exit 1
  fi
done

if ! rg -q '^% megalodon_source_map \(local_type "g_tp" "g" ""\)' "$problem"; then
  echo "th0single source-map smoke lost the unused local variable type for g" >&2
  exit 1
fi

if ! rg -q '^% megalodon_source_map \(conjecture "conj_c_100thms_5F12_5Fh_5Fline11703_5Fchar242" "100thms_12_h_line11703_char242" ""\)' "$problem"; then
  echo "th0single source-map smoke did not use the stable 11703 conjecture source name" >&2
  exit 1
fi

if rg -q '/project/tmp|th0single_source_map|hammer_11703_242' "$problem"; then
  echo "th0single source-map smoke leaked a temporary/output prefix into the source map" >&2
  exit 1
fi

old_conjecture=$(sed -n 's/.*(source negated_conjecture "\([^"]*\)").*/\1/p' "$CASE_NATIVE" | head -1)
new_conjecture=$(sed -n 's/^% megalodon_source_map (conjecture "\([^"]*\)" .*/\1/p' "$problem" | head -1)
if [[ -z "$old_conjecture" || -z "$new_conjecture" ]]; then
  echo "th0single source-map smoke could not identify conjecture names" >&2
  exit 1
fi

rewritten_cert="$WORK_DIR/hammer.11703.242.native.sexp"
sed "s/$old_conjecture/$new_conjecture/g" "$CASE_NATIVE" > "$rewritten_cert"
: > "$WORK_DIR/dummy.mg"

"$MEGALODON" \
  -vampirecertv1sourceaudit \
  -vampirecertv1 "$rewritten_cert" \
  -vampirecertv1source "$problem" \
  "$WORK_DIR/dummy.mg" \
  >"$WORK_DIR/sourceaudit.out" \
  2>"$WORK_DIR/sourceaudit.err"

if ! rg -q 'Vampire certificate v1 source map checked 7 sources\.' "$WORK_DIR/sourceaudit.out"; then
  echo "th0single source-map smoke did not audit all seven 11703 certificate sources" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 source obligations audited total=7 formula_checked=7 formula_unsupported=0 formula_missing=0' "$WORK_DIR/sourceaudit.out"; then
  echo "th0single source-map smoke did not verify the 11703 source obligations" >&2
  exit 1
fi

"$MEGALODON" \
  -vampirecertv1strict \
  -vampirecertv1sourcecontext \
  -vampirecertv1corepfcheck \
  -vampirecertv1 "$rewritten_cert" \
  -vampirecertv1source "$problem" \
  "$WORK_DIR/dummy.mg" \
  >"$WORK_DIR/corepf.out" \
  2>"$WORK_DIR/corepf.err"

if ! rg -q 'Vampire certificate v1 native core proof term checked 44 steps\.' "$WORK_DIR/corepf.out"; then
  echo "th0single source-map smoke did not check the 11703 native core proof term" >&2
  exit 1
fi
if ! rg -q 'Vampire certificate v1 native core source assumptions remaining by kind known=1 local=4 definition=0 generated=0 conjecture=1 unresolved=0\.' "$WORK_DIR/corepf.out"; then
  echo "th0single source-map smoke did not preserve the expected detached 11703 source-context frontier" >&2
  exit 1
fi

live_dir="$WORK_DIR/live_target_reconstruct"
mkdir -p "$live_dir"
cat >"$live_dir/fake_vampire" <<EOF_FAKE_VAMPIRE
#!/usr/bin/env bash
problem="\${@: -1}"
case_file="$CASE_NATIVE"
conj=\$(sed -n 's/^% megalodon_source_map (conjecture "\([^"]*\)" .*/\1/p' "\$problem" | head -1)
old=\$(sed -n 's/.*(source negated_conjecture "\([^"]*\)").*/\1/p' "\$case_file" | head -1)
printf '%% SZS status Theorem\n%% SZS output start Proof\nmegalodon_certificate_native_sexpr_start.\n'
sed "s/\$old/\$conj/g" "\$case_file"
printf 'megalodon_certificate_native_sexpr_end.\n%% SZS output end Proof\n'
EOF_FAKE_VAMPIRE
chmod +x "$live_dir/fake_vampire"

"$MEGALODON" \
  -v 9 \
  -allowincompleteqed \
  -th0single "$live_dir/hammer_11703_242_live" 11703 242 \
  -vampireaby "$live_dir/fake_vampire" \
  -vampireabyproof megalodon \
  -vampireabynative \
  -vampireabynativestrict \
  -vampireabyoutdir "$live_dir/out" \
  "$SOURCE_FILE" \
  >"$live_dir/live.out" \
  2>"$live_dir/live.err"

if ! rg -q 'Vampire native certificate checked 44 steps and 7 sources at line 11703 char 242; source_context known=1 local=4 local_definition=0 conjecture=2 unresolved=0\.' "$live_dir/live.out"; then
  echo "th0single live target reconstruction did not resolve the real 11703 source context" >&2
  exit 1
fi
if ! rg -q 'Vampire native certificate reconstructed aby proof term at line 11703 char 242\.' "$live_dir/live.out"; then
  echo "th0single live target reconstruction did not reconstruct the 11703 target proof term" >&2
  exit 1
fi
if ! rg -q 'Vampire th0single native certificate reconstructed target proof term at line 11703 char 242\.' "$live_dir/live.out"; then
  echo "th0single live target reconstruction did not report the target-only native success marker" >&2
  exit 1
fi

echo "th0single source-map smoke passed"
echo "th0single source-map artifacts: $WORK_DIR"
echo "th0single source-map latest link: $TMPDIR/latest_th0single_source_map"
