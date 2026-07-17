#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

CASES_DIR=${CASES_DIR:-"$ROOT/tests/vampire_certificate/closed_cases"}
WORK_DIR=${WORK_DIR:-"$(mktemp -d "$TMPDIR/native_cert_v1_layered_closed_audit.XXXXXX")"}
JOBS=${JOBS:-10}
RUN_CORE_PF_CASES=${RUN_CORE_PF_CASES:-1}

mkdir -p "$WORK_DIR"
ln -sfn "$WORK_DIR" "$TMPDIR/latest_native_cert_v1_layered_closed_audit"

run_gate() {
  local layer=$1
  shift
  mkdir -p "$WORK_DIR/$layer"
  WORK_DIR="$WORK_DIR/$layer" JOBS="$JOBS" "$@"
}

run_gate core \
  env RUN_CORE_CASES=1 RUN_CORE_PF_CASES="$RUN_CORE_PF_CASES" \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_core_closed_audit.sh"
run_gate preprocess \
  env RUN_PREPROCESS_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_preprocess_closed_audit.sh"
run_gate skolem \
  env RUN_SKOLEM_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_skolem_closed_audit.sh"
run_gate definition \
  env RUN_DEFINITION_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_definition_closed_audit.sh"
run_gate avatar \
  env RUN_AVATAR_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_avatar_closed_audit.sh"
run_gate inequality \
  env RUN_INEQUALITY_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_inequality_closed_audit.sh"
run_gate definition_rewrite \
  env RUN_DEFINITION_REWRITE_CASES=1 \
  "$ROOT/tests/vampire_certificate/run_native_cert_v1_definition_rewrite_closed_audit.sh"

find "$CASES_DIR" -maxdepth 1 -name '*.native.sexp' -type f -printf '%f\n' \
  | sed 's/\.native\.sexp$//' \
  | sort > "$WORK_DIR/all_closed_cases.list"

{
  printf 'definition_rewrite\t%s\n' "$WORK_DIR/definition_rewrite/definition_rewrite_closed_cases.list"
  printf 'inequality\t%s\n' "$WORK_DIR/inequality/inequality_closed_cases.list"
  printf 'avatar\t%s\n' "$WORK_DIR/avatar/avatar_closed_cases.list"
  printf 'definition\t%s\n' "$WORK_DIR/definition/definition_closed_cases.list"
  printf 'skolem\t%s\n' "$WORK_DIR/skolem/skolem_closed_cases.list"
  printf 'preprocess\t%s\n' "$WORK_DIR/preprocess/preprocess_closed_cases.list"
  printf 'core\t%s\n' "$WORK_DIR/core/core_closed_cases.list"
} > "$WORK_DIR/layer_lists.tsv"

: > "$WORK_DIR/covered_with_layer.tsv"
: > "$WORK_DIR/covered_so_far.list"
while IFS=$'\t' read -r layer list_file; do
  if [[ ! -s "$list_file" ]]; then
    echo "layer $layer produced no selected cases at $list_file" >&2
    exit 1
  fi
  sort -u "$list_file" > "$WORK_DIR/$layer.raw_selected.list"
  comm -23 "$WORK_DIR/$layer.raw_selected.list" "$WORK_DIR/covered_so_far.list" \
    > "$WORK_DIR/$layer.selected.list"
  awk -v layer="$layer" '{print $0 "\t" layer}' "$WORK_DIR/$layer.selected.list" \
    >> "$WORK_DIR/covered_with_layer.tsv"
  {
    cat "$WORK_DIR/covered_so_far.list"
    cat "$WORK_DIR/$layer.selected.list"
  } | sort -u > "$WORK_DIR/covered_so_far.next"
  mv "$WORK_DIR/covered_so_far.next" "$WORK_DIR/covered_so_far.list"
done < "$WORK_DIR/layer_lists.tsv"

cut -f1 "$WORK_DIR/covered_with_layer.tsv" | sort > "$WORK_DIR/covered_cases_with_duplicates.list"
sort -u "$WORK_DIR/covered_cases_with_duplicates.list" > "$WORK_DIR/covered_cases.list"

comm -23 "$WORK_DIR/all_closed_cases.list" "$WORK_DIR/covered_cases.list" \
  > "$WORK_DIR/missing_from_layers.list"
comm -13 "$WORK_DIR/all_closed_cases.list" "$WORK_DIR/covered_cases.list" \
  > "$WORK_DIR/extra_layer_cases.list"
uniq -d "$WORK_DIR/covered_cases_with_duplicates.list" > "$WORK_DIR/duplicate_layer_cases.list"

awk -F '\t' '{count[$2]++} END {for (layer in count) print layer, count[layer]}' \
  "$WORK_DIR/covered_with_layer.tsv" | sort > "$WORK_DIR/layer_counts.txt"

total_count=$(wc -l < "$WORK_DIR/all_closed_cases.list" | tr -d ' ')
covered_count=$(wc -l < "$WORK_DIR/covered_cases.list" | tr -d ' ')

cat "$WORK_DIR/layer_counts.txt"
{
  printf 'LAYERED_CLOSED_TOTAL %s\n' "$total_count"
  printf 'LAYERED_CLOSED_COVERED %s\n' "$covered_count"
  printf 'LAYERED_CLOSED_MISSING %s\n' "$(wc -l < "$WORK_DIR/missing_from_layers.list" | tr -d ' ')"
  printf 'LAYERED_CLOSED_EXTRA %s\n' "$(wc -l < "$WORK_DIR/extra_layer_cases.list" | tr -d ' ')"
  printf 'LAYERED_CLOSED_DUPLICATE %s\n' "$(wc -l < "$WORK_DIR/duplicate_layer_cases.list" | tr -d ' ')"
} | tee "$WORK_DIR/counts.txt"

echo "native certificate v1 layered closed audit artifacts: $WORK_DIR"
echo "native certificate v1 layered closed audit latest link: $TMPDIR/latest_native_cert_v1_layered_closed_audit"

if [[ -s "$WORK_DIR/missing_from_layers.list" \
      || -s "$WORK_DIR/extra_layer_cases.list" \
      || -s "$WORK_DIR/duplicate_layer_cases.list" ]]; then
  echo "layered closed audit failed: selected layers are not a disjoint cover of closed_cases" >&2
  echo "missing cases:" >&2
  sed -n '1,40p' "$WORK_DIR/missing_from_layers.list" >&2
  echo "extra cases:" >&2
  sed -n '1,40p' "$WORK_DIR/extra_layer_cases.list" >&2
  echo "duplicate cases:" >&2
  sed -n '1,40p' "$WORK_DIR/duplicate_layer_cases.list" >&2
  exit 1
fi
