#!/usr/bin/env bash
set -euo pipefail

ROOT=${ROOT:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"}
VAMPIRE_ROOT=${VAMPIRE_ROOT:-/project/vampire-leancheck}
TMPDIR=${TMPDIR:-/project/tmp}
export TMPDIR

MEGALODON_SYNTAX="$ROOT/src/vampire_kernel_syntax.ml"
VAMPIRE_SYNTAX="$VAMPIRE_ROOT/Shell/MegalodonChecker/MegalodonKernelSyntax.cpp"

if [[ ! -f "$MEGALODON_SYNTAX" ]]; then
  echo "missing Megalodon kernel syntax file: $MEGALODON_SYNTAX" >&2
  exit 2
fi

if [[ ! -f "$VAMPIRE_SYNTAX" ]]; then
  echo "missing Vampire kernel syntax file: $VAMPIRE_SYNTAX" >&2
  exit 2
fi

python3 - "$MEGALODON_SYNTAX" "$VAMPIRE_SYNTAX" <<'PY'
import re
import sys
from pathlib import Path

megalodon_path = Path(sys.argv[1])
vampire_path = Path(sys.argv[2])
megalodon = megalodon_path.read_text()
vampire = vampire_path.read_text()

def fail(message):
    print(message, file=sys.stderr)
    raise SystemExit(1)

def quoted_strings(text):
    return re.findall(r'"([^"]+)"', text)

def ocaml_list(name):
    pattern = rf"let {re.escape(name)} = \[(.*?)\n\]"
    match = re.search(pattern, megalodon, re.S)
    if not match:
        fail(f"cannot parse OCaml list {name}")
    return quoted_strings(match.group(1))

def ocaml_contracts():
    match = re.search(
        r"let primitive_contracts = \[(.*?)\n\]\n\nlet structural_rules",
        megalodon,
        re.S)
    if not match:
        fail("cannot parse OCaml primitive_contracts")
    contracts = {}
    for rule, body in re.findall(r'\("([^"]+)",\s*\[(.*?)\]\)', match.group(1), re.S):
        contracts[rule] = quoted_strings(body)
    return contracts

def cpp_return_list(function_name):
    pattern = (
        rf"std::vector<std::string> {re.escape(function_name)}\(\)\s*"
        r"\{\s*return\s*\{(.*?)\};\s*\}")
    match = re.search(pattern, vampire, re.S)
    if not match:
        fail(f"cannot parse C++ function {function_name}")
    return quoted_strings(match.group(1))

def cpp_contracts():
    match = re.search(
        r"static const std::vector<std::pair<std::string, std::vector<std::string>>> contracts = \{(.*?)\};",
        vampire,
        re.S)
    if not match:
        fail("cannot parse C++ primitive contracts")
    contracts = {}
    for rule, body in re.findall(r'\{"([^"]+)",\s*\{([^}]*)\}\}', match.group(1), re.S):
        contracts[rule] = quoted_strings(body)
    return contracts

def compare_list(label, left, right):
    if left == right:
        return
    left_only = sorted(set(left) - set(right))
    right_only = sorted(set(right) - set(left))
    print(f"{label} mismatch", file=sys.stderr)
    if left_only:
        print(f"  only in Megalodon: {', '.join(left_only)}", file=sys.stderr)
    if right_only:
        print(f"  only in Vampire: {', '.join(right_only)}", file=sys.stderr)
    if not left_only and not right_only:
        print("  same elements but different order", file=sys.stderr)
    raise SystemExit(1)

megalodon_primitives = ocaml_list("primitive_rules")
vampire_primitives = cpp_return_list("primitiveRules")
compare_list("primitive_rules", megalodon_primitives, vampire_primitives)

megalodon_structural = ocaml_list("structural_rules")
vampire_structural = cpp_return_list("structuralRules")
compare_list("structural_rules", megalodon_structural, vampire_structural)

megalodon_contracts = ocaml_contracts()
vampire_contracts = cpp_contracts()
if megalodon_contracts != vampire_contracts:
    all_rules = sorted(set(megalodon_contracts) | set(vampire_contracts))
    print("primitive contract mismatch", file=sys.stderr)
    for rule in all_rules:
        left = megalodon_contracts.get(rule)
        right = vampire_contracts.get(rule)
        if left != right:
            print(f"  {rule}: Megalodon={left} Vampire={right}", file=sys.stderr)
    raise SystemExit(1)

primitive_set = set(megalodon_primitives)
for rule, primitives in sorted(megalodon_contracts.items()):
    for primitive in primitives:
        if primitive not in primitive_set:
            fail(f"contract {rule} references undeclared primitive {primitive}")

print(
    "kernel vocabulary sync passed: "
    f"{len(megalodon_primitives)} primitive rules, "
    f"{len(megalodon_structural)} structural rules, "
    f"{len(megalodon_contracts)} primitive contracts")
PY
