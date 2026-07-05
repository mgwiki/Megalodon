#!/usr/bin/env python3
"""Summarize Vampire inference-rule coverage from a reconstruction manifest."""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path


INFERENCE_RE = re.compile(r"\binference\((?P<rule>[A-Za-z0-9_]+),")
MEGALODON_STEP_RE = re.compile(r"\bmegalodon_step\([0-9]+,\"(?P<rule>(?:\\.|[^\"])*)\",")
LEAN_STEP_RE = re.compile(r"^-- step [0-9]+ (?P<rule>.+)$", re.MULTILINE)


def unquote_rule(rule: str) -> str:
    return bytes(rule, "utf-8").decode("unicode_escape")


def proof_rules(path: Path) -> collections.Counter[str]:
    text = path.read_text(encoding="utf-8", errors="replace")
    rules = collections.Counter(match.group("rule") for match in INFERENCE_RE.finditer(text))
    rules.update(unquote_rule(match.group("rule")) for match in MEGALODON_STEP_RE.finditer(text))
    rules.update(match.group("rule") for match in LEAN_STEP_RE.finditer(text))
    return rules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    parser.add_argument("--limit", type=int, default=40, help="maximum rule rows to print")
    args = parser.parse_args()

    total_rules: collections.Counter[str] = collections.Counter()
    per_proof: list[dict[str, object]] = []

    for line_no, row in enumerate(args.manifest.read_text(encoding="utf-8").splitlines(), start=1):
        if not row.strip():
            continue
        data = json.loads(row)
        proof = Path(data["proof"])
        if not proof.exists():
            raise SystemExit(f"{args.manifest}:{line_no}: missing proof file: {proof}")
        rules = proof_rules(proof)
        total_rules.update(rules)
        per_proof.append(
            {
                "line": data.get("line"),
                "char": data.get("char"),
                "proof": str(proof),
                "rules": dict(sorted(rules.items())),
                "rule_steps": sum(rules.values()),
            }
        )

    if args.json:
        print(
            json.dumps(
                {
                    "manifest": str(args.manifest),
                    "proofs": len(per_proof),
                    "total_rule_steps": sum(total_rules.values()),
                    "rules": dict(total_rules.most_common()),
                    "per_proof": per_proof,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0

    print(f"manifest: {args.manifest}")
    print(f"proofs: {len(per_proof)}")
    print(f"total inference steps: {sum(total_rules.values())}")
    print("rules:")
    for rule, count in total_rules.most_common(args.limit):
        print(f"  {rule}: {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
