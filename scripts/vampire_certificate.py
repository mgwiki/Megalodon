#!/usr/bin/env python3
"""Check the first Vampire-to-Megalodon certificate fragment.

This is intentionally small. It validates the MVP resolution/factoring/
contradiction fragment from reports/vampire-megalodon-certificate-spec.md.
It does not try to reconstruct missing pivots, substitutions, or proof steps.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


FORMAT = "vampire-megalodon-certificate"
VERSION = 1
MVP_RULES = {
    "input",
    "substitute",
    "resolve",
    "factor",
    "contradiction",
}


class CertificateError(Exception):
    pass


@dataclass(frozen=True, order=True)
class Literal:
    polarity: bool
    atom: str

    @property
    def complement(self) -> "Literal":
        return Literal(not self.polarity, self.atom)


def parse_literal(value: Any, context: str) -> Literal:
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: literal must be an object")
    if set(value) != {"polarity", "atom"}:
        raise CertificateError(f"{context}: literal fields must be polarity and atom")
    polarity = value["polarity"]
    atom = value["atom"]
    if not isinstance(polarity, bool):
        raise CertificateError(f"{context}: literal polarity must be boolean")
    if not isinstance(atom, str) or not atom:
        raise CertificateError(f"{context}: literal atom must be a non-empty string")
    return Literal(polarity, atom)


def parse_clause(value: Any, context: str) -> tuple[Literal, ...]:
    if not isinstance(value, list):
        raise CertificateError(f"{context}: clause must be a list")
    return tuple(parse_literal(item, f"{context}[{index}]") for index, item in enumerate(value))


def normalize_clause(clause: tuple[Literal, ...]) -> tuple[Literal, ...]:
    return tuple(sorted(set(clause)))


def clause_without_one(clause: tuple[Literal, ...], literal: Literal) -> tuple[Literal, ...]:
    removed = False
    result: list[Literal] = []
    for item in clause:
        if not removed and item == literal:
            removed = True
            continue
        result.append(item)
    if not removed:
        raise CertificateError(f"literal {literal.atom} was not present with requested polarity")
    return tuple(result)


def require_fields(step: dict[str, Any], fields: set[str]) -> None:
    missing = sorted(fields - set(step))
    if missing:
        raise CertificateError(f"{step.get('id', '<unknown>')}: missing fields: {', '.join(missing)}")


def require_no_extra_fields(step: dict[str, Any], fields: set[str]) -> None:
    extra = sorted(set(step) - fields)
    if extra:
        raise CertificateError(f"{step.get('id', '<unknown>')}: unexpected fields: {', '.join(extra)}")


def require_parents(step: dict[str, Any], count: int) -> list[str]:
    parents = step.get("parents")
    if not isinstance(parents, list) or len(parents) != count:
        raise CertificateError(f"{step.get('id', '<unknown>')}: expected {count} parent(s)")
    if not all(isinstance(parent, str) and parent for parent in parents):
        raise CertificateError(f"{step.get('id', '<unknown>')}: parent ids must be non-empty strings")
    return parents


def check_certificate(data: Any) -> dict[str, tuple[Literal, ...]]:
    if not isinstance(data, dict):
        raise CertificateError("certificate must be a JSON object")
    if data.get("format") != FORMAT:
        raise CertificateError(f"format must be {FORMAT}")
    if data.get("version") != VERSION:
        raise CertificateError(f"version must be {VERSION}")
    steps = data.get("steps")
    if not isinstance(steps, list) or not steps:
        raise CertificateError("steps must be a non-empty list")

    clauses: dict[str, tuple[Literal, ...]] = {}
    for index, step in enumerate(steps):
        if not isinstance(step, dict):
            raise CertificateError(f"steps[{index}]: step must be an object")
        step_id = step.get("id")
        rule = step.get("rule")
        if not isinstance(step_id, str) or not step_id:
            raise CertificateError(f"steps[{index}]: id must be a non-empty string")
        if step_id in clauses:
            raise CertificateError(f"{step_id}: duplicate step id")
        if rule not in MVP_RULES:
            raise CertificateError(f"{step_id}: unsupported MVP rule {rule!r}")

        if rule == "input":
            allowed = {"id", "rule", "clause", "source"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))

        elif rule == "factor":
            allowed = {"id", "rule", "parents", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            expected = normalize_clause(parent_clause)
            if clause != expected:
                raise CertificateError(f"{step_id}: factor conclusion does not match parent")

        elif rule == "substitute":
            allowed = {"id", "rule", "parents", "substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            substitution = step["substitution"]
            if not isinstance(substitution, dict):
                raise CertificateError(f"{step_id}: substitution must be an object")
            if not all(isinstance(name, str) and name for name in substitution):
                raise CertificateError(f"{step_id}: substitution variables must be non-empty strings")
            if substitution:
                raise CertificateError(f"{step_id}: non-empty substitutions require the structured term phase")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != normalize_clause(parent_clause):
                raise CertificateError(f"{step_id}: empty substitution cannot change the clause")

        elif rule == "resolve":
            allowed = {"id", "rule", "parents", "pivot", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 2)
            left = clauses.get(parents[0])
            right = clauses.get(parents[1])
            if left is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            if right is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[1]}")
            pivot = parse_literal(step["pivot"], f"{step_id}.pivot")
            if pivot not in left:
                raise CertificateError(f"{step_id}: pivot not present in first parent")
            if pivot.complement not in right:
                raise CertificateError(f"{step_id}: complement pivot not present in second parent")
            expected = normalize_clause(
                clause_without_one(left, pivot)
                + clause_without_one(right, pivot.complement)
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: resolve conclusion does not match parents")

        elif rule == "contradiction":
            allowed = {"id", "rule", "parents", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if parent_clause or clause:
                raise CertificateError(f"{step_id}: contradiction requires an empty parent clause and empty conclusion")

        else:
            raise AssertionError(rule)

        clauses[step_id] = clause

    return clauses


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--summary", action="store_true")
    args = parser.parse_args()

    try:
        data = json.loads(args.certificate.read_text(encoding="utf-8"))
        clauses = check_certificate(data)
    except (OSError, json.JSONDecodeError, CertificateError) as exc:
        print(f"certificate check failed: {exc}", file=sys.stderr)
        return 1

    if args.summary:
        empty = sum(1 for clause in clauses.values() if not clause)
        print(json.dumps({"steps": len(clauses), "empty_clauses": empty}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
