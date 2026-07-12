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
    "equality_resolution",
    "contradiction",
}


class CertificateError(Exception):
    pass


@dataclass(frozen=True, order=True)
class Term:
    kind: str
    name: str
    args: tuple["Term", ...] = ()


@dataclass(frozen=True, order=True)
class Literal:
    polarity: bool
    atom: Term

    @property
    def complement(self) -> "Literal":
        return Literal(not self.polarity, self.atom)


def parse_term(value: Any, context: str) -> Term:
    if isinstance(value, str) and value:
        return Term("const", value)
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: term must be a string or object")
    if set(value) == {"var"}:
        name = value["var"]
        if not isinstance(name, str) or not name:
            raise CertificateError(f"{context}: variable name must be a non-empty string")
        return Term("var", name)
    if set(value) == {"const"}:
        name = value["const"]
        if not isinstance(name, str) or not name:
            raise CertificateError(f"{context}: constant name must be a non-empty string")
        return Term("const", name)
    if set(value) == {"app", "args"}:
        name = value["app"]
        args = value["args"]
        if not isinstance(name, str) or not name:
            raise CertificateError(f"{context}: function name must be a non-empty string")
        if not isinstance(args, list):
            raise CertificateError(f"{context}: function args must be a list")
        return Term("app", name, tuple(parse_term(arg, f"{context}.args[{index}]") for index, arg in enumerate(args)))
    raise CertificateError(f"{context}: term must contain var, const, or app/args")


def parse_atom(value: Any, context: str) -> Term:
    if isinstance(value, str) and value:
        return Term("opaque", value)
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: atom must be a string or object")
    if set(value) == {"pred", "args"}:
        name = value["pred"]
        args = value["args"]
        if not isinstance(name, str) or not name:
            raise CertificateError(f"{context}: predicate name must be a non-empty string")
        if not isinstance(args, list):
            raise CertificateError(f"{context}: predicate args must be a list")
        return Term("pred", name, tuple(parse_term(arg, f"{context}.args[{index}]") for index, arg in enumerate(args)))
    if set(value) == {"eq"}:
        args = value["eq"]
        if not isinstance(args, list) or len(args) != 2:
            raise CertificateError(f"{context}: equality atom must contain two terms")
        return Term("eq", "=", (parse_term(args[0], f"{context}.eq[0]"), parse_term(args[1], f"{context}.eq[1]")))
    raise CertificateError(f"{context}: atom must contain pred/args or eq")


def substitute_term(term: Term, substitution: dict[str, Term]) -> Term:
    if term.kind == "var" and term.name in substitution:
        return substitution[term.name]
    if not term.args:
        return term
    return Term(term.kind, term.name, tuple(substitute_term(arg, substitution) for arg in term.args))


def substitute_literal(literal: Literal, substitution: dict[str, Term]) -> Literal:
    return Literal(literal.polarity, substitute_term(literal.atom, substitution))


def is_reflexive_equality_atom(atom: Term) -> bool:
    return atom.kind == "eq" and len(atom.args) == 2 and atom.args[0] == atom.args[1]


def parse_substitution(value: Any, context: str) -> dict[str, Term]:
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: substitution must be an object")
    result: dict[str, Term] = {}
    for name, term in value.items():
        if not isinstance(name, str) or not name:
            raise CertificateError(f"{context}: substitution variables must be non-empty strings")
        result[name] = parse_term(term, f"{context}.{name}")
    return result


def parse_literal(value: Any, context: str) -> Literal:
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: literal must be an object")
    if set(value) != {"polarity", "atom"}:
        raise CertificateError(f"{context}: literal fields must be polarity and atom")
    polarity = value["polarity"]
    atom = value["atom"]
    if not isinstance(polarity, bool):
        raise CertificateError(f"{context}: literal polarity must be boolean")
    return Literal(polarity, parse_atom(atom, f"{context}.atom"))


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
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            expected = normalize_clause(tuple(substitute_literal(literal, substitution) for literal in parent_clause))
            if clause != expected:
                raise CertificateError(f"{step_id}: substitution conclusion does not match parent")

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

        elif rule == "equality_resolution":
            allowed = {"id", "rule", "parents", "literal", "substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            literal = parse_literal(step["literal"], f"{step_id}.literal")
            if literal not in parent_clause:
                raise CertificateError(f"{step_id}: equality-resolution literal not present in parent")
            if literal.polarity:
                raise CertificateError(f"{step_id}: equality-resolution literal must be negative")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            selected = substitute_literal(literal, substitution)
            if not is_reflexive_equality_atom(selected.atom):
                raise CertificateError(f"{step_id}: selected equality is not reflexive after substitution")
            expected = normalize_clause(
                tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(parent_clause, literal)
                )
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: equality-resolution conclusion does not match parent")

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
