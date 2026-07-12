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
    "paramodulate",
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


def parse_position(value: Any, context: str) -> tuple[int, ...]:
    if not isinstance(value, list):
        raise CertificateError(f"{context}: position must be a list")
    result: list[int] = []
    for index, item in enumerate(value):
        if not isinstance(item, int) or item < 0:
            raise CertificateError(f"{context}[{index}]: position entries must be non-negative integers")
        result.append(item)
    return tuple(result)


def term_at_position(term: Term, position: tuple[int, ...], context: str) -> Term:
    selected = term
    for depth, index in enumerate(position):
        if index >= len(selected.args):
            raise CertificateError(f"{context}: position {list(position)} is invalid at depth {depth}")
        selected = selected.args[index]
    return selected


def replace_term_at_position(term: Term, position: tuple[int, ...], replacement: Term, context: str) -> Term:
    if not position:
        return replacement
    index = position[0]
    if index >= len(term.args):
        raise CertificateError(f"{context}: position {list(position)} is invalid")
    args = list(term.args)
    args[index] = replace_term_at_position(args[index], position[1:], replacement, context)
    return Term(term.kind, term.name, tuple(args))


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

        elif rule == "paramodulate":
            allowed = {"id", "rule", "parents", "equality", "from", "to", "target", "position", "substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 2)
            equality_parent = clauses.get(parents[0])
            target_parent = clauses.get(parents[1])
            if equality_parent is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            if target_parent is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[1]}")
            equality = parse_literal(step["equality"], f"{step_id}.equality")
            target = parse_literal(step["target"], f"{step_id}.target")
            if equality not in equality_parent:
                raise CertificateError(f"{step_id}: equality literal not present in equality parent")
            if target not in target_parent:
                raise CertificateError(f"{step_id}: target literal not present in target parent")
            if not equality.polarity:
                raise CertificateError(f"{step_id}: paramodulation equality must be positive")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            selected_equality = substitute_literal(equality, substitution)
            if selected_equality.atom.kind != "eq" or len(selected_equality.atom.args) != 2:
                raise CertificateError(f"{step_id}: selected equality is not an equality atom")
            from_term = substitute_term(parse_term(step["from"], f"{step_id}.from"), substitution)
            to_term = substitute_term(parse_term(step["to"], f"{step_id}.to"), substitution)
            if selected_equality.atom.args != (from_term, to_term):
                raise CertificateError(f"{step_id}: from/to do not match selected equality after substitution")
            position = parse_position(step["position"], f"{step_id}.position")
            selected_target = substitute_literal(target, substitution)
            replaced = term_at_position(selected_target.atom, position, f"{step_id}.position")
            if replaced != from_term:
                raise CertificateError(f"{step_id}: target position does not contain the selected from term")
            rewritten_target = Literal(
                selected_target.polarity,
                replace_term_at_position(selected_target.atom, position, to_term, f"{step_id}.position"),
            )
            expected = normalize_clause(
                tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(equality_parent, equality)
                )
                + tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(target_parent, target)
                )
                + (rewritten_target,)
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: paramodulation conclusion does not match parents")

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


def literal_text(literal: Literal) -> str:
    if literal.atom.kind != "opaque":
        raise CertificateError("Megalodon smoke elaboration currently supports only opaque propositional atoms")
    if literal.polarity:
        return literal.atom.name
    return f"({literal.atom.name} -> False)"


def clause_text(clause: tuple[Literal, ...]) -> str:
    normalized = normalize_clause(clause)
    if not normalized:
        return "False"
    parts = [literal_text(literal) for literal in normalized]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"({part} \\/ {result})"
    return result


def or_left_intro_proof(proof: str) -> str:
    return f"(fun P Hleft Hright => Hleft {proof})"


def or_right_intro_proof(proof: str) -> str:
    return f"(fun P Hleft Hright => Hright {proof})"


def intro_literal_proof(literal: Literal, target: tuple[Literal, ...], proof: str) -> str:
    normalized = normalize_clause(target)
    if not normalized:
        return f"({proof} False)"
    head, *tail = normalized
    if literal == head:
        if not tail:
            return proof
        return or_left_intro_proof(proof)
    if not tail:
        raise CertificateError(f"literal {literal_text(literal)} is not in target clause")
    return or_right_intro_proof(intro_literal_proof(literal, tuple(tail), proof))


def false_from_complements(left: Literal, left_proof: str, right: Literal, right_proof: str) -> str:
    if left.complement != right:
        raise CertificateError("literals are not complementary")
    if left.polarity:
        return f"({right_proof} {left_proof})"
    return f"({left_proof} {right_proof})"


def eliminate_clause_proof(
    clause: tuple[Literal, ...],
    proof: str,
    goal: str,
    branch_proof,
) -> str:
    normalized = normalize_clause(clause)
    if not normalized:
        return f"({proof} {goal})"
    if len(normalized) == 1:
        return branch_proof(normalized[0], proof)
    head = normalized[0]
    tail = tuple(normalized[1:])
    return (
        f"({proof} {goal} "
        f"(fun Hlit => {branch_proof(head, 'Hlit')}) "
        f"(fun Htail => {eliminate_clause_proof(tail, 'Htail', goal, branch_proof)}))"
    )


def resolve_proof_text(
    left_clause: tuple[Literal, ...],
    left_proof: str,
    right_clause: tuple[Literal, ...],
    right_proof: str,
    pivot: Literal,
    conclusion: tuple[Literal, ...],
) -> str:
    goal = clause_text(conclusion)
    complement = pivot.complement

    def right_branch(literal: Literal, proof: str, pivot_proof: str) -> str:
        if literal == complement:
            false_proof = false_from_complements(pivot, pivot_proof, literal, proof)
            return f"({false_proof} {goal})"
        return intro_literal_proof(literal, conclusion, proof)

    def left_branch(literal: Literal, proof: str) -> str:
        if literal == pivot:
            return eliminate_clause_proof(
                right_clause,
                right_proof,
                goal,
                lambda right_literal, right_literal_proof: right_branch(right_literal, right_literal_proof, proof),
            )
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(left_clause, left_proof, goal, left_branch)


def certificate_opaque_atoms(clauses: dict[str, tuple[Literal, ...]]) -> list[str]:
    atoms: set[str] = set()
    for clause in clauses.values():
        for literal in clause:
            if literal.atom.kind != "opaque":
                continue
            atoms.add(literal.atom.name)
    return sorted(atoms)


def emit_megalodon_smoke(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]], theorem_name: str) -> str:
    atoms = certificate_opaque_atoms(clauses)
    if not atoms:
        raise CertificateError("Megalodon smoke elaboration needs at least one opaque atom")
    lines = [
        "Definition False : prop := forall p:prop, p.",
        "Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.",
        "Infix \\/ 785 left := or.",
        f"Variable {' '.join(atoms)}:prop.",
    ]
    step_clauses: dict[str, tuple[Literal, ...]] = {}
    proof_names: dict[str, str] = {}
    assumptions: list[tuple[str, str]] = []
    derived: list[tuple[str, str, str]] = []
    final_empty: str | None = None

    for step in data["steps"]:
        step_id = step["id"]
        rule = step["rule"]
        clause = clauses[step_id]
        step_clauses[step_id] = clause
        if not clause:
            final_empty = step_id
        if rule == "input":
            proof_names[step_id] = step_id
            assumptions.append((step_id, clause_text(clause)))
            continue
        if rule == "resolve":
            parents = step["parents"]
            pivot = parse_literal(step["pivot"], f"{step_id}.pivot")
            proof = resolve_proof_text(
                step_clauses[parents[0]],
                proof_names[parents[0]],
                step_clauses[parents[1]],
                proof_names[parents[1]],
                pivot,
                clause,
            )
        elif rule == "factor":
            parent = step["parents"][0]
            proof = proof_names[parent]
        elif rule == "contradiction":
            parent = step["parents"][0]
            proof = proof_names[parent]
        else:
            raise CertificateError(f"Megalodon smoke elaboration does not yet support {rule}")
        proof_names[step_id] = step_id
        derived.append((step_id, clause_text(clause), proof))

    if final_empty is None:
        raise CertificateError("certificate has no empty-clause step to prove False")
    theorem_type = " -> ".join([*(prop for _name, prop in assumptions), "False"])
    lines.append(f"Theorem {theorem_name} : {theorem_type}.")
    for name, prop in assumptions:
        lines.append(f"assume {name}: {prop}.")
    for name, prop, proof in derived:
        lines.append(f"claim {name}: {prop}.")
        lines.append(f"{{ exact {proof}. }}")
    lines.append(f"exact {proof_names[final_empty]}.")
    lines.append("Qed.")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--emit-megalodon", type=Path)
    parser.add_argument("--theorem-name", default="vampire_certificate_smoke")
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
    if args.emit_megalodon is not None:
        try:
            rendered = emit_megalodon_smoke(data, clauses, args.theorem_name)
        except CertificateError as exc:
            print(f"certificate check failed: {exc}", file=sys.stderr)
            return 1
        args.emit_megalodon.parent.mkdir(parents=True, exist_ok=True)
        args.emit_megalodon.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
