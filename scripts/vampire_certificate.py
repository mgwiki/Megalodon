#!/usr/bin/env python3
"""Check the first Vampire-to-Megalodon certificate fragment.

This is intentionally small. It validates the MVP resolution/factoring/
contradiction fragment from reports/vampire-megalodon-certificate-spec.md.
It does not try to reconstruct missing pivots, substitutions, or proof steps.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
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
PROOF_NAME_COUNTER = itertools.count()


class CertificateError(Exception):
    pass


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


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


def require_megalodon_ident(name: str, context: str) -> str:
    if not IDENT_RE.fullmatch(name):
        raise CertificateError(f"{context}: {name!r} is not a supported Megalodon identifier")
    return name


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


def term_text(term: Term) -> str:
    if term.kind in {"var", "const"}:
        return require_megalodon_ident(term.name, "term")
    if term.kind == "app":
        name = require_megalodon_ident(term.name, "term")
        args = " ".join(term_text(arg) for arg in term.args)
        return f"({name} {args})" if args else name
    raise CertificateError(f"cannot render term kind {term.kind!r}")


def atom_text(atom: Term) -> str:
    if atom.kind == "opaque":
        return require_megalodon_ident(atom.name, "atom")
    if atom.kind == "pred":
        name = require_megalodon_ident(atom.name, "atom")
        args = " ".join(term_text(arg) for arg in atom.args)
        return f"({name} {args})" if args else name
    if atom.kind == "eq" and len(atom.args) == 2:
        return f"({term_text(atom.args[0])} = {term_text(atom.args[1])})"
    raise CertificateError(f"cannot render atom kind {atom.kind!r}")


def literal_text(literal: Literal) -> str:
    atom = atom_text(literal.atom)
    if literal.polarity:
        return atom
    return f"({atom} -> False)"


def clause_body_text(clause: tuple[Literal, ...]) -> str:
    normalized = normalize_clause(clause)
    if not normalized:
        return "False"
    parts = [literal_text(literal) for literal in normalized]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"({part} \\/ {result})"
    return result


def term_free_vars(term: Term) -> set[str]:
    if term.kind == "var":
        return {term.name}
    result: set[str] = set()
    for arg in term.args:
        result.update(term_free_vars(arg))
    return result


def literal_free_vars(literal: Literal) -> set[str]:
    return term_free_vars(literal.atom)


def clause_free_vars(clause: tuple[Literal, ...]) -> tuple[str, ...]:
    variables: set[str] = set()
    for literal in clause:
        variables.update(literal_free_vars(literal))
    return tuple(sorted(variables))


def clause_prop_text(clause: tuple[Literal, ...]) -> str:
    result = clause_body_text(clause)
    for name in reversed(clause_free_vars(clause)):
        result = f"forall {require_megalodon_ident(name, 'binder')}:set, {result}"
    return result


def or_left_intro_proof(proof: str) -> str:
    goal = fresh_proof_name("OrGoal")
    left = fresh_proof_name("Hleft")
    right = fresh_proof_name("Hright")
    return f"(fun {goal} {left} {right} => {left} {proof})"


def or_right_intro_proof(proof: str) -> str:
    goal = fresh_proof_name("OrGoal")
    left = fresh_proof_name("Hleft")
    right = fresh_proof_name("Hright")
    return f"(fun {goal} {left} {right} => {right} {proof})"


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


def equality_refl_proof() -> str:
    return "(fun Q H => H)"


def fresh_proof_name(prefix: str) -> str:
    return f"{prefix}_{next(PROOF_NAME_COUNTER)}"


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
    head_proof = fresh_proof_name("Hlit")
    tail_proof = fresh_proof_name("Htail")
    return (
        f"({proof} {goal} "
        f"(fun {head_proof} => {branch_proof(head, head_proof)}) "
        f"(fun {tail_proof} => {eliminate_clause_proof(tail, tail_proof, goal, branch_proof)}))"
    )


def resolve_proof_text(
    left_clause: tuple[Literal, ...],
    left_proof: str,
    right_clause: tuple[Literal, ...],
    right_proof: str,
    pivot: Literal,
    conclusion: tuple[Literal, ...],
) -> str:
    if clause_free_vars(left_clause) or clause_free_vars(right_clause) or clause_free_vars(conclusion):
        raise CertificateError("Megalodon smoke resolution elaboration currently requires ground clauses")
    goal = clause_body_text(conclusion)
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


def equality_resolution_proof_text(
    parent_clause: tuple[Literal, ...],
    parent_proof: str,
    selected_literal: Literal,
    substitution: dict[str, Term],
    conclusion: tuple[Literal, ...],
) -> str:
    instantiated_parent = tuple(substitute_literal(literal, substitution) for literal in parent_clause)
    instantiated_selected = substitute_literal(selected_literal, substitution)
    if instantiated_selected.polarity or not is_reflexive_equality_atom(instantiated_selected.atom):
        raise CertificateError("selected equality-resolution literal is not negative reflexive equality")
    if clause_free_vars(instantiated_parent) or clause_free_vars(conclusion):
        raise CertificateError("Megalodon smoke equality-resolution elaboration currently requires ground instantiated clauses")
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution)
    goal = clause_body_text(conclusion)
    reflexive_false = lambda proof: f"({proof} {equality_refl_proof()})"

    def branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_selected:
            false_proof = reflexive_false(proof)
            return f"({false_proof} {goal})"
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def paramodulation_proof_text(
    equality_parent_clause: tuple[Literal, ...],
    equality_parent_proof: str,
    target_parent_clause: tuple[Literal, ...],
    target_parent_proof: str,
    selected_equality: Literal,
    selected_target: Literal,
    position: tuple[int, ...],
    substitution: dict[str, Term],
    conclusion: tuple[Literal, ...],
) -> str:
    instantiated_equality_parent = tuple(substitute_literal(literal, substitution) for literal in equality_parent_clause)
    instantiated_target_parent = tuple(substitute_literal(literal, substitution) for literal in target_parent_clause)
    instantiated_equality = substitute_literal(selected_equality, substitution)
    instantiated_target = substitute_literal(selected_target, substitution)
    if clause_free_vars(instantiated_equality_parent) or clause_free_vars(instantiated_target_parent) or clause_free_vars(conclusion):
        raise CertificateError("Megalodon smoke paramodulation elaboration currently requires ground instantiated clauses")
    if instantiated_equality not in normalize_clause(instantiated_equality_parent):
        raise CertificateError("Megalodon smoke paramodulation equality literal is not present after substitution")
    if instantiated_target not in normalize_clause(instantiated_target_parent):
        raise CertificateError("Megalodon smoke paramodulation target literal is not present after substitution")
    if not instantiated_equality.polarity or instantiated_equality.atom.kind != "eq" or len(instantiated_equality.atom.args) != 2:
        raise CertificateError("Megalodon smoke paramodulation selected literal must be positive equality")
    from_term, to_term = instantiated_equality.atom.args
    if term_at_position(instantiated_target.atom, position, "paramodulation.position") != from_term:
        raise CertificateError("Megalodon smoke paramodulation target position does not contain equality left side")
    expected_atom = replace_term_at_position(instantiated_target.atom, position, to_term, "paramodulation.position")
    rewritten_target = Literal(instantiated_target.polarity, expected_atom)
    if rewritten_target not in normalize_clause(conclusion):
        raise CertificateError("Megalodon smoke paramodulation conclusion does not contain the rewritten target")

    equality_proof = instantiate_proof(equality_parent_proof, equality_parent_clause, substitution)
    target_proof = instantiate_proof(target_parent_proof, target_parent_clause, substitution)
    forward_context_atom = replace_term_at_position(
        instantiated_target.atom,
        position,
        Term("var", "cert_x"),
        "paramodulation.position",
    )
    forward_context = f"(fun cert_x cert_y:set => {atom_text(forward_context_atom)})"
    backward_context_atom = replace_term_at_position(
        instantiated_target.atom,
        position,
        Term("var", "cert_y"),
        "paramodulation.position",
    )
    backward_context = f"(fun cert_x cert_y:set => {atom_text(backward_context_atom)})"
    goal = clause_body_text(conclusion)

    def target_branch(literal: Literal, proof: str, equality_literal_proof: str) -> str:
        if literal == instantiated_target:
            if instantiated_target.polarity:
                transported = f"({equality_literal_proof} {forward_context} {proof})"
            else:
                rewritten_proof = fresh_proof_name("Hrewrite")
                transported = f"(fun {rewritten_proof} => ({proof} ({equality_literal_proof} {backward_context} {rewritten_proof})))"
            return intro_literal_proof(rewritten_target, conclusion, transported)
        return intro_literal_proof(literal, conclusion, proof)

    def equality_branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_equality:
            return eliminate_clause_proof(
                instantiated_target_parent,
                target_proof,
                goal,
                lambda target_literal, target_literal_proof: target_branch(target_literal, target_literal_proof, proof),
            )
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_equality_parent, equality_proof, goal, equality_branch)


def collect_term_symbols(term: Term, constants: set[str], functions: dict[str, int]) -> None:
    if term.kind == "const":
        constants.add(term.name)
    elif term.kind == "app":
        previous = functions.setdefault(term.name, len(term.args))
        if previous != len(term.args):
            raise CertificateError(f"function {term.name!r} used with inconsistent arity")
    for arg in term.args:
        collect_term_symbols(arg, constants, functions)


def collect_atom_symbols(atom: Term, prop_atoms: set[str], predicates: dict[str, int], constants: set[str], functions: dict[str, int]) -> None:
    if atom.kind == "opaque":
        prop_atoms.add(atom.name)
    elif atom.kind == "pred":
        previous = predicates.setdefault(atom.name, len(atom.args))
        if previous != len(atom.args):
            raise CertificateError(f"predicate {atom.name!r} used with inconsistent arity")
        for arg in atom.args:
            collect_term_symbols(arg, constants, functions)
    elif atom.kind == "eq":
        for arg in atom.args:
            collect_term_symbols(arg, constants, functions)
    else:
        raise CertificateError(f"cannot collect symbols from atom kind {atom.kind!r}")


def certificate_symbol_declarations(clauses: dict[str, tuple[Literal, ...]]) -> list[str]:
    prop_atoms: set[str] = set()
    constants: set[str] = set()
    functions: dict[str, int] = {}
    predicates: dict[str, int] = {}
    for clause in clauses.values():
        for literal in clause:
            collect_atom_symbols(literal.atom, prop_atoms, predicates, constants, functions)
    declarations: list[str] = []
    for name in sorted(prop_atoms):
        declarations.append(f"Variable {require_megalodon_ident(name, 'atom')}:prop.")
    for name in sorted(constants):
        declarations.append(f"Variable {require_megalodon_ident(name, 'constant')}:set.")
    for name, arity in sorted(functions.items()):
        sort = "->".join(["set"] * arity + ["set"])
        declarations.append(f"Variable {require_megalodon_ident(name, 'function')}:{sort}.")
    for name, arity in sorted(predicates.items()):
        sort = "->".join(["set"] * arity + ["prop"])
        declarations.append(f"Variable {require_megalodon_ident(name, 'predicate')}:{sort}.")
    return declarations


def instantiate_proof(proof_name: str, parent_clause: tuple[Literal, ...], substitution: dict[str, Term]) -> str:
    proof = proof_name
    for name in clause_free_vars(parent_clause):
        term = substitution.get(name, Term("var", name))
        proof = f"({proof} {term_text(term)})"
    return proof


def wrap_clause_binders(clause: tuple[Literal, ...], proof: str) -> str:
    for name in reversed(clause_free_vars(clause)):
        proof = f"(fun {require_megalodon_ident(name, 'binder')} :set => {proof})"
    return proof


def emit_megalodon_smoke(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]], theorem_name: str) -> str:
    declarations = certificate_symbol_declarations(clauses)
    if not declarations:
        raise CertificateError("Megalodon smoke elaboration needs at least one declared atom or symbol")
    uses_equality = any(literal.atom.kind == "eq" for clause in clauses.values() for literal in clause)
    lines = [
        "Definition False : prop := forall p:prop, p.",
        "Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.",
        "Infix \\/ 785 left := or.",
    ]
    if uses_equality:
        lines.extend(
            [
                "Definition eq : set->set->prop := fun x y:set => forall Q:set->set->prop, Q x y -> Q y x.",
                "Infix = 502 := eq.",
            ]
        )
    lines.extend(declarations)
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
            assumptions.append((step_id, clause_prop_text(clause)))
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
        elif rule == "substitute":
            parent = step["parents"][0]
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            proof = wrap_clause_binders(clause, instantiate_proof(proof_names[parent], step_clauses[parent], substitution))
        elif rule == "equality_resolution":
            parent = step["parents"][0]
            selected_literal = parse_literal(step["literal"], f"{step_id}.literal")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            proof = wrap_clause_binders(
                clause,
                equality_resolution_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    selected_literal,
                    substitution,
                    clause,
                ),
            )
        elif rule == "paramodulate":
            parents = step["parents"]
            selected_equality = parse_literal(step["equality"], f"{step_id}.equality")
            selected_target = parse_literal(step["target"], f"{step_id}.target")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            position = parse_position(step["position"], f"{step_id}.position")
            proof = wrap_clause_binders(
                clause,
                paramodulation_proof_text(
                    step_clauses[parents[0]],
                    proof_names[parents[0]],
                    step_clauses[parents[1]],
                    proof_names[parents[1]],
                    selected_equality,
                    selected_target,
                    position,
                    substitution,
                    clause,
                ),
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
        derived.append((step_id, clause_prop_text(clause), proof))

    if final_empty is None:
        raise CertificateError("certificate has no empty-clause step to prove False")
    theorem_type = " -> ".join([*(f"({prop})" for _name, prop in assumptions), "False"])
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
