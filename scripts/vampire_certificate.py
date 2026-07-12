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
    "definition_input",
    "substitute",
    "resolve",
    "factor",
    "equality_factoring",
    "equality_resolution",
    "equality_symmetry",
    "paramodulate",
    "paramodulate_all",
    "paramodulate_clause_all",
    "subsumption_resolution",
    "contradiction",
}
RESOLUTION_LIKE_REPLAY_KINDS = {
    "resolution",
    "subsumption_resolution",
    "unit_resulting_resolution",
}
DERIVED_ASSUMPTION_REPLAY_KINDS = {
    "",
    "backward_demodulation",
    "cnf",
    "definition_rewrite",
    "forward_demodulation",
    "generic",
    "generic_clause",
}
PROOF_NAME_COUNTER = itertools.count()


class CertificateError(Exception):
    pass


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
STEP_RE = re.compile(r'^megalodon_step\((\d+),("(?:\\.|[^"\\])*"),("(?:\\.|[^"\\])*"),\[([0-9,]*)\],')
CLAUSE_RE = re.compile(r"^megalodon_certificate_clause\((\d+),(.+)\)\.$")
CERTIFICATE_STEP_RE = re.compile(r"^megalodon_certificate_step\((\d+),(.+)\)\.$")
CERTIFICATE_STEPS_RE = re.compile(r"^megalodon_certificate_steps\((\d+),(.+)\)\.$")
REPLAY_KIND_RE = re.compile(r'^megalodon_step_replay_kind\((\d+),("(?:\\.|[^"\\])*")\)\.$')
FINAL_STEP_RE = re.compile(r"^megalodon_final_step\((\d+)\)\.$")
SYMBOL_DECL_RE = re.compile(r'^megalodon_symbol_declaration\(("(?:\\.|[^"\\])*")\)\.$')
EXTRA_RE = re.compile(r'^megalodon_step_extra\((\d+),("(?:\\.|[^"\\])*"),(\[.*\])\)\.$')


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
    if set(value) == {"apply"}:
        args = value["apply"]
        if not isinstance(args, list) or len(args) != 2:
            raise CertificateError(f"{context}: apply term must contain function and argument")
        return Term("apply", "", (parse_term(args[0], f"{context}.apply[0]"), parse_term(args[1], f"{context}.apply[1]")))
    raise CertificateError(f"{context}: term must contain var, const, app/args, or apply")


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
    if set(value) in ({"eq"}, {"eq", "sort"}):
        args = value["eq"]
        if not isinstance(args, list) or len(args) != 2:
            raise CertificateError(f"{context}: equality atom must contain two terms")
        sort = value.get("sort", "set")
        if not isinstance(sort, str) or not sort:
            raise CertificateError(f"{context}: equality sort must be a non-empty string")
        sort = require_supported_sort(sort, f"{context}.sort")
        return Term("eq", sort, (parse_term(args[0], f"{context}.eq[0]"), parse_term(args[1], f"{context}.eq[1]")))
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


def term_positions_matching(term: Term, needle: Term, prefix: tuple[int, ...] = ()) -> tuple[tuple[int, ...], ...]:
    if term == needle:
        return (prefix,)
    result: list[tuple[int, ...]] = []
    for index, arg in enumerate(term.args):
        result.extend(term_positions_matching(arg, needle, (*prefix, index)))
    return tuple(result)


def replace_all_terms(term: Term, needle: Term, replacement: Term) -> Term:
    if term == needle:
        return replacement
    if not term.args:
        return term
    return Term(term.kind, term.name, tuple(replace_all_terms(arg, needle, replacement) for arg in term.args))


def is_reflexive_equality_atom(atom: Term) -> bool:
    return atom.kind == "eq" and len(atom.args) == 2 and atom.args[0] == atom.args[1]


def swap_equality_literal(literal: Literal) -> Literal:
    if literal.atom.kind != "eq" or len(literal.atom.args) != 2:
        raise CertificateError("selected literal is not an equality")
    return Literal(literal.polarity, Term("eq", literal.atom.name, (literal.atom.args[1], literal.atom.args[0])))


def equality_symmetric_match(left: Literal, right: Literal) -> bool:
    if left == right:
        return True
    if left.atom.kind != "eq":
        return False
    try:
        return swap_equality_literal(left) == right
    except CertificateError:
        return False


def require_megalodon_ident(name: str, context: str) -> str:
    if not IDENT_RE.fullmatch(name):
        raise CertificateError(f"{context}: {name!r} is not a supported Megalodon identifier")
    return name


def strip_enclosing_sort_parens(sort: str) -> str:
    sort = sort.strip()
    while sort.startswith("(") and sort.endswith(")"):
        depth = 0
        encloses_all = True
        for index, char in enumerate(sort):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    raise CertificateError(f"sort: unbalanced parentheses in {sort!r}")
                if depth == 0 and index != len(sort) - 1:
                    encloses_all = False
                    break
        if depth != 0:
            raise CertificateError(f"sort: unbalanced parentheses in {sort!r}")
        if not encloses_all:
            break
        sort = sort[1:-1].strip()
    return sort


def split_sort(sort: str) -> tuple[str, ...]:
    sort = strip_enclosing_sort_parens(sort)
    parts: list[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(sort):
        char = sort[index]
        if char == "(":
            depth += 1
            index += 1
            continue
        if char == ")":
            depth -= 1
            if depth < 0:
                raise CertificateError(f"sort: unbalanced parentheses in {sort!r}")
            index += 1
            continue
        if char == "-" and index + 1 < len(sort) and sort[index + 1] == ">" and depth == 0:
            part = sort[start:index].strip()
            if not part:
                raise CertificateError(f"sort: empty arrow component in {sort!r}")
            parts.append(part)
            index += 2
            start = index
            continue
        index += 1
    if depth != 0:
        raise CertificateError(f"sort: unbalanced parentheses in {sort!r}")
    part = sort[start:].strip()
    if not part:
        raise CertificateError(f"sort: empty arrow component in {sort!r}")
    parts.append(part)
    return tuple(parts)


def normalize_sort(sort: str, context: str) -> str:
    sort = strip_enclosing_sort_parens(sort)
    parts = split_sort(sort)
    if len(parts) == 1:
        atom = strip_enclosing_sort_parens(parts[0])
        if atom not in {"set", "prop"}:
            raise CertificateError(f"{context}: unsupported sort {sort!r}")
        return atom
    normalized_parts = [normalize_sort(part, context) for part in parts]
    rendered_parts = [
        f"({part})" if "->" in part else part
        for part in normalized_parts
    ]
    return "->".join(rendered_parts)


def require_supported_sort(sort: str, context: str) -> str:
    return normalize_sort(sort, context)


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


def term_to_json(term: Term) -> Any:
    if term.kind == "var":
        return {"var": term.name}
    if term.kind == "const":
        return {"const": term.name}
    if term.kind == "app":
        return {"app": term.name, "args": [term_to_json(arg) for arg in term.args]}
    if term.kind == "apply":
        return {"apply": [term_to_json(term.args[0]), term_to_json(term.args[1])]}
    if term.kind == "pred":
        return {"pred": term.name, "args": [term_to_json(arg) for arg in term.args]}
    if term.kind == "eq":
        result = {"eq": [term_to_json(term.args[0]), term_to_json(term.args[1])]}
        if term.name != "set":
            result["sort"] = term.name
        return result
    if term.kind == "opaque":
        return term.name
    raise CertificateError(f"cannot serialize term kind {term.kind!r}")


def literal_to_json(literal: Literal) -> dict[str, Any]:
    return {"polarity": literal.polarity, "atom": term_to_json(literal.atom)}


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

        elif rule == "definition_input":
            allowed = {"id", "rule", "clause", "symbol", "sort", "value", "source"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            symbol = step["symbol"]
            sort = step["sort"]
            if not isinstance(symbol, str):
                raise CertificateError(f"{step_id}: definition symbol must be a string")
            require_megalodon_ident(symbol, f"{step_id}.symbol")
            if not isinstance(sort, str):
                raise CertificateError(f"{step_id}: definition sort must be a string")
            sort = require_supported_sort(sort, f"{step_id}.sort")
            value = parse_term(step["value"], f"{step_id}.value")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            expected_left = Literal(True, Term("eq", sort, (value, Term("const", symbol))))
            expected_right = Literal(True, Term("eq", sort, (Term("const", symbol), value)))
            if clause not in {(expected_left,), (expected_right,)}:
                raise CertificateError(f"{step_id}: definition_input clause must define the introduced symbol")

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

        elif rule == "equality_factoring":
            allowed = {"id", "rule", "parents", "selected", "other", "selected_lhs", "other_rhs", "substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            selected = parse_literal(step["selected"], f"{step_id}.selected")
            other = parse_literal(step["other"], f"{step_id}.other")
            if selected not in parent_clause:
                raise CertificateError(f"{step_id}: selected equality not present in parent")
            if other not in parent_clause:
                raise CertificateError(f"{step_id}: other equality not present in parent")
            if not selected.polarity or not other.polarity:
                raise CertificateError(f"{step_id}: equality-factoring literals must be positive")
            if selected.atom.kind != "eq" or other.atom.kind != "eq":
                raise CertificateError(f"{step_id}: equality-factoring literals must be equalities")
            if len(selected.atom.args) != 2 or len(other.atom.args) != 2:
                raise CertificateError(f"{step_id}: equality-factoring equalities must be binary")
            selected_lhs = parse_term(step["selected_lhs"], f"{step_id}.selected_lhs")
            other_rhs = parse_term(step["other_rhs"], f"{step_id}.other_rhs")
            if selected_lhs == selected.atom.args[0]:
                selected_rhs = selected.atom.args[1]
            elif selected_lhs == selected.atom.args[1]:
                selected_rhs = selected.atom.args[0]
            else:
                raise CertificateError(f"{step_id}: selected_lhs is not a side of the selected equality")
            if other_rhs == other.atom.args[0]:
                other_lhs = other.atom.args[1]
            elif other_rhs == other.atom.args[1]:
                other_lhs = other.atom.args[0]
            else:
                raise CertificateError(f"{step_id}: other_rhs is not a side of the other equality")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            selected_lhs_subst = substitute_term(selected_lhs, substitution)
            other_lhs_subst = substitute_term(other_lhs, substitution)
            if selected_lhs_subst != other_lhs_subst:
                raise CertificateError(f"{step_id}: selected_lhs and other_lhs do not match after substitution")
            selected_rhs_subst = substitute_term(selected_rhs, substitution)
            other_rhs_subst = substitute_term(other_rhs, substitution)
            if selected.atom.name != other.atom.name:
                raise CertificateError(f"{step_id}: equality-factoring equalities have different sorts")
            introduced = Literal(False, Term("eq", selected.atom.name, (selected_rhs_subst, other_rhs_subst)))
            expected = normalize_clause(
                tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(parent_clause, selected)
                )
                + (introduced,)
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: equality-factoring conclusion does not match parent")

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

        elif rule == "equality_symmetry":
            allowed = {"id", "rule", "parents", "literal", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            literal = parse_literal(step["literal"], f"{step_id}.literal")
            if literal not in parent_clause:
                raise CertificateError(f"{step_id}: equality-symmetry literal not present in parent")
            swapped = swap_equality_literal(literal)
            expected = normalize_clause(clause_without_one(parent_clause, literal) + (swapped,))
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: equality-symmetry conclusion does not match parent")

        elif rule == "subsumption_resolution":
            allowed = {"id", "rule", "parents", "selected", "side_pivot", "side_substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 2)
            main_parent = clauses.get(parents[0])
            side_parent = clauses.get(parents[1])
            if main_parent is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            if side_parent is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[1]}")
            selected = parse_literal(step["selected"], f"{step_id}.selected")
            if selected not in main_parent:
                raise CertificateError(f"{step_id}: selected literal not present in main parent")
            side_substitution = parse_substitution(step["side_substitution"], f"{step_id}.side_substitution")
            side_pivot = parse_literal(step["side_pivot"], f"{step_id}.side_pivot")
            if side_pivot.complement != selected:
                raise CertificateError(f"{step_id}: side pivot is not the complement of the selected literal")
            instantiated_side = normalize_clause(tuple(substitute_literal(literal, side_substitution) for literal in side_parent))
            pivot_indexes = [
                index
                for index, literal in enumerate(instantiated_side)
                if equality_symmetric_match(literal, side_pivot)
            ]
            if not pivot_indexes:
                raise CertificateError(f"{step_id}: side pivot is not present after substitution")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            expected = normalize_clause(clause_without_one(main_parent, selected))
            if clause != expected:
                raise CertificateError(f"{step_id}: subsumption-resolution conclusion does not match main parent")
            covered = False
            for pivot_index in pivot_indexes:
                side_remainder = [
                    literal
                    for index, literal in enumerate(instantiated_side)
                    if index != pivot_index
                ]
                if all(
                    any(equality_symmetric_match(literal, conclusion_literal) for conclusion_literal in clause)
                    for literal in side_remainder
                ):
                    covered = True
                    break
            if not covered:
                raise CertificateError(f"{step_id}: side remainder literals are not covered by conclusion")

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

        elif rule == "paramodulate_all":
            allowed = {"id", "rule", "parents", "equality", "from", "to", "target", "positions", "substitution", "clause"}
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
            if not isinstance(step["positions"], list):
                raise CertificateError(f"{step_id}.positions: positions must be a list")
            positions = tuple(parse_position(item, f"{step_id}.positions[{index}]") for index, item in enumerate(step["positions"]))
            selected_target = substitute_literal(target, substitution)
            expected_positions = term_positions_matching(selected_target.atom, from_term)
            if sorted(positions) != sorted(expected_positions) or not positions:
                raise CertificateError(f"{step_id}: positions do not match all selected redex occurrences")
            rewritten_target = Literal(
                selected_target.polarity,
                replace_all_terms(selected_target.atom, from_term, to_term),
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
                raise CertificateError(f"{step_id}: simultaneous paramodulation conclusion does not match parents")

        elif rule == "paramodulate_clause_all":
            allowed = {"id", "rule", "parents", "equality", "from", "to", "target_rewrites", "substitution", "clause"}
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
            if equality not in equality_parent:
                raise CertificateError(f"{step_id}: equality literal not present in equality parent")
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
            if not isinstance(step["target_rewrites"], list):
                raise CertificateError(f"{step_id}.target_rewrites: target rewrites must be a list")
            rewrite_positions: dict[Literal, tuple[tuple[int, ...], ...]] = {}
            for index, item in enumerate(step["target_rewrites"]):
                if not isinstance(item, dict) or set(item) != {"literal", "positions"}:
                    raise CertificateError(f"{step_id}.target_rewrites[{index}]: expected literal and positions")
                literal = parse_literal(item["literal"], f"{step_id}.target_rewrites[{index}].literal")
                if literal not in target_parent:
                    raise CertificateError(f"{step_id}.target_rewrites[{index}]: literal not present in target parent")
                if literal in rewrite_positions:
                    raise CertificateError(f"{step_id}.target_rewrites[{index}]: duplicate rewritten literal")
                if not isinstance(item["positions"], list):
                    raise CertificateError(f"{step_id}.target_rewrites[{index}].positions: positions must be a list")
                positions = tuple(
                    parse_position(pos, f"{step_id}.target_rewrites[{index}].positions[{pos_index}]")
                    for pos_index, pos in enumerate(item["positions"])
                )
                if not positions:
                    raise CertificateError(f"{step_id}.target_rewrites[{index}]: positions must be nonempty")
                rewrite_positions[literal] = positions

            rewritten_target_literals: list[Literal] = []
            for literal in target_parent:
                selected_target = substitute_literal(literal, substitution)
                expected_positions = term_positions_matching(selected_target.atom, from_term)
                positions = rewrite_positions.pop(literal, ())
                if sorted(positions) != sorted(expected_positions):
                    raise CertificateError(f"{step_id}: target rewrite positions do not match all redex occurrences")
                if expected_positions:
                    rewritten_target_literals.append(
                        Literal(selected_target.polarity, replace_all_terms(selected_target.atom, from_term, to_term))
                    )
                else:
                    rewritten_target_literals.append(selected_target)
            if rewrite_positions:
                raise CertificateError(f"{step_id}: target rewrite literal not consumed")

            expected = normalize_clause(
                tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(equality_parent, equality)
                )
                + tuple(rewritten_target_literals)
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: clause-wide simultaneous paramodulation conclusion does not match parents")

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


def parse_outline_parents(value: str, context: str) -> list[int]:
    if not value:
        return []
    result: list[int] = []
    for item in value.split(","):
        if not item.isdigit():
            raise CertificateError(f"{context}: unsupported parent list {value!r}")
        result.append(int(item))
    return result


def infer_resolution_pivot(
    step_id: str,
    left: tuple[Literal, ...],
    right: tuple[Literal, ...],
    conclusion: tuple[Literal, ...],
) -> Literal:
    candidates: list[Literal] = []
    for literal in left:
        if literal.complement not in right:
            continue
        expected = normalize_clause(
            clause_without_one(left, literal)
            + clause_without_one(right, literal.complement)
        )
        if expected == normalize_clause(conclusion):
            candidates.append(literal)
    unique = sorted(set(candidates))
    if len(unique) != 1:
        raise CertificateError(f"{step_id}: expected a unique resolution pivot, found {len(unique)}")
    return unique[0]


def term_positions(term: Term) -> tuple[tuple[int, ...], ...]:
    result: list[tuple[int, ...]] = [()]
    for index, arg in enumerate(term.args):
        result.extend((index, *position) for position in term_positions(arg))
    return tuple(result)


def infer_paramodulation_step(
    step_id: str,
    parent_numbers: list[int],
    clauses: dict[int, tuple[Literal, ...]],
    conclusion: tuple[Literal, ...],
    conclusion_json: list[Any],
) -> dict[str, Any] | None:
    candidates: list[dict[str, Any]] = []
    for equality_parent_no in parent_numbers:
        equality_parent = clauses[equality_parent_no]
        for target_parent_no in parent_numbers:
            if target_parent_no == equality_parent_no:
                continue
            target_parent = clauses[target_parent_no]
            for equality in equality_parent:
                if not equality.polarity or equality.atom.kind != "eq" or len(equality.atom.args) != 2:
                    continue
                from_term, to_term = equality.atom.args
                for target in target_parent:
                    for position in term_positions(target.atom):
                        try:
                            if term_at_position(target.atom, position, f"{step_id}.candidate") != from_term:
                                continue
                            rewritten_target = Literal(
                                target.polarity,
                                replace_term_at_position(target.atom, position, to_term, f"{step_id}.candidate"),
                            )
                            expected = normalize_clause(
                                clause_without_one(equality_parent, equality)
                                + clause_without_one(target_parent, target)
                                + (rewritten_target,)
                            )
                        except CertificateError:
                            continue
                        if expected == normalize_clause(conclusion):
                            candidates.append(
                                {
                                    "id": step_id,
                                    "rule": "paramodulate",
                                    "parents": [f"u{equality_parent_no}", f"u{target_parent_no}"],
                                    "equality": literal_to_json(equality),
                                    "from": term_to_json(from_term),
                                    "to": term_to_json(to_term),
                                    "target": literal_to_json(target),
                                    "position": list(position),
                                    "substitution": {},
                                    "clause": conclusion_json,
                                }
                            )
    unique = sorted(candidates, key=lambda item: json.dumps(item, sort_keys=True))
    if len(unique) == 1:
        return unique[0]
    return None


def infer_paramodulation_then_symmetry_steps(
    step_id: str,
    parent_numbers: list[int],
    clauses: dict[int, tuple[Literal, ...]],
    conclusion: tuple[Literal, ...],
) -> tuple[list[dict[str, Any]], tuple[Literal, ...]] | None:
    for equality_parent_no in parent_numbers:
        equality_parent = clauses[equality_parent_no]
        for target_parent_no in parent_numbers:
            if target_parent_no == equality_parent_no:
                continue
            target_parent = clauses[target_parent_no]
            for equality in equality_parent:
                if not equality.polarity or equality.atom.kind != "eq" or len(equality.atom.args) != 2:
                    continue
                from_term, to_term = equality.atom.args
                for target in target_parent:
                    for position in term_positions(target.atom):
                        try:
                            if term_at_position(target.atom, position, f"{step_id}.candidate") != from_term:
                                continue
                            rewritten_target = Literal(
                                target.polarity,
                                replace_term_at_position(target.atom, position, to_term, f"{step_id}.candidate"),
                            )
                            param_clause = normalize_clause(
                                clause_without_one(equality_parent, equality)
                                + clause_without_one(target_parent, target)
                                + (rewritten_target,)
                            )
                            symmetric_clause = normalize_clause(
                                clause_without_one(param_clause, rewritten_target)
                                + (swap_equality_literal(rewritten_target),)
                            )
                        except CertificateError:
                            continue
                        if symmetric_clause != normalize_clause(conclusion):
                            continue
                        param_step_id = f"{step_id}_paramodulate"
                        return (
                            [
                                {
                                    "id": param_step_id,
                                    "rule": "paramodulate",
                                    "parents": [f"u{equality_parent_no}", f"u{target_parent_no}"],
                                    "equality": literal_to_json(equality),
                                    "from": term_to_json(from_term),
                                    "to": term_to_json(to_term),
                                    "target": literal_to_json(target),
                                    "position": list(position),
                                    "substitution": {},
                                    "clause": [literal_to_json(literal) for literal in param_clause],
                                },
                                {
                                    "id": step_id,
                                    "rule": "equality_symmetry",
                                    "parents": [param_step_id],
                                    "literal": literal_to_json(rewritten_target),
                                    "clause": [literal_to_json(literal) for literal in conclusion],
                                },
                            ],
                            param_clause,
                        )
    return None


def extra_field(fields: list[str], name: str) -> str | None:
    prefix = name + "="
    for field in fields:
        if field.startswith(prefix):
            return field[len(prefix):]
    return None


def infer_definition_input_step(
    step_id: str,
    clause: tuple[Literal, ...],
    clause_json: list[Any],
    fields: list[str],
) -> dict[str, Any] | None:
    introduced = extra_field(fields, "introduced_symbol")
    sort = extra_field(fields, "sort")
    if introduced is None or sort is None or len(clause) != 1:
        return None
    literal = clause[0]
    if not literal.polarity or literal.atom.kind != "eq" or literal.atom.name != sort or len(literal.atom.args) != 2:
        return None
    left, right = literal.atom.args
    symbol = Term("const", introduced)
    if right == symbol:
        value = left
    elif left == symbol:
        value = right
    else:
        return None
    return {
        "id": step_id,
        "rule": "definition_input",
        "clause": clause_json,
        "symbol": introduced,
        "sort": sort,
        "value": term_to_json(value),
        "source": {
            "kind": "vampire_function_definition",
            "name": step_id,
        },
    }


def certificate_from_vampire_outline(text: str, problem: str) -> dict[str, Any]:
    step_meta: dict[int, dict[str, Any]] = {}
    clause_json: dict[int, list[Any]] = {}
    certificate_steps: dict[int, dict[str, Any]] = {}
    certificate_step_lists: dict[int, list[dict[str, Any]]] = {}
    replay_kinds: dict[int, str] = {}
    extras: dict[int, dict[str, list[str]]] = {}
    declarations: list[str] = []
    final_step: int | None = None

    for lineno, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        match = STEP_RE.match(line)
        if match:
            step_no = int(match.group(1))
            rule = json.loads(match.group(2))
            kind = json.loads(match.group(3))
            parents = parse_outline_parents(match.group(4), f"line {lineno}")
            step_meta[step_no] = {"rule": rule, "kind": kind, "parents": parents}
            continue
        match = CLAUSE_RE.match(line)
        if match:
            step_no = int(match.group(1))
            try:
                clause_value = json.loads(match.group(2))
            except json.JSONDecodeError as exc:
                raise CertificateError(f"line {lineno}: malformed certificate clause JSON: {exc}") from exc
            if not isinstance(clause_value, list):
                raise CertificateError(f"line {lineno}: certificate clause must be a JSON list")
            clause_json[step_no] = clause_value
            continue
        match = CERTIFICATE_STEP_RE.match(line)
        if match:
            step_no = int(match.group(1))
            try:
                step_value = json.loads(match.group(2))
            except json.JSONDecodeError as exc:
                raise CertificateError(f"line {lineno}: malformed certificate step JSON: {exc}") from exc
            if not isinstance(step_value, dict):
                raise CertificateError(f"line {lineno}: certificate step must be a JSON object")
            rule = step_value.get("rule")
            if not isinstance(rule, str) or rule not in MVP_RULES:
                raise CertificateError(f"line {lineno}: unsupported explicit certificate step rule {rule!r}")
            certificate_steps[step_no] = step_value
            continue
        match = CERTIFICATE_STEPS_RE.match(line)
        if match:
            step_no = int(match.group(1))
            try:
                step_values = json.loads(match.group(2))
            except json.JSONDecodeError as exc:
                raise CertificateError(f"line {lineno}: malformed certificate steps JSON: {exc}") from exc
            if not isinstance(step_values, list) or not all(isinstance(item, dict) for item in step_values):
                raise CertificateError(f"line {lineno}: certificate steps must be a JSON object list")
            for index, step_value in enumerate(step_values):
                rule = step_value.get("rule")
                if not isinstance(rule, str) or rule not in MVP_RULES:
                    raise CertificateError(
                        f"line {lineno}: unsupported explicit certificate step rule at index {index}: {rule!r}"
                    )
            certificate_step_lists[step_no] = step_values
            continue
        match = REPLAY_KIND_RE.match(line)
        if match:
            replay_kinds[int(match.group(1))] = json.loads(match.group(2))
            continue
        match = EXTRA_RE.match(line)
        if match:
            step_no = int(match.group(1))
            kind = json.loads(match.group(2))
            try:
                fields = json.loads(match.group(3))
            except json.JSONDecodeError as exc:
                raise CertificateError(f"line {lineno}: malformed step-extra JSON: {exc}") from exc
            if not isinstance(fields, list) or not all(isinstance(field, str) for field in fields):
                raise CertificateError(f"line {lineno}: step-extra fields must be a string list")
            extras.setdefault(step_no, {})[kind] = fields
            continue
        match = FINAL_STEP_RE.match(line)
        if match:
            final_step = int(match.group(1))
            continue
        match = SYMBOL_DECL_RE.match(line)
        if match:
            declarations.append(json.loads(match.group(1)))

    if not clause_json:
        raise CertificateError("Vampire outline contains no megalodon_certificate_clause records")

    steps: list[dict[str, Any]] = []
    clauses: dict[int, tuple[Literal, ...]] = {}
    for step_no in sorted(clause_json):
        meta = step_meta.get(step_no)
        if meta is None:
            raise CertificateError(f"u{step_no}: missing megalodon_step metadata")
        clause = normalize_clause(parse_clause(clause_json[step_no], f"u{step_no}.clause"))
        parent_clause_numbers = [parent for parent in meta["parents"] if parent in clauses]
        replay_kind = replay_kinds.get(step_no, "")
        step_id = f"u{step_no}"

        explicit_steps = certificate_step_lists.get(step_no)
        explicit_step = certificate_steps.get(step_no)
        if explicit_steps is not None:
            for index, explicit in enumerate(explicit_steps):
                step = dict(explicit)
                if "id" not in step and index == len(explicit_steps) - 1:
                    step["id"] = step_id
                if "clause" not in step and index == len(explicit_steps) - 1:
                    step["clause"] = clause_json[step_no]
                if "id" not in step or "clause" not in step:
                    raise CertificateError(f"{step_id}: explicit certificate substep {index} needs id and clause")
                steps.append(step)
            clauses[step_no] = clause
            continue
        if explicit_step is not None:
            step = dict(explicit_step)
            step["id"] = step_id
            step["clause"] = clause_json[step_no]
            steps.append(step)
            clauses[step_no] = clause
            continue

        definition_input = infer_definition_input_step(
            step_id,
            clause,
            clause_json[step_no],
            extras.get(step_no, {}).get("function_definition", []),
        )

        if definition_input is not None:
            steps.append(definition_input)
        elif replay_kind in RESOLUTION_LIKE_REPLAY_KINDS:
            if len(parent_clause_numbers) != 2:
                raise CertificateError(
                    f"{step_id}: {replay_kind} bridge requires exactly two printed clause parents"
                )
            left_no, right_no = parent_clause_numbers
            pivot = infer_resolution_pivot(step_id, clauses[left_no], clauses[right_no], clause)
            steps.append(
                {
                    "id": step_id,
                    "rule": "resolve",
                    "parents": [f"u{left_no}", f"u{right_no}"],
                    "pivot": literal_to_json(pivot),
                    "clause": clause_json[step_no],
                }
            )
        elif replay_kind in {"forward_demodulation", "backward_demodulation", "definition_rewrite"}:
            paramodulation = infer_paramodulation_step(step_id, parent_clause_numbers, clauses, clause, clause_json[step_no])
            if paramodulation is not None:
                steps.append(paramodulation)
            else:
                paramodulation_with_symmetry = infer_paramodulation_then_symmetry_steps(step_id, parent_clause_numbers, clauses, clause)
                if paramodulation_with_symmetry is not None:
                    inferred_steps, _intermediate_clause = paramodulation_with_symmetry
                    steps.extend(inferred_steps)
                else:
                    source_kind = "vampire_input_clause" if not meta["parents"] else "vampire_derived_clause"
                    steps.append(
                        {
                            "id": step_id,
                            "rule": "input",
                            "clause": clause_json[step_no],
                            "source": {
                                "kind": source_kind,
                                "name": step_id,
                                "vampire_rule": meta["rule"],
                                "vampire_parents": [f"u{parent}" for parent in meta["parents"]],
                            },
                        }
                    )
        elif not parent_clause_numbers or replay_kind in DERIVED_ASSUMPTION_REPLAY_KINDS:
            source_kind = "vampire_input_clause" if not meta["parents"] else "vampire_derived_clause"
            steps.append(
                {
                    "id": step_id,
                    "rule": "input",
                    "clause": clause_json[step_no],
                    "source": {
                        "kind": source_kind,
                        "name": step_id,
                        "vampire_rule": meta["rule"],
                        "vampire_parents": [f"u{parent}" for parent in meta["parents"]],
                    },
                }
            )
        else:
            raise CertificateError(f"{step_id}: unsupported outline clause rule {replay_kind or meta['rule']!r}")

        clauses[step_no] = clause

    if final_step is not None and final_step in clauses and clauses[final_step]:
        raise CertificateError(f"u{final_step}: final Vampire step is not an empty clause")

    result = {
        "format": FORMAT,
        "version": VERSION,
        "problem": problem,
        "steps": steps,
    }
    if declarations:
        result["declarations"] = sorted(set(declarations))
    return result


def term_text(term: Term) -> str:
    if term.kind in {"var", "const"}:
        return require_megalodon_ident(term.name, "term")
    if term.kind == "app":
        name = require_megalodon_ident(term.name, "term")
        args = " ".join(term_text(arg) for arg in term.args)
        return f"({name} {args})" if args else name
    if term.kind == "apply":
        return f"({term_text(term.args[0])} {term_text(term.args[1])})"
    raise CertificateError(f"cannot render term kind {term.kind!r}")


def equality_symbol(sort: str) -> str:
    require_supported_sort(sort, "equality sort")
    if sort == "set":
        return "eq"
    if sort == "prop":
        return "vampire_eq_prop"
    return "vampire_eq_" + sort.replace("->", "_to_")


def sort_type_text(sort: str) -> str:
    require_supported_sort(sort, "sort")
    if "->" in sort:
        return f"({sort})"
    return sort


def equality_definition(sort: str) -> str:
    symbol = equality_symbol(sort)
    if sort == "set":
        return "Definition eq : set->set->prop := fun x y:set => forall Q:set->set->prop, Q x y -> Q y x."
    sort_text = sort_type_text(sort)
    return f"Definition {symbol} : {sort_text}->{sort_text}->prop := fun x y:{sort_text} => forall Q:{sort_text}->prop, Q x -> Q y."


def atom_text(atom: Term) -> str:
    if atom.kind == "opaque":
        return require_megalodon_ident(atom.name, "atom")
    if atom.kind == "pred":
        name = require_megalodon_ident(atom.name, "atom")
        args = " ".join(term_text(arg) for arg in atom.args)
        return f"({name} {args})" if args else name
    if atom.kind == "eq" and len(atom.args) == 2:
        if atom.name != "set":
            return f"({equality_symbol(atom.name)} {term_text(atom.args[0])} {term_text(atom.args[1])})"
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


def declaration_symbol_sorts(declarations: list[str]) -> dict[str, tuple[str, ...]]:
    result: dict[str, tuple[str, ...]] = {}
    for declaration in declarations:
        match = re.fullmatch(r"Variable ([A-Za-z_][A-Za-z0-9_']*):(.+)\.", declaration)
        if match is None:
            continue
        result[match.group(1)] = split_sort(require_supported_sort(match.group(2), f"declaration sort for {match.group(1)}"))
    return result


def merge_var_sort(var_sorts: dict[str, str], name: str, sort: str) -> None:
    sort = require_supported_sort(sort, f"sort for {name}")
    previous = var_sorts.get(name)
    if previous is None:
        var_sorts[name] = sort
    elif previous != sort:
        raise CertificateError(f"variable {name!r} used at incompatible sorts {previous!r} and {sort!r}")


def term_spine(term: Term) -> tuple[Term, list[Term]]:
    args: list[Term] = []
    current = term
    while current.kind == "apply" and len(current.args) == 2:
        args.append(current.args[1])
        current = current.args[0]
    if current.kind == "app":
        args.extend(reversed(current.args))
        current = Term("const", current.name)
    args.reverse()
    return current, args


def collect_term_var_sorts(term: Term, expected_sort: str, symbol_sorts: dict[str, tuple[str, ...]], var_sorts: dict[str, str]) -> None:
    if term.kind == "var":
        merge_var_sort(var_sorts, term.name, expected_sort)
        return
    head, args = term_spine(term)
    if head.kind == "var" and args:
        merge_var_sort(var_sorts, head.name, "->".join(["set"] * len(args) + [expected_sort]))
    if head.kind == "const" and args:
        signature = symbol_sorts.get(head.name)
        if signature is not None and len(signature) >= len(args) + 1:
            for arg, arg_sort in zip(args, signature):
                collect_term_var_sorts(arg, arg_sort, symbol_sorts, var_sorts)
            return
    for arg in term.args:
        collect_term_var_sorts(arg, "set", symbol_sorts, var_sorts)


def collect_atom_var_sorts(atom: Term, symbol_sorts: dict[str, tuple[str, ...]], var_sorts: dict[str, str]) -> None:
    if atom.kind == "eq" and len(atom.args) == 2:
        for arg in atom.args:
            collect_term_var_sorts(arg, atom.name, symbol_sorts, var_sorts)
        return
    if atom.kind == "pred":
        signature = symbol_sorts.get(atom.name)
        arg_sorts = signature[:-1] if signature is not None and len(signature) == len(atom.args) + 1 else ("set",) * len(atom.args)
        for arg, arg_sort in zip(atom.args, arg_sorts):
            collect_term_var_sorts(arg, arg_sort, symbol_sorts, var_sorts)
        return
    for arg in atom.args:
        collect_term_var_sorts(arg, "set", symbol_sorts, var_sorts)


def clause_var_sorts(clause: tuple[Literal, ...], symbol_sorts: dict[str, tuple[str, ...]]) -> dict[str, str]:
    var_sorts: dict[str, str] = {}
    for literal in clause:
        collect_atom_var_sorts(literal.atom, symbol_sorts, var_sorts)
    for name in clause_free_vars(clause):
        var_sorts.setdefault(name, "set")
    return var_sorts


def clause_prop_text(clause: tuple[Literal, ...], symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    symbol_sorts = symbol_sorts or {}
    result = clause_body_text(clause)
    var_sorts = clause_var_sorts(clause, symbol_sorts)
    for name in reversed(clause_free_vars(clause)):
        result = f"forall {require_megalodon_ident(name, 'binder')}:{sort_type_text(var_sorts[name])}, {result}"
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


def positive_equality_symmetry_proof(literal: Literal, proof: str) -> str:
    if not literal.polarity or literal.atom.kind != "eq" or len(literal.atom.args) != 2:
        raise CertificateError("equality symmetry needs a positive equality proof")
    left = term_text(literal.atom.args[0])
    right = term_text(literal.atom.args[1])
    if literal.atom.name == "prop":
        return f"(fun Q:prop->prop => fun H:Q {right} => ({proof} (fun cert_z:prop => Q cert_z -> Q {left}) (fun Hx => Hx) H))"
    if literal.atom.name == "set":
        return f"(fun Q:set->set->prop => fun H:Q {right} {left} => ({proof} (fun cert_x cert_y:set => Q cert_y cert_x) H))"
    raise CertificateError(f"unsupported equality symmetry sort {literal.atom.name!r}")


def equality_symmetry_literal_proof(literal: Literal, proof: str) -> str:
    if literal.polarity:
        return positive_equality_symmetry_proof(literal, proof)
    positive_swapped = Literal(True, swap_equality_literal(literal).atom)
    swapped_proof = fresh_proof_name("Hsym")
    positive_original = positive_equality_symmetry_proof(positive_swapped, swapped_proof)
    return f"(fun {swapped_proof} => ({proof} {positive_original}))"


def fresh_proof_name(prefix: str) -> str:
    return f"{prefix}_{next(PROOF_NAME_COUNTER)}"


def eliminate_clause_proof(
    clause: tuple[Literal, ...],
    proof: str,
    goal: str,
    branch_proof,
) -> str:
    if not clause:
        return f"({proof} {goal})"
    if len(clause) == 1:
        return branch_proof(clause[0], proof)
    head = clause[0]
    tail = tuple(clause[1:])
    head_proof = fresh_proof_name("Hlit")
    tail_proof = fresh_proof_name("Htail")
    return (
        f"({proof} {goal} "
        f"(fun {head_proof} => {branch_proof(head, head_proof)}) "
        f"(fun {tail_proof} => {eliminate_clause_proof(tail, tail_proof, goal, branch_proof)}))"
    )


def reorder_clause_proof_text(source_clause: tuple[Literal, ...], source_proof: str, target_clause: tuple[Literal, ...]) -> str:
    if normalize_clause(source_clause) != normalize_clause(target_clause):
        raise CertificateError("cannot reorder non-equivalent clauses")
    goal = clause_body_text(target_clause)
    return eliminate_clause_proof(
        source_clause,
        source_proof,
        goal,
        lambda literal, proof: intro_literal_proof(literal, target_clause, proof),
    )


def resolve_proof_text(
    left_clause: tuple[Literal, ...],
    left_proof: str,
    right_clause: tuple[Literal, ...],
    right_proof: str,
    pivot: Literal,
    conclusion: tuple[Literal, ...],
) -> str:
    conclusion_vars = set(clause_free_vars(conclusion))
    parent_vars = set(clause_free_vars(left_clause)) | set(clause_free_vars(right_clause))
    uncovered_vars = sorted(parent_vars - conclusion_vars)
    if uncovered_vars:
        raise CertificateError(
            "Megalodon smoke resolution elaboration has parent variables not bound by conclusion: "
            + ", ".join(uncovered_vars)
        )
    left_proof = instantiate_proof(left_proof, left_clause, {})
    right_proof = instantiate_proof(right_proof, right_clause, {})
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
    conclusion_vars = set(clause_free_vars(conclusion))
    parent_vars = set(clause_free_vars(instantiated_parent))
    uncovered_vars = sorted(parent_vars - conclusion_vars)
    if uncovered_vars:
        raise CertificateError(
            "Megalodon smoke equality-resolution elaboration has parent variables not bound by conclusion: "
            + ", ".join(uncovered_vars)
        )
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution)
    goal = clause_body_text(conclusion)
    reflexive_false = lambda proof: f"({proof} {equality_refl_proof()})"

    def branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_selected:
            false_proof = reflexive_false(proof)
            return f"({false_proof} {goal})"
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def positive_equality_trans_proof(left_eq: Literal, left_proof: str, right_eq: Literal, right_proof: str) -> str:
    if (
        not left_eq.polarity
        or not right_eq.polarity
        or left_eq.atom.kind != "eq"
        or right_eq.atom.kind != "eq"
        or len(left_eq.atom.args) != 2
        or len(right_eq.atom.args) != 2
        or left_eq.atom.name != right_eq.atom.name
    ):
        raise CertificateError("equality transitivity needs positive equalities of the same sort")
    if left_eq.atom.args[1] != right_eq.atom.args[0]:
        raise CertificateError("equality transitivity middle terms do not match")
    if left_eq.atom.name == "set":
        raise CertificateError("Megalodon smoke equality-factoring for set equality is not implemented yet")
    sort_text = sort_type_text(left_eq.atom.name)
    left = term_text(left_eq.atom.args[0])
    return f"(fun Q:{sort_text}->prop => fun H:Q {left} => ({right_proof} Q ({left_proof} Q H)))"


def equality_factoring_proof_text(
    parent_clause: tuple[Literal, ...],
    parent_proof: str,
    selected: Literal,
    other: Literal,
    selected_lhs: Term,
    other_rhs: Term,
    substitution: dict[str, Term],
    conclusion: tuple[Literal, ...],
) -> str:
    instantiated_parent = tuple(substitute_literal(literal, substitution) for literal in parent_clause)
    instantiated_selected = substitute_literal(selected, substitution)
    instantiated_other = substitute_literal(other, substitution)
    selected_lhs_subst = substitute_term(selected_lhs, substitution)
    if selected_lhs == selected.atom.args[0]:
        selected_rhs = selected.atom.args[1]
    elif selected_lhs == selected.atom.args[1]:
        selected_rhs = selected.atom.args[0]
    else:
        raise CertificateError("selected_lhs is not a side of selected equality")
    if other_rhs == other.atom.args[0]:
        other_lhs = other.atom.args[1]
    elif other_rhs == other.atom.args[1]:
        other_lhs = other.atom.args[0]
    else:
        raise CertificateError("other_rhs is not a side of other equality")
    selected_rhs_subst = substitute_term(selected_rhs, substitution)
    other_lhs_subst = substitute_term(other_lhs, substitution)
    other_rhs_subst = substitute_term(other_rhs, substitution)
    if selected_lhs_subst != other_lhs_subst:
        raise CertificateError("equality-factoring selected and other left sides do not match")
    if instantiated_selected.atom.kind != "eq" or instantiated_other.atom.kind != "eq":
        raise CertificateError("equality-factoring literals must be equalities")
    diff = Literal(True, Term("eq", selected.atom.name, (selected_rhs_subst, other_rhs_subst)))
    introduced = diff.complement
    if introduced not in normalize_clause(conclusion):
        raise CertificateError("equality-factoring conclusion does not contain introduced disequality")
    goal = clause_body_text(conclusion)
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution)

    def prove_other_from_diff(selected_proof: str, diff_proof: str) -> str:
        forward_other = Literal(True, Term("eq", selected.atom.name, (other_lhs_subst, other_rhs_subst)))
        selected_forward = Literal(True, Term("eq", selected.atom.name, (selected_lhs_subst, selected_rhs_subst)))
        if instantiated_selected != selected_forward:
            selected_proof = equality_symmetry_literal_proof(instantiated_selected, selected_proof)
        other_proof = positive_equality_trans_proof(selected_forward, selected_proof, diff, diff_proof)
        if instantiated_other == forward_other:
            return other_proof
        if instantiated_other == swap_equality_literal(forward_other):
            return equality_symmetry_literal_proof(forward_other, other_proof)
        raise CertificateError("equality-factoring kept equality has unsupported orientation")

    def branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_selected:
            diff_proof = fresh_proof_name("Heqfact")
            diseq_proof = fresh_proof_name("Hneqfact")
            return (
                f"((xm {literal_text(diff)}) {goal} "
                f"(fun {diff_proof} => {intro_literal_proof(instantiated_other, conclusion, prove_other_from_diff(proof, diff_proof))}) "
                f"(fun {diseq_proof} => {intro_literal_proof(introduced, conclusion, diseq_proof)}))"
            )
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def equality_symmetry_proof_text(
    parent_clause: tuple[Literal, ...],
    parent_proof: str,
    selected_literal: Literal,
    conclusion: tuple[Literal, ...],
) -> str:
    if selected_literal not in normalize_clause(parent_clause):
        raise CertificateError("Megalodon smoke equality-symmetry literal is not present in parent")
    swapped = swap_equality_literal(selected_literal)
    if swapped not in normalize_clause(conclusion):
        raise CertificateError("Megalodon smoke equality-symmetry conclusion does not contain swapped literal")
    goal = clause_body_text(conclusion)
    parent_proof = instantiate_proof(parent_proof, parent_clause, {})

    def branch(literal: Literal, proof: str) -> str:
        if literal == selected_literal:
            return intro_literal_proof(swapped, conclusion, equality_symmetry_literal_proof(literal, proof))
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(parent_clause, parent_proof, goal, branch)


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
    conclusion_vars = set(clause_free_vars(conclusion))
    parent_vars = set(clause_free_vars(instantiated_equality_parent)) | set(clause_free_vars(instantiated_target_parent))
    uncovered_vars = sorted(parent_vars - conclusion_vars)
    if uncovered_vars:
        raise CertificateError(
            "Megalodon smoke paramodulation elaboration has parent variables not bound by conclusion: "
            + ", ".join(uncovered_vars)
        )
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
    prop_equality = instantiated_equality.atom.name == "prop"
    if prop_equality:
        forward_context = f"(fun cert_x:prop => {atom_text(forward_context_atom)})"
    goal = clause_body_text(conclusion)

    def target_branch(literal: Literal, proof: str, equality_literal_proof: str) -> str:
        if literal == instantiated_target:
            if instantiated_target.polarity:
                transported = f"({equality_literal_proof} {forward_context} {proof})"
            else:
                rewritten_proof = fresh_proof_name("Hrewrite")
                if prop_equality:
                    symmetric_equality = positive_equality_symmetry_proof(instantiated_equality, equality_literal_proof)
                    transported = f"(fun {rewritten_proof} => ({proof} ({symmetric_equality} {forward_context} {rewritten_proof})))"
                else:
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
    elif term.kind == "apply":
        collect_term_symbols(term.args[0], constants, functions)
        collect_term_symbols(term.args[1], constants, functions)
        return
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


def wrap_clause_binders(clause: tuple[Literal, ...], proof: str, symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    symbol_sorts = symbol_sorts or {}
    var_sorts = clause_var_sorts(clause, symbol_sorts)
    for name in reversed(clause_free_vars(clause)):
        proof = f"(fun {require_megalodon_ident(name, 'binder')} :{sort_type_text(var_sorts[name])} => {proof})"
    return proof


def definition_input_declarations(data: dict[str, Any]) -> dict[str, tuple[str, Term]]:
    definitions: dict[str, tuple[str, Term]] = {}
    for step in data.get("steps", []):
        if not isinstance(step, dict) or step.get("rule") != "definition_input":
            continue
        symbol = step.get("symbol")
        sort = step.get("sort")
        if not isinstance(symbol, str) or not isinstance(sort, str):
            continue
        definitions[symbol] = (sort, parse_term(step["value"], f"{step.get('id', '<definition>')}.value"))
    return definitions


def emit_megalodon_smoke(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]], theorem_name: str) -> str:
    outline_declarations = data.get("declarations")
    if outline_declarations is not None:
        if not isinstance(outline_declarations, list) or not all(isinstance(item, str) and item.startswith("Variable ") for item in outline_declarations):
            raise CertificateError("declarations must be a list of Megalodon Variable declarations")
        declarations = sorted(set(outline_declarations))
    else:
        declarations = certificate_symbol_declarations(clauses)
    if not declarations:
        raise CertificateError("Megalodon smoke elaboration needs at least one declared atom or symbol")
    equality_sorts = sorted(
        {
            literal.atom.name
            for clause in clauses.values()
            for literal in clause
            if literal.atom.kind == "eq"
        }
    )
    lines = [
        "Definition False : prop := forall p:prop, p.",
        "Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.",
        "Infix \\/ 785 left := or.",
        "Axiom xm : forall P:prop, P \\/ (P -> False).",
    ]
    for sort in equality_sorts:
        lines.append(equality_definition(sort))
        if sort == "set":
            lines.append("Infix = 502 := eq.")
    definitions = definition_input_declarations(data)
    for declaration in declarations:
        skip = False
        for symbol in definitions:
            if declaration == f"Variable {symbol}:{definitions[symbol][0]}.":
                skip = True
                break
        if not skip:
            lines.append(declaration)
    for symbol, (sort, value) in sorted(definitions.items()):
        lines.append(f"Definition {require_megalodon_ident(symbol, 'definition symbol')} : {require_supported_sort(sort, 'definition sort')} := {term_text(value)}.")
    symbol_sorts = declaration_symbol_sorts(declarations)
    for symbol, (sort, _value) in definitions.items():
        symbol_sorts[symbol] = split_sort(sort)
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
            assumptions.append((step_id, clause_prop_text(clause, symbol_sorts)))
            continue
        if rule == "definition_input":
            proof = wrap_clause_binders(clause, equality_refl_proof(), symbol_sorts)
            proof_names[step_id] = step_id
            derived.append((step_id, clause_prop_text(clause, symbol_sorts), proof))
            continue
        if rule == "resolve":
            parents = step["parents"]
            pivot = parse_literal(step["pivot"], f"{step_id}.pivot")
            proof = wrap_clause_binders(
                clause,
                resolve_proof_text(
                    step_clauses[parents[0]],
                    proof_names[parents[0]],
                    step_clauses[parents[1]],
                    proof_names[parents[1]],
                    pivot,
                    clause,
                ),
                symbol_sorts,
            )
        elif rule == "substitute":
            parent = step["parents"][0]
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            instantiated_parent = tuple(substitute_literal(literal, substitution) for literal in step_clauses[parent])
            proof = wrap_clause_binders(
                clause,
                reorder_clause_proof_text(
                    instantiated_parent,
                    instantiate_proof(proof_names[parent], step_clauses[parent], substitution),
                    clause,
                ),
                symbol_sorts,
            )
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
                symbol_sorts,
            )
        elif rule == "equality_factoring":
            parent = step["parents"][0]
            selected_literal = parse_literal(step["selected"], f"{step_id}.selected")
            other_literal = parse_literal(step["other"], f"{step_id}.other")
            selected_lhs = parse_term(step["selected_lhs"], f"{step_id}.selected_lhs")
            other_rhs = parse_term(step["other_rhs"], f"{step_id}.other_rhs")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            proof = wrap_clause_binders(
                clause,
                equality_factoring_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    selected_literal,
                    other_literal,
                    selected_lhs,
                    other_rhs,
                    substitution,
                    clause,
                ),
                symbol_sorts,
            )
        elif rule == "equality_symmetry":
            parent = step["parents"][0]
            selected_literal = parse_literal(step["literal"], f"{step_id}.literal")
            proof = wrap_clause_binders(
                clause,
                equality_symmetry_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    selected_literal,
                    clause,
                ),
                symbol_sorts,
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
                symbol_sorts,
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
        derived.append((step_id, clause_prop_text(clause, symbol_sorts), proof))

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


def certificate_summary(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]]) -> dict[str, Any]:
    rules: dict[str, int] = {}
    input_sources: dict[str, int] = {}
    derived_assumptions = 0
    for step in data["steps"]:
        rule = step["rule"]
        rules[rule] = rules.get(rule, 0) + 1
        if rule == "input":
            source = step.get("source", {})
            source_kind = source.get("kind", "unknown") if isinstance(source, dict) else "unknown"
            input_sources[source_kind] = input_sources.get(source_kind, 0) + 1
            if source_kind == "vampire_derived_clause":
                derived_assumptions += 1
    return {
        "steps": len(clauses),
        "empty_clauses": sum(1 for clause in clauses.values() if not clause),
        "rules": dict(sorted(rules.items())),
        "input_sources": dict(sorted(input_sources.items())),
        "derived_assumptions": derived_assumptions,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--from-vampire-outline", action="store_true")
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--write-certificate", type=Path)
    parser.add_argument("--emit-megalodon", type=Path)
    parser.add_argument("--theorem-name", default="vampire_certificate_smoke")
    args = parser.parse_args()

    try:
        if args.from_vampire_outline:
            data = certificate_from_vampire_outline(
                args.certificate.read_text(encoding="utf-8"),
                args.certificate.stem,
            )
        else:
            data = json.loads(args.certificate.read_text(encoding="utf-8"))
        clauses = check_certificate(data)
    except (OSError, json.JSONDecodeError, CertificateError) as exc:
        print(f"certificate check failed: {exc}", file=sys.stderr)
        return 1

    if args.write_certificate is not None:
        args.write_certificate.parent.mkdir(parents=True, exist_ok=True)
        args.write_certificate.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.summary:
        print(json.dumps(certificate_summary(data, clauses), sort_keys=True))
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
