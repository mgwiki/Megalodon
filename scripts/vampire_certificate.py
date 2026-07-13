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
CERTIFICATE_BUILTIN_SYMBOLS = {
    "f__false",
    "f__true",
    "vampire_and",
    "vampire_false",
    "vampire_not",
    "vampire_or",
    "vampire_true",
    "vAND",
    "vNOT",
    "vOR",
    "vLAM",
    "vPI",
    "vSIGMA",
}
CERTIFICATE_SYNTAX_SYMBOLS = {"vLAM", "vPI", "vSIGMA"}
MVP_RULES = {
    "input",
    "definition_input",
    "substitute",
    "resolve",
    "factor",
    "equality_factoring",
    "equality_resolution",
    "equality_resolution_constraints",
    "equality_symmetry",
    "truth_conflict_resolution",
    "cnf_formula_exact",
    "cnf_formula_conjunct",
    "cnf_formula_projection",
    "paramodulate",
    "paramodulate_all",
    "paramodulate_clause_all",
    "subsumption_resolution",
    "contradiction",
    "avatar_refutation",
    "avatar_component",
    "definition_rewrite_chain",
    "inequality_split",
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
    "normal_form",
    "avatar_contradiction",
    "avatar_refutation",
    "avatar_split",
}
PROOF_NAME_COUNTER = itertools.count()


class CertificateError(Exception):
    pass


IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
MEGALODON_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
STEP_RE = re.compile(r'^megalodon_step\((\d+),("(?:\\.|[^"\\])*"),("(?:\\.|[^"\\])*"),\[([0-9,]*)\],')
CLAUSE_RE = re.compile(r"^megalodon_certificate_clause\((\d+),(.+)\)\.$")
CERTIFICATE_STEP_RE = re.compile(r"^megalodon_certificate_step\((\d+),(.+)\)\.$")
CERTIFICATE_STEPS_RE = re.compile(r"^megalodon_certificate_steps\((\d+),(.+)\)\.$")
CERTIFICATE_JSON_START = "megalodon_certificate_json_start."
CERTIFICATE_JSON_END = "megalodon_certificate_json_end."
REPLAY_KIND_RE = re.compile(r'^megalodon_step_replay_kind\((\d+),("(?:\\.|[^"\\])*")\)\.$')
FINAL_STEP_RE = re.compile(r"^megalodon_final_step\((\d+)\)\.$")
SYMBOL_DECL_RE = re.compile(r'^megalodon_symbol_declaration\(("(?:\\.|[^"\\])*")\)\.$')
VARIABLE_SORTS_RE = re.compile(r"^megalodon_step_variable_sorts\((\d+),(\[.*\])\)\.$")
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


@dataclass(frozen=True, order=True)
class LambdaHint:
    body: str
    binder: str
    binder_sort: str


@dataclass(frozen=True)
class InequalitySplitDefinition:
    symbol: str
    sort_parts: tuple[str, ...]
    split_arg: Term


@dataclass(frozen=True)
class DefinitionRewriteStep:
    source: Term
    target: Term
    parent: str | None = None
    literal: int | None = None
    position: tuple[int, ...] | None = None
    clause: tuple[Literal, ...] | None = None


LAMBDA_HINTS: tuple[LambdaHint, ...] = ()
DB_NAME_RE = re.compile(r"^db([0-9]+)$")
DB_TOKEN_RE = re.compile(r"\bdb([0-9]+)\b")


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


def translate_vampire_position(term: Term, position: tuple[int, ...], context: str) -> tuple[int, ...]:
    translated: list[int] = []
    current = term
    for depth, index in enumerate(position):
        mapped = index - 2 if index >= 2 and index - 2 < len(current.args) else index
        if mapped >= len(current.args):
            raise CertificateError(f"{context}: position {list(position)} is invalid at depth {depth}")
        translated.append(mapped)
        current = current.args[mapped]
    return tuple(translated)


def certificate_position_for_source(term: Term, position: tuple[int, ...], source: Term, context: str) -> tuple[int, ...]:
    try:
        if term_at_position(term, position, context) == source:
            return position
    except CertificateError:
        pass
    translated = translate_vampire_position(term, position, context)
    selected = term_at_position(term, translated, context)
    if selected != source:
        raise CertificateError(
            f"{context}: rewrite position contains {term_text(selected)}, expected {term_text(source)}"
        )
    return translated


def position_rewrites_bound_lambda_var(term: Term, position: tuple[int, ...], context: str) -> bool:
    return bound_lambda_rewrite_scope(term, position, context) is not None


def is_vlam_term(term: Term) -> bool:
    return term.kind == "app" and term.name == "vLAM" and len(term.args) == 1


def position_enters_lambda_body(term: Term, position: tuple[int, ...], context: str) -> bool:
    current = term
    for depth, index in enumerate(position):
        if index >= len(current.args):
            raise CertificateError(f"{context}: position {list(position)} is invalid at depth {depth}")
        if is_vlam_term(current) and index == 0:
            return True
        current = current.args[index]
    return False


def bound_lambda_rewrite_scope(term: Term, position: tuple[int, ...], context: str) -> tuple[int, int] | None:
    current = term
    lambda_depth = 0
    for depth, index in enumerate(position):
        if index >= len(current.args):
            raise CertificateError(f"{context}: position {list(position)} is invalid at depth {depth}")
        if is_vlam_term(current) and index == 0:
            lambda_depth += 1
        current = current.args[index]
    if current.kind != "const":
        return None
    db_match = DB_NAME_RE.match(current.name)
    if db_match is None:
        return None
    db_index = int(db_match.group(1))
    if db_index >= lambda_depth:
        return None
    return lambda_depth, db_index


def check_rewrite_scope(step: dict[str, Any], term: Term, position: tuple[int, ...], context: str) -> None:
    if "rewrite_scope" not in step:
        return
    scope = step["rewrite_scope"]
    if not isinstance(scope, dict):
        raise CertificateError(f"{context}.rewrite_scope: expected object")
    if set(scope) != {"kind", "lambda_depth", "db_index"}:
        raise CertificateError(f"{context}.rewrite_scope: expected kind, lambda_depth, and db_index")
    if scope["kind"] != "bound_lambda_var":
        raise CertificateError(f"{context}.rewrite_scope.kind: unsupported scope kind {scope['kind']!r}")
    if not isinstance(scope["lambda_depth"], int) or scope["lambda_depth"] < 0:
        raise CertificateError(f"{context}.rewrite_scope.lambda_depth: expected non-negative integer")
    if not isinstance(scope["db_index"], int) or scope["db_index"] < 0:
        raise CertificateError(f"{context}.rewrite_scope.db_index: expected non-negative integer")
    actual = bound_lambda_rewrite_scope(term, position, f"{context}.position")
    if actual is None:
        raise CertificateError(f"{context}.rewrite_scope: position is not a bound-lambda redex")
    if actual != (scope["lambda_depth"], scope["db_index"]):
        raise CertificateError(f"{context}.rewrite_scope: metadata does not match target position")


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


def rewrite_term_once_variants(term: Term, source: Term, target: Term) -> tuple[Term, ...]:
    variants: set[Term] = set()
    if term == source:
        variants.add(target)
    for index, arg in enumerate(term.args):
        for rewritten_arg in rewrite_term_once_variants(arg, source, target):
            args = list(term.args)
            args[index] = rewritten_arg
            variants.add(Term(term.kind, term.name, tuple(args)))
    return tuple(sorted(variants))


def rewrite_literal_once_variants(literal: Literal, source: Term, target: Term) -> tuple[Literal, ...]:
    return tuple(
        Literal(literal.polarity, rewritten_atom)
        for rewritten_atom in rewrite_term_once_variants(literal.atom, source, target)
    )


def rewrite_clause_once_variants(
    clause: tuple[Literal, ...],
    source: Term,
    target: Term,
) -> tuple[tuple[Literal, ...], ...]:
    variants: set[tuple[Literal, ...]] = set()
    for index, literal in enumerate(clause):
        for rewritten_literal in rewrite_literal_once_variants(literal, source, target):
            new_clause = list(clause)
            new_clause[index] = rewritten_literal
            variants.add(normalize_clause(tuple(new_clause)))
    return tuple(sorted(variants))


def rewrite_clause_at_definition_step(
    clause: tuple[Literal, ...],
    step: DefinitionRewriteStep,
    context: str,
) -> tuple[Literal, ...]:
    if step.literal is None or step.position is None:
        raise CertificateError(f"{context}: positioned definition rewrite is missing literal or position")
    if step.literal >= len(clause):
        raise CertificateError(f"{context}: literal index {step.literal} is outside the current clause")
    literal = clause[step.literal]
    position = certificate_position_for_source(literal.atom, step.position, step.source, f"{context}.position")
    rewritten_atom = replace_term_at_position(literal.atom, position, step.target, f"{context}.position")
    rewritten_clause = list(clause)
    rewritten_clause[step.literal] = Literal(literal.polarity, rewritten_atom)
    return tuple(rewritten_clause)


def clauses_match_modulo_equality_symmetry(
    left: tuple[Literal, ...],
    right: tuple[Literal, ...],
) -> bool:
    left = normalize_clause(left)
    right = normalize_clause(right)
    if len(left) != len(right):
        return False

    remaining = list(right)

    def search(index: int) -> bool:
        if index == len(left):
            return True
        literal = left[index]
        for candidate_index, candidate in enumerate(remaining):
            if equality_symmetric_match(literal, candidate):
                removed = remaining.pop(candidate_index)
                if search(index + 1):
                    return True
                remaining.insert(candidate_index, removed)
        return False

    return search(0)


def definition_rewrite_chain_reaches(
    source_clause: tuple[Literal, ...],
    rewrites: tuple[DefinitionRewriteStep, ...],
    target_clause: tuple[Literal, ...],
    context: str,
) -> bool:
    if all(rewrite.literal is not None and rewrite.position is not None for rewrite in rewrites):
        candidate = tuple(source_clause)
        for index, rewrite in enumerate(rewrites):
            computed = rewrite_clause_at_definition_step(candidate, rewrite, f"{context}.rewrites[{index}]")
            if rewrite.clause is not None:
                if not clauses_match_modulo_equality_symmetry(computed, rewrite.clause):
                    return False
                candidate = rewrite.clause
            else:
                candidate = computed
        return clauses_match_modulo_equality_symmetry(candidate, target_clause)

    candidates: set[tuple[Literal, ...]] = {normalize_clause(source_clause)}
    max_candidates = 1024
    for index, rewrite in enumerate(rewrites):
        next_candidates: set[tuple[Literal, ...]] = set()
        for candidate in candidates:
            next_candidates.update(rewrite_clause_once_variants(candidate, rewrite.source, rewrite.target))
            if len(next_candidates) > max_candidates:
                raise CertificateError(f"{context}: definition rewrite chain branches too much at step {index}")
        if not next_candidates:
            return False
        candidates = next_candidates
    return any(clauses_match_modulo_equality_symmetry(candidate, target_clause) for candidate in candidates)


def bool_name_literal_term(literal: Literal, value: bool) -> Term | None:
    if not literal.polarity or literal.atom.kind != "eq" or literal.atom.name != "prop":
        return None
    if len(literal.atom.args) != 2:
        return None
    truth = Term("const", "f__true" if value else "f__false")
    left, right = literal.atom.args
    if left == truth:
        return right
    if right == truth:
        return left
    return None


def application_head_and_arg(term: Term) -> tuple[Term, Term] | None:
    if term.kind != "apply" or len(term.args) != 2:
        return None
    return term.args[0], term.args[1]


def applied_symbol_and_args(term: Term) -> tuple[str, tuple[Term, ...]] | None:
    head, args = term_spine(term)
    if head.kind != "const" or not args:
        return None
    return head.name, tuple(args)


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
    if MEGALODON_IDENT_RE.fullmatch(name):
        return name
    if not name:
        raise CertificateError(f"{context}: empty identifier")
    escaped = "".join(
        char if (char.isalnum() or char == "_") else f"_u{ord(char):x}_"
        for char in name
    )
    if not escaped[0].isalpha() and escaped[0] != "_":
        escaped = f"cert_{escaped}"
    escaped = re.sub(r"_+", "_", escaped)
    if not MEGALODON_IDENT_RE.fullmatch(escaped):
        raise CertificateError(f"{context}: {name!r} cannot be rendered as a Megalodon identifier")
    return escaped


def render_variable_declaration(declaration: str) -> str:
    match = re.fullmatch(r"Variable ([A-Za-z_][A-Za-z0-9_']*):(.+)\.", declaration)
    if match is None:
        return declaration
    return f"Variable {require_megalodon_ident(match.group(1), 'declaration symbol')}:{match.group(2)}."


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


def parse_variable_sort_entries(value: Any, context: str) -> dict[str, str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise CertificateError(f"{context}: variable sorts must be a string list")
    result: dict[str, str] = {}
    for index, item in enumerate(value):
        if ":" not in item:
            raise CertificateError(f"{context}[{index}]: variable sort entry must contain ':'")
        name, sort = item.split(":", 1)
        require_megalodon_ident(name, f"{context}[{index}].name")
        normalized_sort = require_supported_sort(sort, f"{context}[{index}].sort")
        previous = result.get(name)
        if previous is not None and previous != normalized_sort:
            raise CertificateError(
                f"{context}: variable {name!r} has conflicting explicit sorts {previous!r} and {normalized_sort!r}"
            )
        result[name] = normalized_sort
    return result


def parse_key_value_fields(fields: list[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for field in fields:
        key, separator, value = field.partition("=")
        if not separator or not key:
            continue
        result[key] = value
    return result


def parse_lambda_hints(extras: dict[int, dict[str, list[str]]]) -> list[dict[str, str]]:
    hints: list[dict[str, str]] = []
    seen: set[tuple[str, str, str]] = set()
    for step_no in sorted(extras):
        fields = extras[step_no].get("lambda_sorts")
        if not fields:
            continue
        keyed = parse_key_value_fields(fields)
        try:
            count = int(keyed.get("step_lambda_count", "0"))
        except ValueError as exc:
            raise CertificateError(f"u{step_no}.lambda_sorts: malformed step_lambda_count") from exc
        for index in range(count):
            prefix = f"step_lambda_{index}"
            body = keyed.get(prefix + "_body")
            binder = keyed.get(prefix + "_binder_db")
            binder_sort = keyed.get(prefix + "_binder_sort")
            if body is None or binder is None or binder_sort is None:
                continue
            require_megalodon_ident(binder, f"u{step_no}.lambda_sorts.{prefix}.binder")
            normalized_sort = require_supported_sort(binder_sort, f"u{step_no}.lambda_sorts.{prefix}.binder_sort")
            key = (body, binder, normalized_sort)
            if key in seen:
                continue
            seen.add(key)
            hints.append({"body": body, "binder": binder, "binder_sort": normalized_sort})
    return hints


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


def clause_to_json(clause: tuple[Literal, ...]) -> list[dict[str, Any]]:
    return [literal_to_json(literal) for literal in clause]


def positions_are_disjoint(positions: tuple[tuple[int, ...], ...]) -> bool:
    for left, right in itertools.combinations(positions, 2):
        if len(left) <= len(right) and right[: len(left)] == left:
            return False
        if len(right) <= len(left) and left[: len(right)] == right:
            return False
    return True


def expand_paramodulate_all_step(
    step: dict[str, Any],
    available_clauses: dict[str, tuple[Literal, ...]],
    context: str,
) -> list[dict[str, Any]]:
    step_id = step.get("id")
    if not isinstance(step_id, str) or not step_id:
        raise CertificateError(f"{context}: paramodulate_all step needs an id before expansion")
    parents = require_parents(step, 2)
    equality_parent = available_clauses.get(parents[0])
    target_parent = available_clauses.get(parents[1])
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
    substitution_json = step["substitution"]
    substitution = parse_substitution(substitution_json, f"{step_id}.substitution")
    selected_equality = substitute_literal(equality, substitution)
    if not selected_equality.polarity or selected_equality.atom.kind != "eq" or len(selected_equality.atom.args) != 2:
        raise CertificateError(f"{step_id}: selected equality is not a positive equality atom")
    from_term = substitute_term(parse_term(step["from"], f"{step_id}.from"), substitution)
    to_term = substitute_term(parse_term(step["to"], f"{step_id}.to"), substitution)
    if selected_equality.atom.args != (from_term, to_term):
        raise CertificateError(f"{step_id}: from/to do not match selected equality after substitution")

    if not isinstance(step["positions"], list):
        raise CertificateError(f"{step_id}.positions: positions must be a list")
    positions = tuple(parse_position(item, f"{step_id}.positions[{index}]") for index, item in enumerate(step["positions"]))
    if not positions:
        raise CertificateError(f"{step_id}: paramodulate_all needs at least one position")
    selected_target = substitute_literal(target, substitution)
    expected_positions = term_positions_matching(selected_target.atom, from_term)
    if sorted(positions) != sorted(expected_positions):
        raise CertificateError(f"{step_id}: positions do not match all selected redex occurrences")
    if not positions_are_disjoint(positions):
        raise CertificateError(f"{step_id}: overlapping simultaneous redex positions need prover-side primitive expansion")

    expanded: list[dict[str, Any]] = []
    equality_parent_id = parents[0]
    target_parent_id = parents[1]
    instantiated_equality_parent = normalize_clause(tuple(substitute_literal(literal, substitution) for literal in equality_parent))
    instantiated_target_parent = normalize_clause(tuple(substitute_literal(literal, substitution) for literal in target_parent))
    if instantiated_equality_parent != normalize_clause(equality_parent):
        equality_parent_id = f"{step_id}_instantiate_equality_parent"
        expanded.append(
            {
                "id": equality_parent_id,
                "rule": "substitute",
                "parents": [parents[0]],
                "substitution": substitution_json,
                "clause": clause_to_json(instantiated_equality_parent),
            }
        )
    if instantiated_target_parent != normalize_clause(target_parent):
        target_parent_id = f"{step_id}_instantiate_target_parent"
        expanded.append(
            {
                "id": target_parent_id,
                "rule": "substitute",
                "parents": [parents[1]],
                "substitution": substitution_json,
                "clause": clause_to_json(instantiated_target_parent),
            }
        )

    current_parent_id = target_parent_id
    current_clause = instantiated_target_parent
    current_target = selected_target
    equality_parent_for_paramod = instantiated_equality_parent
    equality_for_paramod = selected_equality
    empty_substitution: dict[str, Any] = {}

    for index, position in enumerate(positions):
        if current_target not in current_clause:
            raise CertificateError(f"{step_id}: intermediate target literal is not present before rewrite {index}")
        if term_at_position(current_target.atom, position, f"{step_id}.positions[{index}]") != from_term:
            raise CertificateError(f"{step_id}: position {index} no longer contains the selected from term")
        rewritten_target = Literal(
            current_target.polarity,
            replace_term_at_position(current_target.atom, position, to_term, f"{step_id}.positions[{index}]"),
        )
        next_clause = normalize_clause(
            tuple(clause_without_one(equality_parent_for_paramod, equality_for_paramod))
            + tuple(clause_without_one(current_clause, current_target))
            + (rewritten_target,)
        )
        primitive_id = step_id if index == len(positions) - 1 else f"{step_id}_paramodulate_{index}"
        expanded.append(
            {
                "id": primitive_id,
                "rule": "paramodulate",
                "parents": [equality_parent_id, current_parent_id],
                "equality": literal_to_json(equality_for_paramod),
                "from": term_to_json(from_term),
                "to": term_to_json(to_term),
                "target": literal_to_json(current_target),
                "position": list(position),
                "substitution": empty_substitution,
                "clause": clause_to_json(next_clause),
            }
        )
        current_parent_id = primitive_id
        current_clause = next_clause
        current_target = rewritten_target

    final_clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
    if current_clause != final_clause:
        raise CertificateError(f"{step_id}: expanded paramodulate_all sequence does not reach macro conclusion")
    return expanded


def expand_explicit_certificate_steps(
    step_id: str,
    explicit_steps: list[dict[str, Any]],
    available_clauses: dict[str, tuple[Literal, ...]],
) -> list[dict[str, Any]]:
    expanded_steps: list[dict[str, Any]] = []
    local_clauses = dict(available_clauses)
    for index, step in enumerate(explicit_steps):
        rule = step.get("rule")
        if rule == "paramodulate_all":
            new_steps = expand_paramodulate_all_step(step, local_clauses, f"{step_id}.substeps[{index}]")
        else:
            new_steps = [step]
        for new_step in new_steps:
            new_step_id = new_step.get("id")
            if not isinstance(new_step_id, str) or not new_step_id:
                raise CertificateError(f"{step_id}: expanded explicit substep {index} needs id")
            if new_step_id in local_clauses:
                raise CertificateError(f"{step_id}: expanded explicit substep duplicates id {new_step_id}")
            if "clause" not in new_step:
                raise CertificateError(f"{step_id}: expanded explicit substep {new_step_id} needs clause")
            local_clauses[new_step_id] = normalize_clause(parse_clause(new_step["clause"], f"{new_step_id}.clause"))
            expanded_steps.append(new_step)
    return expanded_steps


def require_fields(step: dict[str, Any], fields: set[str]) -> None:
    missing = sorted(fields - set(step))
    if missing:
        raise CertificateError(f"{step.get('id', '<unknown>')}: missing fields: {', '.join(missing)}")


def require_no_extra_fields(step: dict[str, Any], fields: set[str]) -> None:
    extra = sorted(set(step) - fields - {"variable_sorts"})
    if extra:
        raise CertificateError(f"{step.get('id', '<unknown>')}: unexpected fields: {', '.join(extra)}")


def require_parents(step: dict[str, Any], count: int) -> list[str]:
    parents = step.get("parents")
    if not isinstance(parents, list) or len(parents) != count:
        raise CertificateError(f"{step.get('id', '<unknown>')}: expected {count} parent(s)")
    if not all(isinstance(parent, str) and parent for parent in parents):
        raise CertificateError(f"{step.get('id', '<unknown>')}: parent ids must be non-empty strings")
    return parents


def parse_sat_literal(value: Any, context: str) -> tuple[int, bool]:
    if not isinstance(value, dict):
        raise CertificateError(f"{context}: SAT literal must be an object")
    if set(value) != {"var", "polarity"}:
        raise CertificateError(f"{context}: SAT literal must have exactly var and polarity")
    var = value["var"]
    polarity = value["polarity"]
    if not isinstance(var, int) or var <= 0:
        raise CertificateError(f"{context}.var: SAT variable must be a positive integer")
    if not isinstance(polarity, bool):
        raise CertificateError(f"{context}.polarity: SAT polarity must be boolean")
    return var, polarity


def parse_bool_flag(value: str | None, context: str) -> bool:
    if value == "1":
        return True
    if value == "0":
        return False
    raise CertificateError(f"{context}: expected 0 or 1")


def split_literal_var(literal: Literal) -> int | None:
    if literal.atom.kind != "pred" or literal.atom.args:
        return None
    match = re.fullmatch(r"split_([1-9][0-9]*)", literal.atom.name)
    if match is None:
        return None
    return int(match.group(1))


def avatar_component_metadata(step_id: str, fields: list[str]) -> dict[str, Any] | None:
    values = parse_key_value_fields(fields)
    if values.get("dependency_count") != "1":
        return None
    split_var_text = values.get("dependency_0_split_var")
    split_positive_text = values.get("dependency_0_split_positive")
    split_level_text = values.get("dependency_0_split_level")
    if split_var_text is None or split_positive_text is None:
        return None
    try:
        split_var = int(split_var_text)
    except ValueError as exc:
        raise CertificateError(f"{step_id}: avatar component split var is not an integer") from exc
    if split_var <= 0:
        raise CertificateError(f"{step_id}: avatar component split var must be positive")
    metadata: dict[str, Any] = {
        "split_var": split_var,
        "split_positive": parse_bool_flag(split_positive_text, f"{step_id}: avatar component split polarity"),
    }
    if split_level_text is not None:
        try:
            metadata["split_level"] = int(split_level_text)
        except ValueError as exc:
            raise CertificateError(f"{step_id}: avatar component split level is not an integer") from exc
    return metadata


def parse_sat_clauses(value: Any, context: str) -> tuple[tuple[tuple[int, bool], ...], ...]:
    if not isinstance(value, list) or not value:
        raise CertificateError(f"{context}: SAT clauses must be a non-empty list")
    clauses: list[tuple[tuple[int, bool], ...]] = []
    for clause_index, clause_value in enumerate(value):
        if not isinstance(clause_value, list):
            raise CertificateError(f"{context}[{clause_index}]: SAT clause must be a list")
        literals = tuple(
            parse_sat_literal(literal, f"{context}[{clause_index}][{literal_index}]")
            for literal_index, literal in enumerate(clause_value)
        )
        clauses.append(literals)
    return tuple(clauses)


def sat_clauses_unsat(clauses: tuple[tuple[tuple[int, bool], ...], ...]) -> bool:
    assignment: dict[int, bool] = {}

    def simplify() -> tuple[bool, bool]:
        changed = True
        while changed:
            changed = False
            for clause in clauses:
                unassigned: list[tuple[int, bool]] = []
                satisfied = False
                for var, polarity in clause:
                    value = assignment.get(var)
                    if value is None:
                        unassigned.append((var, polarity))
                    elif value == polarity:
                        satisfied = True
                        break
                if satisfied:
                    continue
                if not unassigned:
                    return False, True
                if len(unassigned) == 1:
                    var, polarity = unassigned[0]
                    value = assignment.get(var)
                    if value is not None and value != polarity:
                        return False, True
                    if value is None:
                        assignment[var] = polarity
                        changed = True
        all_satisfied = all(
            any(assignment.get(var) == polarity for var, polarity in clause)
            for clause in clauses
        )
        return all_satisfied, False

    def search() -> bool:
        complete, conflict = simplify()
        if conflict:
            return False
        if complete:
            return True
        variables = sorted({var for clause in clauses for var, _polarity in clause})
        branch_var = next(var for var in variables if var not in assignment)
        snapshot = dict(assignment)
        for value in (False, True):
            assignment[branch_var] = value
            if search():
                return True
            assignment.clear()
            assignment.update(snapshot)
        return False

    return not search()


def sat_split_name(var: int) -> str:
    if var <= 0:
        raise CertificateError(f"SAT variable must be positive, got {var}")
    return f"split_{var}"


def sat_literal_prop_text(literal: tuple[int, bool]) -> str:
    var, polarity = literal
    atom = sat_split_name(var)
    if polarity:
        return atom
    return f"({atom} -> False)"


def sat_clause_prop_text(clause: tuple[tuple[int, bool], ...]) -> str:
    if not clause:
        return "False"
    parts = [sat_literal_prop_text(literal) for literal in clause]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"({part} \\/ {result})"
    return result


def check_certificate(data: Any) -> dict[str, tuple[Literal, ...]]:
    global LAMBDA_HINTS
    if not isinstance(data, dict):
        raise CertificateError("certificate must be a JSON object")
    if data.get("format") != FORMAT:
        raise CertificateError(f"format must be {FORMAT}")
    if data.get("version") != VERSION:
        raise CertificateError(f"version must be {VERSION}")
    LAMBDA_HINTS = certificate_lambda_hints(data)
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

        elif rule == "cnf_formula_exact":
            allowed = {"id", "rule", "formula_parent", "proposition", "clause", "source", "variable_sorts"}
            require_fields(step, {"id", "rule", "formula_parent", "proposition", "clause"})
            require_no_extra_fields(step, allowed)
            formula_parent = step["formula_parent"]
            proposition = step["proposition"]
            if not isinstance(formula_parent, str) or not re.fullmatch(r"u[0-9]+", formula_parent):
                raise CertificateError(f"{step_id}: formula_parent must be a Vampire unit id")
            if not isinstance(proposition, str) or not proposition:
                raise CertificateError(f"{step_id}: proposition must be a non-empty string")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))

        elif rule == "cnf_formula_conjunct":
            allowed = {"id", "rule", "formula_parent", "source_proposition", "proposition", "path", "clause", "source", "variable_sorts"}
            require_fields(step, {"id", "rule", "formula_parent", "source_proposition", "proposition", "path", "clause"})
            require_no_extra_fields(step, allowed)
            formula_parent = step["formula_parent"]
            source_proposition = step["source_proposition"]
            proposition = step["proposition"]
            path = step["path"]
            if not isinstance(formula_parent, str) or not re.fullmatch(r"u[0-9]+", formula_parent):
                raise CertificateError(f"{step_id}: formula_parent must be a Vampire unit id")
            if not isinstance(source_proposition, str) or not source_proposition:
                raise CertificateError(f"{step_id}: source_proposition must be a non-empty string")
            if not isinstance(proposition, str) or not proposition:
                raise CertificateError(f"{step_id}: proposition must be a non-empty string")
            if not isinstance(path, list) or not path or any(item not in {"left", "right"} for item in path):
                raise CertificateError(f"{step_id}: path must be a non-empty list of left/right entries")
            inferred_path = cnf_formula_conjunct_path(
                {
                    "parent_kind": "formula",
                    "target_clause_checked": True,
                    "source_proposition": source_proposition,
                    "target_proposition": proposition,
                }
            )
            if inferred_path != tuple(path):
                raise CertificateError(f"{step_id}: conjunction projection path does not match source and target propositions")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))

        elif rule == "cnf_formula_projection":
            allowed = {"id", "rule", "formula_parent", "source_proposition", "proposition", "clause", "source", "variable_sorts"}
            require_fields(step, {"id", "rule", "formula_parent", "source_proposition", "proposition", "clause"})
            require_no_extra_fields(step, allowed)
            formula_parent = step["formula_parent"]
            source_proposition = step["source_proposition"]
            proposition = step["proposition"]
            if not isinstance(formula_parent, str) or not re.fullmatch(r"u[0-9]+", formula_parent):
                raise CertificateError(f"{step_id}: formula_parent must be a Vampire unit id")
            if not isinstance(source_proposition, str) or not source_proposition:
                raise CertificateError(f"{step_id}: source_proposition must be a non-empty string")
            if not isinstance(proposition, str) or not proposition:
                raise CertificateError(f"{step_id}: proposition must be a non-empty string")
            if not formula_projection_supported(source_proposition, proposition):
                raise CertificateError(f"{step_id}: CNF projection is not supported by source and target propositions")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            normalized_target = clause_formula_prop_text(clause, None, step_explicit_var_sorts(step, step_id))
            if not formula_projection_supported(source_proposition, normalized_target):
                raise CertificateError(f"{step_id}: CNF projection is not supported by source and normalized clause")

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
            if clause != expected and not clauses_match_modulo_equality_symmetry(expected, clause):
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

        elif rule == "equality_resolution_constraints":
            allowed = {"id", "rule", "parents", "literal", "substitution", "constraints", "clause"}
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
            if not isinstance(step["constraints"], list) or not step["constraints"]:
                raise CertificateError(f"{step_id}: equality-resolution constraints must be a non-empty list")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            base = tuple(
                substitute_literal(item, substitution)
                for item in clause_without_one(parent_clause, literal)
            )
            constraints = parse_clause(step["constraints"], f"{step_id}.constraints")
            expected = normalize_clause(base + constraints)
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: equality-resolution constrained conclusion does not match parent")

        elif rule == "truth_conflict_resolution":
            allowed = {"id", "rule", "parents", "literal", "substitution", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = require_parents(step, 1)
            parent_clause = clauses.get(parents[0])
            if parent_clause is None:
                raise CertificateError(f"{step_id}: unknown parent {parents[0]}")
            literal = parse_literal(step["literal"], f"{step_id}.literal")
            if literal not in parent_clause:
                raise CertificateError(f"{step_id}: truth-conflict literal not present in parent")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            selected = substitute_literal(literal, substitution)
            if not selected.polarity or not is_prop_truth_conflict_atom(selected.atom):
                raise CertificateError(f"{step_id}: selected literal is not true=false or false=true after substitution")
            expected = normalize_clause(
                tuple(
                    substitute_literal(item, substitution)
                    for item in clause_without_one(parent_clause, literal)
                )
            )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause != expected:
                raise CertificateError(f"{step_id}: truth-conflict conclusion does not match parent")

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
                    (
                        literal.polarity
                        and is_reflexive_equality_atom(literal.atom)
                    )
                    or any(equality_symmetric_match(literal, conclusion_literal) for conclusion_literal in clause)
                    for literal in side_remainder
                ):
                    covered = True
                    break
            if not covered:
                raise CertificateError(f"{step_id}: side remainder literals are not covered by conclusion")

        elif rule == "avatar_refutation":
            allowed = {"id", "rule", "parents", "sat_clauses", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = step.get("parents")
            if not isinstance(parents, list) or not parents:
                raise CertificateError(f"{step_id}: avatar_refutation needs at least one parent")
            if not all(isinstance(parent, str) and parent for parent in parents):
                raise CertificateError(f"{step_id}: parent ids must be non-empty strings")
            sat_clauses = parse_sat_clauses(step["sat_clauses"], f"{step_id}.sat_clauses")
            if len(sat_clauses) != len(parents):
                raise CertificateError(f"{step_id}: SAT clause count must match parent count")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            if clause:
                raise CertificateError(f"{step_id}: avatar_refutation conclusion must be empty")
            if not sat_clauses_unsat(sat_clauses):
                raise CertificateError(f"{step_id}: SAT clauses are satisfiable")

        elif rule == "avatar_component":
            allowed = {"id", "rule", "parents", "split_var", "split_positive", "clause", "source"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = step.get("parents")
            if not isinstance(parents, list) or len(parents) != 1:
                raise CertificateError(f"{step_id}: avatar_component expects exactly one definition parent")
            if not isinstance(parents[0], str) or not parents[0]:
                raise CertificateError(f"{step_id}: avatar_component parent id must be a non-empty string")
            split_var = step["split_var"]
            split_positive = step["split_positive"]
            if not isinstance(split_var, int) or split_var <= 0:
                raise CertificateError(f"{step_id}: split_var must be a positive integer")
            if not isinstance(split_positive, bool):
                raise CertificateError(f"{step_id}: split_positive must be boolean")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            split_literals = [literal for literal in clause if split_literal_var(literal) == split_var]
            if len(split_literals) != 1:
                raise CertificateError(f"{step_id}: avatar_component must contain exactly one split_{split_var} literal")
            if split_literals[0].polarity == split_positive:
                raise CertificateError(f"{step_id}: avatar_component split literal must complement the SAT split polarity")

        elif rule == "definition_rewrite_chain":
            allowed = {"id", "rule", "parents", "source_clause", "rewrites", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = step.get("parents")
            if not isinstance(parents, list) or not parents:
                raise CertificateError(f"{step_id}: definition_rewrite_chain needs at least one parent")
            if not all(isinstance(parent, str) and parent for parent in parents):
                raise CertificateError(f"{step_id}: parent ids must be non-empty strings")
            for parent in parents:
                if parent not in clauses:
                    raise CertificateError(f"{step_id}: unknown parent {parent}")
            source_clause_ordered = parse_clause(step["source_clause"], f"{step_id}.source_clause")
            source_clause = normalize_clause(source_clause_ordered)
            if source_clause != clauses[parents[0]]:
                raise CertificateError(f"{step_id}: source_clause does not match first parent")
            rewrite_values = step["rewrites"]
            if not isinstance(rewrite_values, list) or not rewrite_values:
                raise CertificateError(f"{step_id}: rewrites must be a non-empty list")
            rewrites: list[DefinitionRewriteStep] = []
            for rewrite_index, rewrite in enumerate(rewrite_values):
                if not isinstance(rewrite, dict) or not {"from", "to"} <= set(rewrite) or not set(rewrite) <= {"from", "to", "parent", "literal", "position", "clause"}:
                    raise CertificateError(f"{step_id}.rewrites[{rewrite_index}]: expected from/to terms and optional parent/literal/position")
                rewrite_parent = rewrite.get("parent")
                if rewrite_parent is not None and (not isinstance(rewrite_parent, str) or rewrite_parent not in parents[1:]):
                    raise CertificateError(f"{step_id}.rewrites[{rewrite_index}].parent: expected one of the definition parents")
                rewrite_literal = rewrite.get("literal")
                if rewrite_literal is not None and (not isinstance(rewrite_literal, int) or rewrite_literal < 0):
                    raise CertificateError(f"{step_id}.rewrites[{rewrite_index}].literal: expected a non-negative integer")
                rewrite_position = rewrite.get("position")
                if rewrite_position is not None and (
                    not isinstance(rewrite_position, list)
                    or any(not isinstance(item, int) or item < 0 for item in rewrite_position)
                ):
                    raise CertificateError(f"{step_id}.rewrites[{rewrite_index}].position: expected a list of non-negative integers")
                rewrites.append(
                    DefinitionRewriteStep(
                        parse_term(rewrite["from"], f"{step_id}.rewrites[{rewrite_index}].from"),
                        parse_term(rewrite["to"], f"{step_id}.rewrites[{rewrite_index}].to"),
                        rewrite_parent,
                        rewrite_literal,
                        tuple(rewrite_position) if rewrite_position is not None else None,
                        normalize_clause(parse_clause(rewrite["clause"], f"{step_id}.rewrites[{rewrite_index}].clause")) if "clause" in rewrite else None,
                    )
                )
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            replay_source_clause = (
                source_clause_ordered
                if all(rewrite.literal is not None and rewrite.position is not None for rewrite in rewrites)
                else source_clause
            )
            if not definition_rewrite_chain_reaches(replay_source_clause, tuple(rewrites), clause, step_id):
                raise CertificateError(f"{step_id}: definition rewrite chain does not reach conclusion")

        elif rule == "inequality_split":
            allowed = {"id", "rule", "parents", "source_clause", "splits", "clause"}
            require_fields(step, allowed)
            require_no_extra_fields(step, allowed)
            parents = step.get("parents")
            if not isinstance(parents, list) or len(parents) < 2:
                raise CertificateError(f"{step_id}: inequality_split needs a source parent and at least one name parent")
            if not all(isinstance(parent, str) and parent for parent in parents):
                raise CertificateError(f"{step_id}: parent ids must be non-empty strings")
            for parent in parents:
                if parent not in clauses:
                    raise CertificateError(f"{step_id}: unknown parent {parent}")
            source_clause = normalize_clause(parse_clause(step["source_clause"], f"{step_id}.source_clause"))
            if source_clause != clauses[parents[0]]:
                raise CertificateError(f"{step_id}: source_clause does not match first parent")
            split_values = step["splits"]
            if not isinstance(split_values, list) or not split_values:
                raise CertificateError(f"{step_id}: splits must be a non-empty list")
            if len(split_values) != len(parents) - 1:
                raise CertificateError(f"{step_id}: split count must match name parent count")

            remaining_source = list(source_clause)
            replacements: list[Literal] = []
            used_name_parents: set[str] = set()
            for split_index, split in enumerate(split_values):
                if not isinstance(split, dict) or set(split) != {"name_parent", "source", "name_literal", "replacement"}:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: expected name_parent, source, name_literal, replacement")
                name_parent = split["name_parent"]
                if not isinstance(name_parent, str) or name_parent not in parents[1:]:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: name_parent must be one of the name parents")
                if name_parent in used_name_parents:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: duplicate name_parent")
                used_name_parents.add(name_parent)

                name_parent_clause = clauses[name_parent]
                if len(name_parent_clause) != 1:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: name parent must be a unit clause")
                name_literal = parse_literal(split["name_literal"], f"{step_id}.splits[{split_index}].name_literal")
                if name_parent_clause != (name_literal,):
                    raise CertificateError(f"{step_id}.splits[{split_index}]: name_literal does not match name parent")
                name_term = bool_name_literal_term(name_literal, False)
                name_parts = application_head_and_arg(name_term) if name_term is not None else None
                if name_parts is None:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: name_literal must be false = P(term)")
                name_head, split_term = name_parts

                source_literal = parse_literal(split["source"], f"{step_id}.splits[{split_index}].source")
                if source_literal not in remaining_source:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: source literal not present or already used")
                if source_literal.polarity or source_literal.atom.kind != "eq" or len(source_literal.atom.args) != 2:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: source must be a negative equality")
                left, right = source_literal.atom.args
                if left == split_term:
                    other_side = right
                elif right == split_term:
                    other_side = left
                else:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: name literal term is not a side of source equality")

                replacement = parse_literal(split["replacement"], f"{step_id}.splits[{split_index}].replacement")
                replacement_term = bool_name_literal_term(replacement, True)
                replacement_parts = application_head_and_arg(replacement_term) if replacement_term is not None else None
                if replacement_parts is None:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: replacement must be true = P(term)")
                replacement_head, replacement_arg = replacement_parts
                if replacement_head != name_head or replacement_arg != other_side:
                    raise CertificateError(f"{step_id}.splits[{split_index}]: replacement does not use the same split name on the other equality side")

                remaining_source.remove(source_literal)
                replacements.append(replacement)

            if used_name_parents != set(parents[1:]):
                raise CertificateError(f"{step_id}: not all name parents were used")
            clause = normalize_clause(parse_clause(step["clause"], f"{step_id}.clause"))
            expected = normalize_clause(tuple(remaining_source) + tuple(replacements))
            if clause != expected:
                raise CertificateError(f"{step_id}: inequality split conclusion does not match replacements")

        elif rule == "paramodulate":
            allowed = {
                "id",
                "rule",
                "parents",
                "equality",
                "from",
                "to",
                "target",
                "rewritten_target",
                "rewrite_scope",
                "position",
                "substitution",
                "clause",
            }
            require_fields(step, allowed - {"rewritten_target", "rewrite_scope"})
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
            if "rewritten_target" in step:
                explicit_rewritten_target = parse_literal(step["rewritten_target"], f"{step_id}.rewritten_target")
                if explicit_rewritten_target != rewritten_target:
                    raise CertificateError(f"{step_id}: rewritten_target does not match position rewrite")
            check_rewrite_scope(step, selected_target.atom, position, step_id)
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
            allowed = {
                "id",
                "rule",
                "parents",
                "equality",
                "from",
                "to",
                "target",
                "rewritten_target",
                "positions",
                "substitution",
                "clause",
            }
            require_fields(step, allowed - {"rewritten_target"})
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
            if "rewritten_target" in step:
                explicit_rewritten_target = parse_literal(step["rewritten_target"], f"{step_id}.rewritten_target")
                if explicit_rewritten_target != rewritten_target:
                    raise CertificateError(f"{step_id}: rewritten_target does not match simultaneous rewrite")
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


def normal_form_clause_source_metadata(
    step_id: str,
    fields: list[str],
    parent_clause_numbers: list[int],
    clauses: dict[int, tuple[Literal, ...]],
    target_clause: tuple[Literal, ...],
) -> dict[str, Any] | None:
    if not fields:
        return None
    rule = extra_field(fields, "rule")
    parent_unit_text = extra_field(fields, "parent_unit")
    source_clause_text = extra_field(fields, "source_clause")
    target_clause_text = extra_field(fields, "target_clause")
    if parent_unit_text is None or source_clause_text is None or target_clause_text is None:
        return None
    try:
        parent_unit = int(parent_unit_text)
    except ValueError as exc:
        raise CertificateError(f"{step_id}: normal_form_clause parent_unit is not an integer") from exc
    if parent_unit not in parent_clause_numbers:
        raise CertificateError(f"{step_id}: normal_form_clause parent u{parent_unit} is not an outline parent")
    if parent_unit not in clauses:
        raise CertificateError(f"{step_id}: normal_form_clause parent u{parent_unit} is not available")
    try:
        source_clause_json = json.loads(source_clause_text)
        target_clause_json = json.loads(target_clause_text)
    except json.JSONDecodeError as exc:
        raise CertificateError(f"{step_id}: malformed normal_form_clause clause JSON: {exc}") from exc
    source_clause = normalize_clause(parse_clause(source_clause_json, f"{step_id}.normal_form_clause.source_clause"))
    rendered_target = normalize_clause(parse_clause(target_clause_json, f"{step_id}.normal_form_clause.target_clause"))
    if source_clause != normalize_clause(clauses[parent_unit]):
        raise CertificateError(f"{step_id}: normal_form_clause source_clause does not match parent u{parent_unit}")
    if rendered_target != normalize_clause(target_clause):
        raise CertificateError(f"{step_id}: normal_form_clause target_clause does not match conclusion")
    metadata: dict[str, Any] = {
        "rule": rule or "normal_form",
        "parent": f"u{parent_unit}",
        "source_clause_checked": True,
        "target_clause_checked": True,
    }
    source_proposition = extra_field(fields, "source_proposition")
    target_proposition = extra_field(fields, "target_proposition")
    if source_proposition is not None:
        metadata["source_proposition"] = source_proposition
    if target_proposition is not None:
        metadata["target_proposition"] = target_proposition
    return metadata


def cnf_source_metadata(
    step_id: str,
    fields: list[str],
    parent_numbers: list[int],
    target_clause: tuple[Literal, ...],
) -> dict[str, Any] | None:
    if not fields:
        return None
    rule = extra_field(fields, "rule")
    parent_unit_text = extra_field(fields, "parent_unit")
    parent_kind = extra_field(fields, "parent_kind")
    target_clause_text = extra_field(fields, "target_clause")
    if parent_unit_text is None or target_clause_text is None:
        return None
    try:
        parent_unit = int(parent_unit_text)
    except ValueError as exc:
        raise CertificateError(f"{step_id}: cnf parent_unit is not an integer") from exc
    if parent_unit not in parent_numbers:
        raise CertificateError(f"{step_id}: cnf parent u{parent_unit} is not an outline parent")
    try:
        target_clause_json = json.loads(target_clause_text)
    except json.JSONDecodeError as exc:
        raise CertificateError(f"{step_id}: malformed cnf target_clause JSON: {exc}") from exc
    rendered_target = normalize_clause(parse_clause(target_clause_json, f"{step_id}.cnf.target_clause"))
    if rendered_target != normalize_clause(target_clause):
        raise CertificateError(f"{step_id}: cnf target_clause does not match conclusion")
    metadata: dict[str, Any] = {
        "rule": rule or "cnf",
        "parent": f"u{parent_unit}",
        "parent_kind": parent_kind or "unknown",
        "target_clause_checked": True,
    }
    source_proposition = extra_field(fields, "source_proposition") or extra_field(fields, "source")
    target_proposition = extra_field(fields, "target_proposition") or extra_field(fields, "target")
    parent_clause_count = extra_field(fields, "parent_clause_count")
    clause_index = extra_field(fields, "clause_index")
    clause_count = extra_field(fields, "clause_count")
    clause_parent_unit = extra_field(fields, "clause_parent_unit")
    if source_proposition is not None:
        metadata["source_proposition"] = source_proposition
    if target_proposition is not None:
        metadata["target_proposition"] = target_proposition
    if parent_clause_count is not None:
        try:
            metadata["parent_clause_count"] = int(parent_clause_count)
        except ValueError as exc:
            raise CertificateError(f"{step_id}: cnf parent_clause_count is not an integer") from exc
    if clause_parent_unit is not None:
        try:
            metadata["clause_parent_unit"] = int(clause_parent_unit)
        except ValueError as exc:
            raise CertificateError(f"{step_id}: cnf clause_parent_unit is not an integer") from exc
        if metadata["clause_parent_unit"] != parent_unit:
            raise CertificateError(f"{step_id}: cnf clause_parent_unit does not match parent_unit")
    if clause_index is not None:
        try:
            metadata["clause_index"] = int(clause_index)
        except ValueError as exc:
            raise CertificateError(f"{step_id}: cnf clause_index is not an integer") from exc
        if metadata["clause_index"] < 0:
            raise CertificateError(f"{step_id}: cnf clause_index must be non-negative")
    if clause_count is not None:
        try:
            metadata["clause_count"] = int(clause_count)
        except ValueError as exc:
            raise CertificateError(f"{step_id}: cnf clause_count is not an integer") from exc
        if metadata["clause_count"] <= 0:
            raise CertificateError(f"{step_id}: cnf clause_count must be positive")
    if "clause_index" in metadata and "clause_count" in metadata and metadata["clause_index"] >= metadata["clause_count"]:
        raise CertificateError(f"{step_id}: cnf clause_index is outside clause_count")
    if "parent_clause_count" in metadata and "clause_count" in metadata and metadata["parent_clause_count"] != metadata["clause_count"]:
        raise CertificateError(f"{step_id}: cnf clause_count does not match parent_clause_count")
    return metadata


def cnf_formula_exact_supported(cnf: dict[str, Any], clause: tuple[Literal, ...]) -> bool:
    if cnf.get("parent_kind") != "formula":
        return False
    if cnf.get("clause_index") != 0:
        return False
    count = cnf.get("clause_count", cnf.get("parent_clause_count"))
    if count != 1:
        return False
    source = cnf.get("source_proposition")
    if not isinstance(source, str) or not source:
        return False
    if cnf.get("target_clause_checked") is True and cnf.get("target_proposition") == source:
        return True
    blocked_fragments = (
        "vampire_or",
        "vampire_and",
        "vLAM",
        "vampire_exists",
    )
    if any(fragment in source for fragment in blocked_fragments):
        return False
    for literal in clause:
        if literal.atom.kind == "pred" and any(arg.kind not in {"var", "const"} for arg in literal.atom.args):
            return False
    if "forall " in source:
        return False
    return True


def strip_outer_prop_parens(value: str) -> str:
    value = value.strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        encloses = True
        for index, char in enumerate(value):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    return value
                if depth == 0 and index != len(value) - 1:
                    encloses = False
                    break
        if depth != 0 or not encloses:
            return value
        value = value[1:-1].strip()
    return value


def prop_key(value: str) -> str:
    value = normalize_prop_lambdas(value)
    value = strip_outer_prop_parens(value)
    value = re.sub(r"\b(?:f__true|vampire_true)\b", "True", value)
    value = re.sub(r"\b(?:f__false|vampire_false)\b", "False", value)
    value = value.replace("(", " ").replace(")", " ")
    return " ".join(value.split())


def parse_parenthesized_prop(value: str, start: int) -> tuple[str, int] | None:
    if start >= len(value) or value[start] != "(":
        return None
    depth = 0
    for index in range(start, len(value)):
        char = value[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return value[start + 1:index].strip(), index + 1
    return None


def parse_prop_argument(value: str, start: int) -> tuple[str, int] | None:
    while start < len(value) and value[start].isspace():
        start += 1
    if start >= len(value):
        return None
    if value[start] == "(":
        return parse_parenthesized_prop(value, start)
    index = start
    while index < len(value) and not value[index].isspace() and value[index] != ")":
        index += 1
    if index == start:
        return None
    return value[start:index], index


def parse_fun_prop(value: str) -> tuple[str, str, str] | None:
    value = strip_outer_prop_parens(value.strip())
    if not value.startswith("fun "):
        return None
    cursor = 4
    name_start = cursor
    while cursor < len(value) and (value[cursor].isalnum() or value[cursor] in "_'"):
        cursor += 1
    if cursor == name_start or cursor >= len(value) or value[cursor] != ":":
        return None
    binder = value[name_start:cursor]
    cursor += 1
    sort_start = cursor
    depth = 0
    while cursor + 1 < len(value):
        if value[cursor] == "(":
            depth += 1
        elif value[cursor] == ")":
            depth -= 1
            if depth < 0:
                return None
        elif value[cursor] == "=" and value[cursor + 1] == ">" and depth == 0:
            sort = value[sort_start:cursor].strip()
            body = value[cursor + 2 :].strip()
            if not sort or not body:
                return None
            return binder, require_supported_sort(sort, "lambda binder sort"), body
        cursor += 1
    return None


def prop_token_at(value: str, index: int, token: str) -> bool:
    if not value.startswith(token, index):
        return False
    before_ok = index == 0 or not (value[index - 1].isalnum() or value[index - 1] in "_'")
    after = index + len(token)
    after_ok = after >= len(value) or not (value[after].isalnum() or value[after] in "_'")
    return before_ok and after_ok


def normalize_prop_specials(value: str) -> str:
    result: list[str] = []
    index = 0
    changed = False
    while index < len(value):
        if prop_token_at(value, index, "vPI") or prop_token_at(value, index, "vSIGMA"):
            token = "vPI" if value.startswith("vPI", index) else "vSIGMA"
            parsed = parse_prop_argument(value, index + len(token))
            if parsed is not None:
                argument, cursor = parsed
                function = parse_fun_prop(argument)
                if function is not None:
                    binder, binder_sort, body = function
                    binder = require_megalodon_ident(binder, "quantifier binder")
                    normalized_body = normalize_prop_specials(body)
                    if token == "vPI":
                        result.append(f"(forall {binder}:{sort_type_text(binder_sort)}, {normalized_body})")
                    else:
                        result.append(
                            f"({existential_symbol(binder_sort)} "
                            f"(fun {binder}:{sort_type_text(binder_sort)} => {normalized_body}))"
                        )
                    index = cursor
                    changed = True
                    continue
        if prop_token_at(value, index, "vEQ"):
            first = parse_prop_argument(value, index + len("vEQ"))
            if first is not None:
                left, cursor = first
                second = parse_prop_argument(value, cursor)
                if second is not None:
                    right, cursor = second
                    result.append(f"({normalize_prop_specials(left)} = {normalize_prop_specials(right)})")
                    index = cursor
                    changed = True
                    continue
        result.append(value[index])
        index += 1
    normalized = "".join(result)
    if changed and normalized != value:
        return normalize_prop_specials(normalized)
    return normalized


def lambda_hint_for_body_text(body: str) -> LambdaHint | None:
    body_key = normalize_lambda_hint_body(body)
    for hint in LAMBDA_HINTS:
        if normalize_lambda_hint_body(hint.body) == body_key:
            return hint
    if re.search(r"\bdb0\b", body):
        return LambdaHint(body, "db0", "set")
    return None


def rewrite_db_tokens(value: str, db_context: tuple[str, ...]) -> str:
    if not db_context or "db" not in value:
        return value

    def replace(match: re.Match[str]) -> str:
        index = int(match.group(1))
        if index < len(db_context):
            return require_megalodon_ident(db_context[-1 - index], "lambda binder occurrence")
        return match.group(0)

    return DB_TOKEN_RE.sub(replace, value)


def normalize_prop_lambdas(value: str, db_context: tuple[str, ...] = ()) -> str:
    if "vLAM" not in value:
        return normalize_prop_specials(rewrite_db_tokens(value, db_context))
    result: list[str] = []
    index = 0
    while index < len(value):
        if not value.startswith("vLAM", index):
            next_lambda = value.find("vLAM", index + 1)
            if next_lambda == -1:
                result.append(rewrite_db_tokens(value[index:], db_context))
                index = len(value)
            else:
                result.append(rewrite_db_tokens(value[index:next_lambda], db_context))
                index = next_lambda
            continue
        before_ok = index == 0 or not (value[index - 1].isalnum() or value[index - 1] == "_")
        after = index + len("vLAM")
        after_ok = after >= len(value) or value[after].isspace()
        if not before_ok or not after_ok:
            result.append(rewrite_db_tokens(value[index : index + 1], db_context))
            index += 1
            continue
        cursor = after
        while cursor < len(value) and value[cursor].isspace():
            cursor += 1
        parsed = parse_parenthesized_prop(value, cursor)
        if parsed is None:
            result.append(rewrite_db_tokens(value[index : index + 1], db_context))
            index += 1
            continue
        body, cursor = parsed
        hint = lambda_hint_for_body_text(body)
        if hint is None:
            result.append(rewrite_db_tokens(value[index:cursor], db_context))
            index = cursor
            continue
        binder = f"db{len(db_context)}"
        normalized_body = normalize_prop_lambdas(body, (*db_context, binder))
        require_megalodon_ident(binder, "lambda binder")
        result.append(f"(fun {binder}:{sort_type_text(hint.binder_sort)} => {normalized_body})")
        index = cursor
    return normalize_prop_specials("".join(result))


def parse_vampire_and_prop(value: str) -> tuple[str, str] | None:
    return parse_binary_prop(value, "vampire_and")


def parse_vampire_or_prop(value: str) -> tuple[str, str] | None:
    return parse_binary_prop(value, "vampire_or")


def parse_binary_prop(value: str, prefix: str) -> tuple[str, str] | None:
    value = strip_outer_prop_parens(value)
    if not value.startswith(prefix):
        return None
    index = len(prefix)
    if index >= len(value) or not value[index].isspace():
        return None
    while index < len(value) and value[index].isspace():
        index += 1
    left = parse_parenthesized_prop(value, index)
    if left is None:
        return None
    left_text, index = left
    while index < len(value) and value[index].isspace():
        index += 1
    right = parse_parenthesized_prop(value, index)
    if right is None:
        return None
    right_text, index = right
    if value[index:].strip():
        return None
    return left_text, right_text


def parse_forall_prefix(value: str) -> tuple[list[tuple[str, str]], str]:
    binders: list[tuple[str, str]] = []
    rest = strip_outer_prop_parens(value)
    while rest.startswith("forall "):
        match = re.match(r"forall\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^,]+),\s*(.*)\Z", rest, re.S)
        if match is None:
            break
        name = require_megalodon_ident(match.group(1), "CNF formula binder")
        sort = require_supported_sort(match.group(2).strip(), f"CNF formula binder {name}")
        binders.append((name, sort))
        rest = strip_outer_prop_parens(match.group(3))
    return binders, rest


def conjunction_projection_path(source: str, target: str) -> tuple[str, ...] | None:
    source_key = prop_key(source)
    target_key = prop_key(target)
    if source_key == target_key:
        return ()
    parsed = parse_vampire_and_prop(source)
    if parsed is None:
        return None
    left, right = parsed
    if prop_key(left) == target_key:
        return ("left",)
    if prop_key(right) == target_key:
        return ("right",)
    left_path = conjunction_projection_path(left, target)
    if left_path:
        return ("left", *left_path)
    right_path = conjunction_projection_path(right, target)
    if right_path:
        return ("right", *right_path)
    return None


def cnf_formula_conjunct_path(cnf: dict[str, Any]) -> tuple[str, ...] | None:
    if cnf.get("parent_kind") != "formula" or cnf.get("target_clause_checked") is not True:
        return None
    source = cnf.get("source_proposition")
    target = cnf.get("target_proposition")
    if not isinstance(source, str) or not isinstance(target, str) or not source or not target:
        return None
    source_binders, source_body = parse_forall_prefix(source)
    target_binders, target_body = parse_forall_prefix(target)
    if source_binders != target_binders:
        return conjunction_projection_path(source, target)
    path = conjunction_projection_path(source_body, target_body)
    if path:
        return path
    return None


def disjunction_contains_projection(target: str, source: str) -> bool:
    if prop_key(target) == prop_key(source):
        return True
    parsed = parse_vampire_or_prop(target)
    if parsed is None:
        return False
    left, right = parsed
    return disjunction_contains_projection(left, source) or disjunction_contains_projection(right, source)


def formula_projection_supported(source: str, target: str) -> bool:
    try:
        formula_projection_proof_text("Hprojection", source, target)
    except CertificateError:
        return False
    return True


def formula_projection_structurally_supported(source: str, target: str) -> bool:
    if prop_key(source) == prop_key(target):
        return True
    if disjunction_contains_projection(target, source):
        return True
    and_parts = parse_vampire_and_prop(source)
    if and_parts is not None:
        left, right = and_parts
        return formula_projection_supported(left, target) or formula_projection_supported(right, target)
    or_parts = parse_vampire_or_prop(source)
    if or_parts is not None:
        left, right = or_parts
        return formula_projection_supported(left, target) and formula_projection_supported(right, target)
    source_binders, source_body = parse_forall_prefix(source)
    target_binders, target_body = parse_forall_prefix(target)
    if source_binders and source_binders == target_binders:
        return formula_projection_supported(source_body, target_body)
    return False


def cnf_formula_projection_supported(cnf: dict[str, Any]) -> bool:
    if cnf.get("parent_kind") != "formula" or cnf.get("target_clause_checked") is not True:
        return False
    source = cnf.get("source_proposition")
    target = cnf.get("target_proposition")
    if not isinstance(source, str) or not isinstance(target, str) or not source or not target:
        return False
    if prop_key(source) == prop_key(target):
        return False
    if parse_vampire_or_prop(source) is None and parse_vampire_and_prop(source) is None and not source.startswith("forall "):
        return False
    return formula_projection_supported(source, target)


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


def embedded_certificate_json_data(text: str) -> dict[str, Any] | None:
    start = text.find(CERTIFICATE_JSON_START)
    if start < 0:
        return None
    start += len(CERTIFICATE_JSON_START)
    end = text.find(CERTIFICATE_JSON_END, start)
    if end < 0:
        raise CertificateError("embedded certificate JSON start has no matching end marker")
    blob = text[start:end].strip()
    try:
        data = json.loads(blob)
    except json.JSONDecodeError as exc:
        raise CertificateError(f"embedded certificate JSON is malformed: {exc}") from exc
    if not isinstance(data, dict):
        raise CertificateError("embedded certificate JSON must be an object")
    if data.get("format") != FORMAT:
        raise CertificateError(f"embedded certificate JSON has unsupported format {data.get('format')!r}")
    if data.get("version") != VERSION:
        raise CertificateError(f"embedded certificate JSON has unsupported version {data.get('version')!r}")
    steps = data.get("steps")
    if not isinstance(steps, list) or not all(isinstance(step, dict) for step in steps):
        raise CertificateError("embedded certificate JSON steps must be an object list")
    return data


def embedded_certificate_json_summary(text: str) -> dict[str, Any] | None:
    data = embedded_certificate_json_data(text)
    if data is None:
        return None
    steps = data["steps"]
    rules: dict[str, int] = {}
    missing_ids = 0
    missing_clauses = 0
    derived_fallbacks = 0
    for index, step in enumerate(steps):
        rule = step.get("rule")
        if not isinstance(rule, str) or rule not in MVP_RULES:
            raise CertificateError(f"embedded certificate JSON step {index} has unsupported rule {rule!r}")
        rules[rule] = rules.get(rule, 0) + 1
        if "id" not in step:
            missing_ids += 1
        if "clause" not in step and rule not in {"equality_symmetry"}:
            missing_clauses += 1
        source = step.get("source")
        if isinstance(source, dict) and source.get("kind") == "vampire_unexpanded_derived_clause":
            derived_fallbacks += 1
    return {
        "steps": len(steps),
        "rules": dict(sorted(rules.items())),
        "missing_ids": missing_ids,
        "missing_clauses": missing_clauses,
        "derived_fallbacks": derived_fallbacks,
    }


def certificate_from_vampire_outline(text: str, problem: str) -> dict[str, Any]:
    global LAMBDA_HINTS
    embedded_summary = embedded_certificate_json_summary(text)
    step_meta: dict[int, dict[str, Any]] = {}
    clause_json: dict[int, list[Any]] = {}
    certificate_steps: dict[int, dict[str, Any]] = {}
    certificate_step_lists: dict[int, list[dict[str, Any]]] = {}
    replay_kinds: dict[int, str] = {}
    extras: dict[int, dict[str, list[str]]] = {}
    variable_sorts: dict[int, dict[str, str]] = {}
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
        match = VARIABLE_SORTS_RE.match(line)
        if match:
            step_no = int(match.group(1))
            try:
                entries = json.loads(match.group(2))
            except json.JSONDecodeError as exc:
                raise CertificateError(f"line {lineno}: malformed variable-sort JSON: {exc}") from exc
            variable_sorts[step_no] = parse_variable_sort_entries(entries, f"u{step_no}.variable_sorts")
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

    lambda_hints = parse_lambda_hints(extras)
    LAMBDA_HINTS = tuple(
        LambdaHint(
            body=item["body"],
            binder=item["binder"],
            binder_sort=item["binder_sort"],
        )
        for item in lambda_hints
    )

    steps: list[dict[str, Any]] = []
    clauses: dict[int, tuple[Literal, ...]] = {}
    reconstruction_stats = {
        "explicit_step_units": 0,
        "explicit_substeps": 0,
        "inferred_definition_input_units": 0,
        "inferred_resolution_units": 0,
        "inferred_paramodulation_units": 0,
        "derived_assumption_units": 0,
    }
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
            reconstruction_stats["explicit_step_units"] += 1
            prepared_steps: list[dict[str, Any]] = []
            for index, explicit in enumerate(explicit_steps):
                step = dict(explicit)
                if "id" not in step and index == len(explicit_steps) - 1:
                    step["id"] = step_id
                if "clause" not in step and index == len(explicit_steps) - 1:
                    step["clause"] = clause_json[step_no]
                if "id" not in step or "clause" not in step:
                    raise CertificateError(f"{step_id}: explicit certificate substep {index} needs id and clause")
                if step_no in variable_sorts:
                    step.setdefault("variable_sorts", variable_sorts[step_no])
                prepared_steps.append(step)
            expanded_steps = expand_explicit_certificate_steps(
                step_id,
                prepared_steps,
                {f"u{parent_no}": parent_clause for parent_no, parent_clause in clauses.items()},
            )
            reconstruction_stats["explicit_substeps"] += len(expanded_steps)
            if step_no in variable_sorts:
                for step in expanded_steps:
                    step.setdefault("variable_sorts", variable_sorts[step_no])
            steps.extend(expanded_steps)
            clauses[step_no] = clause
            continue
        if explicit_step is not None:
            reconstruction_stats["explicit_step_units"] += 1
            reconstruction_stats["explicit_substeps"] += 1
            step = dict(explicit_step)
            step["id"] = step_id
            step["clause"] = clause_json[step_no]
            if step_no in variable_sorts:
                step.setdefault("variable_sorts", variable_sorts[step_no])
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
            reconstruction_stats["inferred_definition_input_units"] += 1
            if step_no in variable_sorts:
                definition_input.setdefault("variable_sorts", variable_sorts[step_no])
            steps.append(definition_input)
        elif replay_kind in RESOLUTION_LIKE_REPLAY_KINDS:
            if len(parent_clause_numbers) != 2:
                raise CertificateError(
                    f"{step_id}: {replay_kind} bridge requires exactly two printed clause parents"
                )
            left_no, right_no = parent_clause_numbers
            pivot = infer_resolution_pivot(step_id, clauses[left_no], clauses[right_no], clause)
            reconstruction_stats["inferred_resolution_units"] += 1
            steps.append(
                {
                    "id": step_id,
                    "rule": "resolve",
                    "parents": [f"u{left_no}", f"u{right_no}"],
                    "pivot": literal_to_json(pivot),
                    "clause": clause_json[step_no],
                    **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                }
            )
        elif replay_kind in {"forward_demodulation", "backward_demodulation", "definition_rewrite"}:
            paramodulation = infer_paramodulation_step(step_id, parent_clause_numbers, clauses, clause, clause_json[step_no])
            if paramodulation is not None:
                reconstruction_stats["inferred_paramodulation_units"] += 1
                if step_no in variable_sorts:
                    paramodulation.setdefault("variable_sorts", variable_sorts[step_no])
                steps.append(paramodulation)
            else:
                paramodulation_with_symmetry = infer_paramodulation_then_symmetry_steps(step_id, parent_clause_numbers, clauses, clause)
                if paramodulation_with_symmetry is not None:
                    reconstruction_stats["inferred_paramodulation_units"] += 1
                    inferred_steps, _intermediate_clause = paramodulation_with_symmetry
                    if step_no in variable_sorts:
                        for inferred_step in inferred_steps:
                            inferred_step.setdefault("variable_sorts", variable_sorts[step_no])
                    steps.extend(inferred_steps)
                else:
                    source_kind = "vampire_input_clause" if not meta["parents"] else "vampire_derived_clause"
                    if source_kind == "vampire_derived_clause":
                        reconstruction_stats["derived_assumption_units"] += 1
                    steps.append(
                        {
                            "id": step_id,
                            "rule": "input",
                            "clause": clause_json[step_no],
                            **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                            "source": {
                                "kind": source_kind,
                                "name": step_id,
                                "vampire_rule": meta["rule"],
                                "vampire_parents": [f"u{parent}" for parent in meta["parents"]],
                                **({"replay_kind": replay_kind} if replay_kind else {}),
                            },
                        }
                    )
        elif replay_kind == "avatar_component":
            avatar_component = avatar_component_metadata(
                step_id,
                extras.get(step_no, {}).get("split_dependency", []),
            )
            if avatar_component is None:
                raise CertificateError(f"{step_id}: avatar_component is missing checked split dependency metadata")
            reconstruction_stats["avatar_component_units"] = reconstruction_stats.get("avatar_component_units", 0) + 1
            source: dict[str, Any] = {
                "kind": "vampire_avatar_component_clause",
                "name": step_id,
                "vampire_rule": meta["rule"],
                "vampire_parents": [f"u{parent}" for parent in meta["parents"]],
                "replay_kind": replay_kind,
            }
            steps.append(
                {
                    "id": step_id,
                    "rule": "avatar_component",
                    "parents": [f"u{parent}" for parent in meta["parents"]],
                    "split_var": avatar_component["split_var"],
                    "split_positive": avatar_component["split_positive"],
                    "clause": clause_json[step_no],
                    **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                    "source": source,
                }
            )
        elif not parent_clause_numbers or replay_kind in DERIVED_ASSUMPTION_REPLAY_KINDS:
            source_kind = "vampire_input_clause" if not meta["parents"] else "vampire_derived_clause"
            if source_kind == "vampire_derived_clause":
                reconstruction_stats["derived_assumption_units"] += 1
            source: dict[str, Any] = {
                "kind": source_kind,
                "name": step_id,
                "vampire_rule": meta["rule"],
                "vampire_parents": [f"u{parent}" for parent in meta["parents"]],
            }
            if replay_kind:
                source["replay_kind"] = replay_kind
            if replay_kind == "normal_form":
                normal_form_clause = normal_form_clause_source_metadata(
                    step_id,
                    extras.get(step_no, {}).get("normal_form_clause", []),
                    parent_clause_numbers,
                    clauses,
                    clause,
                )
                if normal_form_clause is not None:
                    source["normal_form_clause"] = normal_form_clause
            if replay_kind == "cnf":
                cnf = cnf_source_metadata(
                    step_id,
                    extras.get(step_no, {}).get("cnf", []),
                    meta["parents"],
                    clause,
                )
                if cnf is not None:
                    source["cnf"] = cnf
                    source_proposition = cnf.get("source_proposition")
                    parent = cnf.get("parent")
                    if (
                        cnf_formula_exact_supported(cnf, clause)
                        and isinstance(source_proposition, str)
                        and isinstance(parent, str)
                    ):
                        reconstruction_stats["cnf_formula_exact_units"] = reconstruction_stats.get("cnf_formula_exact_units", 0) + 1
                        if source_kind == "vampire_derived_clause":
                            reconstruction_stats["derived_assumption_units"] -= 1
                        steps.append(
                            {
                                "id": step_id,
                                "rule": "cnf_formula_exact",
                                "formula_parent": parent,
                                "proposition": source_proposition,
                                "clause": clause_json[step_no],
                                **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                                "source": source,
                            }
                        )
                        clauses[step_no] = clause
                        continue
                    conjunct_path = cnf_formula_conjunct_path(cnf)
                    target_proposition = cnf.get("target_proposition")
                    if (
                        conjunct_path
                        and isinstance(source_proposition, str)
                        and isinstance(target_proposition, str)
                        and isinstance(parent, str)
                    ):
                        reconstruction_stats["cnf_formula_conjunct_units"] = reconstruction_stats.get("cnf_formula_conjunct_units", 0) + 1
                        if source_kind == "vampire_derived_clause":
                            reconstruction_stats["derived_assumption_units"] -= 1
                        steps.append(
                            {
                                "id": step_id,
                                "rule": "cnf_formula_conjunct",
                                "formula_parent": parent,
                                "source_proposition": source_proposition,
                                "proposition": target_proposition,
                                "path": list(conjunct_path),
                                "clause": clause_json[step_no],
                                **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                                "source": source,
                            }
                        )
                        clauses[step_no] = clause
                        continue
                    if (
                        isinstance(source_proposition, str)
                        and isinstance(target_proposition, str)
                        and isinstance(parent, str)
                        and cnf_formula_projection_supported(cnf)
                        and formula_projection_supported(
                            source_proposition,
                            clause_formula_prop_text(clause, None, variable_sorts.get(step_no, {})),
                        )
                    ):
                        reconstruction_stats["cnf_formula_projection_units"] = reconstruction_stats.get("cnf_formula_projection_units", 0) + 1
                        if source_kind == "vampire_derived_clause":
                            reconstruction_stats["derived_assumption_units"] -= 1
                        steps.append(
                            {
                                "id": step_id,
                                "rule": "cnf_formula_projection",
                                "formula_parent": parent,
                                "source_proposition": source_proposition,
                                "proposition": target_proposition,
                                "clause": clause_json[step_no],
                                **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                                "source": source,
                            }
                        )
                        clauses[step_no] = clause
                        continue
            steps.append(
                {
                    "id": step_id,
                    "rule": "input",
                    "clause": clause_json[step_no],
                    **({"variable_sorts": variable_sorts[step_no]} if step_no in variable_sorts else {}),
                    "source": source,
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
    result["outline_reconstruction"] = reconstruction_stats
    if embedded_summary is not None:
        result["embedded_certificate_json"] = embedded_summary
    if lambda_hints:
        result["lambda_hints"] = lambda_hints
    return result


def term_text(term: Term) -> str:
    return term_text_with_context(term, ())


def term_contains_symbol(term: Term, name: str) -> bool:
    return term.name == name or any(term_contains_symbol(arg, name) for arg in term.args)


def term_text_expected(
    term: Term,
    expected_sort: str | None,
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    db_context: tuple[str, ...] = (),
) -> str:
    symbol_sorts = symbol_sorts or {}
    if expected_sort is not None:
        expected_sort = require_supported_sort(expected_sort, "expected term sort")
    if term.kind == "const" and term.name in {"vPI", "vSIGMA"} and expected_sort is not None:
        parts = split_sort(expected_sort)
        if len(parts) == 2 and require_supported_sort(parts[1], "quantifier result sort") == "prop":
            predicate_sort = require_supported_sort(parts[0], "quantifier predicate sort")
            predicate_parts = split_sort(predicate_sort)
            if len(predicate_parts) == 2 and require_supported_sort(predicate_parts[1], "quantifier body sort") == "prop":
                binder_sort = require_supported_sort(predicate_parts[0], "quantifier binder sort")
                predicate_name = "cert_Q"
                binder_name = "cert_x"
                if term.name == "vPI":
                    body = f"forall {binder_name}:{sort_type_text(binder_sort)}, ({predicate_name} {binder_name})"
                else:
                    body = f"{existential_symbol(binder_sort)} (fun {binder_name}:{sort_type_text(binder_sort)} => ({predicate_name} {binder_name}))"
                return f"(fun {predicate_name}:{sort_type_text(predicate_sort)} => {body})"
    if named_binary_application(term, "vEQ") is not None or quantifier_application(term) is not None:
        return term_text_with_context(term, db_context)
    if term.kind == "app" and term.name == "vLAM" and len(term.args) == 1 and expected_sort is not None:
        parts = split_sort(expected_sort)
        if len(parts) >= 2:
            binder_sort = require_supported_sort(parts[0], "lambda binder sort")
            body_sort = sort_from_parts(parts[1:])
            binder = f"db{len(db_context)}"
            body = term_text_expected(term.args[0], body_sort, symbol_sorts, (*db_context, binder))
            return (
                f"(fun {require_megalodon_ident(binder, 'lambda binder')}"
                f":{sort_type_text(binder_sort)} => {body})"
            )
    if expected_sort is not None:
        eta_expanded = eta_expand_partial_application(term, expected_sort, symbol_sorts, db_context)
        if eta_expanded is not None:
            return eta_expanded
    if term.kind == "apply" and len(term.args) == 2:
        function = term.args[0]
        argument = term.args[1]
        if (
            expected_sort is not None
            and function.kind == "app"
            and function.name == "vLAM"
            and len(function.args) == 1
        ):
            argument_sort = term_sort_guess(argument, symbol_sorts, db_context) or "set"
            function_sort = sort_from_parts((argument_sort, expected_sort))
            function_text = term_text_expected(function, function_sort, symbol_sorts, db_context)
            argument_text = term_text_expected(argument, argument_sort, symbol_sorts, db_context)
            return f"({function_text} {argument_text})"
        function_sort: str | None = None
        head, existing_args = term_spine(function)
        if head.kind == "const":
            signature = symbol_sorts.get(head.name)
            if signature is not None and len(signature) > len(existing_args):
                function_sort = sort_from_parts(signature[len(existing_args):])
        if function_sort is not None:
            parts = split_sort(function_sort)
            if len(parts) >= 2:
                argument_sort = require_supported_sort(parts[0], "application argument sort")
                if (
                    head.kind == "const"
                    and head.name in {"vPI", "vSIGMA"}
                    and argument.kind == "app"
                    and argument.name == "vLAM"
                    and len(argument.args) == 1
                ):
                    lambda_parts = split_sort(argument_sort)
                    if len(lambda_parts) >= 2 and require_supported_sort(lambda_parts[-1], "quantifier body sort") == "prop":
                        binder_sort = require_supported_sort(lambda_parts[0], "quantifier binder sort")
                        binder = f"db{len(db_context)}"
                        body = term_text_expected(argument.args[0], "prop", symbol_sorts, (*db_context, binder))
                        binder_text = require_megalodon_ident(binder, "quantifier binder")
                        if head.name == "vPI":
                            return f"(forall {binder_text}:{sort_type_text(binder_sort)}, {body})"
                        return f"({existential_symbol(binder_sort)} (fun {binder_text}:{sort_type_text(binder_sort)} => {body}))"
                function_text = term_text_expected(function, None, symbol_sorts, db_context)
                argument_text = term_text_expected(argument, argument_sort, symbol_sorts, db_context)
                return f"({function_text} {argument_text})"
        if expected_sort is not None and term_contains_symbol(function, "vLAM"):
            argument_sort = term_sort_guess(argument, symbol_sorts, db_context) or "set"
            function_sort = sort_from_parts((argument_sort, expected_sort))
            function_text = term_text_expected(function, function_sort, symbol_sorts, db_context)
            argument_text = term_text_expected(argument, argument_sort, symbol_sorts, db_context)
            return f"({function_text} {argument_text})"
        return f"({term_text_expected(function, None, symbol_sorts, db_context)} {term_text_expected(argument, None, symbol_sorts, db_context)})"
    if term.kind == "app" and term.name != "vLAM":
        signature = symbol_sorts.get(term.name)
        if signature is not None and len(signature) >= len(term.args) + 1:
            args = " ".join(
                term_text_expected(arg, arg_sort, symbol_sorts, db_context)
                for arg, arg_sort in zip(term.args, signature)
            )
            name = require_megalodon_ident(term.name, "term")
            return f"({name} {args})" if args else name
    return term_text_with_context(term, db_context)


def term_sort_guess(
    term: Term,
    symbol_sorts: dict[str, tuple[str, ...]],
    db_context: tuple[str, ...] = (),
) -> str | None:
    if term.kind == "const":
        db_match = DB_NAME_RE.match(term.name)
        if db_match is not None:
            return "set"
        parts = symbol_sorts.get(term.name)
        if parts is not None and len(parts) == 1:
            return parts[0]
        return None
    if term.kind == "app" and term.name == "vLAM" and len(term.args) == 1:
        return None
    head, args = term_spine(term)
    if head.kind == "const" and args:
        signature = symbol_sorts.get(head.name)
        if signature is not None and len(signature) >= len(args) + 1:
            return sort_from_parts(signature[len(args):])
    return None


def eta_expand_partial_application(
    term: Term,
    expected_sort: str,
    symbol_sorts: dict[str, tuple[str, ...]],
    db_context: tuple[str, ...],
) -> str | None:
    expected_parts = split_sort(expected_sort)
    if len(expected_parts) < 2:
        return None
    if term.kind in {"var", "const"} or (term.kind == "app" and not term.args):
        return None
    head, existing_args = term_spine(term)
    if head.kind != "const":
        return None
    signature = symbol_sorts.get(head.name)
    if signature is None or len(signature) <= len(existing_args):
        return None
    remaining_sort = sort_from_parts(signature[len(existing_args):])
    if remaining_sort != expected_sort:
        return None
    binders = [
        f"cert_eta{len(db_context) + index}"
        for index in range(len(expected_parts) - 1)
    ]
    rendered_args = [
        term_text_expected(arg, arg_sort, symbol_sorts, db_context)
        for arg, arg_sort in zip(existing_args, signature)
    ]
    rendered_args.extend(require_megalodon_ident(binder, "eta binder occurrence") for binder in binders)
    result = f"({require_megalodon_ident(head.name, 'eta-expanded head')} {' '.join(rendered_args)})"
    for binder, binder_sort in reversed(list(zip(binders, expected_parts[:-1]))):
        result = (
            f"(fun {require_megalodon_ident(binder, 'eta binder')}"
            f":{sort_type_text(binder_sort)} => {result})"
        )
    return result


def term_text_with_context(term: Term, db_context: tuple[str, ...]) -> str:
    v_eq_args = named_binary_application(term, "vEQ")
    if v_eq_args is not None:
        left, right = v_eq_args
        return f"({term_text_with_context(left, db_context)} = {term_text_with_context(right, db_context)})"
    quantifier = quantifier_application(term)
    if quantifier is not None:
        kind, body_term, lambda_hint = quantifier
        binder = f"db{len(db_context)}"
        body = term_text_with_context(body_term.args[0], (*db_context, binder))
        binder_text = require_megalodon_ident(binder, "quantifier binder")
        sort_text = sort_type_text(lambda_hint.binder_sort)
        if kind == "vPI":
            return f"(forall {binder_text}:{sort_text}, {body})"
        return f"({existential_symbol(lambda_hint.binder_sort)} (fun {binder_text}:{sort_text} => {body}))"
    lambda_hint = lambda_hint_for_term(term)
    if lambda_hint is not None:
        binder = f"db{len(db_context)}"
        body = term_text_with_context(term.args[0], (*db_context, binder))
        return (
            f"(fun {require_megalodon_ident(binder, 'lambda binder')}"
            f":{sort_type_text(lambda_hint.binder_sort)} => {body})"
        )
    if term.kind == "const":
        db_match = DB_NAME_RE.match(term.name)
        if db_match is not None:
            index = int(db_match.group(1))
            if index < len(db_context):
                return require_megalodon_ident(db_context[-1 - index], "lambda binder occurrence")
    if term.kind in {"var", "const"}:
        return require_megalodon_ident(term.name, "term")
    if term.kind == "app":
        name = require_megalodon_ident(term.name, "term")
        args = " ".join(term_text_with_context(arg, db_context) for arg in term.args)
        return f"({name} {args})" if args else name
    if term.kind == "apply":
        return f"({term_text_with_context(term.args[0], db_context)} {term_text_with_context(term.args[1], db_context)})"
    raise CertificateError(f"cannot render term kind {term.kind!r}")


def named_binary_application(term: Term, name: str) -> tuple[Term, Term] | None:
    if term.kind == "app" and term.name == name and len(term.args) == 2:
        return term.args[0], term.args[1]
    if term.kind != "apply":
        return None
    spine = application_spine(term)
    if len(spine) != 3:
        return None
    head = spine[0]
    if head.kind == "const" and head.name == name:
        return spine[1], spine[2]
    if head.kind == "app" and head.name == name and not head.args:
        return spine[1], spine[2]
    return None


def quantifier_application(term: Term) -> tuple[str, Term, LambdaHint] | None:
    head_name: str | None = None
    body_term: Term | None = None
    if term.kind == "app" and term.name in {"vPI", "vSIGMA"} and len(term.args) == 1:
        head_name = term.name
        body_term = term.args[0]
    elif term.kind == "apply":
        spine = application_spine(term)
        if len(spine) == 2:
            head, argument = spine
            if head.kind == "const":
                head_name = head.name
            elif head.kind == "app" and not head.args:
                head_name = head.name
            body_term = argument
    if head_name not in {"vPI", "vSIGMA"} or body_term is None:
        return None
    lambda_hint = lambda_hint_for_term(body_term)
    if lambda_hint is None:
        return None
    return head_name, body_term, lambda_hint


def lambda_body_text(term: Term, binder: str) -> str:
    if term.kind == "const" and term.name == binder:
        return require_megalodon_ident(term.name, "lambda binder occurrence")
    return term_text(term)


def lambda_hint_for_term(term: Term) -> LambdaHint | None:
    if term.kind != "app" or term.name != "vLAM" or len(term.args) != 1:
        return None
    body_key = normalize_lambda_hint_body(term_hint_text(term.args[0]))
    for hint in LAMBDA_HINTS:
        if normalize_lambda_hint_body(hint.body) == body_key:
            return hint
    unique_binders = {(hint.binder, hint.binder_sort) for hint in LAMBDA_HINTS}
    if len(unique_binders) == 1:
        binder, binder_sort = next(iter(unique_binders))
        return LambdaHint(term_hint_text(term.args[0]), binder, binder_sort)
    return None


def lambda_binder_sorts() -> dict[str, str]:
    result: dict[str, str] = {}
    for hint in LAMBDA_HINTS:
        result.setdefault(hint.binder, hint.binder_sort)
    return result


def lambda_default_binder_sort() -> str | None:
    sorts = {hint.binder_sort for hint in LAMBDA_HINTS}
    if len(sorts) == 1:
        return next(iter(sorts))
    return None


def term_hint_text(term: Term) -> str:
    if term.kind in {"var", "const"}:
        return term.name
    if term.kind == "apply":
        spine = application_spine(term)
        return " ".join(parenthesize_hint_arg(item) for item in spine)
    if term.kind == "app":
        if not term.args:
            return term.name
        return term.name + " " + " ".join(parenthesize_hint_arg(arg) for arg in term.args)
    return term.name


def application_spine(term: Term) -> list[Term]:
    if term.kind != "apply":
        return [term]
    return application_spine(term.args[0]) + [term.args[1]]


def parenthesize_hint_arg(term: Term) -> str:
    text = term_hint_text(term)
    if term.kind in {"var", "const"}:
        return text
    return f"({text})"


def normalize_lambda_hint_body(value: str) -> str:
    return " ".join(value.replace("(", " ").replace(")", " ").split())


def sort_symbol_suffix(sort: str) -> str:
    normalized = require_supported_sort(sort, "sort symbol suffix")
    normalized = normalized.replace("->", "_to_")
    normalized = normalized.replace("(", "lp_").replace(")", "_rp")
    normalized = re.sub(r"[^A-Za-z0-9_]", "_", normalized)
    normalized = re.sub(r"_+", "_", normalized).strip("_")
    return normalized


def equality_symbol(sort: str) -> str:
    require_supported_sort(sort, "equality sort")
    if sort == "set":
        return "eq"
    if sort == "prop":
        return "vampire_eq_prop"
    return "vampire_eq_" + sort_symbol_suffix(sort)


def existential_symbol(sort: str) -> str:
    return "vampire_exists_" + sort_symbol_suffix(sort)


def sort_type_text(sort: str) -> str:
    require_supported_sort(sort, "sort")
    if "->" in sort:
        return f"({sort})"
    return sort


def sort_from_parts(parts: tuple[str, ...]) -> str:
    if not parts:
        raise CertificateError("empty sort parts")
    normalized_parts = [require_supported_sort(part, "sort part") for part in parts]
    rendered_parts = [
        f"({part})" if "->" in part else part
        for part in normalized_parts
    ]
    return "->".join(rendered_parts)


def existential_definition(sort: str) -> str:
    sort_text = sort_type_text(sort)
    symbol = existential_symbol(sort)
    return (
        f"Definition {symbol} : ({sort_text}->prop)->prop := "
        f"fun Q:{sort_text}->prop => forall P:prop, (forall x:{sort_text}, Q x -> P) -> P."
    )


def equality_definition(sort: str) -> str:
    symbol = equality_symbol(sort)
    if sort == "set":
        return "Definition eq : set->set->prop := fun x y:set => forall Q:set->set->prop, Q x y -> Q y x."
    sort_text = sort_type_text(sort)
    return f"Definition {symbol} : {sort_text}->{sort_text}->prop := fun x y:{sort_text} => forall Q:{sort_text}->prop, Q x -> Q y."


def atom_text(atom: Term, symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    symbol_sorts = symbol_sorts or {}
    if atom.kind == "opaque":
        return require_megalodon_ident(atom.name, "atom")
    if atom.kind == "pred":
        name = require_megalodon_ident(atom.name, "atom")
        signature = symbol_sorts.get(atom.name)
        if signature is not None and len(signature) == len(atom.args) + 1:
            args = " ".join(
                term_text_expected(arg, arg_sort, symbol_sorts)
                for arg, arg_sort in zip(atom.args, signature)
            )
        else:
            args = " ".join(term_text_expected(arg, None, symbol_sorts) for arg in atom.args)
        return f"({name} {args})" if args else name
    if atom.kind == "eq" and len(atom.args) == 2:
        if atom.name != "set":
            return (
                f"({equality_symbol(atom.name)} "
                f"{term_text_expected(atom.args[0], atom.name, symbol_sorts)} "
                f"{term_text_expected(atom.args[1], atom.name, symbol_sorts)})"
            )
        return f"({term_text_expected(atom.args[0], 'set', symbol_sorts)} = {term_text_expected(atom.args[1], 'set', symbol_sorts)})"
    raise CertificateError(f"cannot render atom kind {atom.kind!r}")


def literal_text(literal: Literal, symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    atom = atom_text(literal.atom, symbol_sorts)
    if literal.polarity:
        return atom
    return f"({atom} -> False)"


def clause_body_text(clause: tuple[Literal, ...], symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    normalized = normalize_clause(clause)
    if not normalized:
        return "False"
    parts = [literal_text(literal, symbol_sorts) for literal in normalized]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"({part} \\/ {result})"
    return result


def clause_formula_prop_text(
    clause: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
) -> str:
    symbol_sorts = symbol_sorts or {}
    normalized = normalize_clause(clause)
    if not normalized:
        result = "False"
    else:
        parts = [literal_text(literal, symbol_sorts) for literal in normalized]
        result = parts[-1]
        for part in reversed(parts[:-1]):
            result = f"vampire_or ({part}) ({result})"
    var_sorts = clause_var_sorts(clause, symbol_sorts, explicit_var_sorts)
    for name in reversed(clause_free_vars_sorted(clause, symbol_sorts)):
        result = f"forall {require_megalodon_ident(name, 'binder')}:{sort_type_text(var_sorts[name])}, {result}"
    return result


def clause_formula_body_text(clause: tuple[Literal, ...], symbol_sorts: dict[str, tuple[str, ...]] | None = None) -> str:
    normalized = normalize_clause(clause)
    if not normalized:
        return "False"
    parts = [literal_text(literal, symbol_sorts) for literal in normalized]
    result = parts[-1]
    for part in reversed(parts[:-1]):
        result = f"vampire_or ({part}) ({result})"
    return result


def term_free_vars(term: Term) -> set[str]:
    return term_free_vars_with_context(term, ())


def term_free_vars_with_context(term: Term, db_context: tuple[str, ...]) -> set[str]:
    quantifier = quantifier_application(term)
    if quantifier is not None:
        _kind, body_term, _lambda_hint = quantifier
        binder = f"db{len(db_context)}"
        return term_free_vars_with_context(body_term.args[0], (*db_context, binder))
    lambda_hint = lambda_hint_for_term(term)
    if lambda_hint is not None:
        binder = f"db{len(db_context)}"
        return term_free_vars_with_context(term.args[0], (*db_context, binder))
    if term.kind == "var":
        return {term.name}
    if term.kind == "const":
        db_match = DB_NAME_RE.match(term.name)
        if db_match is not None:
            index = int(db_match.group(1))
            if index < len(db_context):
                return set()
            return {term.name}
    if term.kind == "const" and term.name in lambda_binder_sorts():
        return {term.name}
    result: set[str] = set()
    for arg in term.args:
        result.update(term_free_vars_with_context(arg, db_context))
    return result


def literal_free_vars(literal: Literal) -> set[str]:
    return term_free_vars(literal.atom)


def clause_free_vars(clause: tuple[Literal, ...]) -> tuple[str, ...]:
    variables: set[str] = set()
    for literal in clause:
        variables.update(literal_free_vars(literal))
    return tuple(sorted(variables))


def term_free_vars_sorted(
    term: Term,
    expected_sort: str | None,
    symbol_sorts: dict[str, tuple[str, ...]],
    db_context: tuple[str, ...] = (),
) -> set[str]:
    if expected_sort is not None:
        expected_sort = require_supported_sort(expected_sort, "free variable expected sort")
    v_eq_args = named_binary_application(term, "vEQ")
    if v_eq_args is not None:
        result: set[str] = set()
        for arg in v_eq_args:
            result.update(term_free_vars_sorted(arg, "set", symbol_sorts, db_context))
        return result
    if term.kind == "app" and term.name == "vLAM" and len(term.args) == 1 and expected_sort is not None:
        parts = split_sort(expected_sort)
        if len(parts) >= 2:
            binder = f"db{len(db_context)}"
            body_sort = sort_from_parts(parts[1:])
            return term_free_vars_sorted(term.args[0], body_sort, symbol_sorts, (*db_context, binder))
    if term.kind == "var":
        return {term.name}
    if term.kind == "const":
        db_match = DB_NAME_RE.match(term.name)
        if db_match is not None:
            index = int(db_match.group(1))
            if index < len(db_context):
                return set()
            return {term.name}
        return set()
    head, args = term_spine(term)
    if args:
        if term.kind == "apply" and len(term.args) == 2 and expected_sort is not None:
            function, argument = term.args
            if function.kind == "app" and function.name == "vLAM" and len(function.args) == 1:
                argument_sort = term_sort_guess(argument, symbol_sorts, db_context) or "set"
                function_sort = sort_from_parts((argument_sort, expected_sort))
                result = term_free_vars_sorted(function, function_sort, symbol_sorts, db_context)
                result.update(term_free_vars_sorted(argument, argument_sort, symbol_sorts, db_context))
                return result
        signature = symbol_sorts.get(head.name) if head.kind == "const" else None
        if signature is not None and len(signature) >= len(args) + 1:
            result: set[str] = set()
            for arg, arg_sort in zip(args, signature):
                result.update(term_free_vars_sorted(arg, arg_sort, symbol_sorts, db_context))
            return result
        result = {head.name} if head.kind == "var" else set()
        for arg in args:
            result.update(term_free_vars_sorted(arg, None, symbol_sorts, db_context))
        return result
    result: set[str] = set()
    for arg in term.args:
        result.update(term_free_vars_sorted(arg, None, symbol_sorts, db_context))
    return result


def atom_free_vars_sorted(atom: Term, symbol_sorts: dict[str, tuple[str, ...]]) -> set[str]:
    if atom.kind == "eq" and len(atom.args) == 2:
        result: set[str] = set()
        for arg in atom.args:
            result.update(term_free_vars_sorted(arg, atom.name, symbol_sorts))
        return result
    if atom.kind == "pred":
        signature = symbol_sorts.get(atom.name)
        arg_sorts = signature[:-1] if signature is not None and len(signature) == len(atom.args) + 1 else (None,) * len(atom.args)
        result: set[str] = set()
        for arg, arg_sort in zip(atom.args, arg_sorts):
            result.update(term_free_vars_sorted(arg, arg_sort, symbol_sorts))
        return result
    result: set[str] = set()
    for arg in atom.args:
        result.update(term_free_vars_sorted(arg, None, symbol_sorts))
    return result


def clause_free_vars_sorted(
    clause: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None,
) -> tuple[str, ...]:
    if not symbol_sorts:
        return clause_free_vars(clause)
    variables: set[str] = set()
    for literal in clause:
        variables.update(atom_free_vars_sorted(literal.atom, symbol_sorts))
    return tuple(sorted(variables))


def inequality_split_definitions(
    data: dict[str, Any],
    declarations: list[str],
) -> dict[str, InequalitySplitDefinition]:
    symbol_sorts = declaration_symbol_sorts(declarations)
    definitions: dict[str, InequalitySplitDefinition] = {}
    for step in data.get("steps", []):
        if not isinstance(step, dict) or step.get("rule") != "inequality_split":
            continue
        splits = step.get("splits")
        if not isinstance(splits, list):
            continue
        for split_index, split in enumerate(splits):
            if not isinstance(split, dict):
                continue
            step_id = str(step.get("id", "step"))
            name_literal = parse_literal(split.get("name_literal"), f"{step_id}.splits[{split_index}].name_literal")
            name_term = bool_name_literal_term(name_literal, False)
            if name_term is None:
                continue
            app = applied_symbol_and_args(name_term)
            if app is None:
                continue
            symbol, args = app
            sort_parts = symbol_sorts.get(symbol)
            if sort_parts is None or len(sort_parts) != len(args) + 1 or sort_parts[-1] != "prop":
                continue
            binder_substitution = {
                arg.name: Term("var", f"cert_split{index}")
                for index, arg in enumerate(args)
                if arg.kind == "var"
            }
            split_arg = substitute_term(args[-1], binder_substitution)
            binder_names = {f"cert_split{index}" for index in range(len(args))}
            if term_free_vars(split_arg) - binder_names:
                continue
            definition = InequalitySplitDefinition(symbol, sort_parts, split_arg)
            existing = definitions.get(symbol)
            if existing is not None and existing != definition:
                raise CertificateError(f"{step_id}: conflicting inequality split definitions for {symbol}")
            definitions[symbol] = definition
    return definitions


def inequality_split_definition_text(
    definition: InequalitySplitDefinition,
    symbol_sorts: dict[str, tuple[str, ...]],
) -> str:
    args_count = len(definition.sort_parts) - 1
    if args_count < 1:
        raise CertificateError(f"{definition.symbol}: inequality split predicate must take at least one argument")
    last_binder = Term("var", f"cert_split{args_count - 1}")
    argument_sort = require_supported_sort(definition.sort_parts[-2], f"{definition.symbol} split argument sort")
    equality = Term("eq", argument_sort, (last_binder, definition.split_arg))
    result = f"{atom_text(equality, symbol_sorts)} -> False"
    for index in reversed(range(args_count)):
        binder = f"cert_split{index}"
        sort = require_supported_sort(definition.sort_parts[index], f"{definition.symbol} argument sort")
        result = f"fun {binder}:{sort_type_text(sort)} => {result}"
    return (
        f"Definition {require_megalodon_ident(definition.symbol, 'inequality split symbol')} "
        f": {sort_from_parts(definition.sort_parts)} := {result}."
    )


def collect_existential_sorts_in_term(term: Term, result: set[str], db_context: tuple[str, ...] = ()) -> None:
    v_eq_args = named_binary_application(term, "vEQ")
    if v_eq_args is not None:
        for arg in v_eq_args:
            collect_existential_sorts_in_term(arg, result, db_context)
        return
    quantifier = quantifier_application(term)
    if quantifier is not None:
        kind, body_term, lambda_hint = quantifier
        if kind == "vSIGMA":
            result.add(lambda_hint.binder_sort)
        binder = f"db{len(db_context)}"
        collect_existential_sorts_in_term(body_term.args[0], result, (*db_context, binder))
        return
    lambda_hint = lambda_hint_for_term(term)
    if lambda_hint is not None:
        binder = f"db{len(db_context)}"
        collect_existential_sorts_in_term(term.args[0], result, (*db_context, binder))
        return
    for arg in term.args:
        collect_existential_sorts_in_term(arg, result, db_context)


def certificate_existential_sorts(clauses: dict[str, tuple[Literal, ...]]) -> tuple[str, ...]:
    result: set[str] = set()
    for clause in clauses.values():
        for literal in clause:
            collect_existential_sorts_in_term(literal.atom, result)
    return tuple(sorted(result))


def term_uses_named_binary(term: Term, name: str) -> bool:
    v_eq_args = named_binary_application(term, name)
    if v_eq_args is not None:
        return True
    return any(term_uses_named_binary(arg, name) for arg in term.args)


def certificate_uses_named_binary(clauses: dict[str, tuple[Literal, ...]], name: str) -> bool:
    return any(
        term_uses_named_binary(literal.atom, name)
        for clause in clauses.values()
        for literal in clause
    )


def certificate_metadata_uses_infix_equality(data: dict[str, Any]) -> bool:
    metadata_keys = {
        "proposition",
        "source",
        "target",
        "source_proposition",
        "target_proposition",
    }

    def value_uses_equality(value: Any) -> bool:
        if isinstance(value, str):
            return bool(re.search(r"\s=\s", value))
        if isinstance(value, list):
            return any(value_uses_equality(item) for item in value)
        if isinstance(value, dict):
            return any(
                value_uses_equality(item)
                for key, item in value.items()
                if key in metadata_keys or isinstance(item, (dict, list))
            )
        return False

    return value_uses_equality(data.get("steps", []))


def declaration_symbol_sorts(declarations: list[str]) -> dict[str, tuple[str, ...]]:
    result: dict[str, tuple[str, ...]] = {}
    for declaration in declarations:
        match = re.fullmatch(r"Variable ([A-Za-z_][A-Za-z0-9_']*):(.+)\.", declaration)
        if match is None:
            continue
        result[match.group(1)] = split_sort(require_supported_sort(match.group(2), f"declaration sort for {match.group(1)}"))
    return result


def declaration_symbol_name(declaration: str) -> str | None:
    match = re.fullmatch(r"Variable ([A-Za-z_][A-Za-z0-9_']*):.+\.", declaration)
    return match.group(1) if match is not None else None


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


def collect_term_var_sorts(
    term: Term,
    expected_sort: str,
    symbol_sorts: dict[str, tuple[str, ...]],
    var_sorts: dict[str, str],
    locked_vars: set[str] | None = None,
    db_depth: int = 0,
) -> None:
    locked_vars = locked_vars or set()
    v_eq_args = named_binary_application(term, "vEQ")
    if v_eq_args is not None:
        for arg in v_eq_args:
            collect_term_var_sorts(arg, "set", symbol_sorts, var_sorts, locked_vars, db_depth)
        return
    if term.kind == "app" and term.name == "vLAM" and len(term.args) == 1:
        parts = split_sort(expected_sort)
        body_sort = sort_from_parts(parts[1:]) if len(parts) >= 2 else "set"
        collect_term_var_sorts(term.args[0], body_sort, symbol_sorts, var_sorts, locked_vars, db_depth + 1)
        return
    if term.kind == "var":
        if term.name not in locked_vars:
            merge_var_sort(var_sorts, term.name, expected_sort)
        return
    if term.kind == "const" and DB_NAME_RE.match(term.name):
        db_index = int(DB_NAME_RE.match(term.name).group(1))
        if db_index < db_depth:
            return
        if term.name not in locked_vars:
            merge_var_sort(var_sorts, term.name, expected_sort)
        return
    head, args = term_spine(term)
    if head.kind == "var" and args and head.name not in locked_vars:
        merge_var_sort(var_sorts, head.name, "->".join(["set"] * len(args) + [expected_sort]))
    if head.kind == "const" and args:
        signature = symbol_sorts.get(head.name)
        if signature is not None and len(signature) >= len(args) + 1:
            for arg, arg_sort in zip(args, signature):
                collect_term_var_sorts(arg, arg_sort, symbol_sorts, var_sorts, locked_vars, db_depth)
            return
    for arg in term.args:
        collect_term_var_sorts(arg, "set", symbol_sorts, var_sorts, locked_vars, db_depth)


def collect_atom_var_sorts(
    atom: Term,
    symbol_sorts: dict[str, tuple[str, ...]],
    var_sorts: dict[str, str],
    locked_vars: set[str] | None = None,
) -> None:
    locked_vars = locked_vars or set()
    if atom.kind == "eq" and len(atom.args) == 2:
        for arg in atom.args:
            collect_term_var_sorts(arg, atom.name, symbol_sorts, var_sorts, locked_vars)
        return
    if atom.kind == "pred":
        signature = symbol_sorts.get(atom.name)
        arg_sorts = signature[:-1] if signature is not None and len(signature) == len(atom.args) + 1 else ("set",) * len(atom.args)
        for arg, arg_sort in zip(atom.args, arg_sorts):
            collect_term_var_sorts(arg, arg_sort, symbol_sorts, var_sorts, locked_vars)
        return
    for arg in atom.args:
        collect_term_var_sorts(arg, "set", symbol_sorts, var_sorts, locked_vars)


def clause_var_sorts(
    clause: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]],
    explicit_var_sorts: dict[str, str] | None = None,
) -> dict[str, str]:
    clause_vars = set(clause_free_vars_sorted(clause, symbol_sorts))
    explicit_var_sorts = explicit_var_sorts or {}
    var_sorts: dict[str, str] = {
        name: require_supported_sort(sort, f"explicit sort for {name}")
        for name, sort in explicit_var_sorts.items()
        if name in clause_vars
    }
    for name, sort in lambda_binder_sorts().items():
        if name in clause_vars and not DB_NAME_RE.match(name):
            var_sorts.setdefault(name, sort)
    default_lambda_sort = lambda_default_binder_sort()
    if default_lambda_sort is not None:
        for name in clause_vars:
            if DB_NAME_RE.match(name) and name not in var_sorts:
                var_sorts.setdefault(name, default_lambda_sort)
    locked_vars = set(var_sorts)
    for literal in clause:
        collect_atom_var_sorts(literal.atom, symbol_sorts, var_sorts, locked_vars)
    for name in clause_vars:
        var_sorts.setdefault(name, "set")
    return var_sorts


def clause_prop_text(
    clause: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
) -> str:
    symbol_sorts = symbol_sorts or {}
    result = clause_body_text(clause, symbol_sorts)
    var_sorts = clause_var_sorts(clause, symbol_sorts, explicit_var_sorts)
    for name in reversed(clause_free_vars_sorted(clause, symbol_sorts)):
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
    if literal.atom.name == "set":
        return f"(fun Q:set->set->prop => fun H:Q {right} {left} => ({proof} (fun cert_x cert_y:set => Q cert_y cert_x) H))"
    sort_text = sort_type_text(literal.atom.name)
    return (
        f"(fun Q:{sort_text}->prop => fun H:Q {right} => "
        f"({proof} (fun cert_z:{sort_text} => Q cert_z -> Q {left}) (fun Hx => Hx) H))"
    )


def equality_symmetry_literal_proof(
    literal: Literal,
    proof: str,
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
) -> str:
    if literal.polarity:
        return positive_equality_symmetry_proof(literal, proof)
    positive_swapped = Literal(True, swap_equality_literal(literal).atom)
    swapped_proof = fresh_proof_name("Hsym")
    positive_original = positive_equality_symmetry_proof(positive_swapped, swapped_proof)
    return f"(fun {swapped_proof}:{atom_text(positive_swapped.atom, symbol_sorts)} => ({proof} {positive_original}))"


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


def witness_term_for_sort(sort: str) -> Term:
    normalized = require_supported_sort(sort, "witness sort")
    if normalized == "prop":
        return Term("const", "f__false")
    if normalized == "set":
        return Term("const", "vampire_witness_set")
    if normalized == "set->prop":
        return Term("const", "vampire_witness_set_to_prop")
    raise CertificateError(f"no smoke witness available for sort {normalized!r}")


def uncovered_witness_substitution(
    parent_clause: tuple[Literal, ...],
    conclusion: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None,
    explicit_var_sorts: dict[str, str] | None,
) -> dict[str, Term]:
    conclusion_vars = set(clause_free_vars_sorted(conclusion, symbol_sorts))
    parent_vars = set(clause_free_vars_sorted(parent_clause, symbol_sorts))
    uncovered_vars = sorted(parent_vars - conclusion_vars)
    if not uncovered_vars:
        return {}
    var_sorts = clause_var_sorts(parent_clause + conclusion, symbol_sorts or {}, explicit_var_sorts)
    return {
        var: witness_term_for_sort(var_sorts.get(var, "set"))
        for var in uncovered_vars
    }


def compose_substitution(substitution: dict[str, Term], extra: dict[str, Term]) -> dict[str, Term]:
    if not extra:
        return substitution
    composed = {
        name: substitute_term(term, extra)
        for name, term in substitution.items()
    }
    for name, term in extra.items():
        composed.setdefault(name, term)
    return composed


def resolve_proof_text(
    left_clause: tuple[Literal, ...],
    left_proof: str,
    right_clause: tuple[Literal, ...],
    right_proof: str,
    pivot: Literal,
    conclusion: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
) -> str:
    parent_clause = normalize_clause(left_clause + right_clause)
    substitution = uncovered_witness_substitution(parent_clause, conclusion, symbol_sorts, explicit_var_sorts)
    original_left_clause = left_clause
    original_right_clause = right_clause
    if substitution:
        left_clause = tuple(substitute_literal(literal, substitution) for literal in left_clause)
        right_clause = tuple(substitute_literal(literal, substitution) for literal in right_clause)
        pivot = substitute_literal(pivot, substitution)
    left_proof = instantiate_proof(left_proof, original_left_clause, substitution, symbol_sorts)
    right_proof = instantiate_proof(right_proof, original_right_clause, substitution, symbol_sorts)
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
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
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
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution, symbol_sorts)
    goal = clause_body_text(conclusion)
    reflexive_false = lambda proof: f"({proof} {equality_refl_proof()})"

    def branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_selected:
            false_proof = reflexive_false(proof)
            return f"({false_proof} {goal})"
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def is_prop_truth_conflict_atom(atom: Term) -> bool:
    if atom.kind != "eq" or atom.name != "prop" or len(atom.args) != 2:
        return False
    left, right = atom.args
    return (
        left == Term("const", "f__true") and right == Term("const", "f__false")
    ) or (
        left == Term("const", "f__false") and right == Term("const", "f__true")
    )


def false_from_prop_truth_conflict(literal: Literal, proof: str) -> str:
    if not literal.polarity or not is_prop_truth_conflict_atom(literal.atom):
        raise CertificateError("truth-conflict resolution needs a positive equality between true and false")
    left, right = literal.atom.args
    true_proof = "(fun p:prop => fun h:p => h)"
    if left == Term("const", "f__true") and right == Term("const", "f__false"):
        return f"({proof} (fun cert_z:prop => cert_z) {true_proof})"
    symmetric = positive_equality_symmetry_proof(literal, proof)
    return f"({symmetric} (fun cert_z:prop => cert_z) {true_proof})"


def truth_conflict_resolution_proof_text(
    parent_clause: tuple[Literal, ...],
    parent_proof: str,
    selected_literal: Literal,
    substitution: dict[str, Term],
    conclusion: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
) -> str:
    instantiated_parent = tuple(substitute_literal(literal, substitution) for literal in parent_clause)
    instantiated_selected = substitute_literal(selected_literal, substitution)
    if not instantiated_selected.polarity or not is_prop_truth_conflict_atom(instantiated_selected.atom):
        raise CertificateError("selected truth-conflict literal is not true=false or false=true")
    conclusion_vars = set(clause_free_vars(conclusion))
    parent_vars = set(clause_free_vars(instantiated_parent))
    uncovered_vars = sorted(parent_vars - conclusion_vars)
    if uncovered_vars:
        raise CertificateError(
            "Megalodon smoke truth-conflict elaboration has parent variables not bound by conclusion: "
            + ", ".join(uncovered_vars)
        )
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution, symbol_sorts)
    goal = clause_body_text(conclusion)

    def branch(literal: Literal, proof: str) -> str:
        if literal == instantiated_selected:
            false_proof = false_from_prop_truth_conflict(literal, proof)
            return f"({false_proof} {goal})"
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def eliminate_sat_clause_proof(
    clause: tuple[tuple[int, bool], ...],
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
    head_proof = fresh_proof_name("Hsat")
    tail_proof = fresh_proof_name("Hsat_tail")
    return (
        f"({proof} {goal} "
        f"(fun {head_proof} => {branch_proof(head, head_proof)}) "
        f"(fun {tail_proof} => {eliminate_sat_clause_proof(tail, tail_proof, goal, branch_proof)}))"
    )


def false_from_sat_assignment(
    literal: tuple[int, bool],
    literal_proof: str,
    assignment: dict[int, tuple[bool, str]],
) -> str:
    var, polarity = literal
    assigned = assignment.get(var)
    if assigned is None:
        raise CertificateError(f"SAT literal split_{var} is not assigned")
    value, value_proof = assigned
    if value == polarity:
        raise CertificateError(f"SAT literal split_{var} is satisfied, not contradictory")
    if polarity:
        return f"({value_proof} {literal_proof})"
    return f"({literal_proof} {value_proof})"


def derive_sat_unit_proof(
    clause: tuple[tuple[int, bool], ...],
    clause_proof: str,
    unit_literal: tuple[int, bool],
    assignment: dict[int, tuple[bool, str]],
) -> str:
    goal = sat_literal_prop_text(unit_literal)

    def branch(literal: tuple[int, bool], proof: str) -> str:
        if literal == unit_literal:
            return proof
        false_proof = false_from_sat_assignment(literal, proof, assignment)
        return f"({false_proof} {goal})"

    return eliminate_sat_clause_proof(clause, clause_proof, goal, branch)


def avatar_refutation_proof_text(
    sat_clauses: tuple[tuple[tuple[int, bool], ...], ...],
    sat_clause_proofs: tuple[str, ...],
) -> str:
    if len(sat_clauses) != len(sat_clause_proofs):
        raise CertificateError("avatar refutation proof needs one proof per SAT clause")
    if not sat_clauses_unsat(sat_clauses):
        raise CertificateError("avatar refutation SAT clauses are satisfiable")
    clauses = sat_clauses
    all_vars = sorted({var for clause in clauses for var, _polarity in clause})

    def search(assignment: dict[int, tuple[bool, str]]) -> str:
        while True:
            propagated = False
            for clause, clause_proof in zip(clauses, sat_clause_proofs):
                unassigned: list[tuple[int, bool]] = []
                satisfied = False
                for literal in clause:
                    var, polarity = literal
                    assigned = assignment.get(var)
                    if assigned is None:
                        unassigned.append(literal)
                    elif assigned[0] == polarity:
                        satisfied = True
                        break
                if satisfied:
                    continue
                if not unassigned:
                    return eliminate_sat_clause_proof(
                        clause,
                        clause_proof,
                        "False",
                        lambda literal, proof: false_from_sat_assignment(literal, proof, assignment),
                    )
                if len(unassigned) == 1:
                    unit = unassigned[0]
                    var, polarity = unit
                    unit_proof = derive_sat_unit_proof(clause, clause_proof, unit, assignment)
                    existing = assignment.get(var)
                    if existing is not None:
                        if existing[0] != polarity:
                            false_proof = false_from_sat_assignment(unit, unit_proof, assignment)
                            return false_proof
                        continue
                    assignment[var] = (polarity, unit_proof)
                    propagated = True
                    break
            if not propagated:
                break

        branch_var = next((var for var in all_vars if var not in assignment), None)
        if branch_var is None:
            raise CertificateError("avatar refutation proof search reached a satisfying assignment")
        positive_proof = fresh_proof_name("Hsat_pos")
        negative_proof = fresh_proof_name("Hsat_neg")
        positive_assignment = dict(assignment)
        positive_assignment[branch_var] = (True, positive_proof)
        negative_assignment = dict(assignment)
        negative_assignment[branch_var] = (False, negative_proof)
        atom = sat_split_name(branch_var)
        return (
            f"((xm {atom}) False "
            f"(fun {positive_proof} => {search(positive_assignment)}) "
            f"(fun {negative_proof} => {search(negative_assignment)}))"
        )

    return search({})


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
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
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
    normalized_conclusion = normalize_clause(conclusion)
    introduced_for_conclusion = introduced
    if introduced not in normalized_conclusion:
        swapped_introduced = swap_equality_literal(introduced)
        if swapped_introduced in normalized_conclusion:
            introduced_for_conclusion = swapped_introduced
        else:
            raise CertificateError("equality-factoring conclusion does not contain introduced disequality")
    goal = clause_body_text(conclusion)
    instantiated_parent_proof = instantiate_proof(parent_proof, parent_clause, substitution, symbol_sorts)

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
            introduced_proof = diseq_proof
            if introduced_for_conclusion != introduced:
                introduced_proof = equality_symmetry_literal_proof(introduced, diseq_proof)
            return (
                f"((xm {literal_text(diff)}) {goal} "
                f"(fun {diff_proof} => {intro_literal_proof(instantiated_other, conclusion, prove_other_from_diff(proof, diff_proof))}) "
                f"(fun {diseq_proof} => {intro_literal_proof(introduced_for_conclusion, conclusion, introduced_proof)}))"
            )
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(instantiated_parent, instantiated_parent_proof, goal, branch)


def equality_symmetry_proof_text(
    parent_clause: tuple[Literal, ...],
    parent_proof: str,
    selected_literal: Literal,
    conclusion: tuple[Literal, ...],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    instantiate_parent_proof: bool = True,
) -> str:
    if selected_literal not in normalize_clause(parent_clause):
        raise CertificateError("Megalodon smoke equality-symmetry literal is not present in parent")
    swapped = swap_equality_literal(selected_literal)
    if swapped not in normalize_clause(conclusion):
        raise CertificateError("Megalodon smoke equality-symmetry conclusion does not contain swapped literal")
    goal = clause_body_text(conclusion)
    if instantiate_parent_proof:
        parent_proof = instantiate_proof(parent_proof, parent_clause, {}, symbol_sorts)

    def branch(literal: Literal, proof: str) -> str:
        if literal == selected_literal:
            return intro_literal_proof(swapped, conclusion, equality_symmetry_literal_proof(literal, proof, symbol_sorts))
        return intro_literal_proof(literal, conclusion, proof)

    return eliminate_clause_proof(parent_clause, parent_proof, goal, branch)


def definition_rewrite_literal_variants(
    literal: Literal,
    rewrites: tuple[DefinitionRewriteStep, ...],
) -> tuple[Literal, ...]:
    candidates: set[Literal] = {literal}
    max_candidates = 256
    for rewrite in rewrites:
        next_candidates: set[Literal] = set(candidates)
        for candidate in candidates:
            next_candidates.update(rewrite_literal_once_variants(candidate, rewrite.source, rewrite.target))
            if len(next_candidates) > max_candidates:
                raise CertificateError(
                    "definition rewrite chain branches too much; "
                    "this likely needs primitive prover-side rewrite positions"
                )
        candidates = next_candidates
    return tuple(sorted(candidates))


def definition_rewrite_chain_proof_text(
    source_clause: tuple[Literal, ...],
    source_proof: str,
    rewrites: tuple[DefinitionRewriteStep, ...],
    conclusion: tuple[Literal, ...],
    step_clauses: dict[str, tuple[Literal, ...]] | None = None,
    proof_names: dict[str, str] | None = None,
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
) -> str:
    if (
        step_clauses is not None
        and proof_names is not None
        and all(rewrite.parent is not None and rewrite.literal is not None and rewrite.position is not None for rewrite in rewrites)
    ):
        current_clause = tuple(source_clause)
        current_proof = source_proof
        for index, rewrite in enumerate(rewrites):
            if rewrite.parent is None or rewrite.literal is None or rewrite.position is None:
                raise CertificateError("positioned definition rewrite unexpectedly lost metadata")
            equality_parent_clause = step_clauses.get(rewrite.parent)
            equality_parent_proof = proof_names.get(rewrite.parent)
            if equality_parent_clause is None or equality_parent_proof is None:
                raise CertificateError(f"definition rewrite step {index}: missing proof for parent {rewrite.parent}")
            if len(equality_parent_clause) != 1:
                raise CertificateError(f"definition rewrite step {index}: definition parent is not a unit clause")
            if rewrite.literal >= len(current_clause):
                raise CertificateError(f"definition rewrite step {index}: literal index is outside the current clause")
            selected_equality = equality_parent_clause[0]
            if (
                not selected_equality.polarity
                or selected_equality.atom.kind != "eq"
                or len(selected_equality.atom.args) != 2
                or selected_equality.atom.args[0] != rewrite.source
                or selected_equality.atom.args[1] != rewrite.target
            ):
                raise CertificateError(f"definition rewrite step {index}: definition parent does not match rewrite orientation")
            selected_target = current_clause[rewrite.literal]
            proof_position = certificate_position_for_source(
                selected_target.atom,
                rewrite.position,
                rewrite.source,
                f"definition rewrite step {index}.position",
            )
            next_clause = rewrite_clause_at_definition_step(current_clause, rewrite, f"definition rewrite step {index}")
            raw_next_clause = normalize_clause(next_clause)
            current_proof = paramodulation_proof_text(
                equality_parent_clause,
                equality_parent_proof,
                current_clause,
                current_proof,
                selected_equality,
                selected_target,
                proof_position,
                {},
                raw_next_clause,
                symbol_sorts,
                explicit_var_sorts,
                instantiate_target_proof=(index == 0),
            )
            current_clause = raw_next_clause
            if rewrite.clause is not None and current_clause != rewrite.clause:
                if not clauses_match_modulo_equality_symmetry(current_clause, rewrite.clause):
                    raise CertificateError(f"definition rewrite step {index}: explicit intermediate clause does not match modulo equality symmetry")
                target_clause = rewrite.clause
                for _guard in range(len(current_clause)):
                    if current_clause == target_clause:
                        break
                    changed = False
                    for literal in current_clause:
                        if literal.atom.kind != "eq":
                            continue
                        swapped = swap_equality_literal(literal)
                        if literal in target_clause or swapped not in target_clause:
                            continue
                        next_sym_clause = normalize_clause(swapped if item == literal else item for item in current_clause)
                        current_proof = equality_symmetry_proof_text(
                            current_clause,
                            current_proof,
                            literal,
                            next_sym_clause,
                            symbol_sorts,
                            instantiate_parent_proof=False,
                        )
                        current_clause = next_sym_clause
                        changed = True
                        break
                    if not changed:
                        break
                if current_clause != target_clause:
                    raise CertificateError(f"definition rewrite step {index}: could not normalize explicit intermediate clause")
        if not clauses_match_modulo_equality_symmetry(current_clause, conclusion):
            raise CertificateError("definition rewrite positioned chain does not reach conclusion")
        if normalize_clause(current_clause) == normalize_clause(conclusion):
            return reorder_clause_proof_text(current_clause, current_proof, conclusion)
        target_clause = normalize_clause(conclusion)
        current_clause = normalize_clause(current_clause)
        for guard in range(len(current_clause)):
            if current_clause == target_clause:
                return reorder_clause_proof_text(current_clause, current_proof, conclusion)
            changed = False
            for literal in current_clause:
                if literal.atom.kind != "eq":
                    continue
                swapped = swap_equality_literal(literal)
                if literal in target_clause or swapped not in target_clause:
                    continue
                next_clause = normalize_clause(swapped if item == literal else item for item in current_clause)
                current_proof = equality_symmetry_proof_text(
                    current_clause,
                    current_proof,
                    literal,
                    next_clause,
                    symbol_sorts,
                    instantiate_parent_proof=False,
                )
                current_clause = next_clause
                changed = True
                break
            if not changed:
                break
        if current_clause == target_clause:
            return reorder_clause_proof_text(current_clause, current_proof, conclusion)
        raise CertificateError("definition rewrite positioned proof needs final equality-symmetry normalization")

    goal = clause_body_text(conclusion)

    def branch(literal: Literal, proof: str) -> str:
        for variant in definition_rewrite_literal_variants(literal, rewrites):
            if variant in conclusion:
                return intro_literal_proof(variant, conclusion, proof)
            if variant.atom.kind == "eq":
                swapped = swap_equality_literal(variant)
                if swapped in conclusion:
                    return intro_literal_proof(swapped, conclusion, equality_symmetry_literal_proof(literal, proof))
        raise CertificateError(f"definition rewrite cannot map literal {literal_text(literal)} into conclusion")

    return eliminate_clause_proof(source_clause, source_proof, goal, branch)


def append_definition_rewrite_chain_claims(
    step_id: str,
    source_clause: tuple[Literal, ...],
    source_proof: str,
    rewrites: tuple[DefinitionRewriteStep, ...],
    conclusion: tuple[Literal, ...],
    step_clauses: dict[str, tuple[Literal, ...]],
    proof_names: dict[str, str],
    derived: list[tuple[str, str, str]],
    symbol_sorts: dict[str, tuple[str, ...]],
    explicit_var_sorts: dict[str, str] | None = None,
) -> bool:
    if not all(rewrite.parent is not None and rewrite.literal is not None and rewrite.position is not None for rewrite in rewrites):
        return False
    current_clause = tuple(source_clause)
    current_proof = source_proof

    def append_claim(name: str, claim_clause: tuple[Literal, ...], proof_text: str) -> None:
        step_clauses[name] = claim_clause
        proof_names[name] = name
        derived.append(
            (
                name,
                clause_prop_text(claim_clause, symbol_sorts, explicit_var_sorts),
                wrap_clause_binders(claim_clause, proof_text, symbol_sorts, explicit_var_sorts),
            )
        )

    def append_symmetry_claims(prefix: str, target_clause: tuple[Literal, ...]) -> tuple[tuple[Literal, ...], str]:
        nonlocal current_clause, current_proof
        target_clause = normalize_clause(target_clause)
        current_clause = normalize_clause(current_clause)
        for sym_index in range(len(current_clause)):
            if current_clause == target_clause:
                return current_clause, current_proof
            changed = False
            for literal in current_clause:
                if literal.atom.kind != "eq":
                    continue
                swapped = swap_equality_literal(literal)
                if literal in target_clause or swapped not in target_clause:
                    continue
                next_clause = normalize_clause(swapped if item == literal else item for item in current_clause)
                claim_name = f"{prefix}_sym_{sym_index}"
                proof_text = equality_symmetry_proof_text(
                    current_clause,
                    current_proof,
                    literal,
                    next_clause,
                    symbol_sorts,
                )
                append_claim(claim_name, next_clause, proof_text)
                current_clause = next_clause
                current_proof = claim_name
                changed = True
                break
            if not changed:
                break
        return current_clause, current_proof

    for index, rewrite in enumerate(rewrites):
        if rewrite.parent is None or rewrite.literal is None or rewrite.position is None:
            return False
        equality_parent_clause = step_clauses.get(rewrite.parent)
        equality_parent_proof = proof_names.get(rewrite.parent)
        if equality_parent_clause is None or equality_parent_proof is None:
            raise CertificateError(f"definition rewrite step {index}: missing proof for parent {rewrite.parent}")
        if len(equality_parent_clause) != 1:
            raise CertificateError(f"definition rewrite step {index}: definition parent is not a unit clause")
        if rewrite.literal >= len(current_clause):
            raise CertificateError(f"definition rewrite step {index}: literal index is outside the current clause")
        selected_equality = equality_parent_clause[0]
        if (
            not selected_equality.polarity
            or selected_equality.atom.kind != "eq"
            or len(selected_equality.atom.args) != 2
            or selected_equality.atom.args[0] != rewrite.source
            or selected_equality.atom.args[1] != rewrite.target
        ):
            raise CertificateError(f"definition rewrite step {index}: definition parent does not match rewrite orientation")
        selected_target = current_clause[rewrite.literal]
        proof_position = certificate_position_for_source(
            selected_target.atom,
            rewrite.position,
            rewrite.source,
            f"definition rewrite step {index}.position",
        )
        next_clause = normalize_clause(rewrite_clause_at_definition_step(current_clause, rewrite, f"definition rewrite step {index}"))
        claim_name = f"{step_id}_defrw_{index}"
        proof_text = paramodulation_proof_text(
            equality_parent_clause,
            equality_parent_proof,
            current_clause,
            current_proof,
            selected_equality,
            selected_target,
            proof_position,
            {},
            next_clause,
            symbol_sorts,
            explicit_var_sorts,
        )
        append_claim(claim_name, next_clause, proof_text)
        current_clause = next_clause
        current_proof = claim_name
        if rewrite.clause is not None and current_clause != rewrite.clause:
            if not clauses_match_modulo_equality_symmetry(current_clause, rewrite.clause):
                raise CertificateError(f"definition rewrite step {index}: explicit intermediate clause does not match modulo equality symmetry")
            append_symmetry_claims(f"{step_id}_defrw_{index}", rewrite.clause)
            if current_clause != rewrite.clause:
                raise CertificateError(f"definition rewrite step {index}: could not normalize explicit intermediate clause")

    if not clauses_match_modulo_equality_symmetry(current_clause, conclusion):
        raise CertificateError("definition rewrite positioned chain does not reach conclusion")
    append_symmetry_claims(f"{step_id}_defrw_final", conclusion)
    if normalize_clause(current_clause) != normalize_clause(conclusion):
        raise CertificateError("definition rewrite positioned proof needs final equality-symmetry normalization")
    proof_text = reorder_clause_proof_text(
        current_clause,
        instantiate_proof(current_proof, current_clause, {}, symbol_sorts),
        conclusion,
    )
    append_claim(step_id, conclusion, proof_text)
    return True


def equality_proof_in_orientation(source: Literal, source_proof: str, target: Literal) -> str | None:
    if not source.polarity or not target.polarity or source.atom.kind != "eq" or target.atom.kind != "eq":
        return None
    if source.atom.name != target.atom.name or len(source.atom.args) != 2 or len(target.atom.args) != 2:
        return None
    if source == target:
        return source_proof
    if swap_equality_literal(source) == target:
        return positive_equality_symmetry_proof(source, source_proof)
    return None


def find_prop_exhaustiveness_clause(
    step_clauses: dict[str, tuple[Literal, ...]],
    proof_names: dict[str, str],
) -> tuple[tuple[Literal, ...], str, str] | None:
    for step_id, clause in step_clauses.items():
        if step_id not in proof_names or len(clause) != 2:
            continue
        true_var: Term | None = None
        false_var: Term | None = None
        for literal in clause:
            if not literal.polarity:
                continue
            true_term = bool_name_literal_term(literal, True)
            false_term = bool_name_literal_term(literal, False)
            if true_term is not None:
                true_var = true_term
            if false_term is not None:
                false_var = false_term
        if true_var is not None and false_var is not None and true_var == false_var and true_var.kind == "var":
            return clause, proof_names[step_id], true_var.name
    return None


def split_value_proof_from_disequality(
    source_literal: Literal,
    source_proof: str,
    split_arg: Term,
    other_arg: Term,
) -> str:
    if source_literal.polarity or source_literal.atom.kind != "eq" or len(source_literal.atom.args) != 2:
        raise CertificateError("inequality split source must be a negative equality")
    left, right = source_literal.atom.args
    if left == other_arg and right == split_arg:
        return source_proof
    if left == split_arg and right == other_arg:
        equality_assumption = fresh_proof_name("Hsplit_eq")
        equality = Literal(True, Term("eq", source_literal.atom.name, (other_arg, split_arg)))
        symmetric = positive_equality_symmetry_proof(equality, equality_assumption)
        return f"(fun {equality_assumption} => ({source_proof} {symmetric}))"
    raise CertificateError("inequality split source sides do not match split arguments")


def inequality_split_replacement_proof(
    replacement: Literal,
    split_value_proof: str,
    exhaustiveness_clause: tuple[Literal, ...],
    exhaustiveness_proof: str,
    exhaustiveness_var: str,
    replacement_term: Term,
) -> str:
    target_prop = literal_text(replacement)
    instantiated_exhaustiveness = tuple(
        substitute_literal(literal, {exhaustiveness_var: replacement_term})
        for literal in exhaustiveness_clause
    )
    instantiated_exhaustiveness_proof = instantiate_proof(
        exhaustiveness_proof,
        exhaustiveness_clause,
        {exhaustiveness_var: replacement_term},
    )

    def branch(literal: Literal, proof: str) -> str:
        oriented = equality_proof_in_orientation(literal, proof, replacement)
        if oriented is not None:
            return oriented
        false_term = bool_name_literal_term(literal, False)
        if false_term == replacement_term:
            symmetric = positive_equality_symmetry_proof(literal, proof)
            false_proof = f"({symmetric} (fun cert_prop:prop => cert_prop) {split_value_proof})"
            return f"({false_proof} {target_prop})"
        raise CertificateError("FOOL exhaustiveness branch does not match inequality split replacement")

    return eliminate_clause_proof(
        instantiated_exhaustiveness,
        instantiated_exhaustiveness_proof,
        target_prop,
        branch,
    )


def inequality_split_proof_text(
    source_clause: tuple[Literal, ...],
    source_proof: str,
    splits: list[Any],
    conclusion: tuple[Literal, ...],
    step_clauses: dict[str, tuple[Literal, ...]],
    proof_names: dict[str, str],
) -> str:
    exhaustiveness = find_prop_exhaustiveness_clause(step_clauses, proof_names)
    if exhaustiveness is None:
        raise CertificateError("Megalodon smoke inequality_split elaboration needs a FOOL exhaustiveness clause")
    exhaustiveness_clause, exhaustiveness_proof, exhaustiveness_var = exhaustiveness
    source_proof = instantiate_proof(source_proof, source_clause, {})
    goal = clause_body_text(conclusion)
    split_by_source: dict[Literal, tuple[Literal, Term, Term]] = {}
    for split_index, split in enumerate(splits):
        if not isinstance(split, dict):
            raise CertificateError(f"inequality split {split_index}: expected object")
        name_literal = parse_literal(split["name_literal"], f"inequality_split.splits[{split_index}].name_literal")
        name_term = bool_name_literal_term(name_literal, False)
        name_app = application_head_and_arg(name_term) if name_term is not None else None
        if name_app is None:
            raise CertificateError(f"inequality_split.splits[{split_index}]: name literal must be false = P(term)")
        name_head, split_arg = name_app
        source_literal = parse_literal(split["source"], f"inequality_split.splits[{split_index}].source")
        replacement = parse_literal(split["replacement"], f"inequality_split.splits[{split_index}].replacement")
        replacement_term = bool_name_literal_term(replacement, True)
        replacement_app = application_head_and_arg(replacement_term) if replacement_term is not None else None
        if replacement_app is None:
            raise CertificateError(f"inequality_split.splits[{split_index}]: replacement must be true = P(term)")
        replacement_head, other_arg = replacement_app
        if replacement_head != name_head:
            raise CertificateError(f"inequality_split.splits[{split_index}]: replacement uses a different split predicate")
        split_by_source[source_literal] = (replacement, split_arg, other_arg)

    def branch(literal: Literal, proof: str) -> str:
        split = split_by_source.get(literal)
        if split is None:
            return intro_literal_proof(literal, conclusion, proof)
        replacement, split_arg, other_arg = split
        replacement_term = bool_name_literal_term(replacement, True)
        if replacement_term is None:
            raise CertificateError("inequality split replacement is not a true-name literal")
        value_proof = split_value_proof_from_disequality(literal, proof, split_arg, other_arg)
        replacement_proof = inequality_split_replacement_proof(
            replacement,
            value_proof,
            exhaustiveness_clause,
            exhaustiveness_proof,
            exhaustiveness_var,
            replacement_term,
        )
        return intro_literal_proof(replacement, conclusion, replacement_proof)

    return eliminate_clause_proof(source_clause, source_proof, goal, branch)


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
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
    instantiate_target_proof: bool = True,
) -> str:
    instantiated_equality_parent = tuple(substitute_literal(literal, substitution) for literal in equality_parent_clause)
    instantiated_target_parent = tuple(substitute_literal(literal, substitution) for literal in target_parent_clause)
    instantiated_equality = substitute_literal(selected_equality, substitution)
    instantiated_target = substitute_literal(selected_target, substitution)
    extra_substitution = uncovered_witness_substitution(
        normalize_clause(instantiated_equality_parent + instantiated_target_parent),
        conclusion,
        symbol_sorts,
        explicit_var_sorts,
    )
    if extra_substitution:
        substitution = compose_substitution(substitution, extra_substitution)
        instantiated_equality_parent = tuple(substitute_literal(literal, substitution) for literal in equality_parent_clause)
        instantiated_target_parent = tuple(substitute_literal(literal, substitution) for literal in target_parent_clause)
        instantiated_equality = substitute_literal(selected_equality, substitution)
        instantiated_target = substitute_literal(selected_target, substitution)
    if instantiated_equality not in normalize_clause(instantiated_equality_parent):
        raise CertificateError("Megalodon smoke paramodulation equality literal is not present after substitution")
    if instantiated_target not in normalize_clause(instantiated_target_parent):
        raise CertificateError("Megalodon smoke paramodulation target literal is not present after substitution")
    if not instantiated_equality.polarity or instantiated_equality.atom.kind != "eq" or len(instantiated_equality.atom.args) != 2:
        raise CertificateError("Megalodon smoke paramodulation selected literal must be positive equality")
    from_term, to_term = instantiated_equality.atom.args
    equality_sort = require_supported_sort(instantiated_equality.atom.name, "paramodulation equality sort")
    if term_at_position(instantiated_target.atom, position, "paramodulation.position") != from_term:
        raise CertificateError("Megalodon smoke paramodulation target position does not contain equality left side")
    expected_atom = replace_term_at_position(instantiated_target.atom, position, to_term, "paramodulation.position")
    rewritten_target = Literal(instantiated_target.polarity, expected_atom)
    if rewritten_target not in normalize_clause(conclusion):
        raise CertificateError("Megalodon smoke paramodulation conclusion does not contain the rewritten target")

    equality_proof = instantiate_proof(equality_parent_proof, equality_parent_clause, substitution, symbol_sorts)
    target_proof = (
        instantiate_proof(target_parent_proof, target_parent_clause, substitution, symbol_sorts)
        if instantiate_target_proof
        else target_parent_proof
    )
    forward_context_atom = replace_term_at_position(
        instantiated_target.atom,
        position,
        Term("var", "cert_x"),
        "paramodulation.position",
    )
    forward_context = f"(fun cert_x:{sort_type_text(equality_sort)} => {atom_text(forward_context_atom, symbol_sorts)})"
    backward_context_atom = replace_term_at_position(
        instantiated_target.atom,
        position,
        Term("var", "cert_y"),
        "paramodulation.position",
    )
    backward_context = f"(fun cert_y:{sort_type_text(equality_sort)} => {atom_text(backward_context_atom, symbol_sorts)})"
    prop_equality = instantiated_equality.atom.name == "prop"
    if equality_sort == "set":
        forward_context = f"(fun cert_x cert_y:set => {atom_text(forward_context_atom, symbol_sorts)})"
        backward_context = f"(fun cert_x cert_y:set => {atom_text(backward_context_atom, symbol_sorts)})"
    elif prop_equality:
        forward_context = f"(fun cert_x:prop => {atom_text(forward_context_atom, symbol_sorts)})"
    goal = clause_body_text(conclusion)

    def target_branch(literal: Literal, proof: str, equality_literal_proof: str) -> str:
        if literal == instantiated_target:
            if instantiated_target.polarity:
                transported = f"({equality_literal_proof} {forward_context} {proof})"
            else:
                rewritten_proof = fresh_proof_name("Hrewrite")
                rewritten_proof_type = atom_text(rewritten_target.atom, symbol_sorts)
                if equality_sort != "set":
                    symmetric_equality = positive_equality_symmetry_proof(instantiated_equality, equality_literal_proof)
                    transported = f"(fun {rewritten_proof}:{rewritten_proof_type} => ({proof} ({symmetric_equality} {forward_context} {rewritten_proof})))"
                else:
                    transported = f"(fun {rewritten_proof}:{rewritten_proof_type} => ({proof} ({equality_literal_proof} {backward_context} {rewritten_proof})))"
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


def collect_term_symbols(
    term: Term,
    constants: dict[str, str],
    functions: dict[str, tuple[int, str]],
    bound_constants: set[str] | None = None,
    expected_sort: str | None = None,
) -> None:
    bound_constants = bound_constants or set()
    collect_term_symbols_with_context(term, constants, functions, bound_constants, (), expected_sort)


def record_term_constant(constants: dict[str, str], name: str, sort: str | None) -> None:
    normalized = require_supported_sort(sort or "set", f"constant sort for {name}")
    previous = constants.get(name)
    if previous is None or previous == "set":
        constants[name] = normalized


def record_term_function(functions: dict[str, tuple[int, str]], name: str, arity: int, result_sort: str | None) -> None:
    normalized = require_supported_sort(result_sort or "set", f"function result sort for {name}")
    previous = functions.get(name)
    if previous is None:
        functions[name] = (arity, normalized)
        return
    previous_arity, previous_sort = previous
    if previous_sort == normalized:
        result_sort_text = previous_sort
    elif previous_sort == "set":
        result_sort_text = normalized
    elif normalized == "set":
        result_sort_text = previous_sort
    else:
        result_sort_text = previous_sort
    functions[name] = (max(previous_arity, arity), result_sort_text)


def collect_term_symbols_with_context(
    term: Term,
    constants: dict[str, str],
    functions: dict[str, tuple[int, str]],
    bound_constants: set[str],
    db_context: tuple[str, ...],
    expected_sort: str | None,
) -> None:
    v_eq_args = named_binary_application(term, "vEQ")
    if v_eq_args is not None:
        for arg in v_eq_args:
            collect_term_symbols_with_context(arg, constants, functions, bound_constants, db_context, "prop")
        return
    quantifier = quantifier_application(term)
    if quantifier is not None:
        _kind, body_term, _lambda_hint = quantifier
        binder = f"db{len(db_context)}"
        collect_term_symbols_with_context(body_term.args[0], constants, functions, bound_constants | {binder}, (*db_context, binder), "prop")
        return
    lambda_hint = lambda_hint_for_term(term)
    if lambda_hint is not None:
        binder = f"db{len(db_context)}"
        collect_term_symbols_with_context(term.args[0], constants, functions, bound_constants | {binder}, (*db_context, binder), expected_sort)
        return
    if term.kind == "const":
        db_match = DB_NAME_RE.match(term.name)
        if db_match is not None and int(db_match.group(1)) < len(db_context):
            return
        if (
            term.name in bound_constants
            or term.name in lambda_binder_sorts()
            or term.name in CERTIFICATE_BUILTIN_SYMBOLS
        ):
            return
        record_term_constant(constants, term.name, expected_sort)
    elif term.kind == "app":
        if term.name in CERTIFICATE_SYNTAX_SYMBOLS:
            for arg in term.args:
                collect_term_symbols_with_context(arg, constants, functions, bound_constants, db_context, expected_sort)
            return
        record_term_function(functions, term.name, len(term.args), expected_sort)
        constants.pop(term.name, None)
    elif term.kind == "apply":
        spine = application_spine(term)
        head = spine[0]
        if (
            len(spine) > 1
            and head.kind in {"const", "app"}
            and head.name not in bound_constants
            and head.name not in lambda_binder_sorts()
            and head.name not in CERTIFICATE_BUILTIN_SYMBOLS
        ):
            record_term_function(functions, head.name, len(spine) - 1, expected_sort)
            constants.pop(head.name, None)
            for arg in spine[1:]:
                collect_term_symbols_with_context(arg, constants, functions, bound_constants, db_context, "set")
            return
        collect_term_symbols_with_context(term.args[0], constants, functions, bound_constants, db_context, None)
        collect_term_symbols_with_context(term.args[1], constants, functions, bound_constants, db_context, "set")
        return
    for arg in term.args:
        collect_term_symbols_with_context(arg, constants, functions, bound_constants, db_context, "set")


def collect_atom_symbols(atom: Term, prop_atoms: set[str], predicates: dict[str, int], constants: dict[str, str], functions: dict[str, tuple[int, str]]) -> None:
    if atom.kind == "opaque":
        prop_atoms.add(atom.name)
    elif atom.kind == "pred":
        previous = predicates.setdefault(atom.name, len(atom.args))
        if previous != len(atom.args):
            raise CertificateError(f"predicate {atom.name!r} used with inconsistent arity")
        for arg in atom.args:
            collect_term_symbols(arg, constants, functions, expected_sort="set")
    elif atom.kind == "eq":
        for arg in atom.args:
            collect_term_symbols(arg, constants, functions, expected_sort=atom.name)
    else:
        raise CertificateError(f"cannot collect symbols from atom kind {atom.kind!r}")


def certificate_symbol_declarations(clauses: dict[str, tuple[Literal, ...]]) -> list[str]:
    prop_atoms: set[str] = set()
    constants: dict[str, str] = {}
    functions: dict[str, tuple[int, str]] = {}
    predicates: dict[str, int] = {}
    for clause in clauses.values():
        for literal in clause:
            collect_atom_symbols(literal.atom, prop_atoms, predicates, constants, functions)
    declarations: list[str] = []
    for name in sorted(prop_atoms):
        declarations.append(f"Variable {require_megalodon_ident(name, 'atom')}:prop.")
    for name, sort in sorted(constants.items()):
        declarations.append(f"Variable {require_megalodon_ident(name, 'constant')}:{sort}.")
    for name, (arity, result_sort) in sorted(functions.items()):
        sort = "->".join(["set"] * arity + [result_sort])
        declarations.append(f"Variable {require_megalodon_ident(name, 'function')}:{sort}.")
    for name, arity in sorted(predicates.items()):
        sort = "->".join(["set"] * arity + ["prop"])
        declarations.append(f"Variable {require_megalodon_ident(name, 'predicate')}:{sort}.")
    return declarations


def merge_outline_declarations(outline: list[str], inferred: list[str]) -> list[str]:
    by_symbol: dict[str, str] = {}
    for declaration in outline:
        symbol = declaration_symbol_name(declaration)
        if symbol is not None:
            by_symbol[symbol] = declaration
    for declaration in inferred:
        symbol = declaration_symbol_name(declaration)
        if symbol is not None:
            previous = by_symbol.get(symbol)
            if previous is not None:
                previous_parts = declaration_symbol_sorts([previous]).get(symbol)
                inferred_parts = declaration_symbol_sorts([declaration]).get(symbol)
                if (
                    previous_parts is not None
                    and inferred_parts is not None
                    and (len(previous_parts) > 1 or len(previous_parts) >= len(inferred_parts))
                ):
                    continue
            by_symbol[symbol] = declaration
    return sorted(by_symbol.values())


def instantiate_proof(
    proof_name: str,
    parent_clause: tuple[Literal, ...],
    substitution: dict[str, Term],
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
) -> str:
    proof = proof_name
    for name in clause_free_vars_sorted(parent_clause, symbol_sorts):
        term = substitution.get(name, Term("var", name))
        proof = f"({proof} {term_text(term)})"
    return proof


def wrap_clause_binders(
    clause: tuple[Literal, ...],
    proof: str,
    symbol_sorts: dict[str, tuple[str, ...]] | None = None,
    explicit_var_sorts: dict[str, str] | None = None,
) -> str:
    symbol_sorts = symbol_sorts or {}
    var_sorts = clause_var_sorts(clause, symbol_sorts, explicit_var_sorts)
    for name in reversed(clause_free_vars_sorted(clause, symbol_sorts)):
        proof = f"(fun {require_megalodon_ident(name, 'binder')} :{sort_type_text(var_sorts[name])} => {proof})"
    return proof


def conjunction_projection_proof_text(source_proof: str, source_prop: str, target_prop: str) -> str:
    source_prop = normalize_prop_lambdas(source_prop)
    target_prop = normalize_prop_lambdas(target_prop)
    if "vLAM" in source_prop or "vLAM" in target_prop:
        raise CertificateError("CNF conjunction projection has raw vLAM without lambda hints")

    def project_once(proof: str, lhs: str, rhs: str, side: str, result_prop: str) -> str:
        left = fresh_proof_name("Hleft")
        right = fresh_proof_name("Hright")
        selected = left if side == "left" else right
        return (
            f"({proof} ({strip_outer_prop_parens(result_prop)}) "
            f"(fun {left}:({strip_outer_prop_parens(lhs)}) => "
            f"fun {right}:({strip_outer_prop_parens(rhs)}) => {selected}))"
        )

    def project_body(proof: str, source_body: str, target_body: str) -> str | None:
        if prop_key(source_body) == prop_key(target_body):
            return proof
        parsed = parse_vampire_and_prop(source_body)
        if parsed is None:
            return None
        lhs, rhs = parsed
        if prop_key(lhs) == prop_key(target_body):
            return project_once(proof, lhs, rhs, "left", target_body)
        if prop_key(rhs) == prop_key(target_body):
            return project_once(proof, lhs, rhs, "right", target_body)
        left_projection = project_once(proof, lhs, rhs, "left", lhs)
        left_result = project_body(left_projection, lhs, target_body)
        if left_result is not None:
            return left_result
        right_projection = project_once(proof, lhs, rhs, "right", rhs)
        return project_body(right_projection, rhs, target_body)

    source_binders, source_body = parse_forall_prefix(source_prop)
    target_binders, target_body = parse_forall_prefix(target_prop)
    if source_binders == target_binders:
        proof = source_proof
        for name, _sort in source_binders:
            proof = f"({proof} {require_megalodon_ident(name, 'CNF projection binder')})"
        result = project_body(proof, source_body, target_body)
        if result is None:
            raise CertificateError("CNF conjunction projection path could not be replayed")
        for name, sort in reversed(source_binders):
            result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
        return result

    result = project_body(source_proof, source_prop, target_prop)
    if result is None:
        raise CertificateError("CNF conjunction projection path could not be replayed")
    return result


def disjunction_intro_proof(lhs: str, rhs: str, side: str, proof: str) -> str:
    left_case = fresh_proof_name("Hor_left")
    right_case = fresh_proof_name("Hor_right")
    result = fresh_proof_name("Hor_goal")
    selected = left_case if side == "left" else right_case
    return (
        f"(fun {result}:prop => "
        f"fun {left_case}:(({strip_outer_prop_parens(lhs)}) -> {result}) => "
        f"fun {right_case}:(({strip_outer_prop_parens(rhs)}) -> {result}) => "
        f"({selected} {proof}))"
    )


def inject_into_disjunction_proof(proof: str, source_prop: str, target_prop: str) -> str | None:
    if prop_key(source_prop) == prop_key(target_prop):
        return proof
    parsed = parse_vampire_or_prop(target_prop)
    if parsed is None:
        return None
    lhs, rhs = parsed
    left = inject_into_disjunction_proof(proof, source_prop, lhs)
    if left is not None:
        return disjunction_intro_proof(lhs, rhs, "left", left)
    right = inject_into_disjunction_proof(proof, source_prop, rhs)
    if right is not None:
        return disjunction_intro_proof(lhs, rhs, "right", right)
    return None


def formula_projection_proof_text(source_proof: str, source_prop: str, target_prop: str) -> str:
    source_prop = normalize_prop_lambdas(source_prop)
    target_prop = normalize_prop_lambdas(target_prop)
    if "vLAM" in source_prop or "vLAM" in target_prop:
        raise CertificateError("CNF formula projection has raw vLAM without lambda hints")

    def binders_prefix(prefix: list[tuple[str, str]], full: list[tuple[str, str]]) -> bool:
        return len(prefix) <= len(full) and full[:len(prefix)] == prefix

    def project_conjunct_once(proof: str, lhs: str, rhs: str, side: str, result_prop: str) -> str:
        left = fresh_proof_name("Hand_left")
        right = fresh_proof_name("Hand_right")
        selected = left if side == "left" else right
        return (
            f"({proof} ({strip_outer_prop_parens(result_prop)}) "
            f"(fun {left}:({strip_outer_prop_parens(lhs)}) => "
            f"fun {right}:({strip_outer_prop_parens(rhs)}) => {selected}))"
        )

    def project_body(proof: str, source_body: str, target_body: str, bound_vars: set[str]) -> str | None:
        if prop_key(source_body) == prop_key(target_body):
            return proof
        injected = inject_into_disjunction_proof(proof, source_body, target_body)
        if injected is not None:
            return injected
        source_binders, stripped_source = parse_forall_prefix(source_body)
        target_binders, stripped_target = parse_forall_prefix(target_body)
        if source_binders and source_binders == target_binders:
            instantiated = proof
            for name, _sort in source_binders:
                instantiated = f"({instantiated} {require_megalodon_ident(name, 'CNF projection binder')})"
            extended_bound = bound_vars | {name for name, _sort in source_binders}
            result = project_body(instantiated, stripped_source, stripped_target, extended_bound)
            if result is None:
                return None
            for name, sort in reversed(source_binders):
                result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
            return result
        if source_binders and all(name in bound_vars for name, _sort in source_binders):
            instantiated = proof
            for name, _sort in source_binders:
                instantiated = f"({instantiated} {require_megalodon_ident(name, 'CNF projection binder')})"
            result = project_body(instantiated, stripped_source, target_body, bound_vars)
            if result is not None:
                return result
        if target_binders:
            extended_bound = bound_vars | {name for name, _sort in target_binders}
            result = project_body(proof, source_body, stripped_target, extended_bound)
            if result is not None:
                for name, sort in reversed(target_binders):
                    result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
                return result
        and_parts = parse_vampire_and_prop(source_body)
        if and_parts is not None:
            lhs, rhs = and_parts
            left_projection = project_conjunct_once(proof, lhs, rhs, "left", lhs)
            left_result = project_body(left_projection, lhs, target_body, bound_vars)
            if left_result is not None:
                return left_result
            right_projection = project_conjunct_once(proof, lhs, rhs, "right", rhs)
            return project_body(right_projection, rhs, target_body, bound_vars)
        or_parts = parse_vampire_or_prop(source_body)
        if or_parts is not None:
            lhs, rhs = or_parts
            left_proof = fresh_proof_name("Hor_source_left")
            right_proof = fresh_proof_name("Hor_source_right")
            left_result = project_body(left_proof, lhs, target_body, bound_vars)
            right_result = project_body(right_proof, rhs, target_body, bound_vars)
            if left_result is None or right_result is None:
                return None
            return (
                f"({proof} ({strip_outer_prop_parens(target_body)}) "
                f"(fun {left_proof}:({strip_outer_prop_parens(lhs)}) => {left_result}) "
                f"(fun {right_proof}:({strip_outer_prop_parens(rhs)}) => {right_result}))"
            )
        return None

    source_binders, source_body = parse_forall_prefix(source_prop)
    target_binders, target_body = parse_forall_prefix(target_prop)
    if source_binders == target_binders and source_binders:
        proof = source_proof
        for name, _sort in source_binders:
            proof = f"({proof} {require_megalodon_ident(name, 'CNF projection binder')})"
        result = project_body(proof, source_body, target_body, {name for name, _sort in source_binders})
        if result is None:
            raise CertificateError("CNF formula projection could not be replayed")
        for name, sort in reversed(source_binders):
            result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
        return result
    if source_binders and target_binders and binders_prefix(source_binders, target_binders):
        proof = source_proof
        for name, _sort in source_binders:
            proof = f"({proof} {require_megalodon_ident(name, 'CNF projection binder')})"
        bound_vars = {name for name, _sort in target_binders}
        result = project_body(proof, source_body, target_body, bound_vars)
        if result is None:
            raise CertificateError("CNF formula projection could not be replayed")
        for name, sort in reversed(target_binders):
            result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
        return result
    if target_binders:
        bound_vars = {name for name, _sort in target_binders}
        result = project_body(source_proof, source_prop, target_body, bound_vars)
        if result is None:
            raise CertificateError("CNF formula projection could not be replayed")
        for name, sort in reversed(target_binders):
            result = f"(fun {require_megalodon_ident(name, 'CNF projection binder')}:{sort_type_text(sort)} => {result})"
        return result

    result = project_body(source_proof, source_prop, target_prop, set())
    if result is None:
        raise CertificateError("CNF formula projection could not be replayed")
    return result


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


def term_has_free_db(term: Term, depth: int = 0) -> bool:
    if term.kind == "const":
        match = DB_NAME_RE.match(term.name)
        return match is not None and int(match.group(1)) >= depth
    if term.kind == "app" and term.name == "vLAM" and len(term.args) == 1:
        return term_has_free_db(term.args[0], depth + 1)
    return any(term_has_free_db(arg, depth) for arg in term.args)


def step_explicit_var_sorts(step: dict[str, Any], step_id: str) -> dict[str, str]:
    value = step.get("variable_sorts", {})
    if value is None:
        return {}
    if not isinstance(value, dict):
        raise CertificateError(f"{step_id}.variable_sorts must be an object")
    result: dict[str, str] = {}
    for name, sort in value.items():
        if not isinstance(name, str) or not isinstance(sort, str):
            raise CertificateError(f"{step_id}.variable_sorts must map variable names to sort strings")
        require_megalodon_ident(name, f"{step_id}.variable_sorts.name")
        result[name] = require_supported_sort(sort, f"{step_id}.variable_sorts.{name}")
    return result


def certificate_lambda_hints(data: dict[str, Any]) -> tuple[LambdaHint, ...]:
    value = data.get("lambda_hints", [])
    if value is None:
        return ()
    if not isinstance(value, list):
        raise CertificateError("lambda_hints must be a list")
    hints: list[LambdaHint] = []
    seen: set[tuple[str, str, str]] = set()
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            raise CertificateError(f"lambda_hints[{index}] must be an object")
        body = item.get("body")
        binder = item.get("binder")
        binder_sort = item.get("binder_sort")
        if not isinstance(body, str) or not body:
            raise CertificateError(f"lambda_hints[{index}].body must be a non-empty string")
        if not isinstance(binder, str) or not binder:
            raise CertificateError(f"lambda_hints[{index}].binder must be a non-empty string")
        require_megalodon_ident(binder, f"lambda_hints[{index}].binder")
        if not isinstance(binder_sort, str) or not binder_sort:
            raise CertificateError(f"lambda_hints[{index}].binder_sort must be a non-empty string")
        hint = LambdaHint(body, binder, require_supported_sort(binder_sort, f"lambda_hints[{index}].binder_sort"))
        key = (normalize_lambda_hint_body(hint.body), hint.binder, hint.binder_sort)
        if key in seen:
            continue
        seen.add(key)
        hints.append(hint)
    return tuple(hints)


def certificate_avatar_sat_vars(data: dict[str, Any]) -> set[int]:
    result: set[int] = set()
    steps = data.get("steps", [])
    if not isinstance(steps, list):
        return result
    for step in steps:
        if not isinstance(step, dict):
            continue
        if step.get("rule") == "avatar_component":
            split_var = step.get("split_var")
            if isinstance(split_var, int) and split_var > 0:
                result.add(split_var)
            continue
        if step.get("rule") != "avatar_refutation":
            continue
        try:
            sat_clauses = parse_sat_clauses(step.get("sat_clauses"), f"{step.get('id', 'avatar_refutation')}.sat_clauses")
        except CertificateError:
            continue
        for clause in sat_clauses:
            for var, _polarity in clause:
                result.add(var)
    return result


def emit_megalodon_smoke(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]], theorem_name: str) -> str:
    global LAMBDA_HINTS
    previous_lambda_hints = LAMBDA_HINTS
    LAMBDA_HINTS = certificate_lambda_hints(data)
    try:
        return emit_megalodon_smoke_with_context(data, clauses, theorem_name)
    finally:
        LAMBDA_HINTS = previous_lambda_hints


def emit_megalodon_smoke_with_context(data: dict[str, Any], clauses: dict[str, tuple[Literal, ...]], theorem_name: str) -> str:
    inferred_declarations = certificate_symbol_declarations(clauses)
    outline_declarations = data.get("declarations")
    if outline_declarations is not None:
        if not isinstance(outline_declarations, list) or not all(isinstance(item, str) and item.startswith("Variable ") for item in outline_declarations):
            raise CertificateError("declarations must be a list of Megalodon Variable declarations")
        declarations = merge_outline_declarations(sorted(set(outline_declarations)), inferred_declarations)
    else:
        declarations = inferred_declarations
    equality_sorts = sorted(
        {
            literal.atom.name
            for clause in clauses.values()
            for literal in clause
            if literal.atom.kind == "eq"
        }
    )
    if certificate_uses_named_binary(clauses, "vEQ") and "set" not in equality_sorts:
        equality_sorts.append("set")
        equality_sorts.sort()
    if certificate_metadata_uses_infix_equality(data) and "set" not in equality_sorts:
        equality_sorts.append("set")
        equality_sorts.sort()
    avatar_sat_vars = certificate_avatar_sat_vars(data)
    lines = [
        "Definition False : prop := forall p:prop, p.",
        "Definition True : prop := forall p:prop, p -> p.",
        "Definition not : prop -> prop := fun A:prop => A -> False.",
        "Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.",
        "Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.",
        "Infix \\/ 785 left := or.",
        "Definition f__false : prop := False.",
        "Definition f__true : prop := True.",
        "Definition vNOT : prop -> prop := not.",
        "Definition vAND : prop -> prop -> prop := and.",
        "Definition vOR : prop -> prop -> prop := or.",
        "Definition vampire_false : prop := False.",
        "Definition vampire_true : prop := True.",
        "Definition vampire_not : prop -> prop := not.",
        "Definition vampire_and : prop -> prop -> prop := and.",
        "Definition vampire_or : prop -> prop -> prop := or.",
    ]
    for sort in equality_sorts:
        lines.append(equality_definition(sort))
        if sort == "set":
            lines.append("Infix = 502 := eq.")
    for sort in certificate_existential_sorts(clauses):
        lines.append(existential_definition(sort))
    definitions = definition_input_declarations(data)
    inequality_definitions = inequality_split_definitions(data, declarations)
    inequality_definition_symbols = set(inequality_definitions)
    definable_symbols = {
        symbol
        for symbol, (_sort, value) in definitions.items()
        if not term_has_free_db(value)
    }
    builtin_declarations = {
        "Variable f__false:prop.",
        "Variable f__true:prop.",
        "Variable vAND:prop->prop->prop.",
        "Variable vNOT:prop->prop.",
        "Variable vOR:prop->prop->prop.",
        "Variable vampire_false:prop.",
        "Variable vampire_true:prop.",
        "Variable vampire_and:prop->prop->prop.",
        "Variable vampire_not:prop->prop.",
        "Variable vampire_or:prop->prop->prop.",
    }
    for declaration in declarations:
        skip = False
        if declaration in builtin_declarations:
            skip = True
        declaration_symbol = declaration_symbol_name(declaration)
        if declaration_symbol in definable_symbols:
            skip = True
        if declaration_symbol in inequality_definition_symbols:
            skip = True
        if declaration_symbol in CERTIFICATE_SYNTAX_SYMBOLS:
            skip = True
        if not skip:
            lines.append(render_variable_declaration(declaration))
    for var in sorted(avatar_sat_vars):
        declaration = f"Variable {sat_split_name(var)}:prop."
        if declaration not in declarations:
            lines.append(declaration)
    witness_declaration = "Variable vampire_witness_set:set."
    if witness_declaration not in declarations:
        lines.append(witness_declaration)
    function_witness_declaration = "Variable vampire_witness_set_to_prop:set->prop."
    if function_witness_declaration not in declarations:
        lines.append(function_witness_declaration)
    symbol_sorts = declaration_symbol_sorts(declarations)
    for syntax_symbol in CERTIFICATE_SYNTAX_SYMBOLS:
        symbol_sorts.pop(syntax_symbol, None)
    for symbol in definable_symbols:
        symbol_sorts[symbol] = split_sort(definitions[symbol][0])
    symbol_sorts["vampire_witness_set"] = split_sort("set")
    symbol_sorts["vampire_witness_set_to_prop"] = split_sort("set->prop")
    symbol_sorts.update(
        {
            "f__false": split_sort("prop"),
            "f__true": split_sort("prop"),
            "vAND": split_sort("prop->prop->prop"),
            "vNOT": split_sort("prop->prop"),
            "vOR": split_sort("prop->prop->prop"),
            "vampire_false": split_sort("prop"),
            "vampire_true": split_sort("prop"),
            "vampire_and": split_sort("prop->prop->prop"),
            "vampire_not": split_sort("prop->prop"),
            "vampire_or": split_sort("prop->prop->prop"),
        }
    )

    symbol_renames = {
        symbol: require_megalodon_ident(symbol, "source symbol")
        for symbol in symbol_sorts
        if require_megalodon_ident(symbol, "source symbol") != symbol
    }

    def render_source_proposition(proposition: str) -> str:
        rendered = proposition
        for symbol, replacement in sorted(symbol_renames.items(), key=lambda item: len(item[0]), reverse=True):
            rendered = re.sub(
                rf"(?<![A-Za-z0-9_']){re.escape(symbol)}(?![A-Za-z0-9_'])",
                replacement,
                rendered,
            )
        return rendered

    for symbol, (sort, _value) in definitions.items():
        symbol_sorts[symbol] = split_sort(sort)
    for symbol, definition in inequality_definitions.items():
        symbol_sorts[symbol] = definition.sort_parts
    for symbol, (sort, value) in definitions.items():
        if symbol not in definable_symbols:
            continue
        lines.append(
            f"Definition {require_megalodon_ident(symbol, 'definition symbol')} "
            f": {require_supported_sort(sort, 'definition sort')} := "
            f"{term_text_expected(value, sort, symbol_sorts)}."
        )
    for definition in sorted(inequality_definitions.values(), key=lambda item: item.symbol):
        lines.append(inequality_split_definition_text(definition, symbol_sorts))
    step_clauses: dict[str, tuple[Literal, ...]] = {}
    proof_names: dict[str, str] = {}
    formula_proof_names: dict[str, str] = {}
    assumptions: list[tuple[str, str]] = []
    derived: list[tuple[str, str, str]] = []
    final_empty: str | None = None

    def formula_parent_proof(formula_parent: str, proposition: str) -> str:
        name = formula_proof_names.get(formula_parent)
        if name is not None:
            return name
        name = f"formula_{require_megalodon_ident(formula_parent, 'formula parent')}"
        formula_proof_names[formula_parent] = name
        rendered = normalize_prop_lambdas(render_source_proposition(proposition))
        if "vLAM" in rendered:
            raise CertificateError(f"{formula_parent}: formula parent has raw vLAM without lambda hints")
        assumptions.append((name, rendered))
        return name

    for step in data["steps"]:
        step_id = step["id"]
        rule = step["rule"]
        clause = clauses[step_id]
        explicit_var_sorts = step_explicit_var_sorts(step, step_id)
        step_clauses[step_id] = clause
        if not clause:
            final_empty = step_id
        if rule == "input":
            proof_names[step_id] = step_id
            assumptions.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts)))
            continue
        if rule == "avatar_component":
            proof_names[step_id] = step_id
            assumptions.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts)))
            continue
        if rule == "definition_input":
            if step.get("symbol") not in definable_symbols:
                proof_names[step_id] = step_id
                assumptions.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts)))
                continue
            proof = wrap_clause_binders(clause, equality_refl_proof(), symbol_sorts, explicit_var_sorts)
            proof_names[step_id] = step_id
            derived.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts), proof))
            continue
        if rule == "cnf_formula_exact":
            source_proposition = render_source_proposition(step["proposition"])
            source_proof = formula_parent_proof(step["formula_parent"], source_proposition)
            target_prop = clause_formula_prop_text(clause, None, explicit_var_sorts)
            if prop_key(source_proposition) == prop_key(target_prop):
                proof = source_proof
            else:
                proof = formula_projection_proof_text(source_proof, source_proposition, target_prop)
            proof_names[step_id] = step_id
            derived.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts), proof))
            continue
        if rule == "cnf_formula_conjunct":
            source_proposition = render_source_proposition(step["source_proposition"])
            target_proposition = render_source_proposition(step["proposition"])
            source_proof = formula_parent_proof(step["formula_parent"], source_proposition)
            proof = conjunction_projection_proof_text(source_proof, source_proposition, target_proposition)
            proof_names[step_id] = step_id
            derived.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts), proof))
            continue
        if rule == "cnf_formula_projection":
            source_proposition = render_source_proposition(step["source_proposition"])
            source_proof = formula_parent_proof(step["formula_parent"], source_proposition)
            proof_target = clause_formula_prop_text(clause, None, explicit_var_sorts)
            proof = formula_projection_proof_text(source_proof, source_proposition, proof_target)
            proof_names[step_id] = step_id
            derived.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts), proof))
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
                    symbol_sorts,
                    explicit_var_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        elif rule == "substitute":
            parent = step["parents"][0]
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            instantiated_parent = tuple(substitute_literal(literal, substitution) for literal in step_clauses[parent])
            proof = wrap_clause_binders(
                clause,
                    reorder_clause_proof_text(
                        instantiated_parent,
                        instantiate_proof(proof_names[parent], step_clauses[parent], substitution, symbol_sorts),
                        clause,
                    ),
                symbol_sorts,
                explicit_var_sorts,
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
                    symbol_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        elif rule == "truth_conflict_resolution":
            parent = step["parents"][0]
            selected_literal = parse_literal(step["literal"], f"{step_id}.literal")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            proof = wrap_clause_binders(
                clause,
                truth_conflict_resolution_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    selected_literal,
                    substitution,
                    clause,
                    symbol_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
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
                    symbol_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
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
                    symbol_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        elif rule == "paramodulate":
            parents = step["parents"]
            selected_equality = parse_literal(step["equality"], f"{step_id}.equality")
            selected_target = parse_literal(step["target"], f"{step_id}.target")
            substitution = parse_substitution(step["substitution"], f"{step_id}.substitution")
            position = parse_position(step["position"], f"{step_id}.position")
            instantiated_target = substitute_literal(selected_target, substitution)
            check_rewrite_scope(step, instantiated_target.atom, position, step_id)
            if position_rewrites_bound_lambda_var(
                instantiated_target.atom,
                position,
                f"{step_id}.position",
            ) or position_enters_lambda_body(instantiated_target.atom, position, f"{step_id}.position"):
                proof_names[step_id] = step_id
                assumptions.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts)))
                continue
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
                    symbol_sorts,
                    explicit_var_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        elif rule == "factor":
            parent = step["parents"][0]
            proof = proof_names[parent]
        elif rule == "contradiction":
            parent = step["parents"][0]
            proof = proof_names[parent]
        elif rule == "avatar_refutation":
            sat_clauses = parse_sat_clauses(step["sat_clauses"], f"{step_id}.sat_clauses")
            sat_proof_names: list[str] = []
            for index, sat_clause in enumerate(sat_clauses):
                assumption_name = f"{step_id}_sat_{index}"
                sat_proof_names.append(assumption_name)
                assumptions.append((assumption_name, sat_clause_prop_text(sat_clause)))
            proof = avatar_refutation_proof_text(sat_clauses, tuple(sat_proof_names))
        elif rule == "definition_rewrite_chain":
            parent = step["parents"][0]
            rewrites = tuple(
                DefinitionRewriteStep(
                    parse_term(rewrite["from"], f"{step_id}.rewrites[{index}].from"),
                    parse_term(rewrite["to"], f"{step_id}.rewrites[{index}].to"),
                    rewrite.get("parent"),
                    rewrite.get("literal"),
                    parse_position(rewrite["position"], f"{step_id}.rewrites[{index}].position") if "position" in rewrite else None,
                    normalize_clause(parse_clause(rewrite["clause"], f"{step_id}.rewrites[{index}].clause")) if "clause" in rewrite else None,
                )
                for index, rewrite in enumerate(step["rewrites"])
            )
            if append_definition_rewrite_chain_claims(
                step_id,
                step_clauses[parent],
                proof_names[parent],
                rewrites,
                clause,
                step_clauses,
                proof_names,
                derived,
                symbol_sorts,
                explicit_var_sorts,
            ):
                continue
            proof = wrap_clause_binders(
                clause,
                definition_rewrite_chain_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    rewrites,
                    clause,
                    step_clauses,
                    proof_names,
                    symbol_sorts,
                    explicit_var_sorts,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        elif rule == "inequality_split":
            parent = step["parents"][0]
            proof = wrap_clause_binders(
                clause,
                inequality_split_proof_text(
                    step_clauses[parent],
                    proof_names[parent],
                    step["splits"],
                    clause,
                    step_clauses,
                    proof_names,
                ),
                symbol_sorts,
                explicit_var_sorts,
            )
        else:
            raise CertificateError(f"Megalodon smoke elaboration does not yet support {rule}")
        proof_names[step_id] = step_id
        derived.append((step_id, clause_prop_text(clause, symbol_sorts, explicit_var_sorts), proof))

    if final_empty is None:
        raise CertificateError("certificate has no empty-clause step to prove False")
    theorem_assumptions = [("xm", "forall P:prop, P \\/ (P -> False)"), *assumptions]
    theorem_type = " -> ".join([*(f"({prop})" for _name, prop in theorem_assumptions), "False"])
    lines.append(f"Theorem {theorem_name} : {theorem_type}.")
    for name, prop in theorem_assumptions:
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
    checked_normal_form_clauses = 0
    checked_cnf_clauses = 0
    checked_avatar_components = 0
    for step in data["steps"]:
        rule = step["rule"]
        rules[rule] = rules.get(rule, 0) + 1
        if rule == "avatar_component":
            checked_avatar_components += 1
        if rule == "input":
            source = step.get("source", {})
            source_kind = source.get("kind", "unknown") if isinstance(source, dict) else "unknown"
            input_sources[source_kind] = input_sources.get(source_kind, 0) + 1
            if source_kind == "vampire_derived_clause":
                derived_assumptions += 1
            if isinstance(source, dict) and "normal_form_clause" in source:
                checked_normal_form_clauses += 1
            if isinstance(source, dict) and "cnf" in source:
                checked_cnf_clauses += 1
    summary = {
        "steps": len(clauses),
        "empty_clauses": sum(1 for clause in clauses.values() if not clause),
        "rules": dict(sorted(rules.items())),
        "input_sources": dict(sorted(input_sources.items())),
        "derived_assumptions": derived_assumptions,
        "checked_normal_form_clauses": checked_normal_form_clauses,
        "checked_cnf_clauses": checked_cnf_clauses,
        "checked_avatar_components": checked_avatar_components,
    }
    reconstruction = data.get("outline_reconstruction")
    if isinstance(reconstruction, dict):
        summary["outline_reconstruction"] = {
            key: value
            for key, value in sorted(reconstruction.items())
            if isinstance(key, str) and isinstance(value, int)
        }
    embedded = data.get("embedded_certificate_json")
    if isinstance(embedded, dict):
        summary["embedded_certificate_json"] = {
            key: value
            for key, value in sorted(embedded.items())
            if isinstance(key, str) and isinstance(value, (int, dict))
        }
    outline_error = data.get("outline_reconstruction_error")
    if isinstance(outline_error, str):
        summary["outline_reconstruction_error"] = outline_error
    return summary


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
            outline_text = args.certificate.read_text(encoding="utf-8")
            data = certificate_from_vampire_outline(outline_text, args.certificate.stem)
        else:
            data = json.loads(args.certificate.read_text(encoding="utf-8"))
        clauses = check_certificate(data)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"certificate check failed: {exc}", file=sys.stderr)
        return 1
    except CertificateError as exc:
        if not args.from_vampire_outline:
            print(f"certificate check failed: {exc}", file=sys.stderr)
            return 1
        try:
            embedded = embedded_certificate_json_data(outline_text)
            if embedded is None:
                raise exc
            embedded["problem"] = args.certificate.stem
            embedded["outline_reconstruction_error"] = str(exc)
            data = embedded
            clauses = check_certificate(data)
        except CertificateError as embedded_exc:
            print(f"certificate check failed: {embedded_exc}", file=sys.stderr)
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
