#!/usr/bin/env python3
"""Generate and check Megalodon TH0 hammer obligations with Vampire proofs.

This is the reproducible test driver for the Vampire-to-Megalodon proof
reconstruction work.  It intentionally uses Megalodon's own TH0 generator as
the source of truth, then selects obligations whose source lines are recorded
as HO-Vampire-solvable in examples/hammer/ATPresults2025.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import signal
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable


RESULT_RE = re.compile(r"^hammer\.(?P<line>[0-9]+)\.(?P<char>[0-9]+)\.\*\.p:")
PROBLEM_RE = re.compile(r"^(?P<prefix>.*)\.(?P<line>[0-9]+)\.(?P<char>[0-9]+)\.th0\.p$")
PROVED_RE = re.compile(r"SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)\b")
FATAL_OUTPUT_RE = re.compile(r"Aborted by signal|ASSERTION|User error|missing .* implementation", re.IGNORECASE)
MEGALODON_SOURCE_LINE_RE = re.compile(r'^megalodon_source_line\("(?P<line>(?:\\.|[^"\\])*)"\)\.$')
MEGALODON_STEP_RE = re.compile(r'^megalodon_step\((?P<id>[0-9]+),"(?P<rule>(?:\\.|[^"\\])*)"')
FRESH_SET_RE = re.compile(r"^sF[0-9]+$")
DEFINITION_RE = re.compile(r"^Definition (?P<name>[_A-Za-z][_A-Za-z0-9']*) : (?P<sort>[^:]+?) := (?P<body>.*)\.$")


@dataclass
class Obligation:
    line: int
    char: int
    problem: str
    proof: str
    problem_sha256: str
    proof_sha256: str | None = None
    status: str | None = None
    command: list[str] | None = None
    source: str | None = None
    source_sha256: str | None = None
    source_line_text: str | None = None
    theorem_name: str | None = None
    theorem_line: int | None = None


@dataclass
class RunningVampire:
    line: int
    char: int
    problem: Path
    proof_path: Path
    command: list[str]
    process: subprocess.Popen[str]
    started_at: float


@dataclass(frozen=True)
class Token:
    value: str


@dataclass(frozen=True)
class Expr:
    kind: str
    value: str | None = None
    args: tuple["Expr", ...] = ()
    sort: str | None = None


@dataclass(frozen=True)
class ProofRule:
    name: str
    binders: tuple[str, ...]
    premises: tuple[Expr, ...]
    conclusion: Expr


@dataclass(frozen=True)
class EqFact:
    left: Expr
    right: Expr
    proof: str


@dataclass(frozen=True)
class DefinitionInfo:
    sort: str
    body_text: str
    proof: str
    binders: tuple[str, ...]
    body: Expr


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd: list[str], cwd: Path, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        timeout=timeout,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


def parse_vampire_lines(results: Path) -> set[int]:
    lines: set[int] = set()
    with results.open("r", encoding="utf-8") as f:
        for row in f:
            m = RESULT_RE.match(row)
            if m and "(HO)Vampire" in row:
                lines.add(int(m.group("line")))
    return lines


def generated_th0(prefix: Path) -> list[tuple[int, int, Path]]:
    parent = prefix.parent
    stem = prefix.name
    found: list[tuple[int, int, Path]] = []
    for path in parent.glob(f"{stem}.*.*.th0.p"):
        m = PROBLEM_RE.match(str(path))
        if not m:
            continue
        found.append((int(m.group("line")), int(m.group("char")), path))
    found.sort()
    return found


def generate_problems(repo: Path, megalodon: Path, source: Path, prefix: Path) -> None:
    for old in prefix.parent.glob(f"{prefix.name}.*.p"):
        old.unlink()
    cmd = [
        str(megalodon),
        "-allowincompleteqed",
        "-createabyprobs",
        prefix.name,
        str(source),
    ]
    proc = run(cmd, prefix.parent)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout)
        raise SystemExit(f"Megalodon TH0 generation failed with exit code {proc.returncode}")


THEOREM_RE = re.compile(r"^\s*(?:Theorem|Lemma|Example|Fact|Remark|Corollary|Proposition|Property)\s+(?P<name>[^:\s]+)")


def source_context(source: Path | None, line: int) -> dict[str, str | int | None]:
    if source is None or not source.exists():
        return {
            "source": str(source) if source is not None else None,
            "source_sha256": None,
            "source_line_text": None,
            "theorem_name": None,
            "theorem_line": None,
        }
    rows = source.read_text(encoding="utf-8", errors="replace").splitlines()
    line_text = rows[line - 1].strip() if 1 <= line <= len(rows) else None
    theorem_name = None
    theorem_line = None
    for index in range(min(line, len(rows)), 0, -1):
        match = THEOREM_RE.match(rows[index - 1])
        if match:
            theorem_name = match.group("name")
            theorem_line = index
            break
    return {
        "source": str(source),
        "source_sha256": sha256(source),
        "source_line_text": line_text,
        "theorem_name": theorem_name,
        "theorem_line": theorem_line,
    }


def select_obligations(prefix: Path, vampire_lines: set[int], minimum: int) -> list[tuple[int, int, Path]]:
    selected = [(line, char, path) for line, char, path in generated_th0(prefix) if line in vampire_lines]
    if len(selected) < minimum:
        raise SystemExit(f"Need {minimum} generated HO-Vampire obligations, found {len(selected)}")
    return selected


def obligations_from_manifest(manifest: Path) -> list[tuple[int, int, Path]]:
    selected = []
    for row in manifest.read_text(encoding="utf-8").splitlines():
        if not row.strip():
            continue
        obligation = Obligation(**json.loads(row))
        selected.append((obligation.line, obligation.char, Path(obligation.problem)))
    selected.sort()
    return selected


def vampire_command(args: argparse.Namespace, problem: Path, proof_path: Path) -> list[str]:
    cmd = [str(args.vampire)]
    if args.vampire_arg:
        for item in args.vampire_arg:
            cmd.extend(item)
    else:
        cmd.extend(
            [
                "--input_syntax",
                "tptp",
                "--mode",
                "portfolio",
                "--schedule",
                args.schedule,
                "-t",
                str(args.timeout),
                "--proof",
                args.proof_mode,
            ]
        )
        if args.proof_mode in {"leancheck", "megalodon"}:
            cmd.extend(
                [
                    "--proof_extra",
                    "lean",
                    "--skolemization",
                    "syntactic",
                    "--shuffle_input",
                    "off",
                ]
            )
            if args.proof_mode == "leancheck":
                cmd.extend(["--output_mode", "lean"])
    cmd.append(str(problem))
    return cmd


def proof_has_reconstruction_payload(text: str, proof_mode: str) -> bool:
    if proof_mode == "leancheck":
        return "end vamproof" in text and "theorem fullProof" in text
    if proof_mode == "megalodon":
        return (
            "megalodon_reconstruction_start." in text
            and "megalodon_step(" in text
            and "megalodon_final_step(" in text
            and "megalodon_reconstruction_end." in text
        )
    return "inference(" in text or "SZS output start Proof" in text or "Refutation" in text


def proof_has_fatal_output(text: str) -> bool:
    return FATAL_OUTPUT_RE.search(text) is not None


def proof_mode_from_path(path: Path) -> str:
    if path.name.endswith(".leancheck.out"):
        return "leancheck"
    if path.name.endswith(".megalodon.out"):
        return "megalodon"
    return "tptp"


def extract_marked_megalodon_blocks(text: str, start_marker: str, end_marker: str) -> list[list[str]]:
    candidates: list[list[str]] = []
    current: list[str] | None = None
    for raw in text.splitlines():
        line = raw.strip()
        if line == start_marker:
            current = []
            continue
        if line == end_marker:
            if current is not None:
                candidates.append(current)
            current = None
            continue
        if current is not None:
            match = MEGALODON_SOURCE_LINE_RE.match(line)
            if match:
                current.append(json.loads(f'"{match.group("line")}"'))
    return candidates


def extract_megalodon_source_candidates(text: str) -> list[list[str]]:
    return extract_marked_megalodon_blocks(
        text,
        "megalodon_source_candidate_start.",
        "megalodon_source_candidate_end.",
    )


def source_candidate_claim_proofs(text: str) -> dict[str, list[str]]:
    proofs: dict[str, list[str]] = {}
    for candidate in extract_megalodon_source_candidates(text):
        theorem_index = None
        theorem_proposition = None
        for index, line in enumerate(candidate):
            theorem = proposition_after_colon(line, "Theorem ")
            if theorem is not None:
                theorem_index = index
                theorem_proposition = theorem[1]
                break
        if theorem_index is None or theorem_proposition is None:
            continue
        proof_lines = [line for line in candidate[theorem_index + 1:] if line != "Qed."]
        if proof_lines:
            proofs.setdefault(theorem_proposition, proof_lines)
    return proofs


def extract_megalodon_claim_skeletons(text: str) -> list[list[str]]:
    return extract_marked_megalodon_blocks(
        text,
        "megalodon_claim_skeleton_start.",
        "megalodon_claim_skeleton_end.",
    )


def proposition_after_colon(line: str, prefix: str) -> tuple[str, str] | None:
    if not line.startswith(prefix):
        return None
    rest = line[len(prefix):]
    name, separator, proposition = rest.partition(":")
    if not separator or not proposition.endswith("."):
        return None
    return name.strip(), proposition[:-1].strip()


def function_definition_step_ids(proof_text: str) -> set[str]:
    ids: set[str] = set()
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_RE.match(line.strip())
        if match and json.loads(f'"{match.group("rule")}"') == "function definition":
            ids.add("S" + match.group("id"))
    return ids


TOKEN_RE = re.compile(r"->|[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[(),:=]")


def tokenize_expr(text: str) -> list[Token]:
    tokens: list[Token] = []
    index = 0
    while index < len(text):
        if text[index].isspace():
            index += 1
            continue
        match = TOKEN_RE.match(text, index)
        if not match:
            raise ValueError(f"unexpected expression text at {index}: {text[index:index + 20]}")
        tokens.append(Token(match.group(0)))
        index = match.end()
    return tokens


class ExprParser:
    def __init__(self, text: str):
        self.tokens = tokenize_expr(text)
        self.index = 0

    def peek(self) -> str | None:
        if self.index >= len(self.tokens):
            return None
        return self.tokens[self.index].value

    def pop(self, value: str | None = None) -> str:
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of expression")
        if value is not None and token != value:
            raise ValueError(f"expected {value}, got {token}")
        self.index += 1
        return token

    def parse(self) -> Expr:
        expr = self.parse_arrow()
        if self.peek() is not None:
            raise ValueError(f"unexpected token {self.peek()}")
        return expr

    def parse_arrow(self) -> Expr:
        left = self.parse_forall()
        if self.peek() == "->":
            self.pop("->")
            right = self.parse_arrow()
            return Expr("arrow", args=(left, right))
        return left

    def parse_forall(self) -> Expr:
        if self.peek() != "forall":
            return self.parse_eq()
        self.pop("forall")
        name = self.pop()
        self.pop(":")
        sort_tokens: list[str] = []
        while self.peek() is not None and self.peek() != ",":
            sort_tokens.append(self.pop())
        self.pop(",")
        return Expr("forall", value=name, sort="".join(sort_tokens), args=(self.parse_arrow(),))

    def parse_eq(self) -> Expr:
        left = self.parse_app()
        if self.peek() == "=":
            self.pop("=")
            right = self.parse_app()
            return Expr("eq", args=(left, right))
        return left

    def parse_app(self) -> Expr:
        atoms = [self.parse_atom()]
        while self.peek() is not None and self.peek() not in {")", ",", "->", "="}:
            atoms.append(self.parse_atom())
        if len(atoms) == 1:
            return atoms[0]
        return Expr("app", args=tuple(atoms))

    def parse_atom(self) -> Expr:
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of expression")
        if token == "(":
            self.pop("(")
            expr = self.parse_arrow()
            self.pop(")")
            return expr
        if token in {")", ",", ":", "=", "->"}:
            raise ValueError(f"unexpected token {token}")
        return Expr("var", value=self.pop())


def parse_expr(text: str) -> Expr | None:
    try:
        return ExprParser(text).parse()
    except ValueError:
        return None


def expr_text(expr: Expr, context: str = "top") -> str:
    if expr.kind == "var":
        assert expr.value is not None
        return expr.value
    if expr.kind == "app":
        text = " ".join(expr_text(arg, "app_arg") for arg in expr.args)
    elif expr.kind == "eq":
        text = f"{expr_text(expr.args[0], 'eq_side')} = {expr_text(expr.args[1], 'eq_side')}"
    elif expr.kind == "arrow":
        text = f"{expr_text(expr.args[0], 'arrow_left')} -> {expr_text(expr.args[1], 'arrow_right')}"
    elif expr.kind == "forall":
        assert expr.value is not None and expr.sort is not None
        text = f"forall {expr.value}:{expr.sort}, {expr_text(expr.args[0])}"
    else:
        raise ValueError(f"unknown expression kind {expr.kind}")
    if context in {"app_arg", "eq_side"} and expr.kind in {"app", "eq", "arrow", "forall"}:
        return f"({text})"
    if context == "arrow_left" and expr.kind == "arrow":
        return f"({text})"
    return text


def expr_key(expr: Expr) -> str:
    return expr_text(expr)


def proof_arg_text(expr: Expr) -> str:
    if expr.kind == "var":
        return expr_text(expr)
    return f"({expr_text(expr)})"


def proof_term_text(proof: str) -> str:
    return proof if proof.startswith("(") and proof.endswith(")") else f"({proof})"


def collect_foralls(expr: Expr) -> tuple[list[tuple[str, str]], Expr]:
    binders: list[tuple[str, str]] = []
    while expr.kind == "forall":
        assert expr.value is not None and expr.sort is not None
        binders.append((expr.value, expr.sort))
        expr = expr.args[0]
    return binders, expr


def split_arrows(expr: Expr) -> tuple[list[Expr], Expr]:
    premises: list[Expr] = []
    while expr.kind == "arrow":
        premises.append(expr.args[0])
        expr = expr.args[1]
    return premises, expr


def match_expr(pattern: Expr, target: Expr, variables: set[str], subst: dict[str, Expr]) -> bool:
    if pattern.kind == "var" and pattern.value in variables:
        previous = subst.get(pattern.value)
        if previous is None:
            subst[pattern.value] = target
            return True
        return expr_key(previous) == expr_key(target)
    if pattern.kind != target.kind or pattern.value != target.value or pattern.sort != target.sort:
        return False
    if len(pattern.args) != len(target.args):
        return False
    return all(match_expr(left, right, variables, subst) for left, right in zip(pattern.args, target.args))


def substitute_expr(expr: Expr, subst: dict[str, Expr]) -> Expr:
    if expr.kind == "var" and expr.value in subst:
        return subst[expr.value]
    if not expr.args:
        return expr
    return Expr(expr.kind, value=expr.value, args=tuple(substitute_expr(arg, subst) for arg in expr.args), sort=expr.sort)


def make_proof_rule(name: str, proposition: str) -> ProofRule | None:
    expr = parse_expr(proposition)
    if expr is None:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    return ProofRule(
        name=name,
        binders=tuple(name for name, _ in binders),
        premises=tuple(premises),
        conclusion=conclusion,
    )


def make_eq_fact(name: str, proposition: str) -> EqFact | None:
    expr = parse_expr(proposition)
    if expr is None:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if binders or premises or conclusion.kind != "eq":
        return None
    return EqFact(conclusion.args[0], conclusion.args[1], name)


def fresh_definition(proposition: str, variable_sorts: dict[str, str]) -> tuple[str, DefinitionInfo] | None:
    expr = parse_expr(proposition)
    if expr is None:
        return None

    binders, body = collect_foralls(expr)
    if body.kind != "eq":
        return None
    binder_names = [name for name, _ in binders]
    binder_sorts = [sort for _, sort in binders]
    left, right = body.args
    candidates: list[tuple[Expr, Expr]] = []
    if right.kind == "var" and right.value is not None:
        candidates.append((right, left))
    if left.kind == "var" and left.value is not None:
        candidates.append((left, right))
    if binders:
        if right.kind == "app" and right.args and right.args[0].kind == "var":
            candidates.append((right, left))
        if left.kind == "app" and left.args and left.args[0].kind == "var":
            candidates.append((left, right))
    for target, body in candidates:
        if target.kind == "var":
            target_name = target.value
            target_args: tuple[Expr, ...] = ()
        elif target.kind == "app" and target.args and target.args[0].kind == "var":
            target_name = target.args[0].value
            target_args = target.args[1:]
        else:
            continue
        if target_name is None or not FRESH_SET_RE.match(target_name):
            continue
        if len(target_args) != len(binder_names):
            continue
        if any(arg.kind != "var" or arg.value != name for arg, name in zip(target_args, binder_names)):
            continue
        target_sort = variable_sorts.get(target_name)
        if target_sort is None:
            continue
        expected_sort = "->".join(binder_sorts + ["set"])
        if target_sort != expected_sort:
            continue
        body_text = expr_text(body)
        if target_name in body_text.split():
            continue
        if binders:
            proof = f"({' '.join(['fun'] + binder_names + ['Q', 'H', '=>', 'H'])})"
            definition_body = body_text
            for binder_name, binder_sort in reversed(binders):
                definition_body = f"fun {binder_name}:{binder_sort} => {definition_body}"
        else:
            proof = "(fun Q H => H)"
            definition_body = body_text
        body_expr = parse_expr(body_text)
        if body_expr is None:
            continue
        return target_name, DefinitionInfo(target_sort, definition_body, proof, tuple(binder_names), body_expr)
    return None


def normalize_defined_expr(expr: Expr, definitions: dict[str, DefinitionInfo]) -> Expr:
    if expr.kind == "var":
        assert expr.value is not None
        definition = definitions.get(expr.value)
        if definition is not None and not definition.binders:
            return normalize_defined_expr(definition.body, definitions)
        return expr
    if expr.kind == "app" and expr.args and expr.args[0].kind == "var":
        head = expr.args[0]
        assert head.value is not None
        args = tuple(normalize_defined_expr(arg, definitions) for arg in expr.args[1:])
        definition = definitions.get(head.value)
        if definition is not None and len(definition.binders) == len(args):
            subst = dict(zip(definition.binders, args))
            return normalize_defined_expr(substitute_expr(definition.body, subst), definitions)
        return Expr("app", args=(head,) + args)
    if not expr.args:
        return expr
    return Expr(
        expr.kind,
        value=expr.value,
        args=tuple(normalize_defined_expr(arg, definitions) for arg in expr.args),
        sort=expr.sort,
    )


def definition_reflexivity_proof(proposition: str, definitions: dict[str, DefinitionInfo]) -> str | None:
    expr = parse_expr(proposition)
    if expr is None:
        return None
    binders, body = collect_foralls(expr)
    if body.kind != "eq":
        return None
    left = normalize_defined_expr(body.args[0], definitions)
    right = normalize_defined_expr(body.args[1], definitions)
    if expr_key(left) != expr_key(right):
        return None
    args = [name for name, _ in binders] + ["Q", "H"]
    return f"({' '.join(['fun'] + args + ['=>', 'H'])})"


def unary_application(expr: Expr) -> tuple[str, Expr] | None:
    if expr.kind != "app" or len(expr.args) != 2 or expr.args[0].kind != "var" or expr.args[0].value is None:
        return None
    return expr.args[0].value, expr.args[1]


def successor_depth(expr: Expr) -> int | None:
    if expr.kind == "var" and expr.value == "Empty":
        return 0
    if expr.kind == "app" and len(expr.args) == 2 and expr.args[0].kind == "var" and expr.args[0].value == "ordsucc":
        inner = successor_depth(expr.args[1])
        if inner is not None:
            return inner + 1
    return None


def successor_term_text(depth: int) -> str:
    text = "Empty"
    for _ in range(depth):
        text = f"ordsucc ({text})" if text != "Empty" else "ordsucc Empty"
    return text


def add_function_definition_skeletons(lines: list[str], proof_text: str | None) -> list[str]:
    if proof_text is None:
        return list(lines)
    definition_step_names = function_definition_step_ids(proof_text)
    if not definition_step_names:
        return list(lines)

    variable_sorts: dict[str, str] = {}
    variable_re = re.compile(r"^Variable (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^.]+)\.$")
    for line in lines:
        match = variable_re.match(line)
        if match:
            variable_sorts[match.group("name")] = match.group("sort").strip()

    definitions: dict[str, DefinitionInfo] = {}
    definition_claims: dict[str, str] = {}
    for line in lines:
        claim = proposition_after_colon(line, "claim ")
        if claim is None:
            continue
        claim_name, proposition = claim
        if claim_name not in definition_step_names:
            continue
        found = fresh_definition(proposition, variable_sorts)
        if found is None:
            continue
        target, definition = found
        definitions.setdefault(target, definition)
        definition_claims[claim_name] = definition.proof

    if not definitions:
        return list(lines)

    result: list[str] = []
    inserted_definitions = False
    index = 0
    while index < len(lines):
        line = lines[index]
        variable_match = variable_re.match(line)
        if variable_match and variable_match.group("name") in definitions:
            index += 1
            continue
        if not inserted_definitions and (line.startswith("Axiom ") or line.startswith("Theorem ")):
            for name, definition in definitions.items():
                result.append(f"Definition {name} : {definition.sort} := {definition.body_text}.")
            inserted_definitions = True
        result.append(line)
        claim = proposition_after_colon(line, "claim ")
        if claim is not None and index + 1 < len(lines) and lines[index + 1] == "{ admit. }":
            proof = definition_claims.get(claim[0]) or definition_reflexivity_proof(claim[1], definitions)
            if proof is not None:
                result.append("{ exact " + proof + ". }")
                index += 2
                continue
        index += 1

    if not inserted_definitions:
        for name, definition in definitions.items():
            result.append(f"Definition {name} : {definition.sort} := {definition.body_text}.")
    return result


def fill_source_candidate_claims(lines: list[str], proof_text: str | None) -> list[str]:
    if proof_text is None:
        return list(lines)
    source_proofs = source_candidate_claim_proofs(proof_text)
    if not source_proofs:
        return list(lines)
    used: set[str] = set()
    result: list[str] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        result.append(line)
        claim = proposition_after_colon(line, "claim ")
        if (
            claim is not None
            and claim[1] in source_proofs
            and claim[1] not in used
            and index + 1 < len(lines)
            and lines[index + 1] == "{ admit. }"
        ):
            result.append("{")
            result.extend(source_proofs[claim[1]])
            result.append("}")
            used.add(claim[1])
            index += 2
            continue
        index += 1
    return result


IDENTIFIER_CHARS = "_'0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
FORALL_RE = re.compile(r"forall (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^,]+), ")


def replace_identifier(text: str, name: str, replacement: str) -> str:
    result = []
    index = 0
    while index < len(text):
        found = text.find(name, index)
        if found < 0:
            result.append(text[index:])
            break
        before_ok = found == 0 or text[found - 1] not in IDENTIFIER_CHARS
        after_index = found + len(name)
        after_ok = after_index == len(text) or text[after_index] not in IDENTIFIER_CHARS
        if before_ok and after_ok:
            result.append(text[index:found])
            result.append(replacement)
            index = after_index
        else:
            result.append(text[index:after_index])
            index = after_index
    return "".join(result)


def forall_scope_end(text: str, forall_index: int) -> int:
    if forall_index > 0 and text[forall_index - 1] == "(":
        depth = 0
        for index in range(forall_index - 1, len(text)):
            if text[index] == "(":
                depth += 1
            elif text[index] == ")":
                depth -= 1
                if depth == 0:
                    return index
    return len(text)


def find_forall(text: str, start: int) -> re.Match[str] | None:
    for match in FORALL_RE.finditer(text, start):
        if match.start() == 0 or text[match.start() - 1] not in IDENTIFIER_CHARS:
            return match
    return None


def canonicalize_segment(text: str, next_var: list[int]) -> str:
    result = []
    index = 0
    while True:
        match = find_forall(text, index)
        if match is None:
            result.append(text[index:])
            break
        result.append(text[index:match.start()])
        replacement = f"__v{next_var[0]}"
        next_var[0] += 1
        body_start = match.end()
        scope_end = forall_scope_end(text, match.start())
        body = replace_identifier(text[body_start:scope_end], match.group("name"), replacement)
        result.append(f"forall {replacement}:{match.group('sort').strip()}, ")
        result.append(canonicalize_segment(body, next_var))
        index = scope_end
    return "".join(result)


def canonical_proposition(proposition: str) -> str:
    return canonicalize_segment(proposition, [0])


def proof_head(proof: str) -> str:
    if re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", proof):
        return proof
    if proof.startswith("(") and proof.endswith(")"):
        return proof
    return f"({proof})"


def eq_symmetry_proof(proof: str, left: Expr) -> str:
    return f"({proof_head(proof)} (fun z:set => z = {expr_text(left)}) (fun R Hr => Hr))"


def eq_transitivity_proof(proofs: list[str], start_text: str | None = None) -> str | None:
    if not proofs:
        return None
    if len(proofs) == 1:
        return proofs[0]
    term = "H"
    for proof in proofs:
        term = f"{proof_head(proof)} Q ({term})"
    if start_text is None:
        return f"(fun Q H => {term})"
    return f"(fun Q:set->prop => fun H:Q ({start_text}) => {term})"


def equality_chain_proof(expr: Expr, eq_facts: list[EqFact], max_depth: int = 3) -> str | None:
    if expr.kind != "eq":
        return None
    start = expr_key(expr.args[0])
    target = expr_key(expr.args[1])
    if start == target:
        return "(fun Q H => H)"

    edges: dict[str, list[tuple[str, str]]] = {}
    for fact in eq_facts:
        left_key = expr_key(fact.left)
        right_key = expr_key(fact.right)
        edges.setdefault(left_key, []).append((right_key, fact.proof))
        edges.setdefault(right_key, []).append((left_key, eq_symmetry_proof(fact.proof, fact.left)))

    queue: list[tuple[str, list[str]]] = [(start, [])]
    seen = {start}
    while queue:
        node, proofs = queue.pop(0)
        if len(proofs) >= max_depth:
            continue
        for next_node, proof in edges.get(node, []):
            if next_node in seen:
                continue
            next_proofs = proofs + [proof]
            if next_node == target:
                return eq_transitivity_proof(next_proofs, expr_text(expr.args[0]))
            seen.add(next_node)
            queue.append((next_node, next_proofs))
    return None


def rule_application_parts(
    rule: ProofRule,
    subst: dict[str, Expr],
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
) -> list[str] | None:
    if any(binder not in subst for binder in rule.binders):
        return None
    parts = [rule.name] + [proof_arg_text(subst[binder]) for binder in rule.binders]
    for premise in rule.premises:
        premise_proof = proof_for_expr(
            substitute_expr(premise, subst),
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=False,
        )
        if premise_proof is None:
            return None
        parts.append(premise_proof)
    return parts


def rule_application_text(parts: list[str]) -> str:
    return parts[0] if len(parts) == 1 else f"({' '.join(parts)})"


def equality_rule_chain_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    max_depth: int = 3,
) -> str | None:
    if expr.kind != "eq":
        return None
    start = normalize_defined_expr(expr.args[0], definitions)
    target = normalize_defined_expr(expr.args[1], definitions)
    if expr_key(start) == expr_key(target):
        return "(fun Q H => H)"

    def congruence_edges(node: Expr) -> list[tuple[Expr, str]]:
        if node.kind != "app" or len(node.args) < 2:
            return []

        found: list[tuple[Expr, str]] = []
        args = list(node.args)
        for index, arg in enumerate(node.args[1:], start=1):
            arg_key = expr_key(normalize_defined_expr(arg, definitions))
            rewrites: list[tuple[Expr, str]] = []
            for fact in eq_facts:
                left = normalize_defined_expr(fact.left, definitions)
                right = normalize_defined_expr(fact.right, definitions)
                if expr_key(left) == arg_key:
                    rewrites.append((right, fact.proof))
                if expr_key(right) == arg_key:
                    rewrites.append((left, eq_symmetry_proof(fact.proof, fact.left)))
            for rule in rules:
                if rule.conclusion.kind != "eq":
                    continue
                variables = set(rule.binders)
                direct_subst: dict[str, Expr] = {}
                if match_expr(rule.conclusion.args[0], arg, variables, direct_subst):
                    parts = rule_application_parts(rule, direct_subst, known, known_canonical, rules, eq_facts, definitions)
                    if parts is not None:
                        rewrites.append((normalize_defined_expr(substitute_expr(rule.conclusion.args[1], direct_subst), definitions), rule_application_text(parts)))
                reverse_subst: dict[str, Expr] = {}
                if match_expr(rule.conclusion.args[1], arg, variables, reverse_subst):
                    parts = rule_application_parts(rule, reverse_subst, known, known_canonical, rules, eq_facts, definitions)
                    if parts is not None:
                        proof = rule_application_text(parts)
                        replacement = substitute_expr(rule.conclusion.args[0], reverse_subst)
                        rewrites.append((normalize_defined_expr(replacement, definitions), eq_symmetry_proof(proof, replacement)))
            for replacement, argument_proof in rewrites:
                next_args = args.copy()
                next_args[index] = replacement
                context = app_context_text(node.args[0], tuple(node.args[1:]), index - 1, "z")
                proof = f"(fun Q:set->prop => fun H:Q ({expr_text(node)}) => {proof_term_text(argument_proof)} (fun z:set => Q ({context})) H)"
                found.append((Expr("app", args=tuple(next_args)), proof))
        return found

    def edges(node: Expr) -> list[tuple[Expr, str]]:
        found: list[tuple[Expr, str]] = []
        for fact in eq_facts:
            if expr_key(normalize_defined_expr(fact.left, definitions)) == expr_key(node):
                found.append((normalize_defined_expr(fact.right, definitions), fact.proof))
            if expr_key(normalize_defined_expr(fact.right, definitions)) == expr_key(node):
                found.append((normalize_defined_expr(fact.left, definitions), eq_symmetry_proof(fact.proof, fact.left)))
        for rule in rules:
            if rule.conclusion.kind != "eq":
                continue
            variables = set(rule.binders)
            direct_subst: dict[str, Expr] = {}
            if match_expr(rule.conclusion.args[0], node, variables, direct_subst):
                parts = rule_application_parts(rule, direct_subst, known, known_canonical, rules, eq_facts, definitions)
                if parts is not None:
                    found.append((normalize_defined_expr(substitute_expr(rule.conclusion.args[1], direct_subst), definitions), rule_application_text(parts)))
            reverse_subst: dict[str, Expr] = {}
            if match_expr(rule.conclusion.args[1], node, variables, reverse_subst):
                parts = rule_application_parts(rule, reverse_subst, known, known_canonical, rules, eq_facts, definitions)
                if parts is not None:
                    proof = rule_application_text(parts)
                    found.append((normalize_defined_expr(substitute_expr(rule.conclusion.args[0], reverse_subst), definitions), eq_symmetry_proof(proof, substitute_expr(rule.conclusion.args[0], reverse_subst))))
        found.extend(congruence_edges(node))
        return found

    queue: list[tuple[Expr, list[str]]] = [(start, [])]
    seen = {expr_key(start)}
    while queue:
        node, proofs = queue.pop(0)
        if len(proofs) >= max_depth:
            continue
        for next_node, proof in edges(node):
            key = expr_key(next_node)
            if key in seen:
                continue
            next_proofs = proofs + [proof]
            if key == expr_key(target):
                return eq_transitivity_proof(next_proofs, expr_text(start))
            seen.add(key)
            queue.append((next_node, next_proofs))
    return None


def introduction_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if not binders and not premises:
        return None

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    args = [name for name, _ in binders]
    for index, premise in enumerate(premises):
        name = "H" + str(index)
        args.append(name)
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )

    proof = proof_for_expr(
        conclusion,
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        definitions,
        allow_rule=True,
    )
    if proof is None:
        return None
    return f"({' '.join(['fun'] + args + ['=>', proof])})"


def app_context_text(head: Expr, args: tuple[Expr, ...], hole_index: int, hole_name: str) -> str:
    parts = [expr_text(head)]
    for index, arg in enumerate(args):
        parts.append(hole_name if index == hole_index else proof_arg_text(arg))
    return " ".join(parts)


def equality_congruence_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
) -> str | None:
    if expr.kind != "eq":
        return None
    left = normalize_defined_expr(expr.args[0], definitions)
    right = normalize_defined_expr(expr.args[1], definitions)
    if left.kind != "app" or right.kind != "app" or len(left.args) != len(right.args) or len(left.args) < 2:
        return None
    if expr_key(left.args[0]) != expr_key(right.args[0]):
        return None

    different = [
        index
        for index, (left_arg, right_arg) in enumerate(zip(left.args[1:], right.args[1:]))
        if expr_key(left_arg) != expr_key(right_arg)
    ]
    if len(different) != 1:
        return None

    arg_index = different[0]
    left_arg = left.args[arg_index + 1]
    right_arg = right.args[arg_index + 1]
    argument_equality = Expr("eq", args=(left_arg, right_arg))
    argument_proof = proof_for_expr(
        argument_equality,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=False,
    )
    if argument_proof is None:
        return None

    context = app_context_text(left.args[0], left.args[1:], arg_index, "z")
    return f"(fun Q:set->prop => fun H:Q ({expr_text(left)}) => {proof_term_text(argument_proof)} (fun z:set => Q ({context})) H)"


def direct_proof_expr(expr: Expr) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    binder_names = [name for name, _ in binders]

    if len(binders) == 1 and binders[0][1] == "set->prop" and len(premises) == 2:
        predicate = binders[0][0]
        base = unary_application(premises[0])
        conclusion_app = unary_application(conclusion)
        if base is not None and conclusion_app is not None and base[0] == predicate and conclusion_app[0] == predicate:
            step_binders, step_body = collect_foralls(premises[1])
            step_premises, step_conclusion = split_arrows(step_body)
            if len(step_binders) == 1 and step_binders[0][1] == "set" and len(step_premises) == 1:
                step_var = step_binders[0][0]
                step_left = unary_application(step_premises[0])
                step_right = unary_application(step_conclusion)
                if (
                    step_left is not None
                    and step_right is not None
                    and step_left[0] == predicate
                    and step_right[0] == predicate
                    and step_left[1].kind == "var"
                    and step_left[1].value == step_var
                    and step_right[1].kind == "app"
                    and len(step_right[1].args) == 2
                    and step_right[1].args[0].kind == "var"
                    and step_right[1].args[0].value == "ordsucc"
                    and step_right[1].args[1].kind == "var"
                    and step_right[1].args[1].value == step_var
                    and successor_depth(base[1]) == 0
                ):
                    depth = successor_depth(conclusion_app[1])
                    if depth is not None:
                        proof = "H0"
                        for step in range(depth):
                            proof = f"H1 ({successor_term_text(step)}) ({proof})"
                        return f"(fun {predicate} H0 H1 => {proof})"

    if len(premises) == 1 and expr_key(premises[0]) == expr_key(conclusion):
        args = binder_names + ["H0"]
        return f"({' '.join(['fun'] + args + ['=>', 'H0'])})"

    if not premises and conclusion.kind == "eq" and expr_key(conclusion.args[0]) == expr_key(conclusion.args[1]):
        args = binder_names + ["Q", "H"]
        return f"({' '.join(['fun'] + args + ['=>', 'H'])})"

    if (
        len(premises) == 2
        and all(premise.kind == "eq" for premise in premises)
        and conclusion.kind == "eq"
        and expr_key(premises[0].args[0]) == expr_key(conclusion.args[0])
        and expr_key(premises[0].args[1]) == expr_key(premises[1].args[0])
        and expr_key(premises[1].args[1]) == expr_key(conclusion.args[1])
    ):
        args = binder_names + ["H0", "H1", "Q", "H"]
        return f"({' '.join(['fun'] + args + ['=>', 'H1', 'Q', '(H0 Q H)'])})"

    return None


def proof_for_expr(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool = True,
) -> str | None:
    key = expr_key(expr)
    proof = known.get(key) or known_canonical.get(canonical_proposition(key))
    if proof is not None:
        return proof

    direct = direct_proof_expr(expr)
    if direct is not None:
        return direct

    if allow_rule:
        introduced = introduction_proof(expr, known, known_canonical, rules, eq_facts, definitions)
        if introduced is not None:
            return introduced

    normalized = normalize_defined_expr(expr, definitions)
    if expr_key(normalized) != expr_key(expr):
        normalized_direct = direct_proof_expr(normalized)
        if normalized_direct is not None:
            return normalized_direct
        if normalized.kind == "eq" and expr_key(normalized.args[0]) == expr_key(normalized.args[1]):
            return "(fun Q H => H)"

    eq_proof = equality_chain_proof(expr, eq_facts)
    if eq_proof is not None:
        return eq_proof

    normalized_eq_proof = equality_chain_proof(normalized, eq_facts)
    if normalized_eq_proof is not None:
        return normalized_eq_proof

    if not allow_rule:
        return None

    rule_chain_proof = equality_rule_chain_proof(expr, known, known_canonical, rules, eq_facts, definitions)
    if rule_chain_proof is not None:
        return rule_chain_proof

    congruence_proof = equality_congruence_proof(expr, known, known_canonical, rules, eq_facts, definitions)
    if congruence_proof is not None:
        return congruence_proof

    for rule in reversed(rules):
        subst: dict[str, Expr] = {}
        if not match_expr(rule.conclusion, expr, set(rule.binders), subst):
            continue
        if any(binder not in subst for binder in rule.binders):
            continue
        premise_proofs: list[str] = []
        ok = True
        for premise in rule.premises:
            premise_proof = proof_for_expr(
                substitute_expr(premise, subst),
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=False,
            )
            if premise_proof is None:
                ok = False
                break
            premise_proofs.append(premise_proof)
        if not ok:
            continue
        args = [proof_arg_text(subst[binder]) for binder in rule.binders]
        parts = [rule.name] + args + premise_proofs
        return parts[0] if len(parts) == 1 else f"({' '.join(parts)})"

    return None


def proof_for_proposition(
    proposition: str,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
) -> str | None:
    proof = known.get(proposition) or known_canonical.get(canonical_proposition(proposition))
    if proof is not None:
        return proof
    expr = parse_expr(proposition)
    if expr is None:
        return None
    return proof_for_expr(expr, known, known_canonical, rules, eq_facts, definitions)


def remember_proposition(
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    name: str,
    proposition: str,
) -> None:
    known.setdefault(proposition, name)
    known_canonical.setdefault(canonical_proposition(proposition), name)
    expr = parse_expr(proposition)
    if expr is not None:
        known.setdefault(expr_key(expr), name)
        known_canonical.setdefault(canonical_proposition(expr_key(expr)), name)
    rule = make_proof_rule(name, proposition)
    if rule is not None:
        rules.append(rule)
    eq_fact = make_eq_fact(name, proposition)
    if eq_fact is not None:
        eq_facts.append(eq_fact)


def fill_repeated_claim_admits(lines: list[str]) -> list[str]:
    known: dict[str, str] = {}
    known_canonical: dict[str, str] = {}
    rules: list[ProofRule] = []
    eq_facts: list[EqFact] = []
    definitions: dict[str, DefinitionInfo] = {}
    theorem: str | None = None
    result = list(lines)
    index = 0
    while index < len(result):
        line = result[index]
        definition_match = DEFINITION_RE.match(line)
        if definition_match:
            body = parse_expr(definition_match.group("body").strip())
            if body is not None:
                definitions[definition_match.group("name")] = DefinitionInfo(
                    definition_match.group("sort").strip(),
                    definition_match.group("body").strip(),
                    "(fun Q H => H)",
                    (),
                    body,
                )
            index += 1
            continue
        axiom = proposition_after_colon(line, "Axiom ")
        if axiom is not None:
            name, proposition = axiom
            remember_proposition(known, known_canonical, rules, eq_facts, name, proposition)
            index += 1
            continue
        theorem_match = proposition_after_colon(line, "Theorem ")
        if theorem_match is not None:
            _, theorem = theorem_match
            index += 1
            continue
        claim = proposition_after_colon(line, "claim ")
        if claim is not None:
            name, proposition = claim
            proof_name = proof_for_proposition(proposition, known, known_canonical, rules, eq_facts, definitions)
            if proof_name is not None and index + 1 < len(result) and result[index + 1] == "{ admit. }":
                result[index + 1] = "{ exact " + proof_name + ". }"
            remember_proposition(known, known_canonical, rules, eq_facts, name, proposition)
            index += 2
            continue
        if line == "admit." and theorem is not None:
            proof_name = proof_for_proposition(theorem, known, known_canonical, rules, eq_facts, definitions)
            if proof_name is not None:
                result[index] = "exact " + proof_name + "."
        index += 1
    return result


def comment_text(value: object) -> str:
    text = "" if value is None else str(value)
    return text.replace("\r", " ").replace("\n", " ")


SOURCE_DEPENDENCY_RE = re.compile(r"\baby\b(?P<body>[^.]*)\.")
SOURCE_IDENTIFIER_RE = re.compile(r"[_A-Za-z][_A-Za-z0-9']*")
SOURCE_DEPENDENCY_KEYWORDS = {
    "aby",
    "admit",
    "apply",
    "assume",
    "claim",
    "exact",
    "fun",
    "let",
    "prove",
    "prop",
    "rewrite",
    "set",
}


def source_dependency_names(line_text: str | None) -> list[str]:
    if line_text is None:
        return []
    match = SOURCE_DEPENDENCY_RE.search(line_text)
    if match is None:
        return []
    names: list[str] = []
    seen: set[str] = set()
    for token in SOURCE_IDENTIFIER_RE.findall(match.group("body")):
        if token in SOURCE_DEPENDENCY_KEYWORDS or token in seen:
            continue
        seen.add(token)
        names.append(token)
    return names


def skeleton_header(obligation: Obligation) -> list[str]:
    header = [
        "// Vampire/Megalodon reconstruction skeleton.",
        f"// problem: {comment_text(obligation.problem)}",
        f"// proof: {comment_text(obligation.proof)}",
        f"// source: {comment_text(obligation.source)}:{obligation.line}:{obligation.char}",
    ]
    if obligation.theorem_name is not None:
        header.append(f"// enclosing theorem: {comment_text(obligation.theorem_name)} at line {obligation.theorem_line}")
    if obligation.source_line_text is not None:
        header.append(f"// source line: {comment_text(obligation.source_line_text)}")
    dependencies = source_dependency_names(obligation.source_line_text)
    if dependencies:
        header.append(f"// source dependencies: {', '.join(comment_text(name) for name in dependencies)}")
    return header


def check_megalodon_lines(
    megalodon: Path,
    repo: Path,
    proof: Path,
    index: int,
    lines: list[str],
    kind: str,
    allow_incomplete: bool = False,
    output_dir: Path | None = None,
    header: list[str] | None = None,
    fill_repeated_admits: bool = False,
    proof_text: str | None = None,
) -> list[str]:
    safe_kind = kind.replace(" ", "_")
    output_lines = add_function_definition_skeletons(lines, proof_text)
    output_lines = fill_source_candidate_claims(output_lines, proof_text)
    output_lines = fill_repeated_claim_admits(output_lines) if fill_repeated_admits else output_lines
    if header:
        output_lines = header + output_lines
    if output_dir is None:
        tmp_root = Path(os.environ.get("TMPDIR", "/project/tmp"))
        tmp_root.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            "w",
            encoding="utf-8",
            suffix=".mg",
            prefix=f"{proof.stem}.{safe_kind}{index}.",
            dir=tmp_root,
            delete=False,
        ) as handle:
            candidate = Path(handle.name)
            handle.write("\n".join(output_lines))
            handle.write("\n")
        delete_after = True
    else:
        output_dir.mkdir(parents=True, exist_ok=True)
        candidate = output_dir / f"{proof.stem}.{safe_kind}{index}.mg"
        candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
        delete_after = False
    try:
        cmd = [str(megalodon)]
        if allow_incomplete:
            cmd.append("-allowincompleteqed")
        cmd.append(str(candidate))
        proc = run(cmd, repo)
        if proc.returncode != 0:
            return [f"{proof}: Megalodon rejected {kind} {index}: {proc.stdout.strip()}"]
    finally:
        if delete_after:
            candidate.unlink(missing_ok=True)
    return []


def check_megalodon_source_candidate(
    megalodon: Path,
    repo: Path,
    proof: Path,
    index: int,
    lines: list[str],
    header: list[str] | None = None,
) -> list[str]:
    return check_megalodon_lines(megalodon, repo, proof, index, lines, "source candidate", header=header)


def summarize_claim_skeleton(path: Path) -> dict[str, object]:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    header: dict[str, str] = {}
    for line in lines:
        if not line.startswith("// "):
            break
        key, separator, value = line[3:].partition(":")
        if separator:
            header[key.strip().replace(" ", "_")] = value.strip()
    first_remaining: list[str] = []
    for index, line in enumerate(lines):
        if line == "{ admit. }" and index > 0:
            first_remaining.append(lines[index - 1])
        elif line == "admit." and index > 0:
            first_remaining.append(lines[index - 1])
        if len(first_remaining) >= 5:
            break
    return {
        "file": str(path),
        "problem": header.get("problem"),
        "proof": header.get("proof"),
        "source": header.get("source"),
        "enclosing_theorem": header.get("enclosing_theorem"),
        "source_line": header.get("source_line"),
        "source_dependencies": header.get("source_dependencies"),
        "claims": sum(1 for line in lines if line.startswith("claim ")),
        "claim_admits": sum(1 for line in lines if line == "{ admit. }"),
        "final_admits": sum(1 for line in lines if line == "admit."),
        "filled_claims": sum(1 for line in lines if line.startswith("{ exact ")),
        "first_remaining": first_remaining,
    }


def write_claim_skeleton_index(directory: Path) -> Path | None:
    if not directory.exists():
        return None
    paths = sorted(directory.glob("*.mg"))
    if not paths:
        return None
    index = directory / "index.jsonl"
    with index.open("w", encoding="utf-8") as handle:
        for path in paths:
            handle.write(json.dumps(summarize_claim_skeleton(path), sort_keys=True))
            handle.write("\n")
    return index


def start_vampire(repo: Path, args: argparse.Namespace, proof_dir: Path, item: tuple[int, int, Path]) -> RunningVampire:
    line, char, problem = item
    proof_path = proof_dir / f"{problem.stem}.{args.proof_mode}.out"
    cmd = vampire_command(args, problem, proof_path)
    process = subprocess.Popen(
        cmd,
        cwd=str(repo),
        text=True,
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    return RunningVampire(
        line=line,
        char=char,
        problem=problem,
        proof_path=proof_path,
        command=cmd,
        process=process,
        started_at=time.monotonic(),
    )


def terminate_vampire(process: subprocess.Popen[str]) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass


def finish_vampire(
    running: RunningVampire,
    args: argparse.Namespace,
    timed_out: bool = False,
) -> tuple[Obligation, str | None, bool]:
    if timed_out:
        terminate_vampire(running.process)
    try:
        out, _ = running.process.communicate(timeout=2)
    except subprocess.TimeoutExpired:
        terminate_vampire(running.process)
        out, _ = running.process.communicate()
    running.proof_path.write_text(out, encoding="utf-8")
    status_match = PROVED_RE.search(out)
    status = status_match.group(1) if status_match else None
    obligation = Obligation(
        line=running.line,
        char=running.char,
        problem=str(running.problem),
        proof=str(running.proof_path),
        problem_sha256=sha256(running.problem),
        proof_sha256=sha256(running.proof_path),
        status=status,
        command=running.command,
        **source_context(getattr(args, "resolved_source", None), running.line),
    )
    proof_payload_ok = proof_has_reconstruction_payload(out, args.proof_mode)
    failure = None
    if timed_out:
        failure = f"{running.problem.name}: Vampire subprocess timed out"
    elif proof_has_fatal_output(out):
        failure = f"{running.problem.name}: Vampire output contained a fatal error marker"
    elif args.proof_mode == "leancheck":
        if not proof_payload_ok:
            failure = f"{running.problem.name}: Vampire LeanChecker output had no complete Lean proof payload"
    elif args.proof_mode == "megalodon":
        if not proof_payload_ok:
            failure = f"{running.problem.name}: Vampire Megalodon output had no complete reconstruction payload"
    elif not status:
        failure = f"{running.problem.name}: Vampire did not report a proved SZS status"
    elif not proof_payload_ok:
        failure = f"{running.problem.name}: Vampire output had status {status} but no proof payload"
    return obligation, failure, proof_payload_ok


def run_vampire_suite(
    repo: Path,
    args: argparse.Namespace,
    selected: Iterable[tuple[int, int, Path]],
    proof_dir: Path,
) -> list[Obligation]:
    proof_dir.mkdir(parents=True, exist_ok=True)
    selected_items = list(selected)
    jobs = max(1, args.jobs)
    obligations: list[Obligation] = []
    failures: list[str] = []
    skipped = 0
    running: list[RunningVampire] = []
    next_index = 0
    completed = 0

    def should_schedule() -> bool:
        if next_index >= len(selected_items):
            return False
        if args.collect_successes and len(obligations) >= args.limit:
            return False
        return True

    try:
        while running or should_schedule():
            while len(running) < jobs and should_schedule():
                running.append(start_vampire(repo, args, proof_dir, selected_items[next_index]))
                next_index += 1

            now = time.monotonic()
            made_progress = False
            for item in list(running):
                timed_out = item.process.poll() is None and now - item.started_at > args.timeout
                if item.process.poll() is None and not timed_out:
                    continue
                running.remove(item)
                obligation, failure, proof_payload_ok = finish_vampire(item, args, timed_out=timed_out)
                completed += 1
                made_progress = True
                if args.collect_successes:
                    skeleton_ok = (
                        not args.require_claim_skeletons
                        or "megalodon_claim_skeleton_start." in item.proof_path.read_text(encoding="utf-8", errors="replace")
                    )
                    if failure is None and proof_payload_ok and skeleton_ok:
                        obligations.append(obligation)
                    else:
                        skipped += 1
                else:
                    obligations.append(obligation)
                    if failure is not None:
                        failures.append(failure)

                if args.progress and (completed % args.progress == 0 or len(obligations) >= args.limit):
                    print(
                        f"completed {completed}; accepted {len(obligations)}; "
                        f"running {len(running)}; queued {next_index}/{len(selected_items)}",
                        flush=True,
                    )

                if args.collect_successes and len(obligations) >= args.limit:
                    for rest in running:
                        terminate_vampire(rest.process)
                    running.clear()
                    break

            if running and not made_progress:
                time.sleep(0.05)
    finally:
        for item in running:
            terminate_vampire(item.process)

    if failures:
        for failure in failures:
            print(failure, file=sys.stderr)
        raise SystemExit(f"{len(failures)} Vampire proof checks failed")
    if args.collect_successes and len(obligations) < args.limit:
        raise SystemExit(
            f"Only collected {len(obligations)} successful Vampire proofs "
            f"after skipping {skipped} failed candidates"
        )
    if args.collect_successes:
        print(f"skipped {skipped} non-proving candidates while collecting successes")
    obligations.sort(key=lambda obligation: (obligation.line, obligation.char, obligation.problem))
    return obligations


def check_obligation(
    obligation: Obligation,
    repo: Path,
    megalodon: Path,
    source: Path | None = None,
    check_megalodon_sources: bool = False,
    require_megalodon_sources: bool = False,
    check_claim_skeletons: bool = False,
    require_claim_skeletons: bool = False,
    claim_skeleton_dir: Path | None = None,
) -> tuple[list[str], int, int]:
    failures = []
    checked_sources = 0
    checked_skeletons = 0
    problem = Path(obligation.problem)
    proof = Path(obligation.proof)
    if not problem.exists():
        return [f"{problem}: missing problem file"], checked_sources, checked_skeletons
    if sha256(problem) != obligation.problem_sha256:
        failures.append(f"{problem}: problem hash changed")
    if not proof.exists():
        failures.append(f"{proof}: missing proof file")
        return failures, checked_sources, checked_skeletons
    if obligation.proof_sha256 and sha256(proof) != obligation.proof_sha256:
        failures.append(f"{proof}: proof hash changed")
    text = proof.read_text(encoding="utf-8", errors="replace")
    proof_mode = proof_mode_from_path(proof)
    if proof_has_fatal_output(text):
        failures.append(f"{proof}: fatal error marker")
    elif proof_mode == "leancheck":
        if not proof_has_reconstruction_payload(text, proof_mode):
            failures.append(f"{proof}: no complete Lean proof payload")
    elif proof_mode == "megalodon":
        if not proof_has_reconstruction_payload(text, proof_mode):
            failures.append(f"{proof}: no complete Megalodon reconstruction payload")
    elif not PROVED_RE.search(text):
        failures.append(f"{proof}: no proved SZS status")
    elif not proof_has_reconstruction_payload(text, proof_mode):
        failures.append(f"{proof}: no proof payload")
    if proof_mode == "megalodon" and obligation.source is None and source is not None:
        for field, value in source_context(source, obligation.line).items():
            setattr(obligation, field, value)
    if proof_mode == "megalodon" and (check_megalodon_sources or require_megalodon_sources):
        header = skeleton_header(obligation)
        candidates = extract_megalodon_source_candidates(text)
        if require_megalodon_sources and not candidates:
            failures.append(f"{proof}: no Megalodon source candidate")
        for index, lines in enumerate(candidates):
            checked_sources += 1
            failures.extend(check_megalodon_source_candidate(megalodon, repo, proof, index, lines, header=header))
    if proof_mode == "megalodon" and (check_claim_skeletons or require_claim_skeletons or claim_skeleton_dir is not None):
        header = skeleton_header(obligation)
        skeletons = extract_megalodon_claim_skeletons(text)
        if require_claim_skeletons and not skeletons:
            failures.append(f"{proof}: no Megalodon claim skeleton")
        for index, lines in enumerate(skeletons):
            checked_skeletons += 1
            if check_claim_skeletons:
                failures.extend(
                    check_megalodon_lines(
                        megalodon,
                        repo,
                        proof,
                        index,
                        lines,
                        "claim skeleton",
                        allow_incomplete=True,
                        output_dir=claim_skeleton_dir,
                        header=header,
                        fill_repeated_admits=True,
                        proof_text=text,
                    )
                )
            elif claim_skeleton_dir is not None:
                check_megalodon_lines(
                    megalodon,
                    repo,
                    proof,
                    index,
                    lines,
                    "claim skeleton",
                    allow_incomplete=True,
                    output_dir=claim_skeleton_dir,
                    header=header,
                    fill_repeated_admits=True,
                    proof_text=text,
                )
    return failures, checked_sources, checked_skeletons


def check_existing(
    manifest: Path,
    repo: Path,
    megalodon: Path,
    jobs: int = 1,
    source: Path | None = None,
    check_megalodon_sources: bool = False,
    require_megalodon_sources: bool = False,
    check_claim_skeletons: bool = False,
    require_claim_skeletons: bool = False,
    claim_skeleton_dir: Path | None = None,
) -> tuple[list[Obligation], int, int]:
    obligations = []
    for row in manifest.read_text(encoding="utf-8").splitlines():
        if row.strip():
            obligations.append(Obligation(**json.loads(row)))

    failures = []
    checked_sources = 0
    checked_skeletons = 0
    workers = max(1, jobs)
    if workers == 1:
        for obligation in obligations:
            item_failures, item_sources, item_skeletons = check_obligation(
                obligation,
                repo,
                megalodon,
                source,
                check_megalodon_sources=check_megalodon_sources,
                require_megalodon_sources=require_megalodon_sources,
                check_claim_skeletons=check_claim_skeletons,
                require_claim_skeletons=require_claim_skeletons,
                claim_skeleton_dir=claim_skeleton_dir,
            )
            failures.extend(item_failures)
            checked_sources += item_sources
            checked_skeletons += item_skeletons
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
            futures = [
                executor.submit(
                    check_obligation,
                    obligation,
                    repo,
                    megalodon,
                    source,
                    check_megalodon_sources,
                    require_megalodon_sources,
                    check_claim_skeletons,
                    require_claim_skeletons,
                    claim_skeleton_dir,
                )
                for obligation in obligations
            ]
            for future in concurrent.futures.as_completed(futures):
                item_failures, item_sources, item_skeletons = future.result()
                failures.extend(item_failures)
                checked_sources += item_sources
                checked_skeletons += item_skeletons

    if failures:
        for failure in failures:
            print(failure, file=sys.stderr)
        raise SystemExit(f"{len(failures)} manifest checks failed")
    return obligations, checked_sources, checked_skeletons


def write_manifest(path: Path, obligations: Iterable[Obligation]) -> None:
    with path.open("w", encoding="utf-8") as f:
        for obligation in obligations:
            f.write(json.dumps(asdict(obligation), sort_keys=True))
            f.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--megalodon", type=Path, default=Path("bin/megalodon"))
    parser.add_argument("--source", type=Path, default=Path("examples/hammer/100thms_12_h.mg"))
    parser.add_argument("--results", type=Path, default=Path("examples/hammer/ATPresults2025"))
    parser.add_argument("--work-dir", type=Path, default=Path("tests/vampire_reconstruction/work"))
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--timeout", type=int, default=10)
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("MEGALODON_VAMPIRE_JOBS", "1")))
    parser.add_argument("--progress", type=int, default=10)
    parser.add_argument("--schedule", default="casc")
    parser.add_argument("--proof-mode", choices=["tptp", "leancheck", "megalodon"], default="tptp")
    parser.add_argument("--vampire", type=Path, default=Path(os.environ.get("VAMPIRE", "vampire")))
    parser.add_argument("--vampire-arg", action="append", nargs="+")
    parser.add_argument("--collect-successes", action="store_true")
    parser.add_argument("--generate-only", action="store_true")
    parser.add_argument("--check-existing", type=Path)
    parser.add_argument("--from-manifest", type=Path)
    parser.add_argument("--check-megalodon-sources", action="store_true")
    parser.add_argument("--require-megalodon-sources", action="store_true")
    parser.add_argument("--check-claim-skeletons", action="store_true")
    parser.add_argument("--require-claim-skeletons", action="store_true")
    parser.add_argument("--claim-skeleton-dir", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    megalodon = (repo / args.megalodon).resolve() if not args.megalodon.is_absolute() else args.megalodon
    source = (repo / args.source).resolve() if not args.source.is_absolute() else args.source
    args.resolved_source = source
    if args.timeout > 10:
        args.timeout = 10
    results = (repo / args.results).resolve() if not args.results.is_absolute() else args.results
    work_dir = (repo / args.work_dir).resolve() if not args.work_dir.is_absolute() else args.work_dir
    claim_skeleton_dir = None
    if args.claim_skeleton_dir:
        claim_skeleton_dir = (
            (repo / args.claim_skeleton_dir).resolve()
            if not args.claim_skeleton_dir.is_absolute()
            else args.claim_skeleton_dir
        )

    if args.check_existing:
        obligations, checked_sources, checked_skeletons = check_existing(
            args.check_existing,
            repo,
            megalodon,
            args.jobs,
            source,
            check_megalodon_sources=args.check_megalodon_sources,
            require_megalodon_sources=args.require_megalodon_sources,
            check_claim_skeletons=args.check_claim_skeletons,
            require_claim_skeletons=args.require_claim_skeletons,
            claim_skeleton_dir=claim_skeleton_dir,
        )
        print(f"checked {len(obligations)} recorded Vampire proof outputs")
        if args.check_megalodon_sources or args.require_megalodon_sources:
            print(f"checked {checked_sources} Megalodon source candidates")
        if args.check_claim_skeletons or args.require_claim_skeletons or args.claim_skeleton_dir:
            print(f"checked {checked_skeletons} Megalodon claim skeletons")
            if claim_skeleton_dir is not None:
                print(f"claim skeleton dir: {claim_skeleton_dir}")
                index = write_claim_skeleton_index(claim_skeleton_dir)
                if index is not None:
                    print(f"claim skeleton index: {index}")
        return 0

    if not megalodon.exists():
        raise SystemExit(f"Megalodon executable not found: {megalodon}")

    work_dir.mkdir(parents=True, exist_ok=True)
    prefix = work_dir / "hammer"
    if args.from_manifest:
        selected = obligations_from_manifest(args.from_manifest)
        if len(selected) < args.limit:
            raise SystemExit(f"Need {args.limit} known-solvable obligations, found {len(selected)} in {args.from_manifest}")
        selected_for_run = selected if args.collect_successes else selected[: args.limit]
    else:
        generate_problems(repo, megalodon, source, prefix)
        selected = select_obligations(prefix, parse_vampire_lines(results), args.limit)
        selected_for_run = selected if args.collect_successes else selected[: args.limit]
    selection_path = work_dir / "selected_th0.txt"
    selection_path.write_text("\n".join(str(path) for _, _, path in selected_for_run) + "\n", encoding="utf-8")

    if args.generate_only:
        if args.from_manifest:
            print(f"selected {len(selected_for_run)} known-solvable obligations from {args.from_manifest}")
        else:
            print(f"generated {len(generated_th0(prefix))} TH0 obligations")
        print(f"selected {len(selected_for_run)} HO-Vampire obligations in {selection_path}")
        return 0

    if shutil.which(str(args.vampire)) is None and not args.vampire.exists():
        raise SystemExit(f"Vampire executable not found: {args.vampire}")

    obligations = run_vampire_suite(repo, args, selected_for_run, work_dir / "proofs")
    manifest = work_dir / "manifest.jsonl"
    write_manifest(manifest, obligations)
    checked_sources = 0
    checked_skeletons = 0
    if (
        args.check_megalodon_sources
        or args.require_megalodon_sources
        or args.check_claim_skeletons
        or args.require_claim_skeletons
        or args.claim_skeleton_dir
    ):
        _, checked_sources, checked_skeletons = check_existing(
            manifest,
            repo,
            megalodon,
            args.jobs,
            source,
            check_megalodon_sources=args.check_megalodon_sources,
            require_megalodon_sources=args.require_megalodon_sources,
            check_claim_skeletons=args.check_claim_skeletons,
            require_claim_skeletons=args.require_claim_skeletons,
            claim_skeleton_dir=claim_skeleton_dir,
        )
    print(f"checked {len(obligations)} Vampire proofs")
    if args.check_megalodon_sources or args.require_megalodon_sources:
        print(f"checked {checked_sources} Megalodon source candidates")
    if args.check_claim_skeletons or args.require_claim_skeletons or args.claim_skeleton_dir:
        print(f"checked {checked_skeletons} Megalodon claim skeletons")
        if claim_skeleton_dir is not None:
            print(f"claim skeleton dir: {claim_skeleton_dir}")
            index = write_claim_skeleton_index(claim_skeleton_dir)
            if index is not None:
                print(f"claim skeleton index: {index}")
    print(f"manifest: {manifest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
