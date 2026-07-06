#!/usr/bin/env python3
"""Generate and check Megalodon TH0 obligations with Vampire proofs.

This is the reproducible test driver for the Vampire-to-Megalodon proof
reconstruction work.  It intentionally uses Megalodon's own TH0 generator as
the source of truth.  The default development path exports ordinary admitted
proof states, then runs Vampire and Megalodon reconstruction checks in
parallel.  Generated Megalodon reconstruction scripts must not use `aby`.
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
import threading
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable


RESULT_RE = re.compile(r"^.*\.(?P<line>[0-9]+)\.(?P<char>[0-9]+)\.\*\.p:")
PROBLEM_RE = re.compile(r"^(?P<prefix>.*)\.(?P<line>[0-9]+)(?:\.(?P<char>[0-9]+))?\.th0\.p$")
PROVED_RE = re.compile(r"SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)\b")
FATAL_OUTPUT_RE = re.compile(r"Aborted by signal|ASSERTION|User error|missing .* implementation", re.IGNORECASE)
MEGALODON_SOURCE_LINE_RE = re.compile(r'^megalodon_source_line\("(?P<line>(?:\\.|[^"\\])*)"\)\.$')
MEGALODON_STEP_RE = re.compile(r'^megalodon_step\((?P<id>[0-9]+),"(?P<rule>(?:\\.|[^"\\])*)"')
MEGALODON_STEP_FORMULA_RE = re.compile(
    r'^megalodon_step\((?P<id>[0-9]+),"(?P<rule>(?:\\.|[^"\\])*)","[^"]*",\[[^]]*\],(?:true|false),[0-9]+,"(?P<formula>(?:\\.|[^"\\])*)"\)\.$'
)
MEGALODON_FINAL_STEP_RE = re.compile(r"^megalodon_final_step\((?P<id>[0-9]+)\)\.$")
FRESH_SET_RE = re.compile(r"^sF[0-9]+$")
VAMPIRE_DEPENDENCY_RE = re.compile(r"^(s[FK]|db)[0-9]+$")
INFERRED_DEPENDENCY_RE = re.compile(r"^[_A-Za-z][_A-Za-z0-9']*$")
DEFINITION_RE = re.compile(r"^Definition (?P<name>[_A-Za-z][_A-Za-z0-9']*) : (?P<sort>[^:]+?) := (?P<body>.*)\.$")
THF_TYPE_RE = re.compile(r"^thf\([^,]+,\s*type,\s*\((?P<name>[^:\s]+)\s*:\s*(?P<sort>.*?)\)\)\.", re.DOTALL)
PROOF_SEARCH_STATE = threading.local()
PROOF_SEARCH_SECONDS = float(os.environ.get("MEGALODON_PROOF_SEARCH_SECONDS", "45"))
PROOF_SEARCH_CLOCK = getattr(time, "thread_time", time.monotonic)


def proof_search_now() -> float:
    return PROOF_SEARCH_CLOCK()


def proof_search_timed_out() -> bool:
    deadline = getattr(PROOF_SEARCH_STATE, "deadline", None)
    return deadline is not None and proof_search_now() > deadline


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
class TptpSourceInfo:
    name: str
    decoded_name: str
    role: str
    hash: str | None = None


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
    steps: tuple["RuleStep", ...] = ()
    application_conclusion: Expr | None = None


@dataclass(frozen=True)
class EqFact:
    left: Expr
    right: Expr
    proof: str


@dataclass(frozen=True)
class RuleStep:
    kind: str
    name: str | None = None
    expr: Expr | None = None


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
    for path in parent.glob(f"{stem}.*.th0.p"):
        m = PROBLEM_RE.match(str(path))
        if not m:
            continue
        found.append((int(m.group("line")), int(m.group("char") or "0"), path))
    found.sort()
    return found


def generate_problems(repo: Path, megalodon: Path, source: Path, prefix: Path, export_mode: str) -> None:
    for old in prefix.parent.glob(f"{prefix.name}.*.p"):
        old.unlink()
    if export_mode == "aby":
        export_args = ["-createabyprobs", prefix.name]
    elif export_mode == "admit":
        export_args = ["-th0", prefix.name]
    else:
        raise SystemExit(f"unsupported export mode: {export_mode}")
    cmd = [
        str(megalodon),
        "-allowincompleteqed",
        *export_args,
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


def source_candidate_exact_proof(line: str) -> str | None:
    for pattern in (r"\{ exact (?P<proof>.+)\. \}", r"exact (?P<proof>.+)\."):
        match = re.fullmatch(pattern, line)
        if match is not None:
            return match.group("proof")
    return None


def source_candidate_rewrite_chain_proof(
    proof_lines: list[str],
    target_proposition: str,
) -> str | None:
    current = parse_expr(target_proposition)
    if current is None:
        return None
    steps: list[tuple[Expr, Expr, str, Expr]] = []
    index = 0
    while index + 2 < len(proof_lines):
        local_claim = proposition_after_colon(proof_lines[index], "claim ")
        equality_proof = source_candidate_exact_proof(proof_lines[index + 1])
        rewrite = re.fullmatch(r"rewrite(?P<reverse> <-)? (?P<name>[_A-Za-z][_A-Za-z0-9']*)\.", proof_lines[index + 2])
        if local_claim is None or equality_proof is None or rewrite is None:
            break
        if rewrite.group("name") != local_claim[0]:
            return None
        equality = parse_expr(local_claim[1])
        if equality is None or equality.kind != "eq":
            return None
        before = current
        if rewrite.group("reverse"):
            old, new = equality.args[1], equality.args[0]
        else:
            old, new = equality.args[0], equality.args[1]
        current, changed = replace_expr(current, old, new)
        if not changed:
            return None
        steps.append((before, old, equality_proof, equality.args[0]))
        index += 3

    if not steps or index != len(proof_lines) - 1:
        return None
    proof = source_candidate_exact_proof(proof_lines[index])
    if proof is None:
        return None
    for before, old, equality_proof, equality_left in reversed(steps):
        hole_name = fresh_identifier("zz", expr_text(before), proof)
        context, changed = replace_expr(before, old, Expr("var", value=hole_name))
        if not changed:
            return None
        transport_proof = (
            equality_proof
            if expr_key(old) != expr_key(equality_left)
            else eq_symmetry_proof(equality_proof, equality_left)
        )
        proof = f"{proof_head(transport_proof)} (fun {hole_name}:set => {expr_text(context)}) {proof_argument_text(proof)}"
    return proof


def extract_megalodon_claim_skeletons(text: str) -> list[list[str]]:
    marked = extract_marked_megalodon_blocks(
        text,
        "megalodon_claim_skeleton_start.",
        "megalodon_claim_skeleton_end.",
    )
    return marked or synthesize_megalodon_claim_skeletons(text)


def vampire_step_contexts(proof_text: str | None) -> dict[str, str]:
    if proof_text is None:
        return {}
    contexts: dict[str, str] = {}
    role_re = re.compile(r"\b(?:tff|cnf)\([^,]+,\s*(?P<role>[^,\s)]+)")
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_FORMULA_RE.match(line.strip())
        if match is None:
            continue
        step = "S" + match.group("id")
        rule = json.loads(f'"{match.group("rule")}"')
        formula = json.loads(f'"{match.group("formula")}"')
        role_match = role_re.search(formula)
        role = role_match.group("role") if role_match else "unknown_role"
        contexts[step] = f"{rule}, {role}"
    return contexts


def annotate_remaining_admits(lines: list[str], proof_text: str | None) -> list[str]:
    contexts = vampire_step_contexts(proof_text)
    theorem = None
    for line in lines:
        theorem_match = proposition_after_colon(line, "Theorem ")
        if theorem_match is not None:
            theorem = theorem_match[1]
            break
    result: list[str] = []
    for index, line in enumerate(lines):
        claim = proposition_after_colon(line, "claim ")
        if claim is not None and index + 1 < len(lines) and lines[index + 1] == "{ admit. }":
            already_annotated = any(
                cursor >= 0
                and lines[cursor].startswith("// ")
                and (
                    "conjecture anchor" in lines[cursor]
                    or "refutation boundary" in lines[cursor]
                    or lines[cursor].startswith("// vampire step ")
                )
                for cursor in range(index - 1, max(-1, index - 8), -1)
            )
            if already_annotated:
                result.append(line)
                continue
            context = contexts.get(claim[0])
            if context is not None:
                result.append(f"// vampire step {claim[0]}: {comment_text(context)}")
                if "negated_conjecture" in context and claim[1].endswith("-> vampire_false"):
                    result.append(
                        "// refutation boundary: Vampire proves this negated-conjecture edge; "
                        "eliminating the admit needs a native theorem/classical bridge."
                    )
                elif "negated_conjecture" in context:
                    result.append(
                        "// negated-conjecture fragment: this belongs to Vampire's refutation "
                        "assumption, not to the forward source proof."
                    )
                elif claim[1].endswith("-> vampire_false") and "conjecture" in context:
                    result.append(
                        "// refutation boundary: Vampire proves this conjecture edge under "
                        "the refutation view; eliminating the admit needs a native theorem/"
                        "classical bridge."
                    )
                elif "conjecture" in context:
                    result.append(
                        "// conjecture anchor: this is the original Megalodon obligation used "
                        "as the theorem proof target."
                    )
            elif theorem is not None and canonical_proposition(claim[1]) == canonical_proposition(theorem):
                result.append(
                    "// conjecture anchor: this is the original Megalodon obligation used "
                    "as the theorem proof target."
                )
        result.append(line)
    return result


def prune_unused_rectify_axiom_admits(lines: list[str], proof_text: str | None) -> list[str]:
    contexts = vampire_step_contexts(proof_text)
    if not contexts:
        return list(lines)
    result: list[str] = []
    index = 0
    while index < len(lines):
        claim = proposition_after_colon(lines[index], "claim ")
        if (
            claim is not None
            and index + 1 < len(lines)
            and lines[index + 1] == "{ admit. }"
            and contexts.get(claim[0]) == "rectify, axiom"
        ):
            later_text = "\n".join(lines[index + 2:])
            if not re.search(rf"\b{re.escape(claim[0])}\b", later_text):
                index += 2
                continue
        result.append(lines[index])
        index += 1
    return result


def proof_block_after_claim(lines: list[str], claim_index: int) -> tuple[int, str] | None:
    if claim_index + 1 >= len(lines):
        return None
    next_line = lines[claim_index + 1]
    if next_line.startswith("{ ") and next_line.endswith(" }"):
        return claim_index + 1, next_line
    if next_line != "{":
        return None
    block: list[str] = []
    depth = 0
    for index in range(claim_index + 1, len(lines)):
        line = lines[index]
        if line == "{":
            depth += 1
        elif line == "}":
            depth -= 1
            if depth == 0:
                block.append(line)
                return index, "\n".join(block)
        block.append(line)
    return None


def top_level_claim_blocks(lines: list[str]) -> dict[str, tuple[int, int, str]]:
    claims: dict[str, tuple[int, int, str]] = {}
    index = 0
    block_depth = 0
    while index < len(lines):
        line = lines[index]
        if block_depth > 0:
            if line == "{":
                block_depth += 1
            elif line == "}":
                block_depth -= 1
            index += 1
            continue
        claim = proposition_after_colon(line, "claim ")
        if claim is None:
            index += 1
            continue
        block = proof_block_after_claim(lines, index)
        if block is None:
            index += 1
            continue
        end_index, proof_text = block
        claims[claim[0]] = (index, end_index, proof_text)
        index = end_index + 1
    return claims


def prune_unreachable_claims(lines: list[str]) -> list[str]:
    claims = top_level_claim_blocks(lines)
    if not claims:
        return list(lines)

    claim_body_indices = {
        body_index
        for start, end, _ in claims.values()
        for body_index in range(start, end + 1)
    }
    final_text = "\n".join(
        line
        for line_index, line in enumerate(lines)
        if line_index not in claim_body_indices
        and (line.startswith("exact ") or line.startswith("apply "))
    )
    needed = {
        name
        for name in claims
        if re.search(rf"\b{re.escape(name)}\b", final_text)
    }
    if not needed and not final_text.strip():
        return list(lines)

    pending = list(needed)
    while pending:
        name = pending.pop()
        claim = claims.get(name)
        if claim is None:
            continue
        proof_text = claim[2]
        for dependency in claims:
            if dependency in needed:
                continue
            if re.search(rf"\b{re.escape(dependency)}\b", proof_text):
                needed.add(dependency)
                pending.append(dependency)

    result: list[str] = []
    index = 0
    while index < len(lines):
        claim = proposition_after_colon(lines[index], "claim ")
        if claim is None or claim[0] in needed or claim[0] not in claims:
            result.append(lines[index])
            index += 1
            continue

        _, end, _ = claims[claim[0]]
        while result and result[-1].startswith("// "):
            result.pop()
        index = end + 1
    return result


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


def strip_balanced_parens(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        balanced = True
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        text = text[1:-1].strip()
    return text


def split_sort_arrows(sort: str) -> list[str]:
    text = strip_balanced_parens(sort)
    pieces: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                return [sort.strip()]
        elif char == "-" and index + 1 < len(text) and text[index + 1] == ">" and depth == 0:
            pieces.append(strip_balanced_parens(text[start:index].strip()))
            start = index + 2
            index += 1
        index += 1
    if depth != 0:
        return [sort.strip()]
    pieces.append(strip_balanced_parens(text[start:].strip()))
    return [piece for piece in pieces if piece]


def join_sort_arrows(pieces: Iterable[str]) -> str:
    rendered: list[str] = []
    for piece in pieces:
        stripped = strip_balanced_parens(piece)
        rendered.append(f"({stripped})" if len(split_sort_arrows(stripped)) > 1 else stripped)
    return "->".join(rendered)


def split_tptp_application(text: str) -> list[str] | None:
    text = strip_balanced_parens(text)
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                return None
        elif char == "@" and depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
        index += 1
    if depth != 0:
        return None
    parts.append(text[start:].strip())
    return [part for part in parts if part]


def decode_tptp_identifier(name: str) -> str:
    name = name.strip()
    if name.startswith("c_"):
        name = name[2:]
    return re.sub(r"_([0-9A-Fa-f]{2})", lambda match: chr(int(match.group(1), 16)), name)


def split_top_level_commas(text: str) -> list[str] | None:
    parts: list[str] = []
    start = 0
    depth = 0
    bracket_depth = 0
    for index, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                return None
        elif char == "[":
            bracket_depth += 1
        elif char == "]":
            bracket_depth -= 1
            if bracket_depth < 0:
                return None
        elif char == "," and depth == 0 and bracket_depth == 0:
            parts.append(text[start:index].strip())
            start = index + 1
    if depth != 0 or bracket_depth != 0:
        return None
    parts.append(text[start:].strip())
    return parts


def tptp_decl_parts(text: str) -> tuple[str, str, str, str | None] | None:
    stripped = text.strip()
    hash_match = re.search(r"%\s*(?P<hash>[0-9a-fA-F]{64})\s*$", stripped)
    source_hash = hash_match.group("hash").lower() if hash_match else None
    if hash_match:
        stripped = stripped[: hash_match.start()].rstrip()
    match = re.match(r"^(?:thf|tff|cnf)\((?P<body>.*)\)\.\s*$", stripped, re.DOTALL)
    if match is None:
        return None
    parts = split_top_level_commas(match.group("body"))
    if parts is None or len(parts) < 3:
        return None
    return parts[0].strip(), parts[1].strip(), ",".join(parts[2:]).strip(), source_hash


def normalize_tptp_formula_body(text: str) -> str:
    compact = re.sub(r"\s+", "", strip_balanced_parens(text))
    compact = re.sub(r":[^,\]]+(?=[,\]])", "", compact)
    compact = compact.replace("(", "").replace(")", "")
    return compact


def tptp_sort_to_megalodon(sort: str) -> str:
    text = sort.strip().replace("$i", "set").replace("$o", "prop").replace(">", "->")
    text = re.sub(r"\s+", "", text)
    return strip_balanced_parens(text)


def parse_tptp_lambda(text: str) -> tuple[list[tuple[str, str]], str] | None:
    text = strip_balanced_parens(text)
    match = re.match(r"^\^\s*\[", text)
    if match is None:
        return None
    depth = 0
    end = None
    bracket_start = text.find("[", match.start())
    for index, char in enumerate(text[bracket_start:], start=bracket_start):
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                end = index
                break
    if end is None:
        return None
    rest = text[end + 1 :].strip()
    if not rest.startswith(":"):
        return None
    variable_parts = split_top_level_commas(text[bracket_start + 1 : end])
    if variable_parts is None:
        return None
    variables: list[tuple[str, str]] = []
    for part in variable_parts:
        names_text, separator, sort_text = part.partition(":")
        sort = tptp_sort_to_megalodon(sort_text) if separator else "set"
        for name in [piece.strip() for piece in names_text.split(",") if piece.strip()]:
            decoded = decode_tptp_identifier(name)
            if not re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", decoded):
                return None
            variables.append((decoded, sort))
    return variables, rest[1:].strip()


def tptp_term_to_expr(text: str) -> Expr | None:
    text = strip_balanced_parens(text)
    lambda_expr = parse_tptp_lambda(text)
    if lambda_expr is not None:
        variables, body_text = lambda_expr
        body = tptp_term_to_expr(body_text)
        if body is None:
            return None
        for name, sort in reversed(variables):
            body = Expr("lambda", value=name, sort=sort, args=(body,))
        return body
    parts = split_tptp_application(text)
    if parts is None:
        return None
    if len(parts) == 1:
        name = decode_tptp_identifier(parts[0])
        if not re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", name):
            return None
        return Expr("var", value=name)
    args = [tptp_term_to_expr(part) for part in parts]
    if any(arg is None for arg in args):
        return None
    head = args[0]
    assert head is not None
    return append_application_args(head, [arg for arg in args[1:] if arg is not None])


def sort_argument_sorts(sort: str) -> list[str]:
    pieces = split_sort_arrows(sort)
    return pieces[:-1] if len(pieces) > 1 and pieces[-1] == "set" else []


def append_application_args(expr: Expr, args: list[Expr]) -> Expr:
    if not args:
        return expr
    if expr.kind == "app":
        return Expr("app", args=expr.args + tuple(args))
    return Expr("app", args=(expr,) + tuple(args))


def split_top_level_equality(text: str) -> tuple[str, str] | None:
    text = strip_balanced_parens(text)
    depth = 0
    for index, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                return None
        elif char == "=" and depth == 0:
            if index > 0 and text[index - 1] in "!<>":
                continue
            if index + 1 < len(text) and text[index + 1] == ">":
                continue
            return text[:index].strip(), text[index + 1 :].strip()
    return None


def split_top_level_operator(text: str, operator: str) -> tuple[str, str] | None:
    text = strip_balanced_parens(text)
    depth = 0
    bracket_depth = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                return None
        elif char == "[":
            bracket_depth += 1
        elif char == "]":
            bracket_depth -= 1
            if bracket_depth < 0:
                return None
        elif depth == 0 and bracket_depth == 0 and text.startswith(operator, index):
            return text[:index].strip(), text[index + len(operator) :].strip()
        index += 1
    return None


def parse_tptp_quantifier(text: str) -> tuple[str, list[tuple[str, str]], str] | None:
    text = strip_balanced_parens(text)
    match = re.match(r"^(?P<quantifier>[!?])\s*\[", text)
    if match is None:
        return None
    quantifier = match.group("quantifier")
    depth = 0
    end = None
    bracket_start = text.find("[", match.start())
    for index, char in enumerate(text[bracket_start:], start=bracket_start):
        if char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                end = index
                break
    if end is None:
        return None
    rest = text[end + 1 :].strip()
    if not rest.startswith(":"):
        return None
    variable_parts = split_top_level_commas(text[bracket_start + 1 : end])
    if variable_parts is None:
        return None
    variables: list[tuple[str, str]] = []
    for part in variable_parts:
        names_text, separator, sort_text = part.partition(":")
        sort = tptp_sort_to_megalodon(sort_text) if separator else "set"
        for name in [piece.strip() for piece in names_text.split(",") if piece.strip()]:
            decoded = decode_tptp_identifier(name)
            if not re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", decoded):
                return None
            variables.append((decoded, sort))
    return quantifier, variables, rest[1:].strip()


def tptp_formula_to_megalodon_proposition(text: str, variable_sorts: dict[str, str] | None = None) -> str | None:
    if variable_sorts is None:
        variable_sorts = {}
    text = strip_balanced_parens(text)
    quantified = parse_tptp_quantifier(text)
    if quantified is not None:
        quantifier, variables, body_text = quantified
        inner_sorts = dict(variable_sorts)
        inner_sorts.update(variables)
        body = tptp_formula_to_megalodon_proposition(body_text, inner_sorts)
        if body is None:
            return None
        for name, sort in reversed(variables):
            if quantifier == "!":
                body = f"forall {name}:{sort}, {body}"
            elif sort == "set":
                body = f"vampire_exists_set (fun {name}:set => {body})"
            else:
                return None
        return body

    if text.startswith("~"):
        body = tptp_formula_to_megalodon_proposition(text[1:].strip(), variable_sorts)
        return f"{proposition_argument_text(body)} -> vampire_false" if body is not None else None

    equivalence = split_top_level_operator(text, "<=>")
    if equivalence is not None:
        left = tptp_formula_to_megalodon_proposition(equivalence[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(equivalence[1], variable_sorts)
        if left is None or right is None:
            return None
        return f"vampire_and ({left} -> {right}) ({right} -> {left})"

    implication = split_top_level_operator(text, "=>")
    if implication is not None:
        left = tptp_formula_to_megalodon_proposition(implication[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(implication[1], variable_sorts)
        if left is None or right is None:
            return None
        return f"{proposition_argument_text(left)} -> {right}"

    disjunction = split_top_level_operator(text, "|")
    if disjunction is not None:
        left = tptp_formula_to_megalodon_proposition(disjunction[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(disjunction[1], variable_sorts)
        if left is None or right is None:
            return None
        return f"vampire_or {proposition_argument_text(left)} {proposition_argument_text(right)}"

    conjunction = split_top_level_operator(text, "&")
    if conjunction is not None:
        left = tptp_formula_to_megalodon_proposition(conjunction[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(conjunction[1], variable_sorts)
        if left is None or right is None:
            return None
        return f"vampire_and {proposition_argument_text(left)} {proposition_argument_text(right)}"

    inequality = split_top_level_operator(text, "!=")
    if inequality is not None:
        left = tptp_formula_to_megalodon_proposition(inequality[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(inequality[1], variable_sorts)
        if left is None or right is None:
            return None
        return f"({left} = {right}) -> vampire_false"

    equality = split_top_level_equality(text)
    if equality is not None:
        left_expr = tptp_term_to_expr(equality[0])
        right_expr = tptp_term_to_expr(equality[1])
        left = tptp_formula_to_megalodon_proposition(equality[0], variable_sorts)
        right = tptp_formula_to_megalodon_proposition(equality[1], variable_sorts)
        if left is None or right is None:
            return None
        if (
            left_expr is not None
            and right_expr is not None
            and expr_sort(left_expr, variable_sorts) == "set"
            and expr_sort(right_expr, variable_sorts) == "set"
        ):
            return f"vampire_eq_set {proof_arg_text(left_expr)} {proof_arg_text(right_expr)}"
        if (
            left_expr is not None
            and right_expr is not None
            and expr_sort(left_expr, variable_sorts) == "prop"
            and expr_sort(right_expr, variable_sorts) == "prop"
        ):
            return f"vampire_eq_prop {proof_arg_text(left_expr)} {proof_arg_text(right_expr)}"
        return f"{left} = {right}"

    if text == "$true":
        return "vampire_true"
    if text == "$false":
        return "vampire_false"
    term = tptp_term_to_expr(text)
    return expr_text(term) if term is not None else None


def proposition_argument_text(proposition: str) -> str:
    expr = parse_expr(proposition)
    return proof_arg_text(expr) if expr is not None else f"({proposition})"


def strip_tptp_negation(text: str) -> str | None:
    text = strip_balanced_parens(text)
    if not text.startswith("~"):
        return None
    return strip_balanced_parens(text[1:].strip())


def reconstruction_prelude_for(propositions: list[str]) -> list[str]:
    joined = "\n".join(propositions)
    lines = [
        "Definition vampire_false : prop := forall P:prop, P.",
        "Definition vampire_eq : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.",
        "Infix = 502 := vampire_eq.",
        "Definition vampire_true : prop := forall P:prop, P -> P.",
    ]
    if "vampire_or " in joined:
        lines.append("Definition vampire_or : prop->prop->prop := fun A B:prop => forall P:prop, (A -> P) -> (B -> P) -> P.")
    if "vampire_and " in joined:
        lines.append("Definition vampire_and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.")
    if "vampire_exists_set " in joined:
        lines.append("Definition vampire_exists_set : (set->prop)->prop := fun P => forall Q:prop, (forall X:set, P X -> Q) -> Q.")
    if "vampire_eq_set " in joined:
        lines.append("Definition vampire_eq_set : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.")
    if "vampire_eq_prop " in joined:
        lines.append("Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.")
    return lines


def synthesize_megalodon_claim_skeletons(text: str) -> list[list[str]]:
    input_claim: tuple[str, str] | None = None
    final_step = None
    for raw in text.splitlines():
        line = raw.strip()
        final_match = MEGALODON_FINAL_STEP_RE.match(line)
        if final_match is not None:
            final_step = "S" + final_match.group("id")
            continue
        match = MEGALODON_STEP_FORMULA_RE.match(line)
        if match is None:
            continue
        rule = json.loads(f'"{match.group("rule")}"')
        if rule != "input":
            continue
        formula = json.loads(f'"{match.group("formula")}"')
        parsed = tptp_decl_parts(formula)
        if parsed is None:
            continue
        _, role, body, _ = parsed
        if role != "conjecture":
            continue
        target_body = strip_tptp_negation(body) or body
        proposition = tptp_formula_to_megalodon_proposition(target_body)
        if proposition is None:
            continue
        input_claim = ("S" + match.group("id"), proposition)
        break
    if input_claim is None:
        return []
    claim_name, proposition = input_claim
    lines = reconstruction_prelude_for([proposition])
    lines.extend(
        [
            f"Theorem vampire_reconstruction_skeleton: {proposition}.",
            f"// synthesized claim skeleton from Vampire steps; final refutation step: {comment_text(final_step)}",
            f"claim {claim_name}: {proposition}.",
            "{ admit. }",
            f"exact {claim_name}.",
            "Qed.",
        ]
    )
    return [lines]


def tptp_input_equality(formula: str) -> tuple[Expr, Expr] | None:
    match = re.match(r"\s*tff\([^,]+,\s*axiom,\s*(?P<body>.*)\)\.\s*$", formula, re.DOTALL)
    if match is None:
        return None
    sides = split_top_level_equality(match.group("body"))
    if sides is None:
        return None
    left = tptp_term_to_expr(sides[0])
    right = tptp_term_to_expr(sides[1])
    if left is None or right is None:
        return None
    return left, right


def sort_after_arguments(sort: str, argument_count: int) -> str | None:
    pieces = split_sort_arrows(sort)
    if argument_count >= len(pieces):
        return None
    return join_sort_arrows(pieces[argument_count:])


def expr_sort(expr: Expr, variable_sorts: dict[str, str]) -> str | None:
    if expr.kind == "var":
        assert expr.value is not None
        return variable_sorts.get(expr.value)
    if expr.kind == "app" and expr.args:
        head_sort = expr_sort(expr.args[0], variable_sorts)
        if head_sort is None:
            return None
        return sort_after_arguments(head_sort, len(expr.args) - 1)
    return None


def pointwise_set_equality_proposition(left: Expr, right: Expr, sort: str) -> str | None:
    pieces = split_sort_arrows(sort)
    if len(pieces) < 2 or pieces[-1] != "set" or any(piece != "set" for piece in pieces[:-1]):
        return None
    binders = [Expr("var", value=f"X{index}") for index in range(len(pieces) - 1)]
    left_text = expr_text(append_application_args(left, binders))
    right_text = expr_text(append_application_args(right, binders))
    proposition = f"{left_text} = {right_text}"
    for binder in reversed(binders):
        assert binder.value is not None
        proposition = f"forall {binder.value}:set, {proposition}"
    return proposition


def recovered_input_equalities(proof_text: str, variable_sorts: dict[str, str]) -> list[str]:
    recovered: list[str] = []
    seen: set[str] = set()
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_FORMULA_RE.match(line.strip())
        if match is None or json.loads(f'"{match.group("rule")}"') != "input":
            continue
        formula = json.loads(f'"{match.group("formula")}"')
        equality = tptp_input_equality(formula)
        if equality is None:
            continue
        left, right = equality
        left_sort = expr_sort(left, variable_sorts)
        right_sort = expr_sort(right, variable_sorts)
        if left_sort is None or left_sort != right_sort:
            continue
        proposition = pointwise_set_equality_proposition(left, right, left_sort)
        if proposition is not None and proposition not in seen:
            seen.add(proposition)
            recovered.append(proposition)
    return recovered


def add_recovered_input_equalities(lines: list[str], proof_text: str | None) -> list[str]:
    if proof_text is None:
        return list(lines)
    variable_sorts: dict[str, str] = {}
    variable_re = re.compile(r"^Variable (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^.]+)\.$")
    for line in lines:
        match = variable_re.match(line)
        if match:
            variable_sorts[match.group("name")] = match.group("sort").strip()
    propositions = recovered_input_equalities(proof_text, variable_sorts)
    if not propositions:
        return list(lines)

    existing_propositions = {
        axiom[1]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }
    propositions = [proposition for proposition in propositions if proposition not in existing_propositions]
    if not propositions:
        return list(lines)

    has_equality_prelude = any(line.startswith("Definition vampire_eq ") for line in lines) and any(
        line.startswith("Infix = ") for line in lines
    )
    used_axiom_names = {
        axiom[0]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }

    result: list[str] = []
    inserted_prelude = has_equality_prelude
    inserted_axioms = False
    axiom_index = 0
    for line in lines:
        if not inserted_prelude and (line.startswith("Variable ") or line.startswith("Axiom ") or line.startswith("Theorem ")):
            result.append("Definition vampire_eq : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.")
            result.append("Infix = 502 := vampire_eq.")
            inserted_prelude = True
        if not inserted_axioms and line.startswith("Theorem "):
            for proposition in propositions:
                while f"ax_recovered_{axiom_index}" in used_axiom_names:
                    axiom_index += 1
                name = f"ax_recovered_{axiom_index}"
                used_axiom_names.add(name)
                result.append(f"Axiom {name}:{proposition}.")
                axiom_index += 1
            inserted_axioms = True
        result.append(line)

    if not inserted_prelude:
        result.append("Definition vampire_eq : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.")
        result.append("Infix = 502 := vampire_eq.")
    if not inserted_axioms:
        for proposition in propositions:
            while f"ax_recovered_{axiom_index}" in used_axiom_names:
                axiom_index += 1
            name = f"ax_recovered_{axiom_index}"
            used_axiom_names.add(name)
            result.append(f"Axiom {name}:{proposition}.")
            axiom_index += 1
    return result


def recovered_input_axiom_propositions(proof_text: str, variable_sorts: dict[str, str]) -> list[tuple[str, str]]:
    recovered: list[tuple[str, str]] = []
    seen: set[str] = set()
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_FORMULA_RE.match(line.strip())
        if match is None or json.loads(f'"{match.group("rule")}"') != "input":
            continue
        formula = json.loads(f'"{match.group("formula")}"')
        parsed = tptp_decl_parts(formula)
        if parsed is None:
            continue
        _, role, body, _ = parsed
        if role != "axiom":
            continue
        proposition = tptp_formula_to_megalodon_proposition(body, variable_sorts)
        if proposition is None or proposition in seen:
            continue
        seen.add(proposition)
        recovered.append(("S" + match.group("id"), proposition))
    return recovered


def add_recovered_input_axioms(lines: list[str], proof_text: str | None) -> list[str]:
    if proof_text is None:
        return list(lines)
    has_existing_axioms = any(proposition_after_colon(line, "Axiom ") is not None for line in lines)
    variable_sorts: dict[str, str] = {}
    variable_re = re.compile(r"^Variable (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^.]+)\.$")
    for line in lines:
        match = variable_re.match(line)
        if match:
            variable_sorts[match.group("name")] = match.group("sort").strip()
    recovered = recovered_input_axiom_propositions(proof_text, variable_sorts)
    if not recovered:
        return list(lines)
    existing_names = {
        axiom[0]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }
    existing_propositions = {
        axiom[1]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }
    existing_propositions.update(
        claim[1]
        for line in lines
        for claim in [proposition_after_colon(line, "claim ")]
        if claim is not None
    )
    additions = [
        (name, proposition)
        for name, proposition in recovered
        if name not in existing_names and proposition not in existing_propositions
    ]
    if has_existing_axioms:
        additions = [
            (name, proposition)
            for name, proposition in additions
            if any(token in proposition for token in ("vampire_and ", "vampire_or ", "vampire_exists_", "vampire_eq_"))
        ]
    if has_existing_axioms and len(additions) > 3:
        return list(lines)
    if not additions:
        return list(lines)
    result: list[str] = []
    inserted = False
    needs_set_equality = any("vampire_eq_set " in proposition for _, proposition in additions)
    needs_prop_equality = any("vampire_eq_prop " in proposition for _, proposition in additions)
    has_set_equality = any(line.startswith("Definition vampire_eq_set ") for line in lines)
    has_prop_equality = any(line.startswith("Definition vampire_eq_prop ") for line in lines)
    for line in lines:
        if not inserted and line.startswith("Theorem "):
            if needs_set_equality and not has_set_equality:
                result.append(
                    "Definition vampire_eq_set : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y."
                )
            if needs_prop_equality and not has_prop_equality:
                result.append(
                    "Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y."
                )
            for name, proposition in additions:
                result.append(f"Axiom {name}:{proposition}.")
            inserted = True
        result.append(line)
    if not inserted:
        if needs_set_equality and not has_set_equality:
            result.append("Definition vampire_eq_set : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.")
        if needs_prop_equality and not has_prop_equality:
            result.append("Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.")
        for name, proposition in additions:
            result.append(f"Axiom {name}:{proposition}.")
    return result


def problem_path_for_proof(proof: Path) -> Path | None:
    if proof.parent.name != "proofs":
        return None
    for suffix in (".megalodon.out", ".leancheck.out", ".out"):
        if proof.name.endswith(suffix):
            problem_name = proof.name[: -len(suffix)] + ".p"
            candidate = proof.parent.parent / problem_name
            return candidate if candidate.exists() else None
    return None


def problem_predicate_eliminator_axioms(problem: Path, lines: list[str]) -> list[tuple[str, str]]:
    joined = "\n".join(lines)
    if "Repl " not in joined:
        return []
    variable_sorts: dict[str, str] = {}
    variable_re = re.compile(r"^Variable (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^.]+)\.$")
    for line in lines:
        match = variable_re.match(line)
        if match:
            variable_sorts[match.group("name")] = match.group("sort").strip()

    recovered: list[tuple[str, str]] = []
    seen: set[str] = set()
    for raw in problem.read_text(encoding="utf-8", errors="replace").splitlines():
        parsed = tptp_decl_parts(raw)
        if parsed is None:
            continue
        name, role, body, _ = parsed
        if role != "axiom":
            continue
        proposition = tptp_formula_to_megalodon_proposition(body, variable_sorts)
        if proposition is None or proposition in seen:
            continue
        if "Repl " not in proposition or "set->prop" not in proposition:
            continue
        if "forall" not in proposition or "-> forall" not in proposition:
            continue
        seen.add(proposition)
        recovered.append((decode_tptp_identifier(name), proposition))
        if len(recovered) >= 4:
            break
    return recovered


def add_problem_predicate_eliminator_axioms(lines: list[str], proof: Path | None) -> list[str]:
    if proof is None:
        return list(lines)
    problem = problem_path_for_proof(proof)
    if problem is None:
        return list(lines)
    existing_names = {
        axiom[0]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }
    existing_propositions = {
        axiom[1]
        for line in lines
        for axiom in [proposition_after_colon(line, "Axiom ")]
        if axiom is not None
    }
    candidates = [
        (name, proposition)
        for name, proposition in problem_predicate_eliminator_axioms(problem, lines)
        if name not in existing_names and proposition not in existing_propositions
    ]
    if not candidates:
        return list(lines)

    result: list[str] = []
    inserted = False
    for line in lines:
        if not inserted and line.startswith("Theorem "):
            for name, proposition in candidates:
                axiom_name = name
                suffix = 0
                while axiom_name in existing_names:
                    suffix += 1
                    axiom_name = f"{name}_{suffix}"
                existing_names.add(axiom_name)
                result.append(f"Axiom {axiom_name}:{proposition}.")
            inserted = True
        result.append(line)
    if not inserted:
        for name, proposition in candidates:
            axiom_name = name
            suffix = 0
            while axiom_name in existing_names:
                suffix += 1
                axiom_name = f"{name}_{suffix}"
            existing_names.add(axiom_name)
            result.append(f"Axiom {axiom_name}:{proposition}.")
    return result


def add_problem_type_variables(lines: list[str], proof: Path | None, proof_text: str | None) -> list[str]:
    if proof is None:
        return list(lines)
    problem = problem_path_for_proof(proof)
    if problem is None:
        return list(lines)
    existing = {
        item[0]
        for line in lines
        for item in [proposition_after_colon(line, "Variable ")]
        if item is not None
    }
    existing.update(
        match.group("name")
        for line in lines
        for match in [DEFINITION_RE.match(line)]
        if match is not None
    )
    used_text = "\n".join(lines)
    if proof_text is not None:
        used_text += "\n" + proof_text
    additions: list[str] = []
    for line in problem.read_text(encoding="utf-8", errors="replace").splitlines():
        match = THF_TYPE_RE.match(line.split("%", 1)[0].strip())
        if match is None:
            continue
        raw_name = match.group("name")
        name = decode_tptp_identifier(raw_name)
        if name in existing or not re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", name):
            continue
        if name not in used_text and raw_name not in used_text:
            continue
        existing.add(name)
        additions.append(f"Variable {name}:{tptp_sort_to_megalodon(match.group('sort'))}.")
    if not additions:
        return list(lines)
    result: list[str] = []
    inserted = False
    for line in lines:
        if not inserted and (line.startswith("Variable ") or line.startswith("Axiom ") or line.startswith("Theorem ")):
            result.extend(additions)
            inserted = True
        result.append(line)
    if not inserted:
        result.extend(additions)
    return result


def tptp_function_definition_infos(
    proof_text: str,
    variable_sorts: dict[str, str],
) -> dict[str, DefinitionInfo]:
    definitions: dict[str, DefinitionInfo] = {}
    equation_re = re.compile(r"cnf\([^,]+,axiom,\s*\((?P<left>.*)\s*=\s*(?P<right>sF[0-9]+|.*)\)\s*\)\.", re.DOTALL)
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_FORMULA_RE.match(line.strip())
        if match is None or json.loads(f'"{match.group("rule")}"') != "function definition":
            continue
        formula = json.loads(f'"{match.group("formula")}"')
        equation = equation_re.search(formula)
        if equation is None:
            continue
        sides = [strip_balanced_parens(equation.group("left")), strip_balanced_parens(equation.group("right"))]
        candidates = [(sides[0], sides[1]), (sides[1], sides[0])]
        for target_text, body_text in candidates:
            target = decode_tptp_identifier(strip_balanced_parens(target_text))
            if not FRESH_SET_RE.match(target):
                continue
            body = tptp_term_to_expr(body_text)
            if body is None:
                continue
            definition_sorts = {name: info.sort for name, info in definitions.items()}
            body_sort = expr_sort(body, {**variable_sorts, **definition_sorts})
            target_sort = variable_sorts.get(target) or body_sort
            if target_sort is None:
                continue
            if body_sort is not None and body_sort != target_sort:
                continue
            if (
                body_sort is None
                and body.kind == "var"
                and body.value is not None
                and VAMPIRE_DEPENDENCY_RE.match(body.value)
                and len(split_sort_arrows(target_sort)) > 1
            ):
                continue
            arg_sorts = sort_argument_sorts(target_sort)
            binders = tuple(f"X{index}" for index in range(len(arg_sorts)))
            body = append_application_args(body, [Expr("var", value=name) for name in binders])
            body_expr_text = expr_text(body)
            definition_body = body_expr_text
            for binder_name, binder_sort in reversed(list(zip(binders, arg_sorts))):
                definition_body = f"fun {binder_name}:{binder_sort} => {definition_body}"
            proof_args = list(binders) + ["Q", "H"]
            proof = f"({' '.join(['fun'] + proof_args + ['=>', 'H'])})"
            definitions.setdefault(
                target,
                DefinitionInfo(target_sort, definition_body, proof, binders, body),
            )
            break
    return definitions


TOKEN_RE = re.compile(r"->|=>|[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[(),:=]")


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
        while self.peek() is not None and self.peek() not in {")", ",", "->", "=>", "="}:
            atoms.append(self.parse_atom())
        if len(atoms) == 1:
            return atoms[0]
        return Expr("app", args=tuple(atoms))

    def parse_atom(self) -> Expr:
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of expression")
        if token == "fun":
            return self.parse_lambda()
        if token == "(":
            self.pop("(")
            expr = self.parse_arrow()
            self.pop(")")
            return expr
        if token in {")", ",", ":", "=", "->", "=>"}:
            raise ValueError(f"unexpected token {token}")
        return Expr("var", value=self.pop())

    def parse_lambda(self) -> Expr:
        self.pop("fun")
        name = self.pop()
        self.pop(":")
        sort_tokens: list[str] = []
        while self.peek() is not None and self.peek() != "=>":
            sort_tokens.append(self.pop())
        self.pop("=>")
        return Expr("lambda", value=name, sort="".join(sort_tokens), args=(self.parse_arrow(),))


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
    elif expr.kind == "lambda":
        assert expr.value is not None and expr.sort is not None
        text = f"fun {expr.value}:{expr.sort} => {expr_text(expr.args[0])}"
    else:
        raise ValueError(f"unknown expression kind {expr.kind}")
    if context in {"app_arg", "eq_side"} and expr.kind in {"app", "eq", "arrow", "forall", "lambda"}:
        return f"({text})"
    if context == "arrow_left" and expr.kind in {"arrow", "forall", "lambda"}:
        return f"({text})"
    return text


def expr_key(expr: Expr) -> str:
    return expr_text(expr)


def proof_arg_text(expr: Expr) -> str:
    if expr.kind == "var":
        return expr_text(expr)
    return f"({expr_text(expr)})"


def proof_term_text(proof: str) -> str:
    return proof if re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", proof) else f"({proof})"


def proof_argument_text(proof: str) -> str:
    return proof if re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", proof) else f"({proof})"


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
    if pattern.kind in {"forall", "lambda"}:
        if pattern.kind != target.kind or pattern.sort != target.sort or len(pattern.args) != len(target.args):
            return False
        assert pattern.value is not None and target.value is not None
        local_variables = set(variables)
        local_variables.discard(pattern.value)
        local_variables.discard(target.value)
        target_body = target.args[0]
        if pattern.value != target.value:
            target_body = rename_expr_variables(target_body, {target.value: pattern.value})
        return match_expr(pattern.args[0], target_body, local_variables, subst)
    if pattern.kind != target.kind or pattern.value != target.value or pattern.sort != target.sort:
        return False
    if len(pattern.args) != len(target.args):
        return False
    return all(match_expr(left, right, variables, subst) for left, right in zip(pattern.args, target.args))


def alpha_equivalent(left: Expr, right: Expr) -> bool:
    return canonical_expr_text(left, {}, [0]) == canonical_expr_text(right, {}, [0])


def equality_like_sides(expr: Expr) -> tuple[Expr, Expr] | None:
    if expr.kind == "eq":
        return expr.args[0], expr.args[1]
    if (
        expr.kind == "app"
        and len(expr.args) == 3
        and expr.args[0].kind == "var"
        and expr.args[0].value in {"vampire_eq_set", "vampire_eq_prop"}
    ):
        return expr.args[1], expr.args[2]
    return None


def match_expr_with_alpha_instantiation(
    pattern: Expr,
    target: Expr,
    variables: set[str],
    subst: dict[str, Expr],
) -> bool:
    trial = dict(subst)
    if match_expr(pattern, target, variables, trial):
        subst.clear()
        subst.update(trial)
        return True
    instantiated = substitute_expr(pattern, trial)
    if expr_variables(instantiated) & variables:
        return False
    if not alpha_equivalent(instantiated, target):
        return False
    subst.clear()
    subst.update(trial)
    return True


def infer_rule_binders_from_known(
    steps: tuple[RuleStep, ...],
    binders: tuple[str, ...],
    subst: dict[str, Expr],
    known: dict[str, str],
) -> dict[str, Expr] | None:
    missing = {binder for binder in binders if binder not in subst}
    if not missing:
        return subst

    variables = set(binders)
    known_exprs: list[Expr] = []
    seen: set[str] = set()
    for proposition in known:
        if proposition in seen:
            continue
        seen.add(proposition)
        parsed = parse_expr(proposition)
        if parsed is not None:
            known_exprs.append(parsed)

    candidates = [dict(subst)]
    for step in steps:
        if step.kind != "premise" or step.expr is None:
            continue
        next_candidates = list(candidates)
        for candidate in candidates:
            if all(binder in candidate for binder in binders):
                continue
            premise = substitute_expr(step.expr, candidate)
            for known_expr in known_exprs:
                trial = dict(candidate)
                if match_expr(premise, known_expr, variables, trial):
                    next_candidates.append(trial)
        candidates = next_candidates
        for candidate in candidates:
            if all(binder in candidate for binder in binders):
                return candidate

    for candidate in candidates:
        if all(binder in candidate for binder in binders):
            return candidate
    return None


def infer_rule_binders_from_reflexive_premises(
    steps: tuple[RuleStep, ...],
    binders: tuple[str, ...],
    subst: dict[str, Expr],
    limit: int = 16,
) -> list[dict[str, Expr]]:
    candidates = [dict(subst)]
    for step in steps:
        if step.kind != "premise" or step.expr is None or equality_like_sides(step.expr) is None:
            continue
        next_candidates = list(candidates)
        for candidate in candidates:
            missing = {binder for binder in binders if binder not in candidate}
            if not missing:
                continue
            premise = substitute_expr(step.expr, candidate)
            sides = equality_like_sides(premise)
            if sides is None:
                continue
            for left, right in (sides, (sides[1], sides[0])):
                trial = dict(candidate)
                if match_expr(left, right, missing, trial):
                    key = tuple(sorted((name, expr_key(value)) for name, value in trial.items()))
                    if all(tuple(sorted((name, expr_key(value)) for name, value in existing.items())) != key for existing in next_candidates):
                        next_candidates.append(trial)
                        if len(next_candidates) >= limit:
                            break
            if len(next_candidates) >= limit:
                break
        candidates = next_candidates[:limit]
    return [candidate for candidate in candidates if all(binder in candidate for binder in binders)]


def infer_rule_binder_candidates_from_known(
    steps: tuple[RuleStep, ...],
    binders: tuple[str, ...],
    subst: dict[str, Expr],
    known: dict[str, str],
    limit: int = 32,
    require_premise_match: bool = False,
) -> list[dict[str, Expr]]:
    variables = set(binders)
    known_exprs_cache = getattr(PROOF_SEARCH_STATE, "known_exprs_cache", None)
    if known_exprs_cache is None:
        known_exprs_cache = {}
        PROOF_SEARCH_STATE.known_exprs_cache = known_exprs_cache
    known_key = tuple(sorted(known))
    known_exprs = known_exprs_cache.get(known_key)
    if known_exprs is None:
        parsed_exprs: list[Expr] = []
        for proposition in known_key:
            parsed = parse_expr(proposition)
            if parsed is not None:
                parsed_exprs.append(parsed)
        known_exprs = parsed_exprs
        known_exprs_cache[known_key] = known_exprs

    candidates = [dict(subst)]
    for step in steps:
        if step.kind != "premise" or step.expr is None:
            continue
        next_candidates = [] if require_premise_match else list(candidates)
        for candidate in candidates:
            premise = substitute_expr(step.expr, candidate)
            for known_expr in known_exprs:
                trial = dict(candidate)
                if match_expr(premise, known_expr, variables, trial):
                    next_candidates.append(trial)
        if not next_candidates:
            return []
        deduped: list[dict[str, Expr]] = []
        seen_candidates: set[tuple[tuple[str, str], ...]] = set()
        for candidate in next_candidates:
            key = tuple(sorted((name, expr_key(value)) for name, value in candidate.items()))
            if key in seen_candidates:
                continue
            seen_candidates.add(key)
            deduped.append(candidate)
            if len(deduped) >= limit:
                break
        candidates = deduped

    return [
        candidate
        for candidate in candidates
        if all(binder in candidate for binder in binders)
    ][:limit]


def expr_subterms(expr: Expr, limit: int = 128) -> list[Expr]:
    found: list[Expr] = []
    seen: set[str] = set()

    def visit(node: Expr) -> None:
        if len(found) >= limit:
            return
        key = expr_key(node)
        if key not in seen:
            seen.add(key)
            found.append(node)
        for arg in node.args:
            visit(arg)

    visit(expr)
    return found


def fill_missing_binders_with_terms(
    binders: tuple[str, ...],
    subst: dict[str, Expr],
    terms: list[Expr],
    limit: int = 256,
) -> list[dict[str, Expr]]:
    missing = [binder for binder in binders if binder not in subst]
    if not missing:
        return [dict(subst)]
    candidates = [dict(subst)]
    for binder in missing:
        next_candidates: list[dict[str, Expr]] = []
        for candidate in candidates:
            for term in terms:
                trial = dict(candidate)
                trial[binder] = term
                next_candidates.append(trial)
                if len(next_candidates) >= limit:
                    break
            if len(next_candidates) >= limit:
                break
        candidates = next_candidates
    return candidates


def expr_mentions_any(expr: Expr, names: set[str]) -> bool:
    if expr.kind == "var" and expr.value in names:
        return True
    return any(expr_mentions_any(arg, names) for arg in expr.args)


def expr_argument_subterms(expr: Expr, limit: int = 128) -> list[Expr]:
    found: list[Expr] = []
    seen: set[str] = set()

    def add(node: Expr) -> None:
        if len(found) >= limit:
            return
        key = expr_key(node)
        if key in seen:
            return
        seen.add(key)
        found.append(node)

    def visit(node: Expr) -> None:
        if len(found) >= limit:
            return
        if node.kind == "app":
            for arg in node.args[1:]:
                add(arg)
                visit(arg)
            return
        if node.kind == "eq":
            for arg in node.args:
                add(arg)
                visit(arg)
            return
        for arg in node.args:
            visit(arg)

    visit(expr)
    return found


def candidate_terms_from_state(
    known: dict[str, str],
    eq_facts: list[EqFact],
    seed: Iterable[Expr] = (),
    exclude_names: set[str] | None = None,
    limit: int = 96,
) -> list[Expr]:
    if proof_search_timed_out():
        return []
    seed_tuple = tuple(seed)
    excluded = frozenset(exclude_names or set())
    cache = getattr(PROOF_SEARCH_STATE, "candidate_terms_cache", None)
    if cache is None:
        cache = {}
        PROOF_SEARCH_STATE.candidate_terms_cache = cache
    cache_key = (
        tuple(sorted(known)),
        tuple((expr_key(fact.left), expr_key(fact.right)) for fact in eq_facts),
        tuple(expr_key(expr) for expr in seed_tuple),
        tuple(sorted(excluded)),
        limit,
    )
    cached = cache.get(cache_key)
    if cached is not None:
        return list(cached)

    terms: list[Expr] = []
    seen: set[str] = set()
    excluded_set = set(excluded)

    def add(term: Expr, blocked: set[str] | None = None) -> None:
        if proof_search_timed_out():
            return
        if len(terms) >= limit:
            return
        if expr_mentions_any(term, blocked if blocked is not None else excluded_set):
            return
        key = expr_key(term)
        if key in seen:
            return
        seen.add(key)
        terms.append(term)

    for expr in seed_tuple:
        if proof_search_timed_out():
            break
        for term in expr_argument_subterms(expr, limit=24):
            add(term)
    for proposition in known:
        if proof_search_timed_out():
            break
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        bound_names = {name for name, _ in collect_foralls(parsed)[0]}
        proposition_excluded = excluded_set & bound_names
        for term in expr_argument_subterms(parsed, limit=24):
            add(term, proposition_excluded)
        if len(terms) >= limit:
            break
    for fact in eq_facts:
        if proof_search_timed_out():
            break
        for term in expr_subterms(fact.left, limit=16):
            add(term)
        for term in expr_subterms(fact.right, limit=16):
            add(term)
    terms.sort(key=lambda term: (0 if term.kind == "var" else 1, len(expr_text(term)), expr_text(term)))
    cache[cache_key] = tuple(terms)
    return terms


def substitute_expr(expr: Expr, subst: dict[str, Expr]) -> Expr:
    if expr.kind == "var" and expr.value in subst:
        return subst[expr.value]
    if not expr.args:
        return expr
    if expr.kind in {"forall", "lambda"} and expr.value in subst:
        subst = {name: value for name, value in subst.items() if name != expr.value}
    return Expr(expr.kind, value=expr.value, args=tuple(substitute_expr(arg, subst) for arg in expr.args), sort=expr.sort)


def replace_expr(expr: Expr, needle: Expr, replacement: Expr) -> tuple[Expr, bool]:
    if expr_key(expr) == expr_key(needle):
        return replacement, True
    if not expr.args:
        return expr, False
    changed = False
    args: list[Expr] = []
    for arg in expr.args:
        replaced, arg_changed = replace_expr(arg, needle, replacement)
        args.append(replaced)
        changed = changed or arg_changed
    if not changed:
        return expr, False
    return Expr(expr.kind, value=expr.value, args=tuple(args), sort=expr.sort), True


def make_proof_rule(name: str, proposition: str) -> ProofRule | None:
    expr = parse_expr(proposition)
    if expr is None:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    steps, ordered_conclusion = sequential_rule_steps(expr)
    return ProofRule(
        name=name,
        binders=tuple(name for name, _ in binders),
        premises=tuple(premises),
        conclusion=conclusion,
        steps=tuple(steps),
        application_conclusion=ordered_conclusion,
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


def infer_argument_sorts_from_expr(
    expr: Expr,
    known_sorts: dict[str, str],
    inferred_sorts: dict[str, str],
    expected_sort: str | None = None,
) -> None:
    if expr.kind == "var" and expr.value is not None and expected_sort is not None:
        inferred_sorts.setdefault(expr.value, expected_sort)
        return
    if expr.kind == "app" and expr.args:
        head = expr.args[0]
        if head.kind == "var" and head.value is not None:
            head_sort = known_sorts.get(head.value) or inferred_sorts.get(head.value)
            if head_sort is not None:
                pieces = split_sort_arrows(head_sort)
                for arg, arg_sort in zip(expr.args[1:], pieces[:-1]):
                    if arg.kind == "var" and arg.value is not None:
                        inferred_sorts.setdefault(arg.value, arg_sort)
            elif expected_sort is not None:
                arg_sorts = [
                    (known_sorts.get(arg.value) or inferred_sorts.get(arg.value))
                    if arg.kind == "var" and arg.value is not None
                    else None
                    for arg in expr.args[1:]
                ]
                if all(arg_sort is not None for arg_sort in arg_sorts):
                    head_sort_pieces = [arg_sort for arg_sort in arg_sorts if arg_sort is not None]
                    head_sort_pieces.append(expected_sort)
                    inferred_sorts.setdefault(
                        head.value,
                        join_sort_arrows(head_sort_pieces),
                    )
        for arg in expr.args:
            infer_argument_sorts_from_expr(arg, known_sorts, inferred_sorts)
        return
    for arg in expr.args:
        infer_argument_sorts_from_expr(arg, known_sorts, inferred_sorts)


def fresh_dependency_variables(
    definitions: dict[str, DefinitionInfo],
    variable_sorts: dict[str, str],
) -> dict[str, str]:
    known_sorts = {**variable_sorts, **{name: definition.sort for name, definition in definitions.items()}}
    inferred_sorts: dict[str, str] = {}
    changed = True
    while changed:
        before = len(inferred_sorts)
        for definition in definitions.values():
            pieces = split_sort_arrows(definition.sort)
            binder_sorts = pieces[: len(definition.binders)]
            result_sort = sort_after_arguments(definition.sort, len(definition.binders))
            local_sorts = {**known_sorts, **inferred_sorts, **dict(zip(definition.binders, binder_sorts))}
            infer_argument_sorts_from_expr(definition.body, local_sorts, inferred_sorts, result_sort)
        changed = len(inferred_sorts) != before
    return {
        name: sort
        for name, sort in inferred_sorts.items()
        if (VAMPIRE_DEPENDENCY_RE.match(name) or INFERRED_DEPENDENCY_RE.match(name))
        and name not in known_sorts
        and not name.startswith("X")
    }


def expr_variables(expr: Expr) -> set[str]:
    found: set[str] = set()
    if expr.kind == "var" and expr.value is not None:
        found.add(expr.value)
    for arg in expr.args:
        found.update(expr_variables(arg))
    if expr.kind in {"forall", "lambda"} and expr.value is not None:
        found.discard(expr.value)
    return found


def ordered_definitions(definitions: dict[str, DefinitionInfo]) -> list[tuple[str, DefinitionInfo]]:
    remaining = dict(definitions)
    ordered: list[tuple[str, DefinitionInfo]] = []
    emitted: set[str] = set()
    while remaining:
        progressed = False
        for name, definition in list(remaining.items()):
            dependencies = expr_variables(definition.body) - set(definition.binders)
            if not (dependencies & set(remaining.keys()) - {name}):
                ordered.append((name, definition))
                emitted.add(name)
                del remaining[name]
                progressed = True
        if not progressed:
            ordered.extend(remaining.items())
            break
    return ordered


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


def parse_definition_body(body_text: str) -> tuple[tuple[str, ...], Expr] | None:
    binders: list[str] = []
    text = body_text.strip()
    while text.startswith("fun "):
        match = re.match(r"fun (?P<name>[_A-Za-z][_A-Za-z0-9']*):(?P<sort>[^=]+?) => (?P<body>.*)$", text)
        if match is None:
            return None
        binders.append(match.group("name"))
        text = match.group("body").strip()
    body = parse_expr(text)
    if body is None:
        return None
    return tuple(binders), body


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

    definitions: dict[str, DefinitionInfo] = tptp_function_definition_infos(proof_text, variable_sorts)
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

    dependency_variables: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        next_dependencies = fresh_dependency_variables(definitions, {**variable_sorts, **dependency_variables})
        for name, sort in next_dependencies.items():
            if name not in dependency_variables:
                dependency_variables[name] = sort
                changed = True
        extended_sorts = {
            **variable_sorts,
            **dependency_variables,
            **{name: definition.sort for name, definition in definitions.items()},
        }
        for name, definition in tptp_function_definition_infos(proof_text, extended_sorts).items():
            if name not in definitions:
                definitions[name] = definition
                changed = True

    if not definitions:
        return list(lines)

    dependency_variables = fresh_dependency_variables(definitions, variable_sorts)
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
            for name, sort in dependency_variables.items():
                result.append(f"Variable {name}:{sort}.")
            for name, definition in ordered_definitions(definitions):
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
        for name, sort in dependency_variables.items():
            result.append(f"Variable {name}:{sort}.")
        for name, definition in ordered_definitions(definitions):
            result.append(f"Definition {name} : {definition.sort} := {definition.body_text}.")
    return result


def fill_source_candidate_claims(lines: list[str], proof_text: str | None) -> list[str]:
    if proof_text is None:
        return list(lines)
    source_proofs = source_candidate_claim_proofs(proof_text)
    if not source_proofs:
        return list(lines)
    axiom_propositions = {
        claim[0]: claim[1]
        for line in lines
        for claim in [proposition_after_colon(line, "Axiom ")]
        if claim is not None
    }

    def references_available(lines: list[str]) -> bool:
        referenced = set(re.findall(r"\bax[0-9]+\b", "\n".join(lines)))
        return referenced <= set(axiom_propositions)

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
            and references_available(source_proofs[claim[1]])
        ):
            direct_proof = source_candidate_rewrite_chain_proof(
                source_proofs[claim[1]],
                claim[1],
            )
            if direct_proof is None:
                result.append("{")
                result.extend(source_proofs[claim[1]])
                result.append("}")
            else:
                result.append("{ exact " + direct_proof + ". }")
            used.add(claim[1])
            index += 2
            continue
        index += 1
    return result


BOOLEAN_EXT_HELPERS = [
    "Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.",
    "Definition vampire_eq_prop_fun : (prop->prop)->(prop->prop)->prop := fun x y:prop->prop => forall Q:(prop->prop)->prop, Q x -> Q y.",
    "Axiom vampire_xm: forall P:prop, vampire_or P (P -> vampire_false).",
    "Axiom vampire_prop_ext: forall P Q:prop, (P -> Q) -> (Q -> P) -> vampire_eq_prop P Q.",
    "Axiom vampire_funext_prop: forall F G:prop->prop, (forall X:prop, vampire_eq_prop (F X) (G X)) -> vampire_eq_prop_fun F G.",
    "Axiom vampire_funext_prop_prop: forall F G:prop->prop->prop, (forall X:prop, vampire_eq_prop_fun (F X) (G X)) -> F = G.",
]


def is_or_nand_binary_function_equality(expr: Expr) -> bool:
    if expr.kind != "eq":
        return False
    left_binders, left_body = collect_lambdas(expr.args[0])
    right_binders, right_body = collect_lambdas(expr.args[1])
    if [sort for _, sort in left_binders] != ["prop", "prop"]:
        return False
    if [sort for _, sort in right_binders] != ["prop", "prop"]:
        return False
    left_names = [name for name, _ in left_binders]
    right_names = [name for name, _ in right_binders]
    expected_left = Expr(
        "app",
        args=(Expr("var", value="vampire_or"), Expr("var", value=left_names[0]), Expr("var", value=left_names[1])),
    )
    expected_right = Expr(
        "arrow",
        args=(
            Expr(
                "app",
                args=(
                    Expr("var", value="vampire_and"),
                    Expr("arrow", args=(Expr("var", value=right_names[0]), Expr("var", value="vampire_false"))),
                    Expr("arrow", args=(Expr("var", value=right_names[1]), Expr("var", value="vampire_false"))),
                ),
            ),
            Expr("var", value="vampire_false"),
        ),
    )
    return expr_key(left_body) == expr_key(expected_left) and expr_key(right_body) == expr_key(expected_right)


def collect_lambdas(expr: Expr) -> tuple[list[tuple[str, str]], Expr]:
    binders: list[tuple[str, str]] = []
    while expr.kind == "lambda":
        assert expr.value is not None and expr.sort is not None
        binders.append((expr.value, expr.sort))
        expr = expr.args[0]
    return binders, expr


def needs_boolean_ext_helpers(lines: list[str]) -> bool:
    has_or = any(line.startswith("Definition vampire_or ") for line in lines)
    has_and = any(line.startswith("Definition vampire_and ") for line in lines)
    has_false = any(line.startswith("Definition vampire_false ") for line in lines)
    if not (has_or and has_and and has_false):
        return False
    for line in lines:
        parsed = proposition_after_colon(line, "Theorem ") or proposition_after_colon(line, "claim ")
        if parsed is None:
            continue
        expr = parse_expr(parsed[1])
        if expr is not None and is_or_nand_binary_function_equality(expr):
            return True
    return False


def add_boolean_extensionality_helpers(lines: list[str]) -> list[str]:
    if not needs_boolean_ext_helpers(lines):
        return list(lines)
    existing_names = {
        item[0]
        for line in lines
        for item in [proposition_after_colon(line, "Axiom ") or proposition_after_colon(line, "Definition ")]
        if item is not None
    }
    helpers = [
        line
        for line in BOOLEAN_EXT_HELPERS
        if (proposition_after_colon(line, "Axiom ") or proposition_after_colon(line, "Definition "))[0] not in existing_names
    ]
    if not helpers:
        return list(lines)
    result: list[str] = []
    inserted = False
    for line in lines:
        if not inserted and (line.startswith("Axiom ") or line.startswith("Theorem ")):
            result.extend(helpers)
            inserted = True
        result.append(line)
    if not inserted:
        result.extend(helpers)
    return result


def add_missing_basic_connective_definitions(lines: list[str]) -> list[str]:
    text = "\n".join(lines)
    helpers: list[str] = []
    if "vampire_true" in text and not any(line.startswith("Definition vampire_true ") for line in lines):
        helpers.append("Definition vampire_true : prop := forall P:prop, P -> P.")
    if "vampire_or " in text and not any(line.startswith("Definition vampire_or ") for line in lines):
        helpers.append("Definition vampire_or : prop->prop->prop := fun A B:prop => forall P:prop, (A -> P) -> (B -> P) -> P.")
    if "vampire_and " in text and not any(line.startswith("Definition vampire_and ") for line in lines):
        helpers.append("Definition vampire_and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.")
    needs_exists_definition = "vampire_exists_set " in text and not any(
        line.startswith("Definition vampire_exists_set ") for line in lines
    )
    if needs_exists_definition:
        helpers.append("Definition vampire_exists_set : (set->prop)->prop := fun P => forall Q:prop, (forall X:set, P X -> Q) -> Q.")
    if "vampire_eq_set " in text and not any(line.startswith("Definition vampire_eq_set ") for line in lines):
        helpers.append("Definition vampire_eq_set : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.")
    if "vampire_eq_prop " in text and not any(line.startswith("Definition vampire_eq_prop ") for line in lines):
        helpers.append("Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.")
    if not helpers and not needs_exists_definition:
        return list(lines)
    result: list[str] = []
    inserted = False
    for line in lines:
        if needs_exists_definition and line.startswith("Variable vampire_exists_set:"):
            continue
        if not inserted and (line.startswith("Axiom ") or line.startswith("Theorem ")):
            result.extend(helpers)
            inserted = True
        result.append(line)
    if not inserted:
        result.extend(helpers)
    return result


def parenthesize_atomic_axiom_propositions(lines: list[str]) -> list[str]:
    result: list[str] = []
    for line in lines:
        axiom = proposition_after_colon(line, "Axiom ")
        if axiom is None:
            result.append(line)
            continue
        name, proposition = axiom
        stripped = proposition.strip()
        if stripped.startswith("(") and stripped.endswith(")"):
            result.append(line)
            continue
        expr = parse_expr(stripped)
        if expr is not None and expr.kind == "app" and len(expr.args) >= 3:
            result.append(f"Axiom {name}:({stripped}).")
        else:
            result.append(line)
    return result


def boolean_or_nand_extensionality_proof(expr: Expr, known: dict[str, str]) -> str | None:
    if not is_or_nand_binary_function_equality(expr):
        return None
    required = {
        "vampire_xm",
        "vampire_prop_ext",
        "vampire_funext_prop",
        "vampire_funext_prop_prop",
    }
    if not required <= set(known.values()):
        return None
    return (
        "(vampire_funext_prop_prop "
        "(fun X0:prop => fun X1:prop => vampire_or X0 X1) "
        "(fun X0:prop => fun X1:prop => (vampire_and (X0 -> vampire_false) (X1 -> vampire_false)) -> vampire_false) "
        "(fun X0:prop => vampire_funext_prop "
        "(fun X1:prop => vampire_or X0 X1) "
        "(fun X1:prop => (vampire_and (X0 -> vampire_false) (X1 -> vampire_false)) -> vampire_false) "
        "(fun X1:prop => vampire_prop_ext "
        "(vampire_or X0 X1) "
        "((vampire_and (X0 -> vampire_false) (X1 -> vampire_false)) -> vampire_false) "
        "(fun Hor Hand => Hor vampire_false "
        "(fun HX0 => Hand vampire_false (fun HnX0 HnX1 => HnX0 HX0)) "
        "(fun HX1 => Hand vampire_false (fun HnX0 HnX1 => HnX1 HX1))) "
        "(fun Hnot P Hleft Hright => "
        "(vampire_xm X0) P Hleft "
        "(fun HnX0 => (vampire_xm X1) P Hright "
        "(fun HnX1 => (Hnot (fun R Hpair => Hpair HnX0 HnX1)) P))))))"
    )


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


def canonical_expr_text(expr: Expr, env: dict[str, str], next_var: list[int]) -> str:
    if expr.kind == "var":
        assert expr.value is not None
        return env.get(expr.value, expr.value)
    if expr.kind == "app":
        return " ".join(
            canonical_expr_text(arg, env, next_var)
            if arg.kind == "var"
            else f"({canonical_expr_text(arg, env, next_var)})"
            for arg in expr.args
        )
    if expr.kind == "eq":
        return f"{canonical_expr_text(expr.args[0], env, next_var)} = {canonical_expr_text(expr.args[1], env, next_var)}"
    if expr.kind == "arrow":
        left = canonical_expr_text(expr.args[0], env, next_var)
        if expr.args[0].kind == "arrow":
            left = f"({left})"
        return f"{left} -> {canonical_expr_text(expr.args[1], env, next_var)}"
    if expr.kind in {"forall", "lambda"}:
        assert expr.value is not None and expr.sort is not None
        replacement = f"__v{next_var[0]}"
        next_var[0] += 1
        inner_env = dict(env)
        inner_env[expr.value] = replacement
        body = canonical_expr_text(expr.args[0], inner_env, next_var)
        if expr.kind == "forall":
            return f"forall {replacement}:{expr.sort}, {body}"
        return f"fun {replacement}:{expr.sort} => {body}"
    raise ValueError(f"unknown expression kind {expr.kind}")


def canonical_proposition(proposition: str) -> str:
    expr = parse_expr(proposition)
    if expr is not None:
        return canonical_expr_text(expr, {}, [0])
    return canonicalize_segment(proposition, [0])


def proof_head(proof: str) -> str:
    if re.fullmatch(r"[_A-Za-z][_A-Za-z0-9']*", proof):
        return proof
    return f"({proof})"


def fresh_identifier(base: str, *texts: str) -> str:
    used = set()
    for text in texts:
        used.update(re.findall(r"[_A-Za-z][_A-Za-z0-9']*", text))
    name = base
    index = 0
    while name in used:
        index += 1
        name = f"{base}{index}"
    return name


def eq_symmetry_proof(proof: str, left: Expr) -> str:
    left_text = expr_text(left)
    name = fresh_identifier("zz", left_text)
    return f"({proof_head(proof)} (fun {name}:set => {name} = {left_text}) (fun R Hr => Hr))"


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


@dataclass(frozen=True)
class OrientedRuleRewrite:
    rule: ProofRule
    subst: dict[str, Expr]
    middle: Expr
    reverse: bool


def oriented_rule_rewrites_from(side: Expr, rule: ProofRule) -> list[OrientedRuleRewrite]:
    conclusion = rule_application_conclusion(rule)
    if conclusion.kind != "eq":
        return []
    variables = set(rule_application_binders(rule))
    rewrites: list[OrientedRuleRewrite] = []
    direct_subst: dict[str, Expr] = {}
    if match_expr(conclusion.args[0], side, variables, direct_subst):
        rewrites.append(OrientedRuleRewrite(rule, direct_subst, conclusion.args[1], False))
    reverse_subst: dict[str, Expr] = {}
    if match_expr(conclusion.args[1], side, variables, reverse_subst):
        rewrites.append(OrientedRuleRewrite(rule, reverse_subst, conclusion.args[0], True))
    return rewrites


def merge_substitutions(left: dict[str, Expr], right: dict[str, Expr]) -> dict[str, Expr] | None:
    merged = dict(left)
    for name, value in right.items():
        previous = merged.get(name)
        if previous is not None and expr_key(previous) != expr_key(value):
            return None
        merged[name] = value
    return merged


def resolve_substitution_value(expr: Expr, subst: dict[str, Expr], seen: set[str] | None = None) -> Expr:
    if seen is None:
        seen = set()
    if expr.kind == "var" and expr.value in subst and expr.value not in seen:
        seen.add(expr.value)
        return resolve_substitution_value(subst[expr.value], subst, seen)
    if not expr.args:
        return expr
    return Expr(
        expr.kind,
        value=expr.value,
        args=tuple(resolve_substitution_value(arg, subst, set(seen)) for arg in expr.args),
        sort=expr.sort,
    )


def flatten_substitution(subst: dict[str, Expr]) -> None:
    for name in list(subst):
        subst[name] = resolve_substitution_value(subst[name], subst, {name})


def rename_expr_variables(expr: Expr, renames: dict[str, str]) -> Expr:
    if expr.kind == "var" and expr.value in renames:
        return Expr("var", value=renames[expr.value], sort=expr.sort)
    if not expr.args:
        return expr
    if expr.kind in {"forall", "lambda"} and expr.value in renames:
        renames = {name: replacement for name, replacement in renames.items() if name != expr.value}
    return Expr(
        expr.kind,
        value=expr.value,
        args=tuple(rename_expr_variables(arg, renames) for arg in expr.args),
        sort=expr.sort,
    )


def replace_expr_occurrences(expr: Expr, needle: Expr, replacement: Expr) -> tuple[Expr, bool]:
    if expr_key(expr) == expr_key(needle):
        return replacement, True
    if not expr.args:
        return expr, False
    if (
        expr.kind in {"forall", "lambda"}
        and needle.kind == "var"
        and expr.value == needle.value
    ):
        return expr, False
    changed = False
    replaced_args: list[Expr] = []
    for arg in expr.args:
        replaced_arg, arg_changed = replace_expr_occurrences(arg, needle, replacement)
        changed = changed or arg_changed
        replaced_args.append(replaced_arg)
    if not changed:
        return expr, False
    return Expr(expr.kind, value=expr.value, args=tuple(replaced_args), sort=expr.sort), True


def single_replacement_contexts(
    expr: Expr,
    needle: Expr,
    replacement: Expr,
    hole: Expr,
    limit: int = 8,
) -> list[tuple[Expr, Expr]]:
    if expr_key(expr) == expr_key(needle):
        return [(replacement, hole)]
    if not expr.args:
        return []
    if (
        expr.kind in {"forall", "lambda"}
        and needle.kind == "var"
        and expr.value == needle.value
    ):
        return []
    found: list[tuple[Expr, Expr]] = []
    for index, arg in enumerate(expr.args):
        for replaced_arg, context_arg in single_replacement_contexts(arg, needle, replacement, hole, limit):
            replaced_args = list(expr.args)
            replaced_args[index] = replaced_arg
            context_args = list(expr.args)
            context_args[index] = context_arg
            found.append(
                (
                    Expr(expr.kind, value=expr.value, args=tuple(replaced_args), sort=expr.sort),
                    Expr(expr.kind, value=expr.value, args=tuple(context_args), sort=expr.sort),
                )
            )
            if len(found) >= limit:
                return found
    return found


def rename_rule_binders(rule: ProofRule, prefix: str) -> ProofRule:
    renames = {name: f"{prefix}{name}" for name in rule_application_binders(rule)}
    steps: list[RuleStep] = []
    for step in rule.steps:
        if step.kind == "binder":
            assert step.name is not None
            steps.append(RuleStep("binder", name=renames.get(step.name, step.name)))
        else:
            assert step.expr is not None
            steps.append(RuleStep("premise", expr=rename_expr_variables(step.expr, renames)))
    return ProofRule(
        name=rule.name,
        binders=tuple(renames.get(name, name) for name in rule.binders),
        premises=tuple(rename_expr_variables(premise, renames) for premise in rule.premises),
        conclusion=rename_expr_variables(rule.conclusion, renames),
        steps=tuple(steps),
        application_conclusion=(
            rename_expr_variables(rule.application_conclusion, renames)
            if rule.application_conclusion is not None
            else None
        ),
    )


def bind_match_variable(name: str, value: Expr, subst: dict[str, Expr]) -> bool:
    if value.kind == "var" and value.value == name:
        return True
    previous = subst.get(name)
    if previous is not None and previous.kind == "var" and previous.value == name:
        subst[name] = value
        return True
    if previous is None:
        subst[name] = value
        return True
    return expr_key(previous) == expr_key(value)


def exact_match_with_variables(left: Expr, right: Expr, variables: set[str], subst: dict[str, Expr]) -> bool:
    left = substitute_expr(left, subst)
    right = substitute_expr(right, subst)
    if left.kind == "var" and left.value in variables:
        return bind_match_variable(left.value, right, subst)
    if right.kind == "var" and right.value in variables:
        return bind_match_variable(right.value, left, subst)
    if left.kind != right.kind or left.value != right.value or left.sort != right.sort:
        return False
    if len(left.args) != len(right.args):
        return False
    return all(exact_match_with_variables(larg, rarg, variables, subst) for larg, rarg in zip(left.args, right.args))


def known_equality_match_proof(
    expr: Expr,
    variables: set[str],
    subst: dict[str, Expr],
    known: dict[str, str],
) -> str | None:
    if expr.kind != "eq":
        return None
    for proposition, proof in known.items():
        parsed = parse_expr(proposition)
        if parsed is None or parsed.kind != "eq":
            continue
        direct_subst = dict(subst)
        if exact_match_with_variables(expr.args[0], parsed.args[0], variables, direct_subst) and exact_match_with_variables(
            expr.args[1], parsed.args[1], variables, direct_subst
        ):
            subst.clear()
            subst.update(direct_subst)
            return proof
        reverse_subst = dict(subst)
        if exact_match_with_variables(expr.args[0], parsed.args[1], variables, reverse_subst) and exact_match_with_variables(
            expr.args[1], parsed.args[0], variables, reverse_subst
        ):
            subst.clear()
            subst.update(reverse_subst)
            return eq_symmetry_proof(proof, parsed.args[0])
    return None


def contextual_equality_proof(
    left: Expr,
    right: Expr,
    variables: set[str],
    subst: dict[str, Expr],
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if exact_match_with_variables(left, right, variables, subst):
        return "(fun Q H => H)"

    left = substitute_expr(left, subst)
    right = substitute_expr(right, subst)
    if left.kind != "app" or right.kind != "app" or len(left.args) != len(right.args) or len(left.args) < 2:
        return None
    trial = dict(subst)
    if not exact_match_with_variables(left.args[0], right.args[0], variables, trial):
        return None

    matches: list[tuple[int, str, dict[str, Expr]]] = []
    for candidate_index in range(1, len(left.args)):
        candidate_subst = dict(trial)
        ok = True
        for index, (left_arg, right_arg) in enumerate(zip(left.args[1:], right.args[1:]), start=1):
            if index == candidate_index:
                continue
            if not exact_match_with_variables(left_arg, right_arg, variables, candidate_subst):
                ok = False
                break
        if not ok:
            continue
        left_arg = substitute_expr(left.args[candidate_index], candidate_subst)
        right_arg = substitute_expr(right.args[candidate_index], candidate_subst)
        argument_equality = Expr("eq", args=(left_arg, right_arg))
        argument_key = expr_key(argument_equality)
        argument_proof = known.get(argument_key) or known_canonical.get(canonical_proposition(argument_key))
        if argument_proof is None:
            reverse_equality = Expr("eq", args=(right_arg, left_arg))
            reverse_key = expr_key(reverse_equality)
            reverse_proof = known.get(reverse_key) or known_canonical.get(canonical_proposition(reverse_key))
            if reverse_proof is not None:
                argument_proof = eq_symmetry_proof(reverse_proof, right_arg)
        if argument_proof is None:
            argument_proof = known_equality_match_proof(argument_equality, variables, candidate_subst, known)
        if argument_proof is None:
            continue
        matches.append((candidate_index, argument_proof, candidate_subst))
    if len(matches) != 1:
        return None

    candidate_index, argument_proof, final_subst = matches[0]
    subst.clear()
    subst.update(final_subst)
    instantiated_left = substitute_expr(left, subst)
    instantiated_args = tuple(substitute_expr(arg, subst) for arg in left.args[1:])
    hole_name = fresh_identifier("zz", expr_text(instantiated_left), expr_text(right))
    context = app_context_text(substitute_expr(left.args[0], subst), instantiated_args, candidate_index - 1, hole_name)
    return (
        f"(fun Q:set->prop => fun H:Q ({expr_text(instantiated_left)}) => "
        f"{proof_term_text(argument_proof)} (fun {hole_name}:set => Q ({context})) H)"
    )


def oriented_rule_proof(rewrite: OrientedRuleRewrite, subst: dict[str, Expr], proof: str) -> str:
    if not rewrite.reverse:
        return proof
    conclusion = rule_application_conclusion(rewrite.rule)
    original_left = substitute_expr(conclusion.args[0], subst)
    return eq_symmetry_proof(proof, original_left)


def equality_two_rule_join_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    left_rewrites: list[OrientedRuleRewrite] = []
    right_rewrites: list[OrientedRuleRewrite] = []
    for index, rule in enumerate(rules):
        left_rewrites.extend(oriented_rule_rewrites_from(expr.args[0], rename_rule_binders(rule, f"L{index}_")))
        right_rewrites.extend(oriented_rule_rewrites_from(expr.args[1], rename_rule_binders(rule, f"R{index}_")))
    for left_rewrite in left_rewrites:
        for right_rewrite in right_rewrites:
            subst = merge_substitutions(left_rewrite.subst, right_rewrite.subst)
            if subst is None:
                continue
            variables = set(rule_application_binders(left_rewrite.rule)) | set(rule_application_binders(right_rewrite.rule))
            right_middle = substitute_expr(right_rewrite.middle, subst)
            middle_proof = None
            if match_expr(left_rewrite.middle, right_middle, variables, subst):
                flatten_substitution(subst)
            else:
                middle_subst = dict(subst)
                middle_proof = contextual_equality_proof(
                    left_rewrite.middle,
                    right_rewrite.middle,
                    variables,
                    middle_subst,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    rule_depth,
                )
                if middle_proof is None:
                    continue
                subst = middle_subst
                flatten_substitution(subst)
            left_parts = rule_application_parts(
                left_rewrite.rule,
                subst,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if left_parts is None:
                continue
            right_parts = rule_application_parts(
                right_rewrite.rule,
                subst,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if right_parts is None:
                continue
            left_proof = oriented_rule_proof(left_rewrite, subst, rule_application_text(left_parts))
            right_proof = oriented_rule_proof(right_rewrite, subst, rule_application_text(right_parts))
            proofs = [left_proof]
            if middle_proof is not None:
                proofs.append(middle_proof)
            proofs.append(eq_symmetry_proof(right_proof, expr.args[1]))
            return eq_transitivity_proof(
                proofs,
                expr_text(expr.args[0]),
            )
    return None


def equality_transport_side_proof(
    source: Expr,
    target: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr_key(source) == expr_key(target):
        return f"(fun Q:set->prop => fun H:Q ({expr_text(source)}) => H)"
    equality = Expr("eq", args=(source, target))
    proof = equality_direct_rule_proof(equality, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if proof is not None:
        return proof
    proof = equality_rewrite_join_proof(equality, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if proof is not None:
        return proof
    proof = equality_congruence_proof(equality, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if proof is not None:
        return proof
    proof = equality_multi_congruence_proof(equality, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if proof is not None:
        return proof
    proof = equality_rule_demodulation_proof(
        equality,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    )
    if proof is not None:
        return proof
    proof = equality_rule_chain_proof(
        equality,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        max_depth=4,
        rule_depth=rule_depth,
    )
    if proof is not None:
        return proof
    proof = proof_for_expr(
        equality,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=False,
        rule_depth=max(0, rule_depth - 1),
    )
    if proof is not None:
        return proof
    reverse = Expr("eq", args=(target, source))
    reverse_proof = proof_for_expr(
        reverse,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=False,
        rule_depth=max(0, rule_depth - 1),
    )
    if reverse_proof is None:
        return None
    return eq_symmetry_proof(reverse_proof, target)


def equality_rule_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    target_left = normalize_defined_expr(expr.args[0], definitions)
    target_right = normalize_defined_expr(expr.args[1], definitions)

    for rule_index, original_rule in enumerate(reversed(rules)):
        rule = rename_rule_binders(original_rule, f"ET{rule_index}_")
        conclusion = rule_application_conclusion(rule)
        if conclusion.kind != "eq":
            continue
        binders = rule_application_binders(rule)
        steps = rule.steps
        if not steps:
            steps = tuple(RuleStep("binder", name=binder) for binder in binders) + tuple(
                RuleStep("premise", expr=premise) for premise in rule.premises
            )
        if not any(step.kind == "premise" for step in steps):
            continue
        variables = set(binders)
        seed_substs: list[tuple[dict[str, Expr], list[Expr]]] = []
        for source_side, target_side, other_target_side in (
            (conclusion.args[0], target_left, target_right),
            (conclusion.args[1], target_right, target_left),
            (conclusion.args[0], target_right, target_left),
            (conclusion.args[1], target_left, target_right),
        ):
            trial: dict[str, Expr] = {}
            matched = match_expr(source_side, target_side, variables, trial)
            if matched or trial:
                terms = expr_subterms(other_target_side) + expr_subterms(target_side)
                terms.sort(key=lambda term: (len(expr_text(term)), expr_text(term)))
                seed_substs.append((trial, terms))
        deduped_seeds: list[dict[str, Expr]] = []
        seen_seed_keys: set[tuple[tuple[str, str], ...]] = set()
        for seed, terms in seed_substs:
            for filled_seed in fill_missing_binders_with_terms(binders, seed, terms, limit=64):
                key = tuple(sorted((name, expr_key(value)) for name, value in filled_seed.items()))
                if key in seen_seed_keys:
                    continue
                seen_seed_keys.add(key)
                deduped_seeds.append(filled_seed)
                if len(deduped_seeds) >= 128:
                    break
            if len(deduped_seeds) >= 128:
                break
        for seed in deduped_seeds:
            if all(binder in seed for binder in binders):
                candidates = [seed]
            else:
                candidates = infer_rule_binder_candidates_from_known(
                    steps,
                    binders,
                    seed,
                    known,
                    limit=8,
                    require_premise_match=True,
                )
            for subst in candidates:
                parts = rule_application_parts(
                    rule,
                    subst,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
                if parts is None:
                    continue
                source_left = normalize_defined_expr(substitute_expr(conclusion.args[0], subst), definitions)
                source_right = normalize_defined_expr(substitute_expr(conclusion.args[1], subst), definitions)
                source_proof = rule_application_text(parts)
                for left, right, equality_proof in (
                    (source_left, source_right, source_proof),
                    (source_right, source_left, eq_symmetry_proof(source_proof, source_left)),
                ):
                    left_transport = equality_transport_side_proof(
                        left,
                        target_left,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        max(0, rule_depth - 1),
                    )
                    if left_transport is None:
                        continue
                    right_transport = equality_transport_side_proof(
                        right,
                        target_right,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        max(0, rule_depth - 1),
                    )
                    if right_transport is None:
                        continue
                    return eq_transitivity_proof(
                        [
                            eq_symmetry_proof(left_transport, left),
                            equality_proof,
                            right_transport,
                        ],
                        expr_text(target_left),
                    )

        for subst in infer_rule_binder_candidates_from_known(
            steps,
            binders,
            {},
            known,
            limit=128,
            require_premise_match=True,
        ):
            parts = rule_application_parts(
                rule,
                subst,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if parts is None:
                continue
            source_left = normalize_defined_expr(substitute_expr(conclusion.args[0], subst), definitions)
            source_right = normalize_defined_expr(substitute_expr(conclusion.args[1], subst), definitions)
            source_proof = rule_application_text(parts)
            for left, right, equality_proof in (
                (source_left, source_right, source_proof),
                (source_right, source_left, eq_symmetry_proof(source_proof, source_left)),
            ):
                left_transport = equality_transport_side_proof(
                    left,
                    target_left,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
                if left_transport is None:
                    continue
                right_transport = equality_transport_side_proof(
                    right,
                    target_right,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
                if right_transport is None:
                    continue
                return eq_transitivity_proof(
                    [
                        eq_symmetry_proof(left_transport, left),
                        equality_proof,
                        right_transport,
                    ],
                    expr_text(target_left),
                )
    return None


def rule_application_parts(
    rule: ProofRule,
    subst: dict[str, Expr],
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> list[str] | None:
    application_binders = tuple(
        step.name for step in rule.steps if step.kind == "binder" and step.name is not None
    ) or rule.binders
    parts = [rule.name]
    steps: tuple[RuleStep, ...] = rule.steps
    if not steps:
        steps = tuple(RuleStep("binder", name=binder) for binder in application_binders) + tuple(
            RuleStep("premise", expr=premise) for premise in rule.premises
        )
    candidate_substs: list[dict[str, Expr]] = []
    candidate_substs.extend(infer_rule_binders_from_reflexive_premises(steps, application_binders, subst, limit=32))
    inferred_subst = infer_rule_binders_from_known(steps, application_binders, subst, known)
    if inferred_subst is not None:
        candidate_substs.append(inferred_subst)
    missing = [binder for binder in application_binders if binder not in subst]
    if 0 < len(missing) <= 2 and rule_depth > 0:
        seed_terms = candidate_terms_from_state(
            known,
            eq_facts,
            seed=list(subst.values()),
            exclude_names=set(application_binders),
            limit=80,
        )
        candidate_substs.extend(
            fill_missing_binders_with_terms(application_binders, subst, seed_terms, limit=160)
        )

    seen_substs: set[tuple[tuple[str, str], ...]] = set()
    for candidate_subst in candidate_substs:
        if not all(binder in candidate_subst for binder in application_binders):
            continue
        key = tuple(sorted((name, expr_key(value)) for name, value in candidate_subst.items()))
        if key in seen_substs:
            continue
        seen_substs.add(key)
        candidate_parts = list(parts)
        ok = True
        for step in steps:
            if step.kind == "binder":
                assert step.name is not None
                candidate_parts.append(proof_arg_text(candidate_subst[step.name]))
                continue
            assert step.expr is not None
            premise = substitute_expr(step.expr, candidate_subst)
            premise_proof = proof_for_expr(
                premise,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=rule_depth > 0,
                rule_depth=max(0, rule_depth - 1),
            )
            if premise_proof is None:
                premise_proof = direct_proof_expr(premise)
            if premise_proof is None and premise.kind == "forall" and rule_depth > 0:
                premise_proof = proof_for_expr(
                    premise,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=max(rule_depth, 2),
                )
            if premise_proof is None:
                ok = False
                break
            candidate_parts.append(proof_argument_text(premise_proof))
        if not ok:
            continue
        return candidate_parts
    return None


def rule_application_text(parts: list[str]) -> str:
    return parts[0] if len(parts) == 1 else f"({' '.join(parts)})"


def completed_rule_substs(
    rule: ProofRule,
    subst: dict[str, Expr],
    known: dict[str, str],
    eq_facts: list[EqFact],
    limit: int = 64,
) -> list[dict[str, Expr]]:
    if proof_search_timed_out():
        return []
    binders = rule_application_binders(rule)
    if all(binder in subst for binder in binders):
        return [dict(subst)]

    reflexive_candidates = infer_rule_binders_from_reflexive_premises(rule.steps, binders, subst, limit=limit)
    if reflexive_candidates:
        return reflexive_candidates[:limit]

    candidates = infer_rule_binder_candidates_from_known(
        rule.steps,
        binders,
        subst,
        known,
        limit=limit,
        require_premise_match=True,
    )
    if candidates:
        return candidates[:limit]

    terms = candidate_terms_from_state(
        known,
        eq_facts,
        seed=list(subst.values()),
        exclude_names=set(binders),
        limit=80,
    )
    return fill_missing_binders_with_terms(binders, subst, terms, limit=limit)


def rule_application_binders(rule: ProofRule) -> tuple[str, ...]:
    return tuple(
        step.name for step in rule.steps if step.kind == "binder" and step.name is not None
    ) or rule.binders


def rule_application_conclusion(rule: ProofRule) -> Expr:
    return rule.application_conclusion or rule.conclusion


def sequential_rule_steps(expr: Expr) -> tuple[list[RuleStep], Expr]:
    steps: list[RuleStep] = []
    current = expr
    while True:
        if current.kind == "forall":
            assert current.value is not None
            steps.append(RuleStep("binder", name=current.value))
            current = current.args[0]
            continue
        if current.kind == "arrow":
            steps.append(RuleStep("premise", expr=current.args[0]))
            current = current.args[1]
            continue
        return steps, current


def sequential_rule_application_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    seen_names: set[str] = set()
    for proposition, rule_name in reversed(list(known.items())):
        if rule_name in seen_names:
            continue
        seen_names.add(rule_name)
        rule_expr = parse_expr(proposition)
        if rule_expr is None:
            continue
        steps, conclusion = sequential_rule_steps(rule_expr)
        binders = tuple(step.name for step in steps if step.kind == "binder" and step.name is not None)
        if not binders or not any(step.kind == "premise" for step in steps):
            continue
        subst: dict[str, Expr] = {}
        if not match_expr(conclusion, expr, set(binders), subst):
            continue
        inferred_subst = infer_rule_binders_from_known(tuple(steps), binders, subst, known)
        if inferred_subst is None:
            continue
        subst = inferred_subst
        parts = [rule_name]
        ok = True
        for step in steps:
            if step.kind == "binder":
                assert step.name is not None
                parts.append(proof_arg_text(subst[step.name]))
                continue
            assert step.expr is not None
            premise = substitute_expr(step.expr, subst)
            premise_proof = proof_for_expr(
                premise,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=True,
                rule_depth=rule_depth - 1,
            )
            if premise_proof is None and premise.kind == "forall" and rule_depth > 0:
                premise_proof = proof_for_expr(
                    premise,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=rule_depth,
                )
            if premise_proof is None:
                ok = False
                break
            parts.append(proof_argument_text(premise_proof))
        if ok:
            return rule_application_text(parts)
    return None


def equality_rule_chain_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    max_depth: int = 4,
    rule_depth: int = 2,
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
                conclusion = rule_application_conclusion(rule)
                if conclusion.kind != "eq":
                    continue
                variables = set(rule_application_binders(rule))
                direct_subst: dict[str, Expr] = {}
                if match_expr(conclusion.args[0], arg, variables, direct_subst):
                    for candidate_subst in completed_rule_substs(rule, direct_subst, known, eq_facts):
                        source = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                        if expr_key(source) != expr_key(arg):
                            continue
                        parts = rule_application_parts(rule, candidate_subst, known, known_canonical, rules, eq_facts, definitions, max(0, rule_depth - 1))
                        if parts is not None:
                            replacement = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                            if expr_key(replacement) != arg_key:
                                rewrites.append((replacement, rule_application_text(parts)))
                reverse_subst: dict[str, Expr] = {}
                if match_expr(conclusion.args[1], arg, variables, reverse_subst):
                    for candidate_subst in completed_rule_substs(rule, reverse_subst, known, eq_facts):
                        source = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                        if expr_key(source) != expr_key(arg):
                            continue
                        parts = rule_application_parts(rule, candidate_subst, known, known_canonical, rules, eq_facts, definitions, max(0, rule_depth - 1))
                        if parts is not None:
                            proof = rule_application_text(parts)
                            replacement = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                            if expr_key(replacement) != arg_key:
                                rewrites.append((replacement, eq_symmetry_proof(proof, replacement)))
            for replacement, argument_proof in rewrites:
                next_args = args.copy()
                next_args[index] = replacement
                hole_name = fresh_identifier("zz", expr_text(node), expr_text(replacement))
                context = app_context_text(node.args[0], tuple(node.args[1:]), index - 1, hole_name)
                proof = (
                    f"(fun Q:set->prop => fun H:Q ({expr_text(node)}) => "
                    f"{proof_term_text(argument_proof)} (fun {hole_name}:set => Q ({context})) H)"
                )
                found.append((Expr("app", args=tuple(next_args)), proof))
        return found

    def edges(node: Expr) -> list[tuple[Expr, str]]:
        if proof_search_timed_out():
            return []
        found: list[tuple[Expr, str]] = []
        for fact in eq_facts:
            if proof_search_timed_out():
                return found
            if expr_key(normalize_defined_expr(fact.left, definitions)) == expr_key(node):
                found.append((normalize_defined_expr(fact.right, definitions), fact.proof))
            if expr_key(normalize_defined_expr(fact.right, definitions)) == expr_key(node):
                found.append((normalize_defined_expr(fact.left, definitions), eq_symmetry_proof(fact.proof, fact.left)))
        for rule in rules:
            if proof_search_timed_out():
                return found
            conclusion = rule_application_conclusion(rule)
            if conclusion.kind != "eq":
                continue
            variables = set(rule_application_binders(rule))
            direct_subst: dict[str, Expr] = {}
            if match_expr(conclusion.args[0], node, variables, direct_subst):
                for candidate_subst in completed_rule_substs(rule, direct_subst, known, eq_facts):
                    source = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                    if expr_key(source) != expr_key(node):
                        continue
                    parts = rule_application_parts(rule, candidate_subst, known, known_canonical, rules, eq_facts, definitions, max(0, rule_depth - 1))
                    if parts is not None:
                        replacement = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                        if expr_key(replacement) != expr_key(node):
                            found.append((replacement, rule_application_text(parts)))
            reverse_subst: dict[str, Expr] = {}
            if match_expr(conclusion.args[1], node, variables, reverse_subst):
                for candidate_subst in completed_rule_substs(rule, reverse_subst, known, eq_facts):
                    source = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                    if expr_key(source) != expr_key(node):
                        continue
                    parts = rule_application_parts(rule, candidate_subst, known, known_canonical, rules, eq_facts, definitions, max(0, rule_depth - 1))
                    if parts is not None:
                        proof = rule_application_text(parts)
                        replacement = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                        if expr_key(replacement) != expr_key(node):
                            found.append((replacement, eq_symmetry_proof(proof, replacement)))
        found.extend(congruence_edges(node))
        return found

    queue: list[tuple[Expr, list[str]]] = [(start, [])]
    seen = {expr_key(start)}
    while queue:
        if proof_search_timed_out():
            return None
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
    rule_depth: int,
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
    used_names = set(args)
    used_names.update(known.values())
    for index, premise in enumerate(premises):
        name = "H" + str(index)
        while name in used_names:
            index += 1
            name = "H" + str(index)
        used_names.add(name)
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
        rule_depth=rule_depth,
    )
    if proof is None and conclusion.kind == "eq":
        proof = equality_rule_transport_proof(
            conclusion,
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            definitions,
            rule_depth,
        )
    if proof is None:
        return None
    return f"({' '.join(['fun'] + args + ['=>', proof])})"


def introduced_unary_equality_bridge_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if not binders or conclusion.kind != "eq" or len(premises) > 4:
        return None

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    args = [name for name, _ in binders]
    used_names = set(args)
    used_names.update(known.values())
    for index, premise in enumerate(premises):
        name = "H" + str(index)
        while name in used_names:
            index += 1
            name = "H" + str(index)
        used_names.add(name)
        args.append(name)
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )

    proof = unary_equality_rule_bridge_proof(
        conclusion,
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        definitions,
        rule_depth,
    )
    if proof is None:
        return None
    return f"({' '.join(['fun'] + args + ['=>', proof])})"


def one_rewrite_transport_side_proof(
    source: Expr,
    target: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr_key(source) == expr_key(target):
        return "(fun Q H => H)"
    target_subterms = expr_subterms(target, limit=32)
    seen_pairs: set[tuple[str, str]] = set()
    for old in expr_subterms(source, limit=32):
        for new in target_subterms:
            key = (expr_key(old), expr_key(new))
            if key in seen_pairs or key[0] == key[1]:
                continue
            seen_pairs.add(key)
            replaced, changed = replace_expr(source, old, new)
            if not changed or expr_key(replaced) != expr_key(target):
                continue
            equality = Expr("eq", args=(old, new))
            equality_proof = equality_direct_rule_proof(
                equality,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                rule_depth,
            )
            if equality_proof is None:
                reverse = Expr("eq", args=(new, old))
                reverse_proof = equality_direct_rule_proof(
                    reverse,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    rule_depth,
                )
                if reverse_proof is None:
                    continue
                equality_proof = eq_symmetry_proof(reverse_proof, new)
            hole_name = fresh_identifier("zz", expr_text(source), expr_text(target))
            context, context_changed = replace_expr(source, old, Expr("var", value=hole_name))
            if not context_changed:
                continue
            return (
                f"{proof_term_text(equality_proof)} "
                f"(fun {hole_name}:set => {expr_text(source)} = {expr_text(context)}) "
                f"(fun R Hr => Hr)"
            )
    return None


def introduced_equality_one_rewrite_rule_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if (
        not binders
        or len(binders) > 5
        or not (2 <= len(premises) <= 6)
        or not (2 <= len(rules) <= 5)
        or conclusion.kind != "eq"
    ):
        return None

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    args = [name for name, _ in binders]
    used_names = set(args)
    used_names.update(known.values())
    for index, premise in enumerate(premises):
        name = "H" + str(index)
        while name in used_names:
            index += 1
            name = "H" + str(index)
        used_names.add(name)
        args.append(name)
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )

    target_left = normalize_defined_expr(conclusion.args[0], definitions)
    target_right = normalize_defined_expr(conclusion.args[1], definitions)
    for rule_index, original_rule in enumerate(reversed(local_rules)):
        rule = rename_rule_binders(original_rule, f"IOR{rule_index}_")
        rule_conclusion = rule_application_conclusion(rule)
        if rule_conclusion.kind != "eq":
            continue
        rule_binders = rule_application_binders(rule)
        variables = set(rule_binders)
        for matched_side, moving_side, reverse_base in (
            (rule_conclusion.args[0], rule_conclusion.args[1], False),
            (rule_conclusion.args[1], rule_conclusion.args[0], True),
        ):
            subst: dict[str, Expr] = {}
            if not match_expr(matched_side, target_left, variables, subst):
                continue
            terms = expr_subterms(target_right, limit=32)
            terms.sort(key=lambda term: (len(expr_text(term)), expr_text(term)))
            for candidate_subst in fill_missing_binders_with_terms(rule_binders, subst, terms, limit=48):
                if not all(binder in candidate_subst for binder in rule_binders):
                    continue
                source = normalize_defined_expr(substitute_expr(moving_side, candidate_subst), definitions)
                side_prefix = one_rewrite_transport_side_proof(
                    source,
                    target_right,
                    local_known,
                    local_known_canonical,
                    local_rules,
                    local_eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
                if side_prefix is None:
                    continue
                parts = rule_application_parts(
                    rule,
                    candidate_subst,
                    local_known,
                    local_known_canonical,
                    local_rules,
                    local_eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
                if parts is None:
                    continue
                base_proof = rule_application_text(parts)
                if reverse_base:
                    base_proof = eq_symmetry_proof(base_proof, source)
                proof = eq_transitivity_proof([base_proof, side_prefix], expr_text(target_left))
                if proof is not None:
                    return f"({' '.join(['fun'] + args + ['=>', proof])})"
    return None


def introduced_atomic_rule_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if (
        conclusion.kind != "app"
        or not binders
        or len(binders) > 4
        or len(premises) > 6
        or not (5 <= len(rules) <= 8)
        or len(expr_text(expr)) > 700
    ):
        return None
    for rule in rules:
        rule_binders = rule_application_binders(rule)
        if len(rule_binders) != 2:
            continue
        rule_conclusion = rule_application_conclusion(rule)
        if rule_conclusion.kind != "eq":
            continue
        left = rule_conclusion.args[0]
        right = rule_conclusion.args[1]
        if (
            left.kind == "app"
            and right.kind == "app"
            and len(left.args) == 3
            and len(right.args) == 3
            and expr_key(left.args[0]) == expr_key(right.args[0])
            and left.args[1].kind == "var"
            and left.args[2].kind == "var"
            and right.args[1].kind == "var"
            and right.args[2].kind == "var"
            and left.args[1].value == rule_binders[0]
            and left.args[2].value == rule_binders[1]
            and right.args[1].value == rule_binders[1]
            and right.args[2].value == rule_binders[0]
        ):
            return None

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    args = [name for name, _ in binders]
    used_names = set(args)
    used_names.update(known.values())
    for index, premise in enumerate(premises):
        name = "H" + str(index)
        while name in used_names:
            index += 1
            name = "H" + str(index)
        used_names.add(name)
        args.append(name)
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )

    proof = atomic_rule_transport_proof(
        conclusion,
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        definitions,
        rule_depth,
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
    rule_depth: int,
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
        allow_rule=rule_depth > 0,
        rule_depth=max(0, rule_depth - 1),
    )
    if argument_proof is None:
        return None

    hole_name = fresh_identifier("zz", expr_text(left), expr_text(right))
    context = app_context_text(left.args[0], left.args[1:], arg_index, hole_name)
    return (
        f"(fun Q:set->prop => fun H:Q ({expr_text(left)}) => "
        f"{proof_term_text(argument_proof)} (fun {hole_name}:set => Q ({context})) H)"
    )


def equality_multi_congruence_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
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
    if len(different) < 2 or len(different) > 4:
        return None

    current_args = list(left.args[1:])
    proofs: list[str] = []
    for arg_index in different:
        current_arg = current_args[arg_index]
        target_arg = right.args[arg_index + 1]
        argument_equality = Expr("eq", args=(current_arg, target_arg))
        argument_proof = proof_for_expr(
            argument_equality,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=rule_depth > 0,
            rule_depth=max(0, rule_depth - 1),
        )
        if argument_proof is None:
            argument_proof = equality_rewrite_join_proof(
                argument_equality,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
        if argument_proof is None:
            reverse_equality = Expr("eq", args=(target_arg, current_arg))
            reverse_proof = proof_for_expr(
                reverse_equality,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=rule_depth > 0,
                rule_depth=max(0, rule_depth - 1),
            )
            if reverse_proof is None:
                reverse_proof = equality_rewrite_join_proof(
                    reverse_equality,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    max(0, rule_depth - 1),
                )
            if reverse_proof is not None:
                argument_proof = eq_symmetry_proof(reverse_proof, target_arg)
        if argument_proof is None:
            return None

        current = Expr("app", args=(left.args[0],) + tuple(current_args))
        hole_name = fresh_identifier("zz", expr_text(current), expr_text(right))
        context = app_context_text(left.args[0], tuple(current_args), arg_index, hole_name)
        proofs.append(
            f"(fun Q:set->prop => fun H:Q ({expr_text(current)}) => "
            f"{proof_term_text(argument_proof)} (fun {hole_name}:set => Q ({context})) H)"
        )
        current_args[arg_index] = target_arg

    return eq_transitivity_proof(proofs, expr_text(left))


def unary_equality_rule_bridge_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    left = normalize_defined_expr(expr.args[0], definitions)
    right = normalize_defined_expr(expr.args[1], definitions)
    left_app = unary_application(left)
    right_app = unary_application(right)
    if left_app is None or right_app is None or left_app[0] != right_app[0]:
        return None
    target_arg = right_app[1]

    for rule in rules:
        conclusion = rule_application_conclusion(rule)
        if conclusion.kind != "eq":
            continue
        sides = (conclusion.args[0], conclusion.args[1])
        for match_index, other_index in ((0, 1), (1, 0)):
            subst: dict[str, Expr] = {}
            if not match_expr_with_alpha_instantiation(
                sides[match_index],
                left,
                set(rule_application_binders(rule)),
                subst,
            ):
                continue
            other_side = normalize_defined_expr(substitute_expr(sides[other_index], subst), definitions)
            other_app = unary_application(other_side)
            if other_app is None or other_app[0] != left_app[0]:
                continue
            parts = rule_application_parts(
                rule,
                subst,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if parts is None:
                continue
            rule_proof = rule_application_text(parts)
            if match_index == 0:
                left_to_other = rule_proof
            else:
                original_left = normalize_defined_expr(substitute_expr(sides[0], subst), definitions)
                left_to_other = eq_symmetry_proof(rule_proof, original_left)
            other_to_target_arg = equality_transport_side_proof(
                other_app[1],
                target_arg,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if other_to_target_arg is None:
                continue
            hole_name = fresh_identifier("zz", expr_text(other_side), expr_text(right))
            other_to_target = (
                f"(fun Q:set->prop => fun H:Q ({expr_text(other_side)}) => "
                f"{proof_head(other_to_target_arg)} "
                f"(fun {hole_name}:set => Q ({left_app[0]} {hole_name})) H)"
            )
            return eq_transitivity_proof([left_to_other, other_to_target], expr_text(left))
    return None


def equality_direct_demodulation_proof(
    expr: Expr,
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    max_steps: int = 4,
    max_nodes: int = 64,
) -> str | None:
    if expr.kind != "eq" or not eq_facts:
        return None
    start = normalize_defined_expr(expr.args[0], definitions)
    target = normalize_defined_expr(expr.args[1], definitions)
    if expr_key(start) == expr_key(target):
        return "(fun Q H => H)"
    if start.kind == "lambda" or target.kind == "lambda":
        return None
    if len(expr_text(start)) > 5000 or len(expr_text(target)) > 5000 or len(eq_facts) > 12:
        return None

    rewrites: list[tuple[Expr, Expr, str]] = []
    for fact in eq_facts:
        for source, replacement, proof in (
            (fact.left, fact.right, fact.proof),
            (fact.right, fact.left, eq_symmetry_proof(fact.proof, fact.left)),
        ):
            source = normalize_defined_expr(source, definitions)
            replacement = normalize_defined_expr(replacement, definitions)
            if expr_key(source) == expr_key(replacement):
                continue
            if source.kind in {"forall", "arrow", "lambda"}:
                continue
            rewrites.append((source, replacement, proof))

    queue: list[tuple[Expr, list[str]]] = [(start, [])]
    seen = {expr_key(start)}
    while queue and len(seen) <= max_nodes:
        node, proofs = queue.pop(0)
        if len(proofs) >= max_steps:
            continue
        for source, replacement, equality_proof in rewrites:
            if expr_text(source) not in expr_text(node):
                continue
            hole_name = fresh_identifier("zz", expr_text(node), expr_text(source), expr_text(replacement))
            hole = Expr("var", value=hole_name)
            for next_node, context in single_replacement_contexts(
                node,
                source,
                replacement,
                hole,
                limit=4,
            ):
                next_key = expr_key(normalize_defined_expr(next_node, definitions))
                if next_key in seen:
                    continue
                proof = (
                    f"(fun Q:set->prop => fun H:Q ({expr_text(node)}) => "
                    f"{proof_head(equality_proof)} (fun {hole_name}:set => Q ({expr_text(context)})) H)"
                )
                next_proofs = proofs + [proof]
                if next_key == expr_key(target):
                    return eq_transitivity_proof(next_proofs, expr_text(start))
                seen.add(next_key)
                queue.append((normalize_defined_expr(next_node, definitions), next_proofs))
                if len(seen) > max_nodes:
                    break
            if len(seen) > max_nodes:
                break
    return None


def equality_rule_demodulation_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
    max_steps: int = 4,
    max_nodes: int = 48,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    start = normalize_defined_expr(expr.args[0], definitions)
    target = normalize_defined_expr(expr.args[1], definitions)
    if expr_key(start) == expr_key(target):
        return "(fun Q H => H)"
    if start.kind == "lambda" or target.kind == "lambda":
        return None
    target_text = expr_text(target)
    if len(expr_text(start)) > 3000 or len(target_text) > 3000 or len(rules) > 24:
        return None

    equality_rules = [
        rule
        for rule in rules
        if rule_application_conclusion(rule).kind == "eq"
        and len(rule_application_binders(rule)) <= 6
        and len(rule.premises) <= 8
    ]
    if not equality_rules:
        return None

    def rewrites_for_term(term: Expr) -> list[tuple[Expr, str]]:
        if term.kind in {"forall", "arrow", "lambda"}:
            return []
        found: list[tuple[Expr, str]] = []
        for rule in equality_rules:
            conclusion = rule_application_conclusion(rule)
            variables = set(rule_application_binders(rule))
            direct_subst: dict[str, Expr] = {}
            if match_expr_with_alpha_instantiation(conclusion.args[0], term, variables, direct_subst):
                for candidate_subst in completed_rule_substs(rule, direct_subst, known, eq_facts):
                    source = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                    if expr_key(source) != expr_key(term):
                        continue
                    parts = rule_application_parts(
                        rule,
                        candidate_subst,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        max(0, rule_depth - 1),
                    )
                    if parts is not None:
                        replacement = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                        if expr_key(replacement) != expr_key(term) and expr_text(replacement) in target_text:
                            found.append((replacement, rule_application_text(parts)))
            reverse_subst: dict[str, Expr] = {}
            if match_expr_with_alpha_instantiation(conclusion.args[1], term, variables, reverse_subst):
                for candidate_subst in completed_rule_substs(rule, reverse_subst, known, eq_facts):
                    source = normalize_defined_expr(substitute_expr(conclusion.args[1], candidate_subst), definitions)
                    if expr_key(source) != expr_key(term):
                        continue
                    parts = rule_application_parts(
                        rule,
                        candidate_subst,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        max(0, rule_depth - 1),
                    )
                    if parts is not None:
                        replacement = normalize_defined_expr(substitute_expr(conclusion.args[0], candidate_subst), definitions)
                        if expr_key(replacement) != expr_key(term) and expr_text(replacement) in target_text:
                            proof = rule_application_text(parts)
                            found.append((replacement, eq_symmetry_proof(proof, replacement)))
        return found[:8]

    queue: list[tuple[Expr, list[str]]] = [(start, [])]
    seen = {expr_key(start)}
    while queue and len(seen) <= max_nodes:
        node, proofs = queue.pop(0)
        if len(proofs) >= max_steps:
            continue
        subterms = [
            term for term in expr_argument_subterms(node, limit=80)
            if expr_key(term) != expr_key(node) and expr_text(term) not in target_text
        ]
        subterms.sort(key=lambda term: (-len(expr_text(term)), expr_text(term)))
        for subterm in subterms[:48]:
            for replacement, equality_proof in rewrites_for_term(subterm):
                hole_name = fresh_identifier("zz", expr_text(node), expr_text(subterm), expr_text(replacement))
                hole = Expr("var", value=hole_name)
                for next_node, context in single_replacement_contexts(
                    node,
                    subterm,
                    replacement,
                    hole,
                    limit=2,
                ):
                    next_node = normalize_defined_expr(next_node, definitions)
                    next_key = expr_key(next_node)
                    if next_key in seen:
                        continue
                    proof = (
                        f"(fun Q:set->prop => fun H:Q ({expr_text(node)}) => "
                        f"{proof_head(equality_proof)} (fun {hole_name}:set => Q ({expr_text(context)})) H)"
                    )
                    next_proofs = proofs + [proof]
                    if next_key == expr_key(target):
                        return eq_transitivity_proof(next_proofs, expr_text(start))
                    seen.add(next_key)
                    queue.append((next_node, next_proofs))
                    if len(seen) > max_nodes:
                        break
                if len(seen) > max_nodes:
                    break
            if len(seen) > max_nodes:
                break
    return None


def atomic_transport_context(head: Expr, args: tuple[Expr, ...], hole_index: int, hole_name: str) -> str:
    parts = [expr_text(head)]
    for index, arg in enumerate(args):
        parts.append(hole_name if index == hole_index else proof_arg_text(arg))
    return " ".join(parts)


def transport_atomic_argument_proof(
    target: Expr,
    current_args: list[Expr],
    proof: str,
    index: int,
    equality_proof: str,
) -> str:
    hole_name = fresh_identifier("zz", expr_text(target))
    context = atomic_transport_context(target.args[0], tuple(current_args), index, hole_name)
    return f"{proof_term_text(equality_proof)} (fun {hole_name}:set => {context}) ({proof})"


def atomic_transport_context_with_arg_text(
    head: Expr,
    args: tuple[Expr, ...],
    replace_index: int,
    replacement_text: str,
) -> str:
    parts = [expr_text(head)]
    for index, arg in enumerate(args):
        parts.append(f"({replacement_text})" if index == replace_index else proof_arg_text(arg))
    return " ".join(parts)


def transport_atomic_nested_app_arguments_proof(
    target: Expr,
    current_args: list[Expr],
    proof: str,
    index: int,
    source_arg: Expr,
    target_arg: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool,
    rule_depth: int,
) -> tuple[str, Expr] | None:
    source_app = normalize_defined_expr(source_arg, definitions)
    target_app = normalize_defined_expr(target_arg, definitions)
    if (
        source_app.kind != "app"
        or target_app.kind != "app"
        or len(source_app.args) != len(target_app.args)
        or len(source_app.args) < 2
        or expr_key(source_app.args[0]) != expr_key(target_app.args[0])
    ):
        return None

    current_inner_args = list(source_app.args[1:])
    current_top_args = list(current_args)
    current_top_args[index] = Expr("app", args=(source_app.args[0],) + tuple(current_inner_args))
    nested_proof = proof
    changed = False
    for inner_index, (current_inner, target_inner) in enumerate(zip(current_inner_args, target_app.args[1:])):
        if expr_key(current_inner) == expr_key(target_inner):
            continue
        equality = Expr("eq", args=(current_inner, target_inner))
        equality_proof = proof_for_expr(
            equality,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=allow_rule,
            rule_depth=rule_depth,
        )
        if equality_proof is None:
            reverse_equality = Expr("eq", args=(target_inner, current_inner))
            reverse_proof = proof_for_expr(
                reverse_equality,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=allow_rule,
                rule_depth=rule_depth,
            )
            if reverse_proof is not None:
                equality_proof = eq_symmetry_proof(reverse_proof, target_inner)
        if equality_proof is None:
            return None

        hole_name = fresh_identifier("zz", expr_text(target), expr_text(source_app), expr_text(target_app))
        nested_context = app_context_text(source_app.args[0], tuple(current_inner_args), inner_index, hole_name)
        context = atomic_transport_context_with_arg_text(
            target.args[0],
            tuple(current_top_args),
            index,
            nested_context,
        )
        nested_proof = f"{proof_term_text(equality_proof)} (fun {hole_name}:set => {context}) ({nested_proof})"
        current_inner_args[inner_index] = target_inner
        current_top_args[index] = Expr("app", args=(source_app.args[0],) + tuple(current_inner_args))
        changed = True

    if not changed:
        return None
    return nested_proof, current_top_args[index]


def atomic_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool,
    rule_depth: int,
) -> str | None:
    if expr.kind != "app" or len(expr.args) < 2:
        return None

    target = normalize_defined_expr(expr, definitions)
    if target.kind != "app" or len(target.args) < 2:
        return None

    seen: set[str] = set()
    for proposition, known_proof in list(known.items()):
        if proposition in seen:
            continue
        seen.add(proposition)
        source = parse_expr(proposition)
        if source is None:
            continue
        source = normalize_defined_expr(source, definitions)
        if source.kind != "app" or len(source.args) != len(target.args):
            continue
        if expr_key(source.args[0]) != expr_key(target.args[0]):
            continue

        current_args = list(source.args[1:])
        proof = known_proof
        ok = True
        for index, (current_arg, target_arg) in enumerate(zip(current_args, target.args[1:])):
            if expr_key(current_arg) == expr_key(target_arg):
                continue
            nested = transport_atomic_nested_app_arguments_proof(
                target,
                current_args,
                proof,
                index,
                current_arg,
                target_arg,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule,
                rule_depth,
            )
            if nested is not None:
                proof, rewritten_arg = nested
                current_args[index] = rewritten_arg
                continue
            equality = Expr("eq", args=(current_arg, target_arg))
            equality_proof = proof_for_expr(
                equality,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=allow_rule,
                rule_depth=rule_depth,
            )
            if equality_proof is None:
                reverse_equality = Expr("eq", args=(target_arg, current_arg))
                reverse_proof = proof_for_expr(
                    reverse_equality,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=allow_rule,
                    rule_depth=rule_depth,
                )
                if reverse_proof is not None:
                    equality_proof = eq_symmetry_proof(reverse_proof, target_arg)
            if equality_proof is None:
                ok = False
                break
            proof = transport_atomic_argument_proof(target, current_args, proof, index, equality_proof)
            current_args[index] = target_arg
        if ok:
            return proof
    return None


def equality_rewrites_to_target(
    target: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> list[tuple[Expr, str]]:
    found: list[tuple[Expr, str]] = []
    target_key = expr_key(normalize_defined_expr(target, definitions))
    for fact in eq_facts:
        left = normalize_defined_expr(fact.left, definitions)
        right = normalize_defined_expr(fact.right, definitions)
        if expr_key(right) == target_key:
            found.append((left, fact.proof))
        if expr_key(left) == target_key:
            found.append((right, eq_symmetry_proof(fact.proof, fact.left)))

    if rule_depth <= 0:
        return found

    for rule in rules:
        conclusion = rule_application_conclusion(rule)
        if conclusion.kind != "eq":
            continue
        variables = set(rule_application_binders(rule))
        direct_subst: dict[str, Expr] = {}
        if match_expr(conclusion.args[1], target, variables, direct_subst):
            parts = rule_application_parts(rule, direct_subst, known, known_canonical, rules, eq_facts, definitions, rule_depth - 1)
            if parts is not None:
                source = normalize_defined_expr(substitute_expr(conclusion.args[0], direct_subst), definitions)
                found.append((source, rule_application_text(parts)))
        reverse_subst: dict[str, Expr] = {}
        if match_expr(conclusion.args[0], target, variables, reverse_subst):
            parts = rule_application_parts(rule, reverse_subst, known, known_canonical, rules, eq_facts, definitions, rule_depth - 1)
            if parts is not None:
                source = normalize_defined_expr(substitute_expr(conclusion.args[1], reverse_subst), definitions)
                proof = rule_application_text(parts)
                found.append((source, eq_symmetry_proof(proof, target)))
    return found


def equality_rewrite_join_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    left = normalize_defined_expr(expr.args[0], definitions)
    target = normalize_defined_expr(expr.args[1], definitions)
    if expr_key(left) == expr_key(target):
        return "(fun Q H => H)"
    for middle, middle_to_target in equality_rewrites_to_target(
        target,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    ):
        if expr_key(middle) == expr_key(left):
            return middle_to_target
        left_to_middle = equality_congruence_proof(
            Expr("eq", args=(left, middle)),
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            max(0, rule_depth - 1),
        )
        if left_to_middle is None:
            left_to_middle = equality_multi_congruence_proof(
                Expr("eq", args=(left, middle)),
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
        if left_to_middle is None:
            continue
        return eq_transitivity_proof([left_to_middle, middle_to_target], expr_text(left))
    return None


def atomic_rewrite_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    target = normalize_defined_expr(expr, definitions)
    if target.kind != "app" or len(target.args) < 2:
        return None

    target_args = list(target.args[1:])
    for index, target_arg in enumerate(target_args):
        for source_arg, equality_proof in equality_rewrites_to_target(
            target_arg,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        ):
            if expr_key(source_arg) == expr_key(target_arg):
                continue
            source_args = target_args.copy()
            source_args[index] = source_arg
            source = Expr("app", args=(target.args[0],) + tuple(source_args))
            source_proof = proof_for_expr(
                source,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=True,
                rule_depth=rule_depth - 1,
            )
            if source_proof is None:
                continue
            return transport_atomic_argument_proof(target, source_args, source_proof, index, equality_proof)
    return None


def atomic_multi_rewrite_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 1:
        return None
    target = normalize_defined_expr(expr, definitions)
    if target.kind != "app" or len(target.args) < 3:
        return None

    target_args = list(target.args[1:])
    choices: list[list[tuple[Expr, str | None]]] = []
    for target_arg in target_args:
        argument_choices: list[tuple[Expr, str | None]] = [(target_arg, None)]
        seen = {expr_key(target_arg)}
        for source_arg, equality_proof in equality_rewrites_to_target(
            target_arg,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        ):
            source_key = expr_key(source_arg)
            if source_key in seen:
                continue
            seen.add(source_key)
            argument_choices.append((source_arg, equality_proof))
            if len(argument_choices) >= 4:
                break
        choices.append(argument_choices)

    tried = 0
    max_changed_arguments = 2
    max_sources = 48

    def search(
        index: int,
        source_args: list[Expr],
        transports: list[tuple[int, str]],
        changed: int,
    ) -> str | None:
        nonlocal tried
        if changed > max_changed_arguments or tried >= max_sources:
            return None
        if index == len(choices):
            if changed < 2:
                return None
            tried += 1
            source = Expr("app", args=(target.args[0],) + tuple(source_args))
            source_proof = proof_for_expr(
                source,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                allow_rule=True,
                rule_depth=rule_depth - 1,
            )
            if source_proof is None:
                return None
            proof = source_proof
            current_args = source_args.copy()
            for transport_index, equality_proof in transports:
                proof = transport_atomic_argument_proof(target, current_args, proof, transport_index, equality_proof)
                current_args[transport_index] = target_args[transport_index]
            return proof

        for source_arg, equality_proof in choices[index]:
            if equality_proof is None:
                proof = search(index + 1, source_args + [source_arg], transports, changed)
            else:
                proof = search(
                    index + 1,
                    source_args + [source_arg],
                    transports + [(index, equality_proof)],
                    changed + 1,
                )
            if proof is not None:
                return proof
        return None

    return search(0, [], [], 0)


def atomic_rule_premise_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    target = normalize_defined_expr(expr, definitions)
    if target.kind != "app" or len(target.args) < 2:
        return None
    if target.args[0].kind != "var" or str(target.args[0].value or "").startswith("vampire_"):
        return None

    known_atoms: list[Expr] = []
    seen_known: set[str] = set()
    for proposition in known:
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        parsed = normalize_defined_expr(parsed, definitions)
        key = expr_key(parsed)
        if key in seen_known:
            continue
        seen_known.add(key)
        if parsed.kind == "app" and len(parsed.args) == len(target.args):
            known_atoms.append(parsed)

    seed_terms: list[Expr] = []
    seen_terms: set[str] = set()

    def add_terms(expr: Expr, limit: int = 32) -> None:
        for term in expr_subterms(expr, limit=limit):
            key = expr_key(term)
            if key in seen_terms:
                continue
            seen_terms.add(key)
            seed_terms.append(term)

    for proposition in known:
        parsed = parse_expr(proposition)
        if parsed is not None:
            parsed = normalize_defined_expr(parsed, definitions)
        if parsed is not None and parsed.kind == "app" and len(parsed.args) >= 2:
            for arg in parsed.args[1:]:
                add_terms(arg, limit=16)
        if len(seed_terms) >= 48:
            break
    for atom in known_atoms:
        for arg in atom.args[1:]:
            add_terms(arg, limit=24)
    for fact in eq_facts:
        add_terms(fact.left, limit=16)
        add_terms(fact.right, limit=16)
    for arg in target.args[1:]:
        add_terms(arg, limit=24)

    for rule_index, original_rule in enumerate(reversed(rules)):
        if len(original_rule.premises) > 5:
            continue
        rule = rename_rule_binders(original_rule, f"PT{rule_index}_")
        conclusion = rule_application_conclusion(rule)
        if conclusion.kind != "app" or len(conclusion.args) != len(target.args):
            continue
        binders = rule_application_binders(rule)
        variables = set(binders)
        initial_subst: dict[str, Expr] = {}
        if not match_expr(conclusion.args[0], target.args[0], variables, initial_subst):
            continue
        steps = rule.steps
        if not steps:
            steps = tuple(RuleStep("binder", name=binder) for binder in binders) + tuple(
                RuleStep("premise", expr=premise) for premise in rule.premises
            )
        premise_steps = [step for step in steps if step.kind == "premise" and step.expr is not None]
        if not premise_steps:
            continue
        tried: set[tuple[tuple[str, str], ...]] = set()
        for step in premise_steps:
            assert step.expr is not None
            for atom in known_atoms:
                trial = dict(initial_subst)
                if not match_expr(step.expr, atom, variables, trial):
                    continue
                for subst in fill_missing_binders_with_terms(binders, trial, seed_terms, limit=64):
                    key = tuple(sorted((name, expr_key(value)) for name, value in subst.items()))
                    if key in tried:
                        continue
                    tried.add(key)
                    source = normalize_defined_expr(substitute_expr(conclusion, subst), definitions)
                    if source.kind != "app" or len(source.args) != len(target.args):
                        continue
                    if expr_key(source.args[0]) != expr_key(target.args[0]):
                        continue
                    changed = [
                        index
                        for index, (source_arg, target_arg) in enumerate(zip(source.args[1:], target.args[1:]))
                        if expr_key(source_arg) != expr_key(target_arg)
                    ]
                    if len(changed) > 2:
                        continue
                    previous_premise_transport = getattr(PROOF_SEARCH_STATE, "in_premise_transport", False)
                    PROOF_SEARCH_STATE.in_premise_transport = True
                    try:
                        parts = rule_application_parts(
                            rule,
                            subst,
                            known,
                            known_canonical,
                            rules,
                            eq_facts,
                            definitions,
                            rule_depth + 1,
                        )
                    finally:
                        PROOF_SEARCH_STATE.in_premise_transport = previous_premise_transport
                    if parts is None:
                        continue
                    proof = rule_application_text(parts)
                    if not changed:
                        return proof
                    current_args = list(source.args[1:])
                    ok = True
                    for index in changed:
                        equality_proof = equality_transport_side_proof(
                            current_args[index],
                            target.args[index + 1],
                            known,
                            known_canonical,
                            rules,
                            eq_facts,
                            definitions,
                            rule_depth + 1,
                        )
                        if equality_proof is None:
                            ok = False
                            break
                        proof = transport_atomic_argument_proof(target, current_args, proof, index, equality_proof)
                        current_args[index] = target.args[index + 1]
                    if ok:
                        return proof
    return None


def atomic_rule_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    target = normalize_defined_expr(expr, definitions)
    if target.kind != "app" or len(target.args) < 2:
        return None

    for rule_index, original_rule in enumerate(reversed(rules)):
        rule = rename_rule_binders(original_rule, f"RT{rule_index}_")
        conclusion = rule_application_conclusion(rule)
        if conclusion.kind != "app" or len(conclusion.args) != len(target.args):
            continue
        binders = rule_application_binders(rule)
        variables = set(binders)
        initial_subst: dict[str, Expr] = {}
        if not match_expr(conclusion.args[0], target.args[0], variables, initial_subst):
            continue
        steps = rule.steps
        if not steps:
            steps = tuple(RuleStep("binder", name=binder) for binder in binders) + tuple(
                RuleStep("premise", expr=premise) for premise in rule.premises
            )
        if not any(step.kind == "premise" for step in steps):
            continue
        candidate_sources: list[tuple[tuple[int, int, int], dict[str, Expr], Expr]] = []
        for subst in infer_rule_binder_candidates_from_known(
            steps,
            binders,
            initial_subst,
            known,
            limit=128,
            require_premise_match=True,
        ):
            source = normalize_defined_expr(substitute_expr(conclusion, subst), definitions)
            if source.kind != "app" or len(source.args) != len(target.args):
                continue
            if expr_key(source.args[0]) != expr_key(target.args[0]):
                continue
            target_subterms = sum(
                1
                for source_arg, target_arg in zip(source.args[1:], target.args[1:])
                if expr_text(target_arg) in expr_text(source_arg)
            )
            changed_arguments = sum(
                1
                for source_arg, target_arg in zip(source.args[1:], target.args[1:])
                if expr_key(source_arg) != expr_key(target_arg)
            )
            candidate_sources.append(((-target_subterms, changed_arguments, len(expr_text(source))), subst, source))
        candidate_sources.sort(key=lambda item: item[0])

        for _, subst, source in candidate_sources[:32]:
            parts = rule_application_parts(
                rule,
                subst,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if parts is None:
                continue
            transports: list[tuple[int, str]] = []
            current_args = list(source.args[1:])
            ok = True
            for index, (source_arg, target_arg) in enumerate(zip(source.args[1:], target.args[1:])):
                if expr_key(source_arg) == expr_key(target_arg):
                    continue
                equality = Expr("eq", args=(source_arg, target_arg))
                equality_proof = equality_rewrite_join_proof(
                    equality,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    rule_depth,
                )
                if equality_proof is None:
                    equality_proof = proof_for_expr(
                        equality,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        allow_rule=True,
                        rule_depth=rule_depth,
                    )
                if equality_proof is None:
                    reverse_equality = Expr("eq", args=(target_arg, source_arg))
                    reverse_proof = equality_rewrite_join_proof(
                        reverse_equality,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        rule_depth,
                    )
                else:
                    reverse_proof = None
                if equality_proof is None and reverse_proof is None:
                    reverse_equality = Expr("eq", args=(target_arg, source_arg))
                    reverse_proof = proof_for_expr(
                        reverse_equality,
                        known,
                        known_canonical,
                        rules,
                        eq_facts,
                        definitions,
                        allow_rule=True,
                        rule_depth=rule_depth,
                    )
                if equality_proof is None and reverse_proof is not None:
                    equality_proof = eq_symmetry_proof(reverse_proof, target_arg)
                if equality_proof is None:
                    ok = False
                    break
                transports.append((index, equality_proof))
            if not ok or not transports:
                continue
            proof = rule_application_text(parts)
            for index, equality_proof in transports:
                proof = transport_atomic_argument_proof(target, current_args, proof, index, equality_proof)
                current_args[index] = target.args[index + 1]
            return proof
    return None

def direct_proof_expr(expr: Expr) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    binder_names = [name for name, _ in binders]
    equality_sides = equality_like_sides(conclusion)
    if not premises and equality_sides is not None and expr_key(equality_sides[0]) == expr_key(equality_sides[1]):
        args = binder_names + ["Q", "H"]
        return f"({' '.join(['fun'] + args + ['=>', 'H'])})"

    def vampire_and_parts(node: Expr) -> tuple[Expr, Expr] | None:
        if (
            node.kind == "app"
            and len(node.args) == 3
            and node.args[0].kind == "var"
            and node.args[0].value == "vampire_and"
        ):
            return node.args[1], node.args[2]
        return None

    def flatten_vampire_and(node: Expr) -> list[Expr]:
        parts = vampire_and_parts(node)
        if parts is None:
            return [node]
        return flatten_vampire_and(parts[0]) + flatten_vampire_and(parts[1])

    def local_proof(
        target: Expr,
        local_premises: list[tuple[Expr, str]],
        seen: set[str],
    ) -> str | None:
        target_key = expr_key(target)
        if target_key in seen:
            return None
        seen = set(seen)
        seen.add(target_key)
        for premise, name in reversed(local_premises):
            if expr_key(premise) == target_key:
                return name
            if premise.kind == "var" and premise.value == "vampire_false":
                return f"{name} {proof_arg_text(target)}"
        if target.kind == "forall" and target.sort == "prop" and target.value is not None:
            for premise, name in reversed(local_premises):
                if premise.kind == "var" and premise.value == "vampire_false":
                    return f"(fun {target.value} => {name} {target.value})"
        target_and = vampire_and_parts(target)
        if target_and is not None:
            left_proof = local_proof(target_and[0], local_premises, seen)
            right_proof = local_proof(target_and[1], local_premises, seen)
            if left_proof is not None and right_proof is not None:
                return f"(fun P K => K {proof_argument_text(left_proof)} {proof_argument_text(right_proof)})"
        if target.kind == "arrow":
            arg_name = f"H{len(local_premises)}"
            body_proof = local_proof(target.args[1], local_premises + [(target.args[0], arg_name)], seen)
            if body_proof is not None:
                return f"(fun {arg_name} => {body_proof})"
        for premise, name in reversed(local_premises):
            parts = vampire_and_parts(premise)
            if parts is None:
                continue
            for index, component in enumerate(parts):
                if expr_key(component) == target_key:
                    left_name = f"H{len(local_premises)}L"
                    right_name = f"H{len(local_premises)}R"
                    selected = left_name if index == 0 else right_name
                    return f"({name} {proof_arg_text(target)} (fun {left_name} {right_name} => {selected}))"
                if component.kind == "arrow" and expr_key(component.args[1]) == target_key:
                    source_proof = local_proof(component.args[0], local_premises, seen)
                    if source_proof is not None:
                        left_name = f"H{len(local_premises)}L"
                        right_name = f"H{len(local_premises)}R"
                        selected = left_name if index == 0 else right_name
                        return (
                            f"({name} {proof_arg_text(target)} "
                            f"(fun {left_name} {right_name} => {selected} {proof_argument_text(source_proof)}))"
                        )
        return None

    def nested_and_eliminator(
        proof: str,
        node: Expr,
        result: Expr,
        continuation: str,
        accumulated: list[str],
        depth: int = 0,
    ) -> str:
        parts = vampire_and_parts(node)
        if parts is None:
            return f"({continuation} {' '.join(accumulated + [proof])})"
        left_name = f"HA{depth}"
        right_name = f"HB{depth}"
        body = nested_and_eliminator(right_name, parts[1], result, continuation, accumulated + [left_name], depth + 1)
        return f"({proof} {proof_arg_text(result)} (fun {left_name} {right_name} => {body}))"

    if premises:
        local_premises = [(premise, f"H{index}") for index, premise in enumerate(premises)]
        proof = local_proof(conclusion, local_premises, set())
        if proof is not None:
            args = binder_names + [name for _, name in local_premises]
            return f"({' '.join(['fun'] + args + ['=>', proof])})"

        target_binders, target_body = collect_foralls(conclusion)
        target_premises, target_conclusion = split_arrows(target_body)
        if (
            len(target_binders) == 1
            and target_binders[0][1] == "prop"
            and target_conclusion.kind == "var"
            and target_conclusion.value == target_binders[0][0]
        ):
            continuation_shape = None
            if len(target_premises) == 1:
                continuation_premises, continuation_conclusion = split_arrows(target_premises[0])
                if expr_key(continuation_conclusion) == expr_key(target_conclusion):
                    continuation_shape = [expr_key(item) for item in continuation_premises]
            flattened_target = continuation_shape or [expr_key(item) for item in target_premises]
            for premise_index, premise in enumerate(premises):
                flattened_premise = [expr_key(item) for item in flatten_vampire_and(premise)]
                if flattened_premise == flattened_target:
                    premise_names = [f"H{index}" for index, _ in enumerate(premises)]
                    continuation = "K"
                    proof = nested_and_eliminator(
                        premise_names[premise_index],
                        premise,
                        Expr("var", value=target_binders[0][0]),
                        continuation,
                        [],
                    )
                    args = binder_names + premise_names + [target_binders[0][0], continuation]
                    return f"({' '.join(['fun'] + args + ['=>', proof])})"
    else:
        proof = local_proof(conclusion, [], set())
        if proof is not None:
            return f"({' '.join(['fun'] + binder_names + ['=>', proof])})"

    def branch_continuation_parts(branch: Expr, element: Expr, result_name: str) -> tuple[str, Expr, str, Expr, Expr, bool] | None:
        branch_binders, branch_body = collect_foralls(branch)
        branch_premises, branch_conclusion = split_arrows(branch_body)
        if len(branch_binders) != 1 or branch_binders[0][1] != "set" or len(branch_premises) != 1:
            return None
        first_name = branch_binders[0][0]
        first_membership = binary_atom_parts(branch_premises[0])
        if (
            first_membership is None
            or first_membership[0] != "In"
            or first_membership[1].kind != "var"
            or first_membership[1].value != first_name
        ):
            return None
        second_binders, second_body = collect_foralls(branch_conclusion)
        second_premises, second_conclusion = split_arrows(second_body)
        if len(second_binders) != 1 or second_binders[0][1] != "set" or len(second_premises) != 2:
            return None
        if second_conclusion.kind != "var" or second_conclusion.value != result_name:
            return None
        second_name = second_binders[0][0]
        second_membership = binary_atom_parts(second_premises[0])
        if (
            second_membership is None
            or second_membership[0] != "In"
            or second_membership[1].kind != "var"
            or second_membership[1].value != second_name
        ):
            return None
        equality = second_premises[1]
        if equality.kind != "eq":
            return None
        if expr_key(equality.args[1]) == expr_key(element):
            return first_name, first_membership[2], second_name, second_membership[2], equality.args[0], False
        if expr_key(equality.args[0]) == expr_key(element):
            return first_name, first_membership[2], second_name, second_membership[2], equality.args[1], True
        return None

    def branch_membership_matches(
        branch: Expr,
        first_name: str,
        first_base: Expr,
        second_name: str,
        second_base: Expr,
        image: Expr,
        target_set: Expr,
    ) -> bool:
        first_binders, first_body = collect_foralls(branch)
        first_premises, first_conclusion = split_arrows(first_body)
        if len(first_binders) != 1 or first_binders[0][1] != "set" or len(first_premises) != 1:
            return False
        original_first = first_binders[0][0]
        first_membership = binary_atom_parts(first_premises[0])
        renames = {original_first: first_name}
        renamed_first_base = rename_expr_variables(first_membership[2], renames) if first_membership is not None else None
        if (
            first_membership is None
            or first_membership[0] != "In"
            or first_membership[1].kind != "var"
            or first_membership[1].value != original_first
            or renamed_first_base is None
            or expr_key(renamed_first_base) != expr_key(first_base)
        ):
            return False
        second_binders, second_body = collect_foralls(first_conclusion)
        second_premises, second_conclusion = split_arrows(second_body)
        if len(second_binders) != 1 or second_binders[0][1] != "set" or len(second_premises) != 1:
            return False
        original_second = second_binders[0][0]
        renames[original_second] = second_name
        second_membership = binary_atom_parts(second_premises[0])
        renamed_second_base = rename_expr_variables(second_membership[2], renames) if second_membership is not None else None
        if (
            second_membership is None
            or second_membership[0] != "In"
            or second_membership[1].kind != "var"
            or second_membership[1].value != original_second
            or renamed_second_base is None
            or expr_key(renamed_second_base) != expr_key(second_base)
        ):
            return False
        conclusion_atom = binary_atom_parts(second_conclusion)
        if conclusion_atom is None or conclusion_atom[0] != "In":
            return False
        return (
            expr_key(rename_expr_variables(conclusion_atom[1], renames)) == expr_key(image)
            and expr_key(rename_expr_variables(conclusion_atom[2], renames)) == expr_key(target_set)
        )

    if len(premises) == 3 and conclusion.kind == "forall":
        target_binders, target_body = collect_foralls(conclusion)
        target_premises, target_conclusion = split_arrows(target_body)
        target_atom = binary_atom_parts(target_conclusion)
        if len(target_binders) == 1 and target_binders[0][1] == "set" and len(target_premises) == 1 and target_atom is not None and target_atom[0] == "In":
            target_name = target_binders[0][0]
            target_element = target_atom[1]
            target_set = target_atom[2]
            target_membership = binary_atom_parts(target_premises[0])
            if (
                target_element.kind == "var"
                and target_element.value == target_name
                and target_membership is not None
                and target_membership[0] == "In"
                and target_membership[1].kind == "var"
                and target_membership[1].value == target_name
            ):
                chooser_binders, chooser_body = collect_foralls(premises[0])
                chooser_premises, chooser_conclusion = split_arrows(chooser_body)
                if len(chooser_binders) == 1 and chooser_binders[0][1] == "set" and len(chooser_premises) == 1:
                    chooser_name = chooser_binders[0][0]
                    chooser_membership = binary_atom_parts(chooser_premises[0])
                    result_binders, result_body = collect_foralls(chooser_conclusion)
                    result_premises, result_conclusion = split_arrows(result_body)
                    if (
                        chooser_membership is not None
                        and chooser_membership[0] == "In"
                        and chooser_membership[1].kind == "var"
                        and chooser_membership[1].value == chooser_name
                        and expr_key(chooser_membership[2]) == expr_key(target_membership[2])
                        and len(result_binders) == 1
                        and result_binders[0][1] == "prop"
                        and len(result_premises) == 2
                        and result_conclusion.kind == "var"
                        and result_conclusion.value == result_binders[0][0]
                    ):
                        left = branch_continuation_parts(result_premises[0], Expr("var", value=chooser_name), result_binders[0][0])
                        right = branch_continuation_parts(result_premises[1], Expr("var", value=chooser_name), result_binders[0][0])
                        if left is not None and right is not None:
                            left_first, left_first_base, left_second, left_second_base, left_image, left_reversed = left
                            right_first, right_first_base, right_second, right_second_base, right_image, right_reversed = right
                            if branch_membership_matches(
                                premises[1],
                                left_first,
                                left_first_base,
                                left_second,
                                left_second_base,
                                left_image,
                                target_set,
                            ) and branch_membership_matches(
                                premises[2],
                                right_first,
                                right_first_base,
                                right_second,
                                right_second_base,
                                right_image,
                                target_set,
                            ):
                                target_set_text = proof_arg_text(target_set)
                                target_element_expr = Expr("var", value=target_name)

                                def branch_lambda(
                                    first_name: str,
                                    second_name: str,
                                    premise_name: str,
                                    reversed_equality: bool,
                                ) -> str:
                                    proof = f"({premise_name} {first_name} H{first_name} {second_name} H{second_name})"
                                    if reversed_equality:
                                        equality = eq_symmetry_proof("Heq", target_element_expr)
                                        return (
                                            f"(fun {first_name}:set => fun H{first_name} => "
                                            f"fun {second_name}:set => fun H{second_name} => fun Heq => "
                                            f"{equality} (fun zz:set => In zz {target_set_text}) {proof})"
                                        )
                                    return (
                                        f"(fun {first_name}:set => fun H{first_name} => "
                                        f"fun {second_name}:set => fun H{second_name} => fun Heq => "
                                        f"Heq (fun zz:set => In zz {target_set_text}) {proof})"
                                    )

                                args = binder_names + ["H0", "H1", "H2", target_name, "H3"]
                                return (
                                    f"({' '.join(['fun'] + args + ['=>'])} "
                                    f"H0 {target_name} H3 (In {target_name} {target_set_text}) "
                                    f"{branch_lambda(left_first, left_second, 'H1', left_reversed)} "
                                    f"{branch_lambda(right_first, right_second, 'H2', right_reversed)})"
                                )

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


def vampire_or_intro_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if (
        expr.kind != "app"
        or len(expr.args) != 3
        or expr.args[0].kind != "var"
        or expr.args[0].value != "vampire_or"
    ):
        return None
    left, right = expr.args[1], expr.args[2]
    left_proof = proof_for_expr(
        left,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=rule_depth > 0,
        rule_depth=max(0, rule_depth - 1),
    )
    if left_proof is not None:
        return f"(fun P Hleft Hright => Hleft {proof_term_text(left_proof)})"
    right_proof = proof_for_expr(
        right,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=rule_depth > 0,
        rule_depth=max(0, rule_depth - 1),
    )
    if right_proof is not None:
        return f"(fun P Hleft Hright => Hright {proof_term_text(right_proof)})"
    return None


def implication_intro_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool,
    rule_depth: int,
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if not premises:
        return None
    if len(premises) > 2:
        return None
    if (
        conclusion.kind != "app"
        or len(conclusion.args) != 3
        or expr_key(conclusion.args[0]) != "vampire_or"
    ):
        return None
    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    premise_names = [f"H{index}" for index, _ in enumerate(premises)]
    for premise, name in zip(premises, premise_names):
        key = expr_key(premise)
        local_known[key] = name
        local_known_canonical[canonical_proposition(key)] = name
    conclusion_proof = proof_for_expr(
        conclusion,
        local_known,
        local_known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=allow_rule,
        rule_depth=rule_depth,
    )
    if conclusion_proof is None:
        return None
    args = [name for name, _ in binders] + premise_names
    return f"({' '.join(['fun'] + args + ['=>', conclusion_proof])})"


def implication_from_false_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool,
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if not premises:
        return None
    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    premise_names = [f"H{index}" for index, _ in enumerate(premises)]
    for premise, name in zip(premises, premise_names):
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )
    false_expr = parse_expr("vampire_false")
    if false_expr is None:
        return None
    false_proof = proof_for_expr(
        false_expr,
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        definitions,
        allow_rule=allow_rule,
        rule_depth=max(0, rule_depth - 1),
    )
    if false_proof is None:
        return None
    args = [name for name, _ in binders] + premise_names
    conclusion_from_false = f"({proof_term_text(false_proof)} {proof_arg_text(conclusion)})"
    return f"({' '.join(['fun'] + args + ['=>', conclusion_from_false])})"


def build_quantified_implication(
    binders: list[tuple[str, str]],
    premises: list[Expr],
    conclusion: Expr,
) -> Expr:
    result = conclusion
    for premise in reversed(premises):
        result = Expr("arrow", args=(premise, result))
    for name, sort in reversed(binders):
        result = Expr("forall", value=name, sort=sort, args=(result,))
    return result


def prop_eliminator_projection_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
) -> str | None:
    binders, body = collect_foralls(expr)
    target_premises, target_conclusion = split_arrows(body)
    if not binders or not target_premises:
        return None
    target_binder_names = [name for name, _ in binders]
    target_premise_names = [f"H{index}" for index, _ in enumerate(target_premises)]

    for rule in rules:
        if len(rule.binders) > len(binders):
            continue
        subst = {
            rule_binder: Expr("var", value=target_binder)
            for rule_binder, target_binder in zip(rule.binders, target_binder_names)
        }
        instantiated_premises = [substitute_expr(premise, subst) for premise in rule.premises]
        if len(instantiated_premises) > len(target_premises):
            continue
        if not all(expr_key(left) == expr_key(right) for left, right in zip(instantiated_premises, target_premises)):
            continue

        instantiated_conclusion = substitute_expr(rule.conclusion, subst)
        elim_binders, elim_body = collect_foralls(instantiated_conclusion)
        if len(elim_binders) != 1 or elim_binders[0][1] != "prop":
            continue
        result_name = elim_binders[0][0]
        elim_premises, elim_result = split_arrows(elim_body)
        if (
            len(elim_premises) != 1
            or elim_result.kind != "var"
            or elim_result.value != result_name
        ):
            continue

        remaining_binders = binders[len(rule.binders) :]
        remaining_premises = target_premises[len(instantiated_premises) :]
        remainder = build_quantified_implication(remaining_binders, remaining_premises, target_conclusion)
        continuation = substitute_expr(elim_premises[0], {result_name: remainder})
        continuation_premises, continuation_result = split_arrows(continuation)
        if expr_key(continuation_result) != expr_key(remainder):
            continue

        local_known = dict(known)
        local_known_canonical = dict(known_canonical)
        continuation_names = [f"K{index}" for index, _ in enumerate(continuation_premises)]
        for premise, name in zip(continuation_premises, continuation_names):
            key = expr_key(premise)
            local_known[key] = name
            local_known_canonical[canonical_proposition(key)] = name
        remainder_proof = (
            local_known.get(expr_key(remainder))
            or local_known_canonical.get(canonical_proposition(expr_key(remainder)))
        )
        if remainder_proof is None:
            continue

        rule_args = [proof_arg_text(subst[name]) for name in rule.binders]
        rule_args.extend(target_premise_names[: len(instantiated_premises)])
        continuation_proof = f"({' '.join(['fun'] + continuation_names + ['=>', remainder_proof])})"
        application = rule_application_text(
            [rule.name]
            + rule_args
            + [proof_arg_text(remainder), proof_argument_text(continuation_proof)]
        )
        args = target_binder_names + target_premise_names
        return f"({' '.join(['fun'] + args + ['=>', application])})"
    return None


def equality_direct_rule_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if expr.kind != "eq" or rule_depth <= 0:
        return None
    target_pairs = [(expr.args[0], expr.args[1])]
    normalized_pair = (normalize_defined_expr(expr.args[0], definitions), normalize_defined_expr(expr.args[1], definitions))
    if (expr_key(normalized_pair[0]), expr_key(normalized_pair[1])) != (expr_key(expr.args[0]), expr_key(expr.args[1])):
        target_pairs.append(normalized_pair)

    for target_left, target_right in target_pairs:
        for rule in reversed(rules):
            conclusion = rule_application_conclusion(rule)
            if conclusion.kind != "eq":
                continue
            variables = set(rule_application_binders(rule))

            direct_subst: dict[str, Expr] = {}
            if (
                match_expr(conclusion.args[0], target_left, variables, direct_subst)
                and match_expr(conclusion.args[1], target_right, variables, direct_subst)
            ):
                parts = rule_application_parts(
                    rule,
                    direct_subst,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    rule_depth - 1,
                )
                if parts is not None:
                    return rule_application_text(parts)

            reverse_subst: dict[str, Expr] = {}
            if (
                match_expr(conclusion.args[0], target_right, variables, reverse_subst)
                and match_expr(conclusion.args[1], target_left, variables, reverse_subst)
            ):
                parts = rule_application_parts(
                    rule,
                    reverse_subst,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    rule_depth - 1,
                )
                if parts is not None:
                    proof = rule_application_text(parts)
                    return eq_symmetry_proof(proof, target_right)
    return None


def atom2(expr: Expr, head: str, left: Expr, right: Expr) -> bool:
    return (
        expr.kind == "app"
        and len(expr.args) == 3
        and expr.args[0].kind == "var"
        and expr.args[0].value == head
        and expr_key(expr.args[1]) == expr_key(left)
        and expr_key(expr.args[2]) == expr_key(right)
    )


def binary_atom_parts(expr: Expr) -> tuple[str, Expr, Expr] | None:
    if expr.kind != "app" or len(expr.args) != 3 or expr.args[0].kind != "var" or expr.args[0].value is None:
        return None
    return expr.args[0].value, expr.args[1], expr.args[2]


def unary_app(head: str, arg: Expr) -> Expr:
    return Expr("app", args=(Expr("var", value=head), arg))


def binary_transitivity_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    target = binary_atom_parts(expr)
    if target is None:
        return None
    target_head, target_left, target_right = target
    known_atoms: list[tuple[str, Expr, Expr, str]] = []
    seen_proofs: set[str] = set()
    for proposition, proof in known.items():
        if proof in seen_proofs:
            continue
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        atom = binary_atom_parts(parsed)
        if atom is None:
            continue
        seen_proofs.add(proof)
        head, left, right = atom
        if head == target_head:
            known_atoms.append((head, left, right, proof))

    for rule in reversed(rules):
        if len(rule.binders) != 3:
            continue
        conclusion = binary_atom_parts(rule.conclusion)
        if conclusion is None or conclusion[0] != target_head:
            continue
        binder_vars = {name: Expr("var", value=name) for name in rule.binders}
        if expr_key(conclusion[1]) != rule.binders[0] or expr_key(conclusion[2]) != rule.binders[2]:
            continue
        left_relation = Expr("app", args=(Expr("var", value=target_head), binder_vars[rule.binders[0]], binder_vars[rule.binders[1]]))
        right_relation = Expr("app", args=(Expr("var", value=target_head), binder_vars[rule.binders[1]], binder_vars[rule.binders[2]]))
        if not any(expr_key(premise) == expr_key(left_relation) for premise in rule.premises):
            continue
        if not any(expr_key(premise) == expr_key(right_relation) for premise in rule.premises):
            continue
        for _, left, middle, _ in known_atoms:
            if expr_key(left) != expr_key(target_left):
                continue
            for _, middle2, right, _ in known_atoms:
                if expr_key(middle2) != expr_key(middle) or expr_key(right) != expr_key(target_right):
                    continue
                subst = {
                    rule.binders[0]: target_left,
                    rule.binders[1]: middle,
                    rule.binders[2]: target_right,
                }
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
                        allow_rule=True,
                        rule_depth=rule_depth - 1,
                    )
                    if premise_proof is None:
                        ok = False
                        break
                    premise_proofs.append(proof_argument_text(premise_proof))
                if ok:
                    args = [proof_arg_text(subst[binder]) for binder in rule.binders]
                    return rule_application_text([rule.name] + args + premise_proofs)
    return None


def repl_eliminator_name(known: dict[str, str]) -> str | None:
    for proposition, proof in known.items():
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        steps, conclusion = sequential_rule_steps(parsed)
        binders = [step.name for step in steps if step.kind == "binder"]
        if len(steps) < 6 or len(binders) < 4 or conclusion.kind != "var" or conclusion.value != binders[3]:
            continue
        if steps[0].kind != "binder" or steps[1].kind != "binder" or steps[2].kind != "binder":
            continue
        if steps[3].kind != "premise" or steps[3].expr is None:
            continue
        base = Expr("var", value=binders[0])
        function = Expr("var", value=binders[1])
        image = Expr("var", value=binders[2])
        repl = Expr("app", args=(Expr("var", value="Repl"), base, function))
        if not atom2(steps[3].expr, "In", image, repl):
            continue
        if steps[4].kind != "binder" or steps[5].kind != "premise" or steps[5].expr is None:
            continue
        continuation_binders, continuation_body = collect_foralls(steps[5].expr)
        continuation_premises, continuation_conclusion = split_arrows(continuation_body)
        if len(continuation_binders) != 1 or len(continuation_premises) != 2:
            continue
        preimage = Expr("var", value=continuation_binders[0][0])
        if not atom2(continuation_premises[0], "In", preimage, base):
            continue
        function_preimage = Expr("app", args=(function, preimage))
        if (
            continuation_premises[1].kind == "eq"
            and expr_key(continuation_premises[1].args[0]) == expr_key(function_preimage)
            and expr_key(continuation_premises[1].args[1]) == expr_key(image)
            and continuation_conclusion.kind == "var"
            and continuation_conclusion.value == binders[3]
        ):
            return proof
    return None


def repl_elimination_goal_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    eliminator = repl_eliminator_name(known)
    if eliminator is None:
        return None

    seen: set[str] = set()
    for proposition, image_proof in list(known.items()):
        if image_proof in seen:
            continue
        seen.add(image_proof)
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        atom = binary_atom_parts(parsed)
        if atom is None or atom[0] != "In":
            continue
        image = atom[1]
        repl = atom[2]
        if repl.kind != "app" or len(repl.args) != 3 or expr_key(repl.args[0]) != "Repl":
            continue
        base = repl.args[1]
        function = repl.args[2]
        preimage_name = fresh_identifier("W", expr_text(expr), expr_text(base), expr_text(function))
        preimage = Expr("var", value=preimage_name)
        function_preimage = append_application_args(function, [preimage])
        target_at_preimage, changed = replace_expr(expr, image, function_preimage)
        if not changed:
            continue
        hole_name = fresh_identifier("zz", expr_text(expr), expr_text(image), expr_text(function_preimage))
        context_expr, context_changed = replace_expr(expr, image, Expr("var", value=hole_name))
        if not context_changed:
            continue

        local_known = dict(known)
        local_known_canonical = dict(known_canonical)
        local_rules = list(rules)
        local_eq_facts = list(eq_facts)
        membership = f"In {preimage_name} {proof_arg_text(base)}"
        remember_proposition(local_known, local_known_canonical, local_rules, local_eq_facts, "Hw", membership)
        preimage_proof = proof_for_expr(
            target_at_preimage,
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            definitions,
            allow_rule=True,
            rule_depth=rule_depth - 1,
        )
        if preimage_proof is None:
            continue
        return (
            f"({eliminator} {proof_arg_text(base)} {proof_arg_text(function)} {proof_arg_text(image)} "
            f"{proof_argument_text(image_proof)} {proof_arg_text(expr)} "
            f"(fun {preimage_name}:set => fun Hw => fun Heq => "
            f"Heq (fun {hole_name}:set => {expr_text(context_expr)}) {proof_argument_text(preimage_proof)}))"
        )
    return None


def empty_power_singleton_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    if expr.kind != "eq":
        return None
    empty = Expr("var", value="Empty")
    power_empty = unary_app("Power", empty)
    sing_empty = unary_app("Sing", empty)
    forward = expr_key(expr.args[0]) == expr_key(power_empty) and expr_key(expr.args[1]) == expr_key(sing_empty)
    reverse = expr_key(expr.args[0]) == expr_key(sing_empty) and expr_key(expr.args[1]) == expr_key(power_empty)
    if not forward and not reverse:
        return None

    names: dict[str, str] = {}
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) >= 2 and len(rule.premises) == 2 and rule.conclusion.kind == "eq":
            if expr_key(rule.conclusion.args[0]) == rule.binders[0] and expr_key(rule.conclusion.args[1]) == rule.binders[1]:
                names.setdefault("ext", rule.name)
        if len(rule.binders) == 1 and len(rule.premises) == 1 and rule.conclusion.kind == "eq":
            if expr_key(rule.conclusion.args[0]) == "Empty" and expr_key(rule.conclusion.args[1]) == rule.binders[0]:
                names.setdefault("empty_eq", rule.name)
        if len(rule.binders) == 1 and not rule.premises:
            if atom2(rule.conclusion, "In", empty, unary_app("Power", b[rule.binders[0]])):
                names.setdefault("power_empty", rule.name)
            if atom2(rule.conclusion, "In", b[rule.binders[0]], unary_app("Sing", b[rule.binders[0]])):
                names.setdefault("sing_intro", rule.name)
        if len(rule.binders) == 2 and len(rule.premises) == 1:
            if atom2(rule.premises[0], "In", b[rule.binders[1]], unary_app("Power", b[rule.binders[0]])):
                names.setdefault("power_elim", rule.name)
            if (
                atom2(rule.premises[0], "In", b[rule.binders[1]], unary_app("Sing", b[rule.binders[0]]))
                and rule.conclusion.kind == "eq"
                and expr_key(rule.conclusion.args[0]) == rule.binders[0]
                and expr_key(rule.conclusion.args[1]) == rule.binders[1]
            ):
                names.setdefault("sing_elim", rule.name)

    if {"ext", "empty_eq", "power_empty", "power_elim", "sing_intro", "sing_elim"} - names.keys():
        return None
    proof = (
        f"({names['ext']} (Power Empty) (Sing Empty) "
        f"(fun X H => ({names['empty_eq']} X ({names['power_elim']} Empty X H)) "
        f"(fun zz:set => In zz (Sing Empty)) ({names['sing_intro']} Empty)) "
        f"(fun X H => ({names['sing_elim']} Empty X H) "
        f"(fun zz:set => In zz (Power Empty)) ({names['power_empty']} Empty)))"
    )
    return proof if forward else eq_symmetry_proof(proof, power_empty)


def app_args(expr: Expr, head: str, arity: int) -> tuple[Expr, ...] | None:
    if expr.kind != "app" or len(expr.args) != arity + 1:
        return None
    if expr.args[0].kind != "var" or expr.args[0].value != head:
        return None
    return expr.args[1:]


def vampire_and_parts(expr: Expr) -> tuple[Expr, Expr] | None:
    return app_args(expr, "vampire_and", 2)


def vampire_exists_body(expr: Expr) -> tuple[str, Expr] | None:
    args = app_args(expr, "vampire_exists_set", 1)
    if args is None:
        return None
    predicate = args[0]
    if predicate.kind != "lambda" or predicate.value is None:
        return None
    return predicate.value, predicate.args[0]


def vampire_exists_intro_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    exists = vampire_exists_body(expr)
    if exists is None:
        return None
    witness_var, body = exists
    for proposition, proof in reversed(list(known.items())):
        known_expr = parse_expr(proposition)
        if known_expr is None:
            continue
        subst: dict[str, Expr] = {}
        if not match_expr(body, known_expr, {witness_var}, subst):
            continue
        witness = subst.get(witness_var)
        if witness is None:
            continue
        return f"(fun Q H => H {proof_arg_text(witness)} {proof_argument_text(proof)})"
    if rule_depth <= 0:
        return None
    candidates = candidate_terms_from_state(
        known,
        eq_facts,
        seed=expr_subterms(body, limit=16),
        exclude_names={witness_var},
        limit=64,
    )
    contradiction_names = {
        proof
        for proposition, proof in known.items()
        if proposition.endswith("-> vampire_false")
        or proposition.endswith("-> (forall P:prop, P)")
    }
    for witness in candidates:
        instantiated = substitute_expr(body, {witness_var: witness})
        if expr_key(instantiated) == expr_key(expr):
            continue
        proof = proof_for_expr(
            instantiated,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=True,
            rule_depth=rule_depth - 1,
        )
        if proof is not None:
            if any(re.search(rf"\\b{re.escape(name)}\\b", proof) for name in contradiction_names):
                continue
            return f"(fun Q H => H {proof_arg_text(witness)} {proof_argument_text(proof)})"
    return None


def empty_equality_contradiction_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if not binders or not premises or not false_eliminator_expr(conclusion):
        return None
    empty = Expr("var", value="Empty")
    contradiction_name = None
    for proposition, proof in known.items():
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        rule_premises, rule_conclusion = split_arrows(parsed)
        if len(rule_premises) != 1 or not false_eliminator_expr(rule_conclusion):
            continue
        exists = vampire_exists_body(rule_premises[0])
        if exists is None:
            continue
        witness_var, exists_body = exists
        witness = Expr("var", value=witness_var)
        if atom2(exists_body, "In", witness, empty):
            contradiction_name = proof
            break
    if contradiction_name is None:
        return None

    args = [name for name, _ in binders]
    used_names = set(args)
    used_names.update(known.values())
    premise_names: list[str] = []
    for index, _ in enumerate(premises):
        name = "H" + str(index)
        while name in used_names:
            index += 1
            name = "H" + str(index)
        used_names.add(name)
        premise_names.append(name)
        args.append(name)

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    for name, premise in zip(premise_names, premises):
        remember_proposition(
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            name,
            expr_text(premise),
        )

    for premise_name, premise in zip(premise_names, premises):
        sides = equality_like_sides(premise)
        if sides is None:
            continue
        if expr_key(sides[0]) == "Empty":
            target_set = sides[1]
            target_eq_empty = eq_symmetry_proof(premise_name, empty)
        elif expr_key(sides[1]) == "Empty":
            target_set = sides[0]
            target_eq_empty = premise_name
        else:
            continue
        for rule in reversed(rules):
            membership = app_args(rule.conclusion, "In", 2)
            if membership is None:
                continue
            member_pattern, set_pattern = membership
            subst: dict[str, Expr] = {}
            if not match_expr(set_pattern, target_set, set(rule.binders), subst):
                continue
            if not all(binder in subst for binder in rule.binders):
                continue
            parts = rule_application_parts(
                rule,
                subst,
                local_known,
                local_known_canonical,
                local_rules,
                local_eq_facts,
                definitions,
                max(0, rule_depth - 1),
            )
            if parts is None:
                continue
            member = substitute_expr(member_pattern, subst)
            membership_proof = rule_application_text(parts)
            transported = (
                f"{proof_term_text(target_eq_empty)} "
                f"(fun zz:set => In {proof_arg_text(member)} zz) "
                f"{proof_argument_text(membership_proof)}"
            )
            exists_proof = f"(fun Q H => H {proof_arg_text(member)} ({transported}))"
            false_proof = f"({contradiction_name} {exists_proof})"
            return f"({' '.join(['fun'] + args + ['=>', false_proof])})"
    return None


def ordsucc_empty_cases_proof(expr: Expr, known: dict[str, str], rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 1 or binders[0][1] != "set" or len(premises) != 1:
        return None
    target_binders, target_body = collect_foralls(conclusion)
    target_premises, target_conclusion = split_arrows(target_body)
    if len(target_binders) != 1 or target_binders[0][1] != "set->prop" or len(target_premises) != 1:
        return None
    element_name = binders[0][0]
    predicate_name = target_binders[0][0]
    element = Expr("var", value=element_name)
    predicate = Expr("var", value=predicate_name)
    empty = Expr("var", value="Empty")
    ordsucc_empty = Expr("app", args=(Expr("var", value="ordsucc"), empty))
    if not atom2(premises[0], "In", element, ordsucc_empty):
        return None
    if expr_key(target_premises[0]) != expr_key(append_application_args(predicate, [empty])):
        return None
    if expr_key(target_conclusion) != expr_key(append_application_args(predicate, [element])):
        return None

    contradiction_name = None
    for proposition, proof in known.items():
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        rule_premises, rule_conclusion = split_arrows(parsed)
        if len(rule_premises) != 1 or not false_eliminator_expr(rule_conclusion):
            continue
        exists = vampire_exists_body(rule_premises[0])
        if exists is None:
            continue
        witness_var, exists_body = exists
        if atom2(exists_body, "In", Expr("var", value=witness_var), empty):
            contradiction_name = proof
            break
    if contradiction_name is None:
        return None

    for rule in rules:
        if len(rule.binders) != 2 or len(rule.premises) != 1:
            continue
        b0 = Expr("var", value=rule.binders[0])
        b1 = Expr("var", value=rule.binders[1])
        if not atom2(rule.premises[0], "In", b1, Expr("app", args=(Expr("var", value="ordsucc"), b0))):
            continue
        disjuncts = app_args(rule.conclusion, "vampire_or", 2)
        if disjuncts is None:
            continue
        branches: list[str] = []
        for disjunct in disjuncts:
            if atom2(disjunct, "In", b1, b0):
                branches.append(
                    f"(fun HinEmpty => ({contradiction_name} (fun Q K => K {element_name} HinEmpty) "
                    f"({predicate_name} {element_name})))"
                )
            elif disjunct.kind == "eq" and expr_key(disjunct.args[0]) == expr_key(b0) and expr_key(disjunct.args[1]) == expr_key(b1):
                branches.append(f"(fun Heq => Heq {predicate_name} H1)")
            elif disjunct.kind == "eq" and expr_key(disjunct.args[0]) == expr_key(b1) and expr_key(disjunct.args[1]) == expr_key(b0):
                branches.append(f"(fun Heq => ({eq_symmetry_proof('Heq', element)}) {predicate_name} H1)")
        if len(branches) != 2:
            continue
        return (
            f"(fun {element_name} H0 {predicate_name} H1 => "
            f"({rule.name} Empty {element_name} H0 ({predicate_name} {element_name}) "
            f"{branches[0]} {branches[1]}))"
        )
    return None


def compatible_repl_equality(left: Expr, right: Expr) -> bool:
    left_sides = equality_like_sides(left)
    right_sides = equality_like_sides(right)
    if left_sides is None or right_sides is None:
        return False
    return expr_key(left_sides[0]) == expr_key(right_sides[0]) and expr_key(left_sides[1]) == expr_key(right_sides[1])


def compatible_conj_component(source: Expr, target: Expr) -> bool:
    return expr_key(source) == expr_key(target) or compatible_repl_equality(source, target)


def conjunction_reorder_proof(source_name: str, source_left: Expr, source_right: Expr, target_left: Expr, target_right: Expr) -> str | None:
    source_vars = [("HL", source_left), ("HR", source_right)]
    target_proofs: list[str] = []
    for target in (target_left, target_right):
        matches = [name for name, source in source_vars if compatible_conj_component(source, target)]
        if not matches:
            return None
        target_proofs.append(matches[0])
    return f"({source_name} (vampire_and {proof_arg_text(target_left)} {proof_arg_text(target_right)}) (fun HL HR => fun P K => K {target_proofs[0]} {target_proofs[1]}))"


def find_repl_equivalence_rule(rules: list[ProofRule]) -> tuple[ProofRule, int, str, Expr, Expr, Expr, Expr, Expr] | None:
    for rule in rules:
        if len(rule.binders) != 3 or rule.premises:
            continue
        components = vampire_and_parts(rule.conclusion)
        if components is None:
            continue
        base = Expr("var", value=rule.binders[0])
        function = Expr("var", value=rule.binders[1])
        image = Expr("var", value=rule.binders[2])
        def is_image_membership(candidate: Expr) -> bool:
            membership = app_args(candidate, "In", 2)
            if membership is None or expr_key(membership[0]) != expr_key(image):
                return False
            repl_args = app_args(membership[1], "Repl", 2)
            if repl_args is None or expr_key(repl_args[0]) != expr_key(base):
                return False
            return expr_key(eta_reduce_unary_function(repl_args[1])) == expr_key(function)

        forward_index: int | None = None
        backward_index: int | None = None
        exists_expr: Expr | None = None
        exists_var: str | None = None
        exists_body_expr: Expr | None = None
        for index, component in enumerate(components):
            premises, conclusion = split_arrows(component)
            if len(premises) != 1:
                continue
            premise, = premises
            conclusion_exists = vampire_exists_body(conclusion)
            premise_exists = vampire_exists_body(premise)
            if is_image_membership(premise) and conclusion_exists is not None:
                forward_index = index
                exists_expr = conclusion
                exists_var, exists_body_expr = conclusion_exists
            elif is_image_membership(conclusion) and premise_exists is not None:
                backward_index = index
                exists_expr = premise
                exists_var, exists_body_expr = premise_exists
        if forward_index is not None and backward_index is not None and exists_var is not None and exists_expr is not None and exists_body_expr is not None:
            return rule, forward_index, exists_var, base, function, image, exists_expr, exists_body_expr
    return None


def find_repl_intro_elim_rules(rules: list[ProofRule]) -> tuple[str | None, str | None]:
    intro = None
    elim = None
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) == 3 and len(rule.premises) == 1:
            repl = Expr("app", args=(Expr("var", value="Repl"), b[rule.binders[0]], b[rule.binders[1]]))
            image = Expr("app", args=(b[rule.binders[1]], b[rule.binders[2]]))
            if atom2(rule.premises[0], "In", b[rule.binders[2]], b[rule.binders[0]]) and atom2(rule.conclusion, "In", image, repl):
                intro = rule.name
            if atom2(rule.premises[0], "In", b[rule.binders[2]], repl):
                elim = rule.name
    return intro, elim


def eta_reduce_unary_function(expr: Expr) -> Expr:
    if expr.kind != "lambda" or expr.sort != "set" or expr.value is None:
        return expr
    body = expr.args[0]
    if body.kind != "app" or len(body.args) != 2:
        return expr
    argument = body.args[1]
    if argument.kind != "var" or argument.value != expr.value:
        return expr
    function = body.args[0]
    if expr.value in expr_variables(function):
        return expr
    return function


def find_repl_predicate_elim_rule(rules: list[ProofRule]) -> ProofRule | None:
    for rule in rules:
        if len(rule.binders) != 3 or len(rule.premises) != 1:
            continue
        base_name, function_name, predicate_name = rule.binders
        base = Expr("var", value=base_name)
        function = Expr("var", value=function_name)
        predicate = Expr("var", value=predicate_name)

        premise_binders, premise_body = collect_foralls(rule.premises[0])
        premise_premises, premise_conclusion = split_arrows(premise_body)
        if len(premise_binders) != 1 or premise_binders[0][1] != "set" or len(premise_premises) != 1:
            continue
        source = Expr("var", value=premise_binders[0][0])
        if not atom2(premise_premises[0], "In", source, base):
            continue
        if expr_key(premise_conclusion) != expr_key(Expr("app", args=(predicate, append_application_args(function, [source])))):
            continue

        target_binders, target_body = collect_foralls(rule.conclusion)
        target_premises, target_conclusion = split_arrows(target_body)
        if len(target_binders) != 1 or target_binders[0][1] != "set" or len(target_premises) != 1:
            continue
        image = Expr("var", value=target_binders[0][0])
        repl_args = app_args(target_premises[0], "In", 2)
        if repl_args is None or expr_key(repl_args[0]) != expr_key(image):
            continue
        image_set_args = app_args(repl_args[1], "Repl", 2)
        if image_set_args is None or expr_key(image_set_args[0]) != expr_key(base):
            continue
        expected_eta = Expr(
            "lambda",
            value=target_binders[0][0],
            sort="set",
            args=(append_application_args(function, [image]),),
        )
        image_function = eta_reduce_unary_function(image_set_args[1])
        if expr_key(image_function) != expr_key(function) and expr_key(image_set_args[1]) != expr_key(expected_eta):
            continue
        if expr_key(target_conclusion) != expr_key(Expr("app", args=(predicate, image))):
            continue
        return rule
    return None


def repl_projection_text(rule: ProofRule, component_index: int, base: Expr, function: Expr, image: Expr, target: Expr) -> str:
    selected = "HL" if component_index == 0 else "HR"
    return (
        f"({rule.name} {proof_arg_text(base)} {proof_arg_text(function)} {proof_arg_text(image)} "
        f"{proof_arg_text(target)} (fun HL HR => {selected}))"
    )


def repl_intro_from_equivalence_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    equivalence = find_repl_equivalence_rule(rules)
    if equivalence is None:
        return None
    rule, forward_index, exists_var, _, _, _, exists_expr, exists_body = equivalence
    backward_index = 1 - forward_index
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    base_name, function_name, source_name = [name for name, _ in binders]
    if [sort for _, sort in binders] != ["set", "set->set", "set"]:
        return None
    base = Expr("var", value=base_name)
    function = Expr("var", value=function_name)
    source = Expr("var", value=source_name)
    membership = Expr("app", args=(Expr("var", value="In"), source, base))
    if expr_key(premises[0]) != expr_key(membership):
        return None
    image = append_application_args(function, [source])
    conclusion_membership = app_args(conclusion, "In", 2)
    if conclusion_membership is None or expr_key(conclusion_membership[0]) != expr_key(image):
        return None
    repl_args = app_args(conclusion_membership[1], "Repl", 2)
    if repl_args is None or expr_key(repl_args[0]) != expr_key(base):
        return None
    if expr_key(eta_reduce_unary_function(repl_args[1])) != expr_key(function):
        return None

    source_body = substitute_expr(
        exists_body,
        {
            rule.binders[0]: base,
            rule.binders[1]: function,
            rule.binders[2]: image,
            exists_var: source,
        },
    )
    source_components = vampire_and_parts(source_body)
    if source_components is None:
        return None
    component_proofs: list[str] = []
    for component in source_components:
        sides = equality_like_sides(component)
        if sides is not None and expr_key(sides[0]) == expr_key(sides[1]):
            component_proofs.append("(fun Q H => H)")
        elif expr_key(component) == expr_key(membership):
            component_proofs.append("H0")
        else:
            return None
    exists_proof = f"(fun Q H => H {source_name} (fun P K => K {component_proofs[0]} {component_proofs[1]}))"
    source_exists_expr = substitute_expr(
        exists_expr,
        {
            rule.binders[0]: base,
            rule.binders[1]: function,
            rule.binders[2]: image,
        },
    )
    selected_component = Expr("arrow", args=(source_exists_expr, conclusion))
    projection = repl_projection_text(rule, backward_index, base, function, image, selected_component)
    return f"(fun {base_name} {function_name} {source_name} H0 => ({projection} {exists_proof}))"


def repl_exists_from_equivalence_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    equivalence = find_repl_equivalence_rule(rules)
    if equivalence is None:
        return None
    rule, forward_index, exists_var, _, _, _, exists_expr, exists_body = equivalence
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    base_name, function_name, image_name = [name for name, _ in binders]
    if [sort for _, sort in binders] != ["set", "set->set", "set"]:
        return None
    base = Expr("var", value=base_name)
    function = Expr("var", value=function_name)
    image = Expr("var", value=image_name)
    membership = app_args(premises[0], "In", 2)
    if membership is None or expr_key(membership[0]) != expr_key(image):
        return None
    repl_args = app_args(membership[1], "Repl", 2)
    if repl_args is None or expr_key(repl_args[0]) != expr_key(base):
        return None
    if expr_key(eta_reduce_unary_function(repl_args[1])) != expr_key(function):
        return None
    target_exists = vampire_exists_body(conclusion)
    if target_exists is None:
        return None
    target_var, target_body = target_exists
    target_predicate = app_args(conclusion, "vampire_exists_set", 1)
    if target_predicate is None:
        return None

    source_exists_expr = substitute_expr(
        exists_expr,
        {
            rule.binders[0]: base,
            rule.binders[1]: function,
            rule.binders[2]: image,
        },
    )
    selected_component = Expr("arrow", args=(premises[0], source_exists_expr))
    projection = repl_projection_text(rule, forward_index, base, function, image, selected_component)
    witness_name = fresh_identifier("W", expr_text(expr), base_name, function_name, image_name)
    witness = Expr("var", value=witness_name)
    source_body = substitute_expr(
        exists_body,
        {
            rule.binders[0]: base,
            rule.binders[1]: function,
            rule.binders[2]: image,
            exists_var: witness,
        },
    )
    target_body_at_witness = substitute_expr(target_body, {target_var: witness})
    source_components = vampire_and_parts(source_body)
    target_components = vampire_and_parts(target_body_at_witness)
    if source_components is None or target_components is None:
        return None
    reordered = conjunction_reorder_proof("HW", source_components[0], source_components[1], target_components[0], target_components[1])
    if reordered is None:
        return None
    target_exists_proof = f"(fun Q H => H {witness_name} {reordered})"
    converted = (
        f"(({projection} H0) (vampire_exists_set {proof_arg_text(target_predicate[0])}) "
        f"(fun {witness_name} HW => {target_exists_proof}))"
    )
    return f"(fun {base_name} {function_name} {image_name} H0 => {converted})"


def find_repl_exists_rule(rules: list[ProofRule]) -> tuple[ProofRule, str, Expr] | None:
    for rule in rules:
        if len(rule.binders) != 3 or len(rule.premises) != 1:
            continue
        base = Expr("var", value=rule.binders[0])
        function = Expr("var", value=rule.binders[1])
        image = Expr("var", value=rule.binders[2])
        premise = app_args(rule.premises[0], "In", 2)
        if premise is None or expr_key(premise[0]) != expr_key(image):
            continue
        repl_args = app_args(premise[1], "Repl", 2)
        if repl_args is None or expr_key(repl_args[0]) != expr_key(base):
            continue
        if expr_key(eta_reduce_unary_function(repl_args[1])) != expr_key(function):
            continue
        exists = vampire_exists_body(rule.conclusion)
        if exists is None:
            continue
        return rule, exists[0], exists[1]
    return None


def repl_predicate_from_exists_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    exists_rule = find_repl_exists_rule(rules)
    if exists_rule is None:
        return None
    rule, exists_var, exists_body = exists_rule
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    base_name, function_name, predicate_name = [name for name, _ in binders]
    if [sort for _, sort in binders] != ["set", "set->set", "set->prop"]:
        return None
    target_binders, target_body = collect_foralls(conclusion)
    target_premises, target_conclusion = split_arrows(target_body)
    if len(target_binders) != 1 or len(target_premises) != 1:
        return None
    image_name = target_binders[0][0]
    image = Expr("var", value=image_name)
    base = Expr("var", value=base_name)
    function = Expr("var", value=function_name)
    predicate = Expr("var", value=predicate_name)
    target_membership = app_args(target_premises[0], "In", 2)
    if target_membership is None or expr_key(target_membership[0]) != expr_key(image):
        return None
    repl_args = app_args(target_membership[1], "Repl", 2)
    if repl_args is None or expr_key(repl_args[0]) != expr_key(base):
        return None
    if expr_key(eta_reduce_unary_function(repl_args[1])) != expr_key(function):
        return None
    if expr_key(target_conclusion) != expr_key(append_application_args(predicate, [image])):
        return None

    witness_name = fresh_identifier("W", expr_text(expr), base_name, function_name, image_name)
    witness = Expr("var", value=witness_name)
    source_body = substitute_expr(
        exists_body,
        {
            rule.binders[0]: base,
            rule.binders[1]: function,
            rule.binders[2]: image,
            exists_var: witness,
        },
    )
    source_components = vampire_and_parts(source_body)
    if source_components is None:
        return None
    membership_name: str | None = None
    equality_name: str | None = None
    equality_component: Expr | None = None
    for name, component in (("HL", source_components[0]), ("HR", source_components[1])):
        if expr_key(component) == expr_key(Expr("app", args=(Expr("var", value="In"), witness, base))):
            membership_name = name
        sides = equality_like_sides(component)
        if sides is not None:
            expected_left = append_application_args(function, [witness])
            if expr_key(sides[0]) == expr_key(expected_left) and expr_key(sides[1]) == expr_key(image):
                equality_name = name
                equality_component = component
    if membership_name is None or equality_name is None or equality_component is None:
        return None
    exists_proof = f"({rule.name} {base_name} {function_name} {image_name} H1)"
    transported = f"({equality_name} {predicate_name} (H0 {witness_name} {membership_name}))"
    continuation = f"(fun {witness_name} HW => HW ({predicate_name} {image_name}) (fun HL HR => {transported}))"
    return (
        f"(fun {base_name} {function_name} {predicate_name} H0 {image_name} H1 => "
        f"({exists_proof} ({predicate_name} {image_name}) {continuation}))"
    )


def repl_elimination_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    names = [name for name, _ in binders]
    sorts = [sort for _, sort in binders]
    if sorts != ["set", "set->set", "set->prop"]:
        return None
    target_binders, target_body = collect_foralls(conclusion)
    target_premises, target_conclusion = split_arrows(target_body)
    if len(target_binders) != 1 or target_binders[0][1] != "set" or len(target_premises) != 1:
        return None
    source_set, function, predicate = [Expr("var", value=name) for name in names]
    target = Expr("var", value=target_binders[0][0])
    repl = Expr("app", args=(Expr("var", value="Repl"), source_set, function))
    if not atom2(target_premises[0], "In", target, repl):
        return None
    if target_conclusion.kind != "app" or len(target_conclusion.args) != 2 or expr_key(target_conclusion.args[0]) != names[2] or expr_key(target_conclusion.args[1]) != target_binders[0][0]:
        return None
    if premises[0].kind != "forall":
        return None
    _, step_body = collect_foralls(premises[0])
    step_premises, step_conclusion = split_arrows(step_body)
    if len(step_premises) != 1 or step_conclusion.kind != "app" or len(step_conclusion.args) != 2:
        return None
    if expr_key(step_conclusion.args[0]) != predicate.value:
        return None
    elim = None
    _, elim = find_repl_intro_elim_rules(rules)
    if elim is None:
        return None
    args = names + ["H0", "H1"]
    return (
        f"(fun {names[0]} {names[1]} {names[2]} H0 {target_binders[0][0]} H1 => "
        f"({elim} {names[0]} {names[1]} {target_binders[0][0]} H1 ({names[2]} {target_binders[0][0]}) "
        f"(fun W HW HE => HE (fun zz:set => {names[2]} zz) (H0 W HW))))"
    )


def repl_image_membership_elim_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 1 or binders[0][1] != "set" or len(premises) != 1:
        return None
    image = Expr("var", value=binders[0][0])
    premise_args = app_args(premises[0], "In", 2)
    conclusion_args = app_args(conclusion, "In", 2)
    if premise_args is None or conclusion_args is None:
        return None
    if expr_key(premise_args[0]) != expr_key(image) or expr_key(conclusion_args[0]) != expr_key(image):
        return None
    repl_args = app_args(premise_args[1], "Repl", 2)
    if repl_args is None:
        return None
    base, function = repl_args
    target_set = conclusion_args[1]
    _, elim = find_repl_intro_elim_rules(rules)
    if elim is None:
        return None

    image_name = binders[0][0]
    membership_name = fresh_identifier("Himg", expr_text(expr))
    witness_name = fresh_identifier("W", expr_text(expr), membership_name)
    witness = Expr("var", value=witness_name)
    witness_membership_name = fresh_identifier("HW", expr_text(expr), membership_name, witness_name)
    equality_name = fresh_identifier("Heq", expr_text(expr), membership_name, witness_name, witness_membership_name)

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    remember_proposition(
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        witness_membership_name,
        expr_text(Expr("app", args=(Expr("var", value="In"), witness, base))),
    )

    for rule in reversed(rules):
        if len(rule.binders) != 1 or len(rule.premises) != 1:
            continue
        rule_var = Expr("var", value=rule.binders[0])
        expected_image = Expr("app", args=(function, rule_var))
        if not atom2(rule.conclusion, "In", expected_image, target_set):
            continue
        subst = {rule.binders[0]: witness}
        domain_premise = substitute_expr(rule.premises[0], subst)
        domain_proof = proof_for_expr(
            domain_premise,
            local_known,
            local_known_canonical,
            local_rules,
            local_eq_facts,
            definitions,
            allow_rule=True,
            rule_depth=max(0, rule_depth - 1),
        )
        if domain_proof is None:
            continue
        mapped_proof = f"({rule.name} {witness_name} {proof_argument_text(domain_proof)})"
        return (
            f"(fun {image_name} {membership_name} => "
            f"({elim} {proof_arg_text(base)} {proof_arg_text(function)} {image_name} {membership_name} "
            f"(In {image_name} {proof_arg_text(target_set)}) "
            f"(fun {witness_name}:set => fun {witness_membership_name} => fun {equality_name} => "
                f"{equality_name} (fun zz:set => In zz {proof_arg_text(target_set)}) {mapped_proof})))"
        )
    return None


def repl_image_property_elim_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 1 or binders[0][1] != "set" or len(premises) != 1:
        return None
    image_name = binders[0][0]
    image = Expr("var", value=image_name)
    premise_args = app_args(premises[0], "In", 2)
    if premise_args is None or expr_key(premise_args[0]) != expr_key(image):
        return None
    repl_args = app_args(premise_args[1], "Repl", 2)
    if repl_args is None:
        return None
    base, function = repl_args
    predicate_rule = find_repl_predicate_elim_rule(rules)
    if predicate_rule is not None:
        function_for_rule = eta_reduce_unary_function(function)
        predicate_name = fresh_identifier("Y", expr_text(expr), image_name)
        predicate_body, predicate_changed = replace_expr(conclusion, image, Expr("var", value=predicate_name))
        if predicate_changed:
            predicate = Expr("lambda", value=predicate_name, sort="set", args=(predicate_body,))
            witness_name = fresh_identifier("W", expr_text(expr), image_name, predicate_name)
            witness = Expr("var", value=witness_name)
            witness_membership_name = fresh_identifier("HW", expr_text(expr), image_name, witness_name)
            function_witness = append_application_args(function_for_rule, [witness])
            target_at_witness, changed = replace_expr(conclusion, image, function_witness)
            if changed:
                local_known = dict(known)
                local_known_canonical = dict(known_canonical)
                local_rules = list(rules)
                local_eq_facts = list(eq_facts)
                remember_proposition(
                    local_known,
                    local_known_canonical,
                    local_rules,
                    local_eq_facts,
                    witness_membership_name,
                    expr_text(Expr("app", args=(Expr("var", value="In"), witness, base))),
                )
                witness_proof = proof_for_expr(
                    target_at_witness,
                    local_known,
                    local_known_canonical,
                    local_rules,
                    local_eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=max(0, rule_depth - 1),
                )
                if witness_proof is not None:
                    image_membership_name = fresh_identifier("Himg", expr_text(expr), image_name, witness_name)
                    premise_proof = f"(fun {witness_name} {witness_membership_name} => {proof_argument_text(witness_proof)})"
                    return (
                        f"(fun {image_name} {image_membership_name} => "
                        f"({predicate_rule.name} {proof_arg_text(base)} {proof_arg_text(function_for_rule)} "
                        f"{proof_arg_text(predicate)} {premise_proof} {image_name} {image_membership_name}))"
                    )
    _, elim = find_repl_intro_elim_rules(rules)
    if elim is None:
        return None

    witness_name = fresh_identifier("W", expr_text(expr), image_name)
    witness = Expr("var", value=witness_name)
    witness_membership_name = fresh_identifier("HW", expr_text(expr), image_name, witness_name)
    equality_name = fresh_identifier("Heq", expr_text(expr), image_name, witness_name, witness_membership_name)
    function_witness = append_application_args(function, [witness])
    target_at_witness, changed = replace_expr(conclusion, image, function_witness)
    if not changed:
        return None
    hole_name = fresh_identifier("zz", expr_text(expr), image_name, witness_name)
    context_expr, context_changed = replace_expr(conclusion, image, Expr("var", value=hole_name))
    if not context_changed:
        return None

    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    remember_proposition(
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        witness_membership_name,
        expr_text(Expr("app", args=(Expr("var", value="In"), witness, base))),
    )
    witness_proof = proof_for_expr(
        target_at_witness,
        local_known,
        local_known_canonical,
        local_rules,
        local_eq_facts,
        definitions,
        allow_rule=True,
        rule_depth=max(0, rule_depth - 1),
    )
    if witness_proof is None:
        return None

    image_membership_name = fresh_identifier("Himg", expr_text(expr), image_name, witness_name)
    return (
        f"(fun {image_name} {image_membership_name} => "
        f"({elim} {proof_arg_text(base)} {proof_arg_text(function)} {image_name} {image_membership_name} "
        f"{proof_arg_text(conclusion)} "
        f"(fun {witness_name}:set => fun {witness_membership_name} => fun {equality_name} => "
        f"{equality_name} (fun {hole_name}:set => {expr_text(context_expr)}) "
        f"{proof_argument_text(witness_proof)})))"
    )


def image_monotone_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    names = [name for name, _ in binders]
    sorts = [sort for _, sort in binders]
    if sorts != ["set->set", "set", "set"]:
        return None
    target_binders, target_body = collect_foralls(conclusion)
    target_premises, target_conclusion = split_arrows(target_body)
    if len(target_binders) != 1 or target_binders[0][1] != "set" or len(target_premises) != 1:
        return None
    function, source, target = [Expr("var", value=name) for name in names]
    image = Expr("var", value=target_binders[0][0])
    source_repl = Expr("app", args=(Expr("var", value="Repl"), source, function))
    target_repl = Expr("app", args=(Expr("var", value="Repl"), target, function))
    if not atom2(target_premises[0], "In", image, source_repl) or not atom2(target_conclusion, "In", image, target_repl):
        return None
    intro, elim = find_repl_intro_elim_rules(rules)
    if intro is None or elim is None:
        return None
    return (
        f"(fun {names[0]} {names[1]} {names[2]} Hsub {target_binders[0][0]} Himg => "
        f"({elim} {names[1]} {names[0]} {target_binders[0][0]} Himg (In {target_binders[0][0]} (Repl {names[2]} {names[0]})) "
        f"(fun W HW HE => HE (fun zz:set => In zz (Repl {names[2]} {names[0]})) "
        f"({intro} {names[2]} {names[0]} W (Hsub W HW)))))"
    )


def image_in_power_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 1 or len(premises) != 1:
        return None
    subset_name, subset_sort = binders[0]
    if subset_sort != "set":
        return None
    subset = Expr("var", value=subset_name)
    if not atom2(premises[0], "In", subset, unary_app("Power", Expr("var", value="A"))):
        return None
    if not atom2(
        conclusion,
        "In",
        Expr(
            "app",
            args=(
                Expr("var", value="Repl"),
                Expr(
                    "app",
                    args=(
                        Expr("var", value="setminus"),
                        Expr("var", value="B"),
                        Expr("app", args=(Expr("var", value="Repl"), Expr("app", args=(Expr("var", value="setminus"), Expr("var", value="A"), subset)), Expr("var", value="f"))),
                    ),
                ),
                Expr("var", value="g"),
            ),
        ),
        unary_app("Power", Expr("var", value="A")),
    ):
        return None
    setminus_power = None
    image_power = None
    map_into = None
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) == 2 and not rule.premises:
            if atom2(rule.conclusion, "In", Expr("app", args=(Expr("var", value="setminus"), b[rule.binders[0]], b[rule.binders[1]])), unary_app("Power", b[rule.binders[0]])):
                setminus_power = rule.name
        if len(rule.binders) == 1 and len(rule.premises) == 1:
            if atom2(rule.premises[0], "In", b[rule.binders[0]], Expr("var", value="B")) and atom2(rule.conclusion, "In", Expr("app", args=(Expr("var", value="g"), b[rule.binders[0]])), Expr("var", value="A")):
                map_into = rule.name
        if len(rule.binders) == 3 and len(rule.premises) == 1:
            conclusion_binders, conclusion_body = collect_foralls(rule.conclusion)
            conclusion_premises, conclusion_final = split_arrows(conclusion_body)
            concl_args = app_args(conclusion_final, "In", 2)
            if conclusion_binders and conclusion_premises and concl_args is not None and app_args(concl_args[0], "Repl", 2) is not None and app_args(concl_args[1], "Power", 1) is not None:
                image_power = rule.name
    if setminus_power is None or image_power is None or map_into is None:
        return None
    inner = f"(setminus A {subset_name})"
    return (
        f"(fun {subset_name} H0 => "
        f"({image_power} B A g {map_into} (setminus B (Repl {inner} f)) "
        f"({setminus_power} B (Repl {inner} f))))"
    )


def if_union_successor_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
) -> str | None:
    if expr.kind != "eq":
        return None
    left = expr.args[0]
    right = expr.args[1]
    if left.kind != "app" or len(left.args) != 4:
        return None
    if left.args[0].kind != "var" or left.args[0].value != "If_i":
        return None
    condition, then_branch, else_branch = left.args[1:]
    cond_args = app_args(condition, "In", 2)
    if cond_args is None:
        return None
    union_args = app_args(cond_args[0], "Union", 1)
    succ_args = app_args(cond_args[1], "ordsucc", 1)
    if union_args is None or succ_args is None:
        return None
    succ_inner_args = app_args(union_args[0], "ordsucc", 1)
    if succ_inner_args is None or expr_key(succ_inner_args[0]) != expr_key(succ_args[0]):
        return None
    base = succ_args[0]
    union_succ = cond_args[0]
    if then_branch.kind != "app" or right.kind != "app" or len(then_branch.args) != len(right.args) or len(right.args) < 2:
        return None
    if expr_key(then_branch.args[0]) != expr_key(right.args[0]):
        return None
    different = [
        index
        for index, (left_arg, right_arg) in enumerate(zip(then_branch.args[1:], right.args[1:]), start=1)
        if expr_key(left_arg) != expr_key(right_arg)
    ]
    if different != [1, 2]:
        return None
    if expr_key(then_branch.args[1]) != expr_key(union_succ) or expr_key(right.args[1]) != expr_key(base):
        return None
    left_rec = then_branch.args[2]
    right_rec = right.args[2]
    left_rec_args = app_args(left_rec, "In_rec_i", 2)
    right_rec_args = app_args(right_rec, "In_rec_i", 2)
    if left_rec_args is None or right_rec_args is None:
        return None
    if expr_key(left_rec_args[0]) != expr_key(right_rec_args[0]):
        return None
    if expr_key(left_rec_args[1]) != expr_key(union_succ) or expr_key(right_rec_args[1]) != expr_key(base):
        return None

    if_rule = None
    union_rule = None
    succ_in_rule = None
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) == 3 and len(rule.premises) == 1:
            if_rule_conclusion = Expr(
                "eq",
                args=(
                    Expr("app", args=(Expr("var", value="If_i"), b[rule.binders[0]], b[rule.binders[1]], b[rule.binders[2]])),
                    b[rule.binders[1]],
                ),
            )
            if expr_key(rule.conclusion) == expr_key(if_rule_conclusion):
                if_rule = rule.name
        if len(rule.binders) == 1 and not rule.premises:
            if atom2(rule.conclusion, "In", b[rule.binders[0]], unary_app("ordsucc", b[rule.binders[0]])):
                succ_in_rule = rule.name
        if len(rule.binders) == 1 and len(rule.premises) == 1 and rule.conclusion.kind == "eq":
            expected_left = unary_app("Union", unary_app("ordsucc", b[rule.binders[0]]))
            if expr_key(rule.conclusion.args[0]) == expr_key(expected_left) and expr_key(rule.conclusion.args[1]) == rule.binders[0]:
                union_rule = rule
    if if_rule is None or succ_in_rule is None or union_rule is None:
        return None

    subst = {union_rule.binders[0]: base}
    premise = substitute_expr(union_rule.premises[0], subst)
    premise_proof = known.get(expr_key(premise)) or known_canonical.get(canonical_proposition(expr_key(premise)))
    if premise_proof is None:
        return None
    base_text = expr_text(base)
    base_arg = proof_arg_text(base)
    union_text = expr_text(union_succ)
    union_arg = proof_arg_text(union_succ)
    condition_text = proof_arg_text(condition)
    then_text = proof_arg_text(then_branch)
    else_text = proof_arg_text(else_branch)
    rec_fun_text = proof_arg_text(left_rec_args[0])
    head_text = expr_text(then_branch.args[0])
    union_eq = f"({union_rule.name} {base_text} {premise_proof})"
    union_eq_sym = f"({union_eq} (fun zz:set => zz = {union_text}) (fun R Hr => Hr))"
    condition_proof = f"({union_eq_sym} (fun zz:set => In zz (ordsucc {base_text})) ({succ_in_rule} {base_text}))"
    if_proof = f"({if_rule} {condition_text} {then_text} {else_text} {condition_proof})"
    return (
        f"(fun Q:set->prop => fun H:Q ({expr_text(left)}) => "
        f"{union_eq} (fun zz:set => Q ({head_text} {base_arg} (In_rec_i {rec_fun_text} zz))) "
        f"({union_eq} (fun zz:set => Q ({head_text} zz (In_rec_i {rec_fun_text} {union_arg}))) "
        f"({if_proof} Q H)))"
    )


def if_correct_branch_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if conclusion.kind != "eq":
        return None
    left = conclusion.args[0]
    if left.kind != "app" or len(left.args) != 4 or expr_key(left.args[0]) != "If_i":
        return None
    condition, then_branch, else_branch = left.args[1:]
    if expr_key(conclusion.args[1]) == expr_key(then_branch):
        target_branch = "then"
    elif expr_key(conclusion.args[1]) == expr_key(else_branch):
        target_branch = "else"
    else:
        return None
    premise_names = [f"H{index}" for index, _ in enumerate(premises)]
    condition_proof = None
    neg_condition_proof = None
    neg_condition = Expr("arrow", args=(condition, Expr("var", value="vampire_false")))
    for premise, name in zip(premises, premise_names):
        if expr_key(premise) == expr_key(condition):
            condition_proof = name
        elif expr_key(premise) == expr_key(neg_condition):
            neg_condition_proof = name
    if target_branch == "then" and condition_proof is None:
        return None
    if target_branch == "else" and neg_condition_proof is None:
        return None

    def vampire_and_parts(node: Expr) -> tuple[Expr, Expr] | None:
        if node.kind == "app" and len(node.args) == 3 and expr_key(node.args[0]) == "vampire_and":
            return node.args[1], node.args[2]
        return None

    def vampire_or_parts(node: Expr) -> tuple[Expr, Expr] | None:
        if node.kind == "app" and len(node.args) == 3 and expr_key(node.args[0]) == "vampire_or":
            return node.args[1], node.args[2]
        return None

    def component_handler(component: Expr, name: str) -> str | None:
        parts = vampire_and_parts(component)
        if parts is None:
            return None
        for component_expr, component_name in ((parts[0], "HA"), (parts[1], "HB")):
            if expr_key(component_expr) == expr_key(conclusion):
                return f"(fun {name} => {name} {proof_arg_text(conclusion)} (fun HA HB => {component_name}))"
            if target_branch == "then" and condition_proof is not None and expr_key(component_expr) == expr_key(neg_condition):
                return (
                    f"(fun {name} => {name} {proof_arg_text(conclusion)} "
                    f"(fun HA HB => {component_name} {condition_proof} {proof_arg_text(conclusion)}))"
                )
            if target_branch == "else" and neg_condition_proof is not None and expr_key(component_expr) == expr_key(condition):
                return (
                    f"(fun {name} => {name} {proof_arg_text(conclusion)} "
                    f"(fun HA HB => {neg_condition_proof} {component_name} {proof_arg_text(conclusion)}))"
                )
        return None

    for rule in rules:
        if len(rule.binders) != 3 or rule.premises:
            continue
        subst = {
            rule.binders[0]: condition,
            rule.binders[1]: then_branch,
            rule.binders[2]: else_branch,
        }
        disjuncts = vampire_or_parts(substitute_expr(rule.conclusion, subst))
        if disjuncts is None:
            continue
        left_handler = component_handler(disjuncts[0], "HL")
        right_handler = component_handler(disjuncts[1], "HR")
        if left_handler is None or right_handler is None:
            continue
        rule_args = [proof_arg_text(condition), proof_arg_text(then_branch), proof_arg_text(else_branch)]
        body_proof = f"({rule.name} {' '.join(rule_args)} {proof_arg_text(conclusion)} {left_handler} {right_handler})"
        proof_args = [name for name, _ in binders] + premise_names
        return f"({' '.join(['fun'] + proof_args + ['=>', body_proof])})"
    return None


def binary_application(node: Expr) -> tuple[str, Expr, Expr] | None:
    if (
        node.kind == "app"
        and len(node.args) == 3
        and node.args[0].kind == "var"
        and node.args[0].value is not None
    ):
        return node.args[0].value, node.args[1], node.args[2]
    return None


def unary_predicate_application(node: Expr) -> tuple[str, Expr] | None:
    if (
        node.kind == "app"
        and len(node.args) == 2
        and node.args[0].kind == "var"
        and node.args[0].value is not None
    ):
        return node.args[0].value, node.args[1]
    return None


def make_binary_application(name: str, left: Expr, right: Expr) -> Expr:
    return Expr("app", args=(Expr("var", value=name), left, right))


def algebraic_interchange_commutativity_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    sides = equality_like_sides(conclusion)
    if sides is None or len(binders) != 5 or len(premises) != 5:
        return None
    binder_exprs = [Expr("var", value=name) for name, _ in binders]
    binder_names = [name for name, _ in binders]

    def premise_predicate_terms() -> tuple[str, dict[str, str]] | None:
        pred_name: str | None = None
        proof_by_term: dict[str, str] = {}
        for index, (premise, binder) in enumerate(zip(premises, binder_exprs)):
            pred = unary_predicate_application(premise)
            if pred is None or expr_key(pred[1]) != expr_key(binder):
                return None
            if pred_name is None:
                pred_name = pred[0]
            elif pred_name != pred[0]:
                return None
            proof_by_term[expr_key(binder)] = f"H{index}"
        return (pred_name, proof_by_term) if pred_name is not None else None

    pred_info = premise_predicate_terms()
    if pred_info is None:
        return None
    predicate, premise_proofs = pred_info

    left = sides[0]
    right = sides[1]
    left_top = binary_application(left)
    right_top = binary_application(right)
    if left_top is None or right_top is None or left_top[0] != right_top[0]:
        return None
    op = left_top[0]
    left_outer_left = binary_application(left_top[1])
    left_outer_right = binary_application(left_top[2])
    right_outer_left = binary_application(right_top[1])
    right_outer_right = binary_application(right_top[2])
    if left_outer_left is None or left_outer_right is None or right_outer_left is None or right_outer_right is None:
        return None
    if any(part[0] != op for part in (left_outer_left, left_outer_right, right_outer_left, right_outer_right)):
        return None
    nested = binary_application(left_outer_left[2])
    if nested is None or nested[0] != op:
        return None
    a, b, c, d, e = binder_exprs
    bc = make_binary_application(op, b, c)
    if (
        expr_key(left_outer_left[1]) != expr_key(a)
        or expr_key(left_outer_left[2]) != expr_key(bc)
        or expr_key(left_outer_right[1]) != expr_key(d)
        or expr_key(left_outer_right[2]) != expr_key(e)
        or expr_key(right_outer_left[1]) != expr_key(e)
        or expr_key(right_outer_left[2]) != expr_key(bc)
        or expr_key(right_outer_right[1]) != expr_key(d)
        or expr_key(right_outer_right[2]) != expr_key(a)
    ):
        return None

    def apply_rule(rule: ProofRule, subst: dict[str, Expr], premise_proofs_by_key: dict[str, str]) -> str | None:
        parts = [rule.name]
        for binder_name in rule.binders:
            if binder_name not in subst:
                return None
            parts.append(proof_arg_text(subst[binder_name]))
        for premise in rule.premises:
            instantiated = substitute_expr(premise, subst)
            proof = premise_proofs_by_key.get(expr_key(instantiated))
            if proof is None:
                return None
            parts.append(proof_argument_text(proof))
        return rule_application_text(parts)

    closure_rule: ProofRule | None = None
    comm_rule: ProofRule | None = None
    interchange_rule: ProofRule | None = None
    for rule in rules:
        if len(rule.binders) == 2:
            x = Expr("var", value=rule.binders[0])
            y = Expr("var", value=rule.binders[1])
            conclusion_pred = unary_predicate_application(rule.conclusion)
            if (
                conclusion_pred is not None
                and conclusion_pred[0] == predicate
                and expr_key(conclusion_pred[1]) == expr_key(make_binary_application(op, x, y))
            ):
                premise_keys = {expr_key(premise) for premise in rule.premises}
                expected = {
                    expr_key(Expr("app", args=(Expr("var", value=predicate), x))),
                    expr_key(Expr("app", args=(Expr("var", value=predicate), y))),
                }
                if premise_keys == expected:
                    closure_rule = rule
            rule_sides = equality_like_sides(rule.conclusion)
            if rule_sides is not None:
                if (
                    expr_key(rule_sides[0]) == expr_key(make_binary_application(op, x, y))
                    and expr_key(rule_sides[1]) == expr_key(make_binary_application(op, y, x))
                ):
                    premise_keys = {expr_key(premise) for premise in rule.premises}
                    expected = {
                        expr_key(Expr("app", args=(Expr("var", value=predicate), x))),
                        expr_key(Expr("app", args=(Expr("var", value=predicate), y))),
                    }
                    if premise_keys == expected:
                        comm_rule = rule
        if len(rule.binders) == 4:
            w = Expr("var", value=rule.binders[0])
            x = Expr("var", value=rule.binders[1])
            y = Expr("var", value=rule.binders[2])
            z = Expr("var", value=rule.binders[3])
            rule_sides = equality_like_sides(rule.conclusion)
            if rule_sides is None:
                continue
            expected_left = make_binary_application(op, make_binary_application(op, w, x), make_binary_application(op, y, z))
            expected_right = make_binary_application(op, make_binary_application(op, w, y), make_binary_application(op, x, z))
            if expr_key(rule_sides[0]) == expr_key(expected_left) and expr_key(rule_sides[1]) == expr_key(expected_right):
                premise_keys = {expr_key(premise) for premise in rule.premises}
                expected = {
                    expr_key(Expr("app", args=(Expr("var", value=predicate), item)))
                    for item in (w, x, y, z)
                }
                if premise_keys == expected:
                    interchange_rule = rule

    if closure_rule is None or comm_rule is None or interchange_rule is None:
        return None

    def predicate_expr(term: Expr) -> Expr:
        return Expr("app", args=(Expr("var", value=predicate), term))

    def closure(left_term: Expr, left_proof: str, right_term: Expr, right_proof: str) -> str | None:
        subst = {closure_rule.binders[0]: left_term, closure_rule.binders[1]: right_term}
        return apply_rule(
            closure_rule,
            subst,
            {expr_key(predicate_expr(left_term)): left_proof, expr_key(predicate_expr(right_term)): right_proof},
        )

    def comm(left_term: Expr, left_proof: str, right_term: Expr, right_proof: str) -> str | None:
        subst = {comm_rule.binders[0]: left_term, comm_rule.binders[1]: right_term}
        return apply_rule(
            comm_rule,
            subst,
            {expr_key(predicate_expr(left_term)): left_proof, expr_key(predicate_expr(right_term)): right_proof},
        )

    def interchange(w_term: Expr, w_proof: str, x_term: Expr, x_proof: str, y_term: Expr, y_proof: str, z_term: Expr, z_proof: str) -> str | None:
        subst = {
            interchange_rule.binders[0]: w_term,
            interchange_rule.binders[1]: x_term,
            interchange_rule.binders[2]: y_term,
            interchange_rule.binders[3]: z_term,
        }
        return apply_rule(
            interchange_rule,
            subst,
            {
                expr_key(predicate_expr(w_term)): w_proof,
                expr_key(predicate_expr(x_term)): x_proof,
                expr_key(predicate_expr(y_term)): y_proof,
                expr_key(predicate_expr(z_term)): z_proof,
            },
        )

    ha, hb, hc, hd, he = [premise_proofs[expr_key(term)] for term in (a, b, c, d, e)]
    p_bc = closure(b, hb, c, hc)
    if p_bc is None:
        return None
    ad = make_binary_application(op, a, d)
    da = make_binary_application(op, d, a)
    bce = make_binary_application(op, bc, e)
    ebc = make_binary_application(op, e, bc)
    p_da = closure(d, hd, a, ha)
    p_ebc = closure(e, he, bc, p_bc)
    p1 = interchange(a, ha, bc, p_bc, d, hd, e, he)
    p_ad = comm(a, ha, d, hd)
    p_bce = comm(bc, p_bc, e, he)
    if p_da is None or p_ebc is None or p1 is None or p_ad is None or p_bce is None:
        return None
    middle = make_binary_application(op, ad, bce)
    p2 = (
        f"(fun Q:set->prop => fun H:Q ({expr_text(middle)}) => "
        f"{proof_term_text(p_bce)} (fun zz:set => Q ({expr_text(make_binary_application(op, da, Expr('var', value='zz')))})) "
        f"({proof_term_text(p_ad)} (fun zz:set => Q ({expr_text(make_binary_application(op, Expr('var', value='zz'), bce))})) H))"
    )
    p3 = comm(da, p_da, ebc, p_ebc)
    if p3 is None:
        return None
    proof = eq_transitivity_proof([p1, p2, p3], expr_text(left))
    if proof is None:
        return None
    args = binder_names + [f"H{index}" for index, _ in enumerate(premises)]
    return f"({' '.join(['fun'] + args + ['=>', proof])})"


def rule_conjunction_projection_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    target_premises, target_conclusion = split_arrows(body)
    target_binder_names = [name for name, _ in binders]

    def vampire_and_parts(node: Expr) -> tuple[Expr, Expr] | None:
        if node.kind == "app" and len(node.args) == 3 and expr_key(node.args[0]) == "vampire_and":
            return node.args[1], node.args[2]
        return None

    def premise_prefix_matches(prefix: list[Expr]) -> bool:
        if len(prefix) > len(target_premises):
            return False
        return all(expr_key(left) == expr_key(right) for left, right in zip(prefix, target_premises))

    def project_from_conjunction(proof: str, node: Expr, target: Expr, depth: int = 0) -> str | None:
        if expr_key(node) == expr_key(target):
            return proof
        parts = vampire_and_parts(node)
        if parts is None:
            return None
        left_name = f"HL{depth}"
        right_name = f"HR{depth}"
        left_projection = project_from_conjunction(left_name, parts[0], target, depth + 1)
        if left_projection is not None:
            return (
                f"({proof} {proof_arg_text(target)} "
                f"(fun {left_name} {right_name} => {left_projection}))"
            )
        right_projection = project_from_conjunction(right_name, parts[1], target, depth + 1)
        if right_projection is not None:
            return (
                f"({proof} {proof_arg_text(target)} "
                f"(fun {left_name} {right_name} => {right_projection}))"
            )
        return None

    def flattened_components(node: Expr) -> list[Expr]:
        parts = vampire_and_parts(node)
        if parts is None:
            return [node]
        return flattened_components(parts[0]) + flattened_components(parts[1])

    for rule in rules:
        if len(rule.binders) != len(binders):
            continue
        subst = {
            rule_binder: Expr("var", value=target_binder)
            for rule_binder, target_binder in zip(rule.binders, target_binder_names)
        }
        instantiated_premises = [substitute_expr(premise, subst) for premise in rule.premises]
        if not premise_prefix_matches(instantiated_premises):
            continue
        conjunction = vampire_and_parts(substitute_expr(rule.conclusion, subst))
        if conjunction is None:
            continue
        instantiated_conclusion = substitute_expr(rule.conclusion, subst)
        for component in flattened_components(instantiated_conclusion):
            component_premises, component_conclusion = split_arrows(component)
            if len(instantiated_premises) + len(component_premises) != len(target_premises):
                continue
            residual = target_premises[len(instantiated_premises) :]
            if not all(expr_key(left) == expr_key(right) for left, right in zip(component_premises, residual)):
                continue
            if expr_key(component_conclusion) != expr_key(target_conclusion):
                continue
            premise_names = [f"H{index}" for index, _ in enumerate(target_premises)]
            rule_args = [proof_arg_text(subst[name]) for name in rule.binders]
            rule_args.extend(premise_names[: len(instantiated_premises)])
            rule_proof = rule_application_text([rule.name] + rule_args)
            projection = project_from_conjunction(rule_proof, instantiated_conclusion, component)
            if projection is None:
                continue
            for premise_name in premise_names[len(instantiated_premises) :]:
                projection = f"({projection} {premise_name})"
            args = target_binder_names + premise_names
            return f"({' '.join(['fun'] + args + ['=>', projection])})"
    return None


def rule_conjunction_component_application_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    binders, body = collect_foralls(expr)
    target_premises, target_conclusion = split_arrows(body)
    target_binder_names = [name for name, _ in binders]
    premise_names = [f"H{index}" for index, _ in enumerate(target_premises)]
    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    local_rules = list(rules)
    local_eq_facts = list(eq_facts)
    for premise, name in zip(target_premises, premise_names):
        remember_proposition(local_known, local_known_canonical, local_rules, local_eq_facts, name, expr_text(premise))

    def flatten_vampire_and(node: Expr) -> list[Expr]:
        parts = vampire_and_parts(node)
        if parts is None:
            return [node]
        return flatten_vampire_and(parts[0]) + flatten_vampire_and(parts[1])

    def project_from_conjunction(proof: str, node: Expr, target: Expr, depth: int = 0) -> str | None:
        if expr_key(node) == expr_key(target):
            return proof
        parts = vampire_and_parts(node)
        if parts is None:
            return None
        left_name = f"HL{depth}"
        right_name = f"HR{depth}"
        left_projection = project_from_conjunction(left_name, parts[0], target, depth + 1)
        if left_projection is not None:
            return f"({proof} {proof_arg_text(target)} (fun {left_name} {right_name} => {left_projection}))"
        right_projection = project_from_conjunction(right_name, parts[1], target, depth + 1)
        if right_projection is not None:
            return f"({proof} {proof_arg_text(target)} (fun {left_name} {right_name} => {right_projection}))"
        return None

    for rule in rules:
        if vampire_and_parts(rule.conclusion) is None:
            continue
        variables = set(rule_application_binders(rule))
        for component in flatten_vampire_and(rule.conclusion):
            component_premises, component_conclusion = split_arrows(component)
            if len(component_premises) > len(target_premises):
                continue
            residual = target_premises[len(target_premises) - len(component_premises) :] if component_premises else []
            subst: dict[str, Expr] = {}
            if not match_expr(component_conclusion, target_conclusion, variables, subst):
                continue
            ok = True
            for component_premise, target_premise in zip(component_premises, residual):
                if not match_expr(component_premise, target_premise, variables, subst):
                    ok = False
                    break
            if not ok:
                continue
            for candidate in completed_rule_substs(rule, subst, local_known, local_eq_facts, limit=16):
                if not all(binder in candidate for binder in rule_application_binders(rule)):
                    continue
                rule_parts = [rule.name]
                for binder in rule_application_binders(rule):
                    rule_parts.append(proof_arg_text(candidate[binder]))
                candidate_ok = True
                for premise in rule.premises:
                    premise_proof = proof_for_expr(
                        substitute_expr(premise, candidate),
                        local_known,
                        local_known_canonical,
                        local_rules,
                        local_eq_facts,
                        definitions,
                        allow_rule=True,
                        rule_depth=max(0, rule_depth - 1),
                    )
                    if premise_proof is None:
                        candidate_ok = False
                        break
                    rule_parts.append(proof_argument_text(premise_proof))
                if not candidate_ok:
                    continue
                instantiated_conclusion = substitute_expr(rule.conclusion, candidate)
                instantiated_component = substitute_expr(component, candidate)
                projection = project_from_conjunction(rule_application_text(rule_parts), instantiated_conclusion, instantiated_component)
                if projection is None:
                    continue
                for premise_name in premise_names[len(target_premises) - len(component_premises) :] if component_premises else []:
                    projection = f"({projection} {premise_name})"
                args = target_binder_names + premise_names
                return f"({' '.join(['fun'] + args + ['=>', projection])})" if args else projection
    return None


def rule_conjunction_implication_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    binders, body = collect_foralls(expr)
    target_premises, target_conclusion = split_arrows(body)
    premise_names = [f"H{index}" for index, _ in enumerate(target_premises)]
    local_known = dict(known)
    local_known_canonical = dict(known_canonical)
    for premise, name in zip(target_premises, premise_names):
        key = expr_key(premise)
        local_known[key] = name
        local_known_canonical[canonical_proposition(key)] = name

    def vampire_and_parts(node: Expr) -> tuple[Expr, Expr] | None:
        if node.kind == "app" and len(node.args) == 3 and expr_key(node.args[0]) == "vampire_and":
            return node.args[1], node.args[2]
        return None

    for rule in rules:
        conjunction = vampire_and_parts(rule.conclusion)
        if conjunction is None:
            continue
        variables = set(rule.binders)
        for component_index, component in enumerate(conjunction):
            component_premises, component_conclusion = split_arrows(component)
            if not component_premises:
                continue
            subst: dict[str, Expr] = {}
            if not match_expr(component_conclusion, target_conclusion, variables, subst):
                continue
            if not all(name in subst for name in rule.binders):
                continue
            rule_premise_proofs: list[str] = []
            ok = True
            for premise in rule.premises:
                instantiated = substitute_expr(premise, subst)
                premise_proof = proof_for_expr(
                    instantiated,
                    local_known,
                    local_known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=rule_depth - 1,
                )
                if premise_proof is None:
                    ok = False
                    break
                rule_premise_proofs.append(proof_argument_text(premise_proof))
            if not ok:
                continue
            component_premise_proofs: list[str] = []
            for premise in component_premises:
                instantiated = substitute_expr(premise, subst)
                premise_proof = proof_for_expr(
                    instantiated,
                    local_known,
                    local_known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=rule_depth - 1,
                )
                if premise_proof is None:
                    ok = False
                    break
                component_premise_proofs.append(proof_argument_text(premise_proof))
            if not ok:
                continue
            rule_args = [proof_arg_text(subst[name]) for name in rule.binders] + rule_premise_proofs
            instantiated_component = substitute_expr(component, subst)
            left_name = "HL"
            right_name = "HR"
            selected = left_name if component_index == 0 else right_name
            proof = (
                f"({rule.name} {' '.join(rule_args)} {proof_arg_text(instantiated_component)} "
                f"(fun {left_name} {right_name} => {selected}))"
            )
            for premise_proof in component_premise_proofs:
                proof = f"({proof} {premise_proof})"
            proof_args = [name for name, _ in binders] + premise_names
            return f"({' '.join(['fun'] + proof_args + ['=>', proof])})"
    return None


def find_pair_sigma_rules(rules: list[ProofRule]) -> tuple[str | None, str | None, str | None]:
    proj0_pair = None
    proj1_pair = None
    proj1_sigma = None
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) == 2 and not rule.premises and rule.conclusion.kind == "eq":
            left, right = rule.conclusion.args
            pair = Expr("app", args=(Expr("var", value="setsum"), b[rule.binders[0]], b[rule.binders[1]]))
            if expr_key(left) == expr_key(Expr("app", args=(Expr("var", value="proj0"), pair))) and expr_key(right) == rule.binders[0]:
                proj0_pair = rule.name
            if expr_key(left) == expr_key(Expr("app", args=(Expr("var", value="proj1"), pair))) and expr_key(right) == rule.binders[1]:
                proj1_pair = rule.name
        if len(rule.binders) == 3 and len(rule.premises) == 1:
            base, family, pair_var = (b[name] for name in rule.binders)
            sigma = Expr("app", args=(Expr("var", value="Sigma"), base, family))
            if not atom2(rule.premises[0], "In", pair_var, sigma):
                continue
            proj0 = Expr("app", args=(Expr("var", value="proj0"), pair_var))
            proj1 = Expr("app", args=(Expr("var", value="proj1"), pair_var))
            fiber = Expr("app", args=(family, proj0))
            if atom2(rule.conclusion, "In", proj1, fiber):
                proj1_sigma = rule.name
    return proj0_pair, proj1_pair, proj1_sigma


def pair_sigma_e1_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 4 or len(premises) != 1:
        return None
    names = [name for name, _ in binders]
    sorts = [sort for _, sort in binders]
    if sorts != ["set", "set->set", "set", "set"]:
        return None
    base, family, left, right = (Expr("var", value=name) for name in names)
    pair = Expr("app", args=(Expr("var", value="setsum"), left, right))
    sigma = Expr("app", args=(Expr("var", value="Sigma"), base, family))
    if not atom2(premises[0], "In", pair, sigma):
        return None
    if not atom2(conclusion, "In", right, Expr("app", args=(family, left))):
        return None
    proj0_pair, proj1_pair, proj1_sigma = find_pair_sigma_rules(rules)
    if proj0_pair is None or proj1_pair is None or proj1_sigma is None:
        return None
    return (
        f"(fun {names[0]} {names[1]} {names[2]} {names[3]} H0 => "
        f"({proj1_pair} {names[2]} {names[3]}) (fun zz:set => In zz ({names[1]} {names[2]})) "
        f"(({proj0_pair} {names[2]} {names[3]}) "
        f"(fun zz:set => In (proj1 (setsum {names[2]} {names[3]})) ({names[1]} zz)) "
        f"({proj1_sigma} {names[0]} {names[1]} (setsum {names[2]} {names[3]}) H0)))"
    )


def find_ap_projection_rules(rules: list[ProofRule]) -> tuple[str | None, str | None, str | None]:
    proj0_ap = None
    proj1_ap = None
    proj1_sigma = None
    for rule in rules:
        b = {name: Expr("var", value=name) for name in rule.binders}
        if len(rule.binders) == 1 and not rule.premises and rule.conclusion.kind == "eq":
            item = b[rule.binders[0]]
            left, right = rule.conclusion.args
            proj0 = Expr("app", args=(Expr("var", value="proj0"), item))
            proj1 = Expr("app", args=(Expr("var", value="proj1"), item))
            ap0 = Expr("app", args=(Expr("var", value="ap"), item, Expr("var", value="Empty")))
            ap1 = Expr("app", args=(Expr("var", value="ap"), item, unary_app("ordsucc", Expr("var", value="Empty"))))
            if expr_key(left) == expr_key(proj0) and expr_key(right) == expr_key(ap0):
                proj0_ap = rule.name
            if expr_key(left) == expr_key(proj1) and expr_key(right) == expr_key(ap1):
                proj1_ap = rule.name
        if len(rule.binders) == 3 and len(rule.premises) == 1:
            base, family, pair_var = (b[name] for name in rule.binders)
            sigma = Expr("app", args=(Expr("var", value="Sigma"), base, family))
            if not atom2(rule.premises[0], "In", pair_var, sigma):
                continue
            proj0 = Expr("app", args=(Expr("var", value="proj0"), pair_var))
            proj1 = Expr("app", args=(Expr("var", value="proj1"), pair_var))
            fiber = Expr("app", args=(family, proj0))
            if atom2(rule.conclusion, "In", proj1, fiber):
                proj1_sigma = rule.name
    return proj0_ap, proj1_ap, proj1_sigma


def ap1_sigma_proof(expr: Expr, rules: list[ProofRule]) -> str | None:
    binders, body = collect_foralls(expr)
    premises, conclusion = split_arrows(body)
    if len(binders) != 3 or len(premises) != 1:
        return None
    names = [name for name, _ in binders]
    sorts = [sort for _, sort in binders]
    if sorts != ["set", "set->set", "set"]:
        return None
    base, family, pair = (Expr("var", value=name) for name in names)
    sigma = Expr("app", args=(Expr("var", value="Sigma"), base, family))
    if not atom2(premises[0], "In", pair, sigma):
        return None
    ap0 = Expr("app", args=(Expr("var", value="ap"), pair, Expr("var", value="Empty")))
    ap1 = Expr("app", args=(Expr("var", value="ap"), pair, unary_app("ordsucc", Expr("var", value="Empty"))))
    if not atom2(conclusion, "In", ap1, Expr("app", args=(family, ap0))):
        return None
    proj0_ap, proj1_ap, proj1_sigma = find_ap_projection_rules(rules)
    if proj0_ap is None or proj1_ap is None or proj1_sigma is None:
        return None
    return (
        f"(fun {names[0]} {names[1]} {names[2]} H0 => "
        f"({proj1_ap} {names[2]}) (fun zz:set => In zz ({names[1]} (ap {names[2]} Empty))) "
        f"(({proj0_ap} {names[2]}) (fun zz:set => In (proj1 {names[2]}) ({names[1]} zz)) "
        f"({proj1_sigma} {names[0]} {names[1]} {names[2]} H0)))"
    )


def forall_prop_identity(expr: Expr) -> bool:
    binders, body = collect_foralls(expr)
    return (
        len(binders) == 1
        and binders[0][1] == "prop"
        and body.kind == "var"
        and body.value == binders[0][0]
    )


def false_eliminator_expr(expr: Expr) -> bool:
    return (expr.kind == "var" and expr.value == "vampire_false") or forall_prop_identity(expr)


def contradiction_transport_proof(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    rule_depth: int,
) -> str | None:
    if rule_depth <= 0:
        return None
    for proposition, contradiction_name in reversed(list(known.items())):
        parsed = parse_expr(proposition)
        if parsed is None:
            continue
        premises, conclusion = split_arrows(parsed)
        if len(premises) != 1 or not false_eliminator_expr(conclusion):
            continue
        premise = premises[0]
        premise_proof = proof_for_expr(
            premise,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=True,
            rule_depth=rule_depth - 1,
        )
        if premise_proof is not None:
            return f"({contradiction_name} {proof_argument_text(premise_proof)} ({expr_text(expr)}))"
        for fact in reversed(eq_facts):
            replacements = (
                (fact.left, fact.right, fact.proof),
                (fact.right, fact.left, eq_symmetry_proof(fact.proof, fact.left)),
            )
            for source, target, equality_proof in replacements:
                source_premise, changed = replace_expr_occurrences(premise, target, source)
                if not changed:
                    continue
                source_proof = proof_for_expr(
                    source_premise,
                    known,
                    known_canonical,
                    rules,
                    eq_facts,
                    definitions,
                    allow_rule=True,
                    rule_depth=rule_depth - 1,
                )
                if source_proof is None:
                    continue
                hole_name = fresh_identifier("zz", expr_text(premise), expr_text(source), expr_text(target))
                context_expr, context_changed = replace_expr_occurrences(
                    premise,
                    target,
                    Expr("var", value=hole_name),
                )
                if not context_changed:
                    continue
                transported = (
                    f"{proof_term_text(equality_proof)} "
                    f"(fun {hole_name}:set => {expr_text(context_expr)}) "
                    f"{proof_argument_text(source_proof)}"
                )
                return f"({contradiction_name} ({transported}) ({expr_text(expr)}))"
    return None


def _proof_for_expr_impl(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool = True,
    rule_depth: int = 2,
) -> str | None:
    key = expr_key(expr)
    if key == "vampire_true":
        return "(fun P H => H)"
    proof = known.get(key) or known_canonical.get(canonical_proposition(key))
    if proof is not None:
        return proof

    direct = direct_proof_expr(expr)
    if direct is not None:
        return direct

    implication_intro = implication_intro_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule,
        rule_depth,
    )
    if implication_intro is not None:
        return implication_intro

    implication_false = implication_from_false_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule,
        rule_depth,
    )
    if implication_false is not None:
        return implication_false

    prop_eliminator = prop_eliminator_projection_proof(expr, known, known_canonical, rules)
    if prop_eliminator is not None:
        return prop_eliminator

    if_union = if_union_successor_proof(expr, known, known_canonical, rules)
    if if_union is not None:
        return if_union

    if_branch = if_correct_branch_proof(expr, rules)
    if if_branch is not None:
        return if_branch

    rule_conjunction = rule_conjunction_projection_proof(expr, rules)
    if rule_conjunction is not None:
        return rule_conjunction

    rule_conjunction_component = rule_conjunction_component_application_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    )
    if rule_conjunction_component is not None:
        return rule_conjunction_component

    rule_conjunction_implication = rule_conjunction_implication_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    )
    if rule_conjunction_implication is not None:
        return rule_conjunction_implication

    exists_intro = vampire_exists_intro_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    )
    if exists_intro is not None:
        return exists_intro

    for derived in (
        empty_equality_contradiction_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth),
        ordsucc_empty_cases_proof(expr, known, rules),
        repl_intro_from_equivalence_proof(expr, rules),
        repl_exists_from_equivalence_proof(expr, rules),
        repl_predicate_from_exists_proof(expr, rules),
        repl_elimination_proof(expr, rules),
        repl_image_membership_elim_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth),
        repl_image_property_elim_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth),
        image_monotone_proof(expr, rules),
        image_in_power_proof(expr, rules),
        algebraic_interchange_commutativity_proof(expr, rules),
        pair_sigma_e1_proof(expr, rules),
        ap1_sigma_proof(expr, rules),
    ):
        if derived is not None:
            return derived

    if allow_rule:
        contradiction = contradiction_transport_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if contradiction is not None:
            return contradiction

    or_intro = vampire_or_intro_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if or_intro is not None:
        return or_intro

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

    if allow_rule:
        direct_rule_proof = equality_direct_rule_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if direct_rule_proof is not None:
            return direct_rule_proof

    if (
        expr.kind == "eq"
        and rule_depth >= 2
        and len({expr_key(rule_application_conclusion(rule)) for rule in rules}) <= 8
    ):
        deep_rule_chain_proof = equality_rule_chain_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            max_depth=5,
            rule_depth=rule_depth,
        )
        if deep_rule_chain_proof is not None:
            return deep_rule_chain_proof

    two_rule_join = equality_two_rule_join_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth,
    )
    if two_rule_join is not None:
        return two_rule_join

    empty_power = empty_power_singleton_proof(expr, rules)
    if empty_power is not None:
        return empty_power

    if allow_rule:
        direct_rule_proof = equality_direct_rule_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if direct_rule_proof is not None:
            return direct_rule_proof

    deadline = getattr(PROOF_SEARCH_STATE, "deadline", None)
    if deadline is not None and proof_search_now() > deadline:
        return None

    if allow_rule and not getattr(PROOF_SEARCH_STATE, "in_premise_transport", False):
        premise_transport_proof = atomic_rule_premise_transport_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=rule_depth,
        )
        if premise_transport_proof is not None:
            return premise_transport_proof

    if allow_rule:
        introduced = introduction_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth)
        if introduced is not None:
            return introduced

    if allow_rule:
        sequential_rule_proof = sequential_rule_application_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if sequential_rule_proof is not None:
            return sequential_rule_proof

    if allow_rule:
        rule_transport_proof = atomic_rule_transport_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=rule_depth,
        )
        if rule_transport_proof is not None:
            return rule_transport_proof

    if allow_rule:
        transitivity_proof = binary_transitivity_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if transitivity_proof is not None:
            return transitivity_proof

    if allow_rule:
        repl_goal_proof = repl_elimination_goal_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if repl_goal_proof is not None:
            return repl_goal_proof

    congruence_proof = equality_congruence_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if congruence_proof is not None:
        return congruence_proof

    multi_congruence_proof = equality_multi_congruence_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth)
    if multi_congruence_proof is not None:
        return multi_congruence_proof

    if allow_rule:
        unary_bridge_proof = unary_equality_rule_bridge_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if unary_bridge_proof is not None:
            return unary_bridge_proof

    direct_demodulation_proof = equality_direct_demodulation_proof(expr, eq_facts, definitions)
    if direct_demodulation_proof is not None:
        return direct_demodulation_proof

    if allow_rule:
        rule_demodulation_proof = equality_rule_demodulation_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth,
        )
        if rule_demodulation_proof is not None:
            return rule_demodulation_proof

    transport_proof = atomic_transport_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        allow_rule=allow_rule,
        rule_depth=rule_depth,
    )
    if transport_proof is not None:
        return transport_proof

    if not allow_rule:
        return None

    rewritten_atom_proof = atomic_rewrite_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth=rule_depth,
    )
    if rewritten_atom_proof is not None:
        return rewritten_atom_proof

    multi_rewritten_atom_proof = atomic_multi_rewrite_proof(
        expr,
        known,
        known_canonical,
        rules,
        eq_facts,
        definitions,
        rule_depth=rule_depth,
    )
    if multi_rewritten_atom_proof is not None:
        return multi_rewritten_atom_proof

    rule_chain_proof = equality_rule_chain_proof(expr, known, known_canonical, rules, eq_facts, definitions, rule_depth=rule_depth)
    if rule_chain_proof is not None:
        return rule_chain_proof

    for rule_index, original_rule in enumerate(reversed(rules)):
        rule = rename_rule_binders(original_rule, f"FR{rule_index}_")
        subst: dict[str, Expr] = {}
        if not match_expr_with_alpha_instantiation(
            rule_application_conclusion(rule),
            expr,
            set(rule_application_binders(rule)),
            subst,
        ):
            continue
        parts = rule_application_parts(
            rule,
            subst,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            max(0, rule_depth - 1),
        )
        if parts is None:
            continue
        return rule_application_text(parts)

    return None


def proof_for_expr(
    expr: Expr,
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    definitions: dict[str, DefinitionInfo],
    allow_rule: bool = True,
    rule_depth: int = 2,
) -> str | None:
    key = expr_key(expr)
    proof = known.get(key) or known_canonical.get(canonical_proposition(key))
    if proof is not None:
        return proof
    direct = direct_proof_expr(expr)
    if direct is not None:
        return direct

    active = getattr(PROOF_SEARCH_STATE, "active_goals", None)
    if active is None:
        active = set()
        PROOF_SEARCH_STATE.active_goals = active
    active_key = (key, allow_rule, rule_depth)
    if active_key in active:
        return None
    active.add(active_key)
    try:
        return _proof_for_expr_impl(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            allow_rule=allow_rule,
            rule_depth=rule_depth,
        )
    finally:
        active.discard(active_key)


def known_false_proof(known: dict[str, str], known_canonical: dict[str, str]) -> str | None:
    proof = known.get("vampire_false") or known_canonical.get(canonical_proposition("vampire_false"))
    if proof is not None:
        return proof
    suffix = " -> vampire_false"
    for known_proposition, implication_proof in list(known.items()):
        if not known_proposition.endswith(suffix):
            continue
        premise = strip_balanced_parens(known_proposition[: -len(suffix)].strip())
        premise_proof = known.get(premise) or known_canonical.get(canonical_proposition(premise))
        if premise_proof is None:
            premise_expr = parse_expr(premise)
            premise_proof = direct_proof_expr(premise_expr) if premise_expr is not None else None
        if premise_proof is not None:
            return f"({implication_proof} {premise_proof})"
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
    if proposition == "vampire_false":
        false_proof = known_false_proof(known, known_canonical)
        if false_proof is not None:
            return false_proof
        false_expr = parse_expr("vampire_false")
        if false_expr is None:
            return None
        return proof_for_expr(false_expr, known, known_canonical, rules, eq_facts, definitions, rule_depth=4)
    false_proof = known_false_proof(known, known_canonical)
    if false_proof is not None:
        return f"({proof_term_text(false_proof)} ({proposition}))"
    expr = parse_expr(proposition)
    if expr is None:
        return None
    if expr.kind == "eq":
        boolean_ext_proof = boolean_or_nand_extensionality_proof(expr, known)
        if boolean_ext_proof is not None:
            return boolean_ext_proof
        direct_rule_proof = equality_direct_rule_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=2,
        )
        if direct_rule_proof is not None:
            return direct_rule_proof
        transported_rule_proof = equality_rule_transport_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=2,
        )
        if transported_rule_proof is not None:
            return transported_rule_proof
        congruence_proof = equality_congruence_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=3,
        )
        if congruence_proof is not None:
            return congruence_proof
        multi_congruence_proof = equality_multi_congruence_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=3,
        )
        if multi_congruence_proof is not None:
            return multi_congruence_proof
    if expr.kind == "forall" and len(expr_text(expr)) <= 500:
        introduced_bridge_proof = introduced_unary_equality_bridge_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=3,
        )
        if introduced_bridge_proof is not None:
            return introduced_bridge_proof
        one_rewrite_rule_proof = introduced_equality_one_rewrite_rule_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=3,
        )
        if one_rewrite_rule_proof is not None:
            return one_rewrite_rule_proof
    if expr.kind == "forall" and len(expr_text(expr)) <= 700:
        introduced_atomic_proof = introduced_atomic_rule_transport_proof(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=3,
        )
        if introduced_atomic_proof is not None:
            return introduced_atomic_proof
    proof = proof_for_expr(expr, known, known_canonical, rules, eq_facts, definitions)
    if proof is not None:
        return proof
    if expr.kind == "app" and len(expr_text(expr)) <= 500:
        return proof_for_expr(
            expr,
            known,
            known_canonical,
            rules,
            eq_facts,
            definitions,
            rule_depth=4,
        )
    if expr.kind == "forall" and len(expr_text(expr)) <= 500:
        steps, conclusion = sequential_rule_steps(expr)
        binder_count = sum(1 for step in steps if step.kind == "binder")
        premise_count = sum(1 for step in steps if step.kind == "premise")
        if (
            0 < binder_count <= 4
            and premise_count <= 3
            and (
                conclusion.kind == "app"
                or (conclusion.kind == "eq" and "set->" in expr_text(expr))
            )
        ):
            return proof_for_expr(
                expr,
                known,
                known_canonical,
                rules,
                eq_facts,
                definitions,
                rule_depth=3,
            )
    return None


def remember_proposition(
    known: dict[str, str],
    known_canonical: dict[str, str],
    rules: list[ProofRule],
    eq_facts: list[EqFact],
    name: str,
    proposition: str,
) -> None:
    expr = parse_expr(proposition)
    expr_proposition = expr_key(expr) if expr is not None else None
    already_known = proposition in known or canonical_proposition(proposition) in known_canonical
    if expr_proposition is not None:
        already_known = (
            already_known
            or expr_proposition in known
            or canonical_proposition(expr_proposition) in known_canonical
        )
    known.setdefault(proposition, name)
    known_canonical.setdefault(canonical_proposition(proposition), name)
    if expr_proposition is not None:
        known.setdefault(expr_proposition, name)
        known_canonical.setdefault(canonical_proposition(expr_proposition), name)
    if already_known:
        return
    rule = make_proof_rule(name, proposition)
    if rule is not None:
        rules.append(rule)
    eq_fact = make_eq_fact(name, proposition)
    if eq_fact is not None:
        eq_facts.append(eq_fact)


def known_proof_for_proposition(
    proposition: str,
    known: dict[str, str],
    known_canonical: dict[str, str],
) -> str | None:
    return known.get(proposition) or known_canonical.get(canonical_proposition(proposition))


def fill_repeated_claim_admits(lines: list[str]) -> list[str]:
    previous_deadline = getattr(PROOF_SEARCH_STATE, "deadline", None)
    PROOF_SEARCH_STATE.deadline = proof_search_now() + PROOF_SEARCH_SECONDS
    known: dict[str, str] = {}
    known_canonical: dict[str, str] = {}
    rules: list[ProofRule] = []
    eq_facts: list[EqFact] = []
    definitions: dict[str, DefinitionInfo] = {}
    theorem: str | None = None
    result = list(lines)
    index = 0
    block_depth = 0
    try:
        while index < len(result):
            timed_out = proof_search_timed_out()
            line = result[index]
            if block_depth > 0:
                if line == "{":
                    block_depth += 1
                elif line == "}":
                    block_depth -= 1
                index += 1
                continue
            if line == "{":
                block_depth = 1
                index += 1
                continue
            definition_match = DEFINITION_RE.match(line)
            if definition_match:
                parsed_definition = parse_definition_body(definition_match.group("body").strip())
                if parsed_definition is not None:
                    binders, body = parsed_definition
                    definitions[definition_match.group("name")] = DefinitionInfo(
                        definition_match.group("sort").strip(),
                        definition_match.group("body").strip(),
                        "(fun Q H => H)",
                        binders,
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
                if timed_out:
                    proof_name = known_proof_for_proposition(proposition, known, known_canonical)
                else:
                    proof_name = proof_for_proposition(proposition, known, known_canonical, rules, eq_facts, definitions)
                if proof_name is not None and index + 1 < len(result) and result[index + 1] == "{ admit. }":
                    result[index + 1] = "{ exact " + proof_argument_text(proof_name) + ". }"
                remember_proposition(known, known_canonical, rules, eq_facts, name, proposition)
                index += 2 if index + 1 < len(result) and result[index + 1].startswith("{ ") else 1
                continue
            if line == "admit." and theorem is not None:
                if timed_out:
                    proof_name = known_proof_for_proposition(theorem, known, known_canonical)
                else:
                    proof_name = proof_for_proposition(theorem, known, known_canonical, rules, eq_facts, definitions)
                if proof_name is not None:
                    result[index] = "exact " + proof_argument_text(proof_name) + "."
            index += 1
        return result
    finally:
        if previous_deadline is None:
            if hasattr(PROOF_SEARCH_STATE, "deadline"):
                delattr(PROOF_SEARCH_STATE, "deadline")
        else:
            PROOF_SEARCH_STATE.deadline = previous_deadline


def proof_for_claim_at(lines: list[str], claim_index: int) -> str | None:
    claim = proposition_after_colon(lines[claim_index], "claim ") if 0 <= claim_index < len(lines) else None
    if claim is None:
        return None
    known: dict[str, str] = {}
    known_canonical: dict[str, str] = {}
    rules: list[ProofRule] = []
    eq_facts: list[EqFact] = []
    definitions: dict[str, DefinitionInfo] = {}
    index = 0
    block_depth = 0
    while index < claim_index:
        line = lines[index]
        if block_depth > 0:
            if line == "{":
                block_depth += 1
            elif line == "}":
                block_depth -= 1
            index += 1
            continue
        if line == "{":
            block_depth = 1
            index += 1
            continue
        definition_match = DEFINITION_RE.match(line)
        if definition_match:
            parsed_definition = parse_definition_body(definition_match.group("body").strip())
            if parsed_definition is not None:
                binders, body = parsed_definition
                definitions[definition_match.group("name")] = DefinitionInfo(
                    definition_match.group("sort").strip(),
                    definition_match.group("body").strip(),
                    "(fun Q H => H)",
                    binders,
                    body,
                )
        axiom = proposition_after_colon(line, "Axiom ")
        if axiom is not None:
            remember_proposition(known, known_canonical, rules, eq_facts, axiom[0], axiom[1])
            index += 1
            continue
        previous_claim = proposition_after_colon(line, "claim ")
        if previous_claim is not None:
            remember_proposition(known, known_canonical, rules, eq_facts, previous_claim[0], previous_claim[1])
            index += 1
            continue
        index += 1
    return proof_for_proposition(claim[1], known, known_canonical, rules, eq_facts, definitions)


def comment_text(value: object) -> str:
    text = "" if value is None else str(value)
    return text.replace("\r", " ").replace("\n", " ")


SOURCE_DEPENDENCY_RE = re.compile(r"\baby\b(?P<body>[^.]*)\.")
SOURCE_IDENTIFIER_RE = re.compile(r"[_A-Za-z][_A-Za-z0-9']*")
SOURCE_DECL_RE = re.compile(
    r"^\s*(?:Theorem|Lemma|Example|Fact|Remark|Corollary|Proposition|Property|Definition|Axiom)\s+(?P<name>[_A-Za-z][_A-Za-z0-9']*)\b"
)
ABY_COMMAND_RE = re.compile(r"^\s*aby(?:[\s.]|$)")
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


def contains_executable_aby(lines: list[str]) -> bool:
    return any(ABY_COMMAND_RE.match(line) for line in lines if not line.lstrip().startswith("//"))


def normalize_vampire_boolean_literals(lines: list[str]) -> list[str]:
    result: list[str] = []
    for line in lines:
        if line.lstrip().startswith("//"):
            result.append(line)
            continue
        line = replace_identifier(line, "false", "vampire_false")
        line = replace_identifier(line, "true", "vampire_true")
        result.append(line)
    return result


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


def source_dependency_locations(source: str | None, names: list[str]) -> list[str]:
    if source is None or not names:
        return []
    path = Path(source)
    if not path.exists():
        return []
    wanted = set(names)
    found: dict[str, int] = {}
    for index, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
        match = SOURCE_DECL_RE.match(line)
        if match and match.group("name") in wanted and match.group("name") not in found:
            found[match.group("name")] = index
    return [f"{name}@{found[name]}" for name in names if name in found]


def source_local_dependency_locations(source: str | None, theorem_line: int | None, line: int, names: list[str]) -> list[str]:
    if source is None or theorem_line is None or not names:
        return []
    path = Path(source)
    if not path.exists():
        return []
    rows = path.read_text(encoding="utf-8", errors="replace").splitlines()
    wanted = set(names)
    found: dict[str, tuple[int, str]] = {}
    for index in range(max(1, theorem_line), min(line, len(rows)) + 1):
        row = rows[index - 1].strip()
        for command in re.finditer(r"\b(?P<keyword>let|assume)\s+(?P<body>[^.]*)\.", row):
            keyword = command.group("keyword")
            body = command.group("body")
            for token in SOURCE_IDENTIFIER_RE.findall(body):
                if token in wanted and token not in found:
                    found[token] = (index, keyword)
        claim = re.match(r"claim\s+(?P<name>[_A-Za-z][_A-Za-z0-9']*)\s*:", row)
        if claim and claim.group("name") in wanted and claim.group("name") not in found:
            found[claim.group("name")] = (index, "claim")
        local_set = re.match(r"set\s+(?P<name>[_A-Za-z][_A-Za-z0-9']*)\s*:", row)
        if local_set and local_set.group("name") in wanted and local_set.group("name") not in found:
            found[local_set.group("name")] = (index, "set")
    return [f"{name}@{found[name][0]}({found[name][1]})" for name in names if name in found]


def problem_formula_sources(problem: Path | None) -> dict[str, TptpSourceInfo]:
    if problem is None or not problem.exists():
        return {}
    sources: dict[str, TptpSourceInfo] = {}
    for line in problem.read_text(encoding="utf-8", errors="replace").splitlines():
        parsed = tptp_decl_parts(line)
        if parsed is None:
            continue
        name, role, body, source_hash = parsed
        if role not in {"axiom", "conjecture", "definition"}:
            continue
        normalized = normalize_tptp_formula_body(body)
        if not normalized:
            continue
        sources.setdefault(
            normalized,
            TptpSourceInfo(name=name, decoded_name=decode_tptp_identifier(name), role=role, hash=source_hash),
        )
    return sources


def vampire_input_step_sources(proof_text: str | None, problem: Path | None) -> dict[str, TptpSourceInfo]:
    if proof_text is None:
        return {}
    by_formula = problem_formula_sources(problem)
    if not by_formula:
        return {}
    sources: dict[str, TptpSourceInfo] = {}
    for line in proof_text.splitlines():
        match = MEGALODON_STEP_FORMULA_RE.match(line.strip())
        if match is None or json.loads(f'"{match.group("rule")}"') != "input":
            continue
        formula = json.loads(f'"{match.group("formula")}"')
        parsed = tptp_decl_parts(formula)
        if parsed is None:
            continue
        _, role, body, _ = parsed
        if role not in {"axiom", "conjecture"}:
            continue
        source = by_formula.get(normalize_tptp_formula_body(body))
        if source is not None:
            sources["S" + match.group("id")] = source
    return sources


def source_info_comment(prefix: str, info: TptpSourceInfo, source: str | None) -> list[str]:
    label = f"{prefix}: {comment_text(info.decoded_name)}"
    details: list[str] = []
    if info.name != info.decoded_name:
        details.append(f"tptp {comment_text(info.name)}")
    if info.hash is not None:
        details.append(f"hash {info.hash}")
    comments = [f"// {label}" + (f" ({', '.join(details)})" if details else "")]
    locations = source_dependency_locations(source, [info.decoded_name])
    if locations:
        comments.append(f"// source location: {', '.join(comment_text(location) for location in locations)}")
    return comments


def annotate_source_links(lines: list[str], proof: Path | None, proof_text: str | None, source: str | None) -> list[str]:
    problem = problem_path_for_proof(proof) if proof is not None else None
    step_sources = vampire_input_step_sources(proof_text, problem)
    if not step_sources:
        return list(lines)

    proposition_sources: dict[str, TptpSourceInfo] = {}
    for line in lines:
        claim = proposition_after_colon(line, "claim ")
        if claim is not None and claim[0] in step_sources:
            proposition_sources.setdefault(claim[1], step_sources[claim[0]])

    result: list[str] = []
    for line in lines:
        axiom = proposition_after_colon(line, "Axiom ")
        if axiom is not None and axiom[1] in proposition_sources:
            result.extend(source_info_comment("source axiom", proposition_sources[axiom[1]], source))
        claim = proposition_after_colon(line, "claim ")
        if claim is not None and claim[0] in step_sources:
            info = step_sources[claim[0]]
            result.extend(source_info_comment(f"source {info.role}", info, source))
        result.append(line)
    return result


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
        locations = source_dependency_locations(obligation.source, dependencies)
        if locations:
            header.append(f"// source dependency locations: {', '.join(comment_text(location) for location in locations)}")
        local_locations = source_local_dependency_locations(obligation.source, obligation.theorem_line, obligation.line, dependencies)
        if local_locations:
            header.append(f"// source local dependencies: {', '.join(comment_text(location) for location in local_locations)}")
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
    source: str | None = None,
) -> list[str]:
    safe_kind = kind.replace(" ", "_")
    lines = add_problem_type_variables(lines, proof, proof_text)
    output_lines = add_function_definition_skeletons(lines, proof_text)
    output_lines = add_recovered_input_equalities(output_lines, proof_text)
    output_lines = add_recovered_input_axioms(output_lines, proof_text)
    output_lines = add_problem_predicate_eliminator_axioms(output_lines, proof)
    output_lines = add_problem_type_variables(output_lines, proof, proof_text)
    output_lines = normalize_vampire_boolean_literals(output_lines)
    output_lines = add_missing_basic_connective_definitions(output_lines)
    output_lines = add_boolean_extensionality_helpers(output_lines)
    output_lines = parenthesize_atomic_axiom_propositions(output_lines)
    output_lines = fill_source_candidate_claims(output_lines, proof_text)
    output_lines = fill_repeated_claim_admits(output_lines) if fill_repeated_admits else output_lines
    output_lines = prune_unused_rectify_axiom_admits(output_lines, proof_text)
    output_lines = prune_unreachable_claims(output_lines) if fill_repeated_admits else output_lines
    output_lines = annotate_remaining_admits(output_lines, proof_text)
    output_lines = annotate_source_links(output_lines, proof, proof_text, source)
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
    if contains_executable_aby(output_lines):
        candidate.unlink(missing_ok=True)
        return [f"{proof}: generated {kind} {index} uses aby"]
    demoted_exact = False
    def demote_failed_exact(stdout: str) -> bool:
        nonlocal demoted_exact
        if not allow_incomplete or kind != "claim skeleton":
            return False
        match = re.search(r"Failure at line (?P<line>[0-9]+) char [0-9]+:", stdout)
        if match is None:
            return False
        line_index = int(match.group("line")) - 1
        if not (0 <= line_index < len(output_lines)):
            return False

        def replacement_for_claim(claim_index: int, proof_index: int | None = None) -> str:
            proof_name = proof_for_claim_at(output_lines, claim_index)
            if proof_name is None:
                return "{ admit. }"
            replacement = "{ exact " + proof_argument_text(proof_name) + ". }"
            if proof_index is not None and 0 <= proof_index < len(output_lines) and output_lines[proof_index] == replacement:
                return "{ admit. }"
            return replacement

        inline_candidates = [line_index]
        if line_index + 1 < len(output_lines):
            inline_candidates.append(line_index + 1)
        for candidate_index in inline_candidates:
            if (
                0 <= candidate_index < len(output_lines)
                and (
                    output_lines[candidate_index].startswith("{ exact ")
                    or output_lines[candidate_index].lstrip().startswith("exact ")
                )
                and candidate_index > 0
                and output_lines[candidate_index - 1].startswith("claim ")
            ):
                output_lines[candidate_index] = replacement_for_claim(candidate_index - 1, candidate_index)
                candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
                demoted_exact = True
                return True

        nearest_claim = line_index
        while nearest_claim >= 0 and not output_lines[nearest_claim].startswith("claim "):
            nearest_claim -= 1
        if nearest_claim >= 0 and nearest_claim + 1 < len(output_lines):
            proof_index = nearest_claim + 1
            if output_lines[proof_index].startswith("{ exact "):
                output_lines[proof_index] = replacement_for_claim(nearest_claim, proof_index)
                candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
                demoted_exact = True
                return True
            if output_lines[proof_index] == "{":
                block_end = proof_index + 1
                while block_end < len(output_lines) and output_lines[block_end] != "}":
                    block_end += 1
                if block_end < len(output_lines):
                    output_lines[proof_index : block_end + 1] = [replacement_for_claim(nearest_claim)]
                    candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
                    demoted_exact = True
                    return True

        block_start = line_index
        while block_start >= 0 and output_lines[block_start] != "{":
            block_start -= 1
        if (
            block_start > 0
            and output_lines[block_start - 1].startswith("claim ")
            and line_index + 1 < len(output_lines)
            and output_lines[line_index].lstrip().startswith("exact ")
        ):
            block_end = line_index + 1
            while block_end < len(output_lines) and output_lines[block_end] != "}":
                block_end += 1
            if block_end < len(output_lines):
                output_lines[block_start : block_end + 1] = [replacement_for_claim(block_start - 1)]
                candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
                demoted_exact = True
                return True
        return False

    try:
        cmd = [str(megalodon)]
        if allow_incomplete:
            cmd.append("-allowincompleteqed")
        cmd.append(str(candidate))
        for _ in range(8):
            proc = run(cmd, repo)
            if proc.returncode == 0:
                if demoted_exact and output_dir is not None:
                    output_lines = annotate_remaining_admits(output_lines, proof_text)
                    candidate.write_text("\n".join(output_lines) + "\n", encoding="utf-8")
                return []
            if not demote_failed_exact(proc.stdout):
                return [f"{proof}: Megalodon rejected {kind} {index}: {proc.stdout.strip()}"]
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
    claim_admits = 0
    refutation_implication_admits = 0
    refutation_boundary_admits = 0
    negated_conjecture_admits = 0
    conjecture_anchor_admits = 0
    false_admits = 0
    constructive_admits = 0
    constructive_non_anchor_admits = 0
    admitted_roles: dict[str, int] = {}

    def preceding_vampire_role(index: int) -> str | None:
        cursor = index - 2
        while cursor >= 0 and lines[cursor].startswith("// "):
            if lines[cursor].startswith("// vampire step "):
                return lines[cursor].split(": ", 1)[1] if ": " in lines[cursor] else lines[cursor]
            cursor -= 1
        return None

    for index, line in enumerate(lines):
        if line != "{ admit. }" or index == 0:
            continue
        claim_admits += 1
        claim = proposition_after_colon(lines[index - 1], "claim ")
        proposition = claim[1] if claim is not None else ""
        role = preceding_vampire_role(index)
        is_negated_conjecture = role is not None and "negated_conjecture" in role
        if role is not None:
            admitted_roles[role] = admitted_roles.get(role, 0) + 1
            if proposition.endswith("-> vampire_false") and "conjecture" in role:
                refutation_boundary_admits += 1
            elif "conjecture" in role and not is_negated_conjecture:
                conjecture_anchor_admits += 1
        if proposition == "vampire_false":
            false_admits += 1
        elif proposition.endswith("-> vampire_false"):
            refutation_implication_admits += 1
        elif is_negated_conjecture:
            negated_conjecture_admits += 1
        else:
            constructive_admits += 1
            if not (role is not None and "conjecture" in role):
                constructive_non_anchor_admits += 1
    return {
        "file": str(path),
        "problem": header.get("problem"),
        "proof": header.get("proof"),
        "source": header.get("source"),
        "enclosing_theorem": header.get("enclosing_theorem"),
        "source_line": header.get("source_line"),
        "source_dependencies": header.get("source_dependencies"),
        "source_local_dependencies": header.get("source_local_dependencies"),
        "claims": sum(1 for line in lines if line.startswith("claim ")),
        "claim_admits": claim_admits,
        "constructive_claim_admits": constructive_admits,
        "constructive_non_anchor_admits": constructive_non_anchor_admits,
        "refutation_implication_admits": refutation_implication_admits,
        "refutation_boundary_admits": refutation_boundary_admits,
        "negated_conjecture_admits": negated_conjecture_admits,
        "conjecture_anchor_admits": conjecture_anchor_admits,
        "false_claim_admits": false_admits,
        "admitted_vampire_roles": admitted_roles,
        "final_admits": sum(1 for line in lines if line == "admit."),
        "aby_commands": sum(1 for line in lines if ABY_COMMAND_RE.match(line) and not line.lstrip().startswith("//")),
        "filled_claims": sum(1 for line in lines if line.startswith("{ exact ")),
        "first_remaining": first_remaining,
    }


def write_claim_skeleton_summary(index: Path, rows: list[dict[str, object]]) -> Path:
    summary = {
        "files": len(rows),
        "claims": sum(int(row["claims"]) for row in rows),
        "claim_admits": sum(int(row["claim_admits"]) for row in rows),
        "constructive_claim_admits": sum(int(row["constructive_claim_admits"]) for row in rows),
        "constructive_non_anchor_admits": sum(int(row.get("constructive_non_anchor_admits", 0)) for row in rows),
        "refutation_implication_admits": sum(int(row["refutation_implication_admits"]) for row in rows),
        "refutation_boundary_admits": sum(int(row.get("refutation_boundary_admits", 0)) for row in rows),
        "negated_conjecture_admits": sum(int(row.get("negated_conjecture_admits", 0)) for row in rows),
        "conjecture_anchor_admits": sum(int(row.get("conjecture_anchor_admits", 0)) for row in rows),
        "false_claim_admits": sum(int(row["false_claim_admits"]) for row in rows),
        "final_admits": sum(int(row["final_admits"]) for row in rows),
        "aby_commands": sum(int(row.get("aby_commands", 0)) for row in rows),
        "filled_claims": sum(int(row["filled_claims"]) for row in rows),
    }
    role_counts: dict[str, int] = {}
    for row in rows:
        for role, count in dict(row["admitted_vampire_roles"]).items():
            role_counts[str(role)] = role_counts.get(str(role), 0) + int(count)
    summary["admitted_vampire_roles"] = role_counts
    path = index.with_suffix(".summary.json")
    path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def write_claim_skeleton_index(directory: Path) -> Path | None:
    if not directory.exists():
        return None
    paths = sorted(directory.glob("*.mg"))
    if not paths:
        return None
    index = directory / "index.jsonl"
    rows = [summarize_claim_skeleton(path) for path in paths]
    with index.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True))
            handle.write("\n")
    write_claim_skeleton_summary(index, rows)
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


def cached_vampire_result(
    args: argparse.Namespace,
    line: int,
    char: int,
    problem: Path,
    proof_path: Path,
) -> tuple[Obligation, str | None, bool]:
    out = proof_path.read_text(encoding="utf-8", errors="replace")
    status_match = PROVED_RE.search(out)
    status = status_match.group(1) if status_match else None
    obligation = Obligation(
        line=line,
        char=char,
        problem=str(problem),
        proof=str(proof_path),
        problem_sha256=sha256(problem),
        proof_sha256=sha256(proof_path),
        status=status,
        command=vampire_command(args, problem, proof_path),
        **source_context(getattr(args, "resolved_source", None), line),
    )
    proof_payload_ok = proof_has_reconstruction_payload(out, args.proof_mode)
    failure = None
    if proof_has_fatal_output(out):
        failure = f"{problem.name}: cached Vampire output contained a fatal error marker"
    elif args.proof_mode == "leancheck":
        if not proof_payload_ok:
            failure = f"{problem.name}: cached Vampire LeanChecker output had no complete Lean proof payload"
    elif args.proof_mode == "megalodon":
        if not proof_payload_ok:
            failure = f"{problem.name}: cached Vampire Megalodon output had no complete reconstruction payload"
    elif not status:
        failure = f"{problem.name}: cached Vampire output did not report a proved SZS status"
    elif not proof_payload_ok:
        failure = f"{problem.name}: cached Vampire output had status {status} but no proof payload"
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
    accepted_label = "accepted" if args.collect_successes else "recorded"

    def accept_finished_result(obligation: Obligation, failure: str | None, proof_payload_ok: bool) -> None:
        nonlocal skipped
        if args.collect_successes:
            skeleton_ok = (
                not args.require_claim_skeletons
                or "megalodon_claim_skeleton_start."
                in Path(obligation.proof).read_text(encoding="utf-8", errors="replace")
            )
            if failure is None and proof_payload_ok and skeleton_ok:
                obligations.append(obligation)
            else:
                skipped += 1
        else:
            obligations.append(obligation)
            if failure is not None:
                failures.append(failure)

    def should_schedule() -> bool:
        if next_index >= len(selected_items):
            return False
        if args.collect_successes and len(obligations) >= args.limit:
            return False
        return True

    try:
        while running or should_schedule():
            while len(running) < jobs and should_schedule():
                line, char, problem = selected_items[next_index]
                next_index += 1
                proof_path = proof_dir / f"{problem.stem}.{args.proof_mode}.out"
                if args.reuse_existing_proofs and proof_path.exists():
                    obligation, failure, proof_payload_ok = cached_vampire_result(args, line, char, problem, proof_path)
                    completed += 1
                    accept_finished_result(obligation, failure, proof_payload_ok)
                    if args.progress and (completed % args.progress == 0 or len(obligations) >= args.limit):
                        print(
                            f"completed {completed}; {accepted_label} {len(obligations)}; "
                            f"running {len(running)}; queued {next_index}/{len(selected_items)}",
                            flush=True,
                        )
                    continue
                running.append(start_vampire(repo, args, proof_dir, (line, char, problem)))

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
                accept_finished_result(obligation, failure, proof_payload_ok)

                if args.progress and (completed % args.progress == 0 or len(obligations) >= args.limit):
                    print(
                        f"completed {completed}; {accepted_label} {len(obligations)}; "
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
                        source=obligation.source,
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
                    source=obligation.source,
                )
    return failures, checked_sources, checked_skeletons


def check_existing(
    manifest: Path,
    repo: Path,
    megalodon: Path,
    jobs: int = 1,
    progress: int = 0,
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
    completed = 0

    def report_progress() -> None:
        nonlocal completed
        completed += 1
        if progress and (completed % progress == 0 or completed == len(obligations)):
            print(
                f"checked {completed}/{len(obligations)} manifest entries",
                file=sys.stderr,
                flush=True,
            )

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
            report_progress()
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as executor:
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
                report_progress()

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
    parser.add_argument("--export-mode", choices=["aby", "admit"], default="aby")
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--timeout", type=int, default=10)
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("MEGALODON_VAMPIRE_JOBS", "1")))
    parser.add_argument("--progress", type=int, default=10)
    parser.add_argument("--schedule", default="casc")
    parser.add_argument("--proof-mode", choices=["tptp", "leancheck", "megalodon"], default="tptp")
    parser.add_argument("--vampire", type=Path, default=Path(os.environ.get("VAMPIRE", "vampire")))
    parser.add_argument("--vampire-arg", action="append", nargs="+")
    parser.add_argument("--collect-successes", action="store_true")
    parser.add_argument("--reuse-existing-proofs", action="store_true")
    parser.add_argument("--generate-only", action="store_true")
    parser.add_argument("--select-all-generated", action="store_true")
    parser.add_argument("--check-existing", type=Path)
    parser.add_argument("--from-manifest", type=Path)
    parser.add_argument("--check-megalodon-sources", action="store_true")
    parser.add_argument("--require-megalodon-sources", action="store_true")
    parser.add_argument("--check-claim-skeletons", action="store_true")
    parser.add_argument("--require-claim-skeletons", action="store_true")
    parser.add_argument("--claim-skeleton-dir", type=Path)
    parser.add_argument("--index-claim-skeleton-dir", type=Path)
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

    if args.index_claim_skeleton_dir:
        skeleton_dir = (
            (repo / args.index_claim_skeleton_dir).resolve()
            if not args.index_claim_skeleton_dir.is_absolute()
            else args.index_claim_skeleton_dir
        )
        index = write_claim_skeleton_index(skeleton_dir)
        if index is None:
            raise SystemExit(f"no claim skeletons found in {skeleton_dir}")
        print(f"claim skeleton index: {index}")
        print(f"claim skeleton summary: {index.with_suffix('.summary.json')}")
        return 0

    if args.check_existing:
        obligations, checked_sources, checked_skeletons = check_existing(
            args.check_existing,
            repo,
            megalodon,
            args.jobs,
            args.progress,
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
    prefix = work_dir / args.export_mode
    if args.from_manifest:
        selected = obligations_from_manifest(args.from_manifest)
        if len(selected) < args.limit:
            raise SystemExit(f"Need {args.limit} known-solvable obligations, found {len(selected)} in {args.from_manifest}")
        selected_for_run = selected if args.collect_successes else selected[: args.limit]
    else:
        generate_problems(repo, megalodon, source, prefix, args.export_mode)
        if args.select_all_generated:
            selected = generated_th0(prefix)
            if len(selected) < args.limit:
                raise SystemExit(f"Need {args.limit} generated TH0 obligations, found {len(selected)}")
        else:
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
            args.progress,
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
