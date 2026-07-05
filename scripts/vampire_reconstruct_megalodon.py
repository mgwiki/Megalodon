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


def fill_repeated_claim_admits(lines: list[str]) -> list[str]:
    known: dict[str, str] = {}
    theorem: str | None = None
    result = list(lines)
    index = 0
    while index < len(result):
        line = result[index]
        axiom = proposition_after_colon(line, "Axiom ")
        if axiom is not None:
            name, proposition = axiom
            known.setdefault(proposition, name)
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
            proof_name = known.get(proposition)
            if proof_name is not None and index + 1 < len(result) and result[index + 1] == "{ admit. }":
                result[index + 1] = "{ exact " + proof_name + ". }"
            known.setdefault(proposition, name)
            index += 2
            continue
        if line == "admit." and theorem is not None:
            proof_name = known.get(theorem)
            if proof_name is not None:
                result[index] = "exact " + proof_name + "."
        index += 1
    return result


def comment_text(value: object) -> str:
    text = "" if value is None else str(value)
    return text.replace("\r", " ").replace("\n", " ")


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
) -> list[str]:
    safe_kind = kind.replace(" ", "_")
    output_lines = fill_repeated_claim_admits(lines) if fill_repeated_admits else list(lines)
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
    print(f"manifest: {manifest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
