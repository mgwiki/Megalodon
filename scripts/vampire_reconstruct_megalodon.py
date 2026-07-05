#!/usr/bin/env python3
"""Generate and check Megalodon TH0 hammer obligations with Vampire proofs.

This is the reproducible test driver for the Vampire-to-Megalodon proof
reconstruction work.  It intentionally uses Megalodon's own TH0 generator as
the source of truth, then selects obligations whose source lines are recorded
as HO-Vampire-solvable in examples/hammer/ATPresults2025.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable


RESULT_RE = re.compile(r"^hammer\.(?P<line>[0-9]+)\.(?P<char>[0-9]+)\.\*\.p:")
PROBLEM_RE = re.compile(r"^(?P<prefix>.*)\.(?P<line>[0-9]+)\.(?P<char>[0-9]+)\.th0\.p$")
PROVED_RE = re.compile(r"SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)\b")


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


def select_obligations(prefix: Path, vampire_lines: set[int], minimum: int) -> list[tuple[int, int, Path]]:
    selected = [(line, char, path) for line, char, path in generated_th0(prefix) if line in vampire_lines]
    if len(selected) < minimum:
        raise SystemExit(f"Need {minimum} generated HO-Vampire obligations, found {len(selected)}")
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
        if args.proof_mode == "leancheck":
            cmd.extend(
                [
                    "--output_mode",
                    "lean",
                    "--proof_extra",
                    "lean",
                    "--skolemization",
                    "syntactic",
                    "--shuffle_input",
                    "off",
                ]
            )
    cmd.append(str(problem))
    return cmd


def proof_has_reconstruction_payload(text: str, proof_mode: str) -> bool:
    if proof_mode == "leancheck":
        return "end vamproof" in text or "theorem fullProof" in text
    return "inference(" in text or "SZS output start Proof" in text or "Refutation" in text


def proof_mode_from_path(path: Path) -> str:
    if path.name.endswith(".leancheck.out"):
        return "leancheck"
    return "tptp"


def start_vampire(repo: Path, args: argparse.Namespace, proof_dir: Path, item: tuple[int, int, Path]) -> RunningVampire:
    line, char, problem = item
    proof_path = proof_dir / f"{problem.stem}.{args.proof_mode}.out"
    cmd = vampire_command(args, problem, proof_path)
    process = subprocess.Popen(
        cmd,
        cwd=str(repo),
        text=True,
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
    )
    proof_payload_ok = proof_has_reconstruction_payload(out, args.proof_mode) if status else False
    failure = None
    if timed_out:
        failure = f"{running.problem.name}: Vampire subprocess timed out"
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
                timed_out = item.process.poll() is None and now - item.started_at > args.timeout + 15
                if item.process.poll() is None and not timed_out:
                    continue
                running.remove(item)
                obligation, failure, proof_payload_ok = finish_vampire(item, args, timed_out=timed_out)
                completed += 1
                made_progress = True
                if args.collect_successes:
                    if failure is None and proof_payload_ok:
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


def check_existing(manifest: Path) -> list[Obligation]:
    obligations = []
    failures = []
    for row in manifest.read_text(encoding="utf-8").splitlines():
        if not row.strip():
            continue
        data = json.loads(row)
        obligation = Obligation(**data)
        obligations.append(obligation)
        problem = Path(obligation.problem)
        proof = Path(obligation.proof)
        if not problem.exists():
            failures.append(f"{problem}: missing problem file")
            continue
        if sha256(problem) != obligation.problem_sha256:
            failures.append(f"{problem}: problem hash changed")
        if not proof.exists():
            failures.append(f"{proof}: missing proof file")
            continue
        if obligation.proof_sha256 and sha256(proof) != obligation.proof_sha256:
            failures.append(f"{proof}: proof hash changed")
        text = proof.read_text(encoding="utf-8", errors="replace")
        if not PROVED_RE.search(text):
            failures.append(f"{proof}: no proved SZS status")
        elif not proof_has_reconstruction_payload(text, proof_mode_from_path(proof)):
            failures.append(f"{proof}: no proof payload")
    if failures:
        for failure in failures:
            print(failure, file=sys.stderr)
        raise SystemExit(f"{len(failures)} manifest checks failed")
    return obligations


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
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--jobs", type=int, default=int(os.environ.get("MEGALODON_VAMPIRE_JOBS", "1")))
    parser.add_argument("--progress", type=int, default=10)
    parser.add_argument("--schedule", default="casc")
    parser.add_argument("--proof-mode", choices=["tptp", "leancheck"], default="tptp")
    parser.add_argument("--vampire", type=Path, default=Path(os.environ.get("VAMPIRE", "vampire")))
    parser.add_argument("--vampire-arg", action="append", nargs="+")
    parser.add_argument("--collect-successes", action="store_true")
    parser.add_argument("--generate-only", action="store_true")
    parser.add_argument("--check-existing", type=Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    megalodon = (repo / args.megalodon).resolve() if not args.megalodon.is_absolute() else args.megalodon
    source = (repo / args.source).resolve() if not args.source.is_absolute() else args.source
    results = (repo / args.results).resolve() if not args.results.is_absolute() else args.results
    work_dir = (repo / args.work_dir).resolve() if not args.work_dir.is_absolute() else args.work_dir

    if args.check_existing:
        obligations = check_existing(args.check_existing)
        print(f"checked {len(obligations)} recorded Vampire proof outputs")
        return 0

    if not megalodon.exists():
        raise SystemExit(f"Megalodon executable not found: {megalodon}")

    work_dir.mkdir(parents=True, exist_ok=True)
    prefix = work_dir / "hammer"
    generate_problems(repo, megalodon, source, prefix)
    selected = select_obligations(prefix, parse_vampire_lines(results), args.limit)
    selected_for_run = selected if args.collect_successes else selected[: args.limit]
    selection_path = work_dir / "selected_th0.txt"
    selection_path.write_text("\n".join(str(path) for _, _, path in selected_for_run) + "\n", encoding="utf-8")

    if args.generate_only:
        print(f"generated {len(generated_th0(prefix))} TH0 obligations")
        print(f"selected {len(selected_for_run)} HO-Vampire obligations in {selection_path}")
        return 0

    if shutil.which(str(args.vampire)) is None and not args.vampire.exists():
        raise SystemExit(f"Vampire executable not found: {args.vampire}")

    obligations = run_vampire_suite(repo, args, selected_for_run, work_dir / "proofs")
    manifest = work_dir / "manifest.jsonl"
    write_manifest(manifest, obligations)
    print(f"checked {len(obligations)} Vampire proofs")
    print(f"manifest: {manifest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
