"""Run the canonical local SOLO benchmark.

Usage:
    python3 -m pipeline.solo_benchmark
    python3 -m pipeline.solo_benchmark --dry-run

The versioned profile lives at ``benchmarks/solo.json``. Results are written
under the ignored ``pipeline/results/`` tree and resume by solver/profile/input
fingerprint.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import platform
import subprocess
import sys
import time
from concurrent.futures import Future, ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from pipeline.proxy import load_config, load_problems, run_solver

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = REPO_ROOT / "benchmarks" / "solo.json"


@dataclass(frozen=True, slots=True)
class ProblemJob:
    source_path: Path
    source_relative: Path
    source_index: int
    problem: dict[str, Any]
    timeout_seconds: int


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_profile(profile_path: Path) -> dict[str, Any]:
    profile = json.loads(profile_path.read_text(encoding="utf-8"))
    if profile.get("schema_version") != 1 or profile.get("mode") != "solo":
        raise ValueError("benchmark profile must use schema_version=1 and mode=solo")
    return profile


def discover_problem_files(profile: dict[str, Any]) -> list[Path]:
    problem_config = profile["problems"]
    root = REPO_ROOT / problem_config["root"]
    extensions = set(problem_config["include_extensions"])
    excludes = tuple(problem_config["exclude_globs"])
    files = []
    for path in root.rglob("*"):
        if not path.is_file() or path.suffix not in extensions:
            continue
        relative = path.relative_to(root)
        if any(relative.match(pattern) for pattern in excludes):
            continue
        files.append(path)
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def timeout_for(
    problem: dict[str, Any], source_relative: Path, profile: dict[str, Any]
) -> int:
    timeout_config = profile["timeouts_seconds"]
    markers = [str(marker).casefold() for marker in timeout_config["hard_markers"]]
    difficulty = str(problem.get("difficulty", "")).casefold()
    source = source_relative.as_posix().casefold()
    if any(marker in difficulty or marker in source for marker in markers):
        return int(timeout_config["hard_or_order5"])
    return int(timeout_config["normal"])


def _git_commit() -> str | None:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def _benchmark_fingerprint(
    profile_path: Path,
    profile: dict[str, Any],
    submission: Path,
    base_config_path: Path,
    problem_files: list[Path],
) -> str:
    problem_root = REPO_ROOT / profile["problems"]["root"]
    material = {
        "profile_sha256": _sha256(profile_path),
        "solver_sha256": _sha256(submission / "solver.py"),
        "pipeline_config_sha256": _sha256(base_config_path),
        "problem_files": [
            {
                "path": path.relative_to(problem_root).as_posix(),
                "sha256": _sha256(path),
            }
            for path in problem_files
        ],
    }
    encoded = json.dumps(material, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def _atomic_write_json(path: Path, value: Any) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _result_path(run_directory: Path, source_relative: Path) -> Path:
    return run_directory / source_relative.parent / f"{source_relative.name}.results.jsonl"


def _load_completed(path: Path) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    completed: dict[str, dict[str, Any]] = {}
    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw.strip():
            continue
        try:
            row = json.loads(raw)
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{line_number}: corrupt result row") from error
        problem_id = str(row["id"])
        if problem_id in completed:
            raise ValueError(f"{path}: duplicate completed id {problem_id!r}")
        completed[problem_id] = row
    return completed


def _append_result(path: Path, row: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(row, ensure_ascii=False) + "\n")
        stream.flush()


def _run_job(
    job: ProblemJob,
    submission: Path,
    base_config: dict[str, Any],
    strip_answer: bool,
) -> dict[str, Any]:
    config = copy.deepcopy(base_config)
    config["solver"]["timeout_seconds"] = job.timeout_seconds
    public_problem = dict(job.problem)
    if strip_answer:
        public_problem.pop("answer", None)
    started = time.monotonic()
    result = run_solver(submission, public_problem, config)
    elapsed = time.monotonic() - started
    expected = job.problem.get("answer")
    expected_verdict = None
    if isinstance(expected, bool):
        expected_verdict = "true" if expected else "false"
    return {
        "id": job.problem["id"],
        "source_file": job.source_relative.as_posix(),
        "source_index": job.source_index,
        "eq1_id": job.problem["eq1_id"],
        "eq2_id": job.problem["eq2_id"],
        "difficulty": job.problem.get("difficulty"),
        "expected_answer": expected,
        "timeout_seconds": job.timeout_seconds,
        "elapsed_seconds": round(elapsed, 3),
        "label_match": (
            result.get("verdict") == expected_verdict
            if result.get("solved") and expected_verdict is not None
            else None
        ),
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        **result,
    }


def _summarize(
    jobs: list[ProblemJob], completed: dict[Path, dict[str, dict[str, Any]]]
) -> dict[str, Any]:
    by_source: dict[str, dict[str, Any]] = {}
    all_rows: list[dict[str, Any]] = []
    for source_path, rows_by_id in completed.items():
        rows = list(rows_by_id.values())
        all_rows.extend(rows)
        by_source[source_path.as_posix()] = {
            "completed": len(rows),
            "solved": sum(bool(row.get("solved")) for row in rows),
            "judge_calls": sum(int(row.get("judge_calls", 0)) for row in rows),
            "llm_calls": sum(int(row.get("llm_calls", 0)) for row in rows),
            "elapsed_seconds": round(
                sum(float(row.get("elapsed_seconds", 0.0)) for row in rows), 3
            ),
        }
    return {
        "updated_at_utc": datetime.now(timezone.utc).isoformat(),
        "scheduled": len(jobs),
        "completed": len(all_rows),
        "solved": sum(bool(row.get("solved")) for row in all_rows),
        "label_mismatches": sum(row.get("label_match") is False for row in all_rows),
        "judge_calls": sum(int(row.get("judge_calls", 0)) for row in all_rows),
        "llm_calls": sum(int(row.get("llm_calls", 0)) for row in all_rows),
        "elapsed_seconds": round(
            sum(float(row.get("elapsed_seconds", 0.0)) for row in all_rows), 3
        ),
        "by_source": dict(sorted(by_source.items())),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the canonical local SOLO benchmark")
    parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    parser.add_argument("--workers", type=int, default=None)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    profile_path = args.profile.resolve()
    profile = load_profile(profile_path)
    submission = (REPO_ROOT / profile["submission"]).resolve()
    base_config_path = (REPO_ROOT / profile["base_pipeline_config"]).resolve()
    base_config = load_config(base_config_path)
    problem_root = (REPO_ROOT / profile["problems"]["root"]).resolve()
    problem_files = discover_problem_files(profile)
    if not problem_files:
        raise ValueError("benchmark profile selected no problem files")

    jobs: list[ProblemJob] = []
    seen_per_file: dict[Path, set[str]] = {}
    for source_path in problem_files:
        relative = source_path.relative_to(problem_root)
        seen_per_file[relative] = set()
        for index, problem in enumerate(load_problems(source_path), 1):
            problem_id = str(problem["id"])
            if problem_id in seen_per_file[relative]:
                raise ValueError(f"{relative}: duplicate problem id {problem_id!r}")
            seen_per_file[relative].add(problem_id)
            jobs.append(
                ProblemJob(
                    source_path,
                    relative,
                    index,
                    problem,
                    timeout_for(problem, relative, profile),
                )
            )

    tier_counts: dict[int, int] = {}
    for job in jobs:
        tier_counts[job.timeout_seconds] = tier_counts.get(job.timeout_seconds, 0) + 1
    print(f"SOLO benchmark: {len(problem_files)} files, {len(jobs)} file entries")
    print(
        "Timeout tiers: "
        + ", ".join(f"{timeout}s={count}" for timeout, count in sorted(tier_counts.items()))
    )
    for path in problem_files:
        print(f"  {path.relative_to(REPO_ROOT)}")
    if args.dry_run:
        return 0

    workers = args.workers or int(profile["execution"]["workers"])
    if workers < 1:
        raise ValueError("workers must be positive")
    fingerprint = _benchmark_fingerprint(
        profile_path, profile, submission, base_config_path, problem_files
    )
    output_root = REPO_ROOT / profile["output_directory"]
    run_directory = output_root / f"{submission.name}-{fingerprint[:12]}"
    run_directory.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema_version": 1,
        "benchmark_fingerprint": fingerprint,
        "profile": profile,
        "profile_path": profile_path.relative_to(REPO_ROOT).as_posix(),
        "submission": submission.relative_to(REPO_ROOT).as_posix(),
        "solver_sha256": _sha256(submission / "solver.py"),
        "base_pipeline_config_sha256": _sha256(base_config_path),
        "git_commit": _git_commit(),
        "python": sys.version,
        "platform": platform.platform(),
        "workers": workers,
        "problem_files": [
            {
                "path": path.relative_to(problem_root).as_posix(),
                "sha256": _sha256(path),
            }
            for path in problem_files
        ],
    }
    manifest_path = run_directory / "manifest.json"
    if manifest_path.exists():
        existing_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if existing_manifest["benchmark_fingerprint"] != fingerprint:
            raise ValueError(f"fingerprint mismatch in {manifest_path}")
    else:
        _atomic_write_json(manifest_path, manifest)

    completed: dict[Path, dict[str, dict[str, Any]]] = {}
    pending: list[ProblemJob] = []
    for job in jobs:
        if job.source_relative not in completed:
            completed[job.source_relative] = _load_completed(
                _result_path(run_directory, job.source_relative)
            )
        rows = completed[job.source_relative]
        if job.problem["id"] not in rows:
            pending.append(job)

    print(f"Workers: {workers}; resumed: {len(jobs) - len(pending)}; pending: {len(pending)}")
    print(f"Output: {run_directory.relative_to(REPO_ROOT)}")
    strip_answer = bool(profile["execution"]["strip_answer_before_solver"])
    done = len(jobs) - len(pending)

    futures: dict[Future[dict[str, Any]], ProblemJob] = {}
    with ThreadPoolExecutor(max_workers=workers) as executor:
        for job in pending:
            future = executor.submit(
                _run_job, job, submission, base_config, strip_answer
            )
            futures[future] = job
        for future in as_completed(futures):
            job = futures[future]
            row = future.result()
            path = _result_path(run_directory, job.source_relative)
            _append_result(path, row)
            completed[job.source_relative][str(row["id"])] = row
            done += 1
            state = "SOLVED" if row["solved"] else "FAILED"
            print(
                f"[{done}/{len(jobs)}] {job.source_relative}:{row['id']} "
                f"{state} {row['elapsed_seconds']:.1f}s "
                f"[judge:{row['judge_calls']}, llm:{row['llm_calls']}]",
                flush=True,
            )
            if done % 25 == 0:
                _atomic_write_json(
                    run_directory / "summary.json", _summarize(jobs, completed)
                )

    summary = _summarize(jobs, completed)
    _atomic_write_json(run_directory / "summary.json", summary)
    print(
        f"Complete: {summary['solved']}/{summary['completed']} solved; "
        f"judge={summary['judge_calls']}; llm={summary['llm_calls']}; "
        f"aggregate case time={summary['elapsed_seconds']:.1f}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
