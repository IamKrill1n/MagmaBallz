"""Run the locked, balanced local Marathon benchmark.

The profile is intentionally offline: every solver receives the same wall
budget and zero LLM tokens. This keeps iteration deterministic and free while
still exercising problem ordering, native search, validation, and interruption
handling. The official token-enabled runner remains ``scripts/run_marathon.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import tempfile
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pipeline.marathon_runner import run_marathon
from pipeline.marathon_score import score_marathon


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = REPO_ROOT / "benchmarks" / "marathon.json"


@dataclass(frozen=True, slots=True)
class SolverCandidate:
    name: str
    source: Path


def load_profile(path: Path) -> dict[str, Any]:
    profile = json.loads(path.read_text(encoding="utf-8"))
    if profile.get("schema_version") != 1 or profile.get("mode") != "marathon":
        raise ValueError("benchmark profile must use schema_version=1 and mode=marathon")
    return profile


def load_manifest(path: Path) -> list[dict[str, Any]]:
    problems = [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    ids = [str(problem.get("id")) for problem in problems]
    if len(ids) != len(set(ids)):
        raise ValueError("benchmark manifest contains duplicate problem ids")
    if any("answer" in problem for problem in problems):
        raise ValueError("benchmark manifest must not expose answer labels")
    return problems


def validate_balance(
    problems: list[dict[str, Any]], profile: dict[str, Any]
) -> Counter[str]:
    actual = Counter(str(problem.get("difficulty")) for problem in problems)
    expected = Counter(
        {str(key): int(value) for key, value in profile["expected_difficulty_counts"].items()}
    )
    if actual != expected:
        raise ValueError(f"manifest difficulty counts {dict(actual)} != {dict(expected)}")
    return actual


def discover_demo_solvers(root: Path) -> list[SolverCandidate]:
    candidates: list[SolverCandidate] = []
    for path in sorted(root.iterdir(), key=lambda item: item.name.casefold()):
        if path.is_file() and path.suffix == ".py":
            candidates.append(SolverCandidate(path.stem, path))
        elif path.is_dir() and (path / "solver.py").is_file():
            candidates.append(SolverCandidate(path.name, path / "solver.py"))
    return candidates


def parse_candidate(value: str) -> SolverCandidate:
    if "=" in value:
        name, raw_path = value.split("=", 1)
    else:
        raw_path = value
        name = Path(value).stem
    source = Path(raw_path)
    if not source.is_absolute():
        source = REPO_ROOT / source
    if source.is_dir():
        source = source / "solver.py"
    if not source.is_file():
        raise ValueError(f"candidate solver not found: {source}")
    return SolverCandidate(name, source.resolve())


def _fingerprint(profile_path: Path, manifest: Path, solver: Path) -> str:
    digest = hashlib.sha256()
    for path in (profile_path, manifest, solver):
        digest.update(path.read_bytes())
    return digest.hexdigest()


def _category_scores(
    problems: list[dict[str, Any]], summary: dict[str, Any]
) -> dict[str, dict[str, int]]:
    difficulty_by_id = {
        str(problem["id"]): str(problem["difficulty"]) for problem in problems
    }
    scores: dict[str, dict[str, int]] = {}
    for problem in problems:
        difficulty = str(problem["difficulty"])
        scores.setdefault(difficulty, {"accepted": 0, "total": 0})["total"] += 1
    for result in summary["per_problem"]:
        if result["status"] == "accepted":
            scores[difficulty_by_id[result["id"]]]["accepted"] += 1
    return scores


def run_candidate(
    candidate: SolverCandidate,
    *,
    profile_path: Path,
    profile: dict[str, Any],
    manifest_path: Path,
    problems: list[dict[str, Any]],
    batch_directory: Path,
) -> dict[str, Any]:
    run_directory = batch_directory / candidate.name
    run_directory.mkdir(parents=True, exist_ok=True)
    output_path = run_directory / "answers.jsonl"
    log_path = run_directory / "run.log"
    budget_seconds = float(profile["budget_seconds"])
    budget_tokens = int(profile["budget_tokens"])

    with tempfile.TemporaryDirectory(prefix="magma-marathon-") as raw_stage:
        stage = Path(raw_stage)
        shutil.copy2(candidate.source, stage / "solver.py")
        with log_path.open("w", encoding="utf-8") as log:
            result = run_marathon(
                submission_dir=stage,
                manifest_path=manifest_path,
                output_path=output_path,
                scratch_dir=run_directory / "scratch",
                budget_seconds=budget_seconds,
                budget_tokens=budget_tokens,
                enable_proxy=budget_tokens != 0,
                log_stream=log,
            )
            summary = score_marathon(
                manifest_problems=result.manifest_problems,
                output_path=output_path,
                wall_seconds=result.wall_seconds,
                sigterm_fired=result.sigterm_fired,
                sigkill_fired=result.sigkill_fired,
                tokens_used=result.tokens_used,
                tokens_exhausted=result.tokens_exhausted,
                log_stream=log,
            ).to_dict()

    payload = {
        "name": candidate.name,
        "source": candidate.source.relative_to(REPO_ROOT).as_posix(),
        "fingerprint": _fingerprint(profile_path, manifest_path, candidate.source),
        "exit_code": result.exit_code,
        "sigterm_reason": result.sigterm_reason,
        "category_scores": _category_scores(problems, summary),
        **summary,
    }
    (run_directory / "summary.json").write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the local Marathon benchmark")
    parser.add_argument("--profile", type=Path, default=DEFAULT_PROFILE)
    parser.add_argument(
        "--candidate",
        action="append",
        default=[],
        metavar="[NAME=]PATH",
        help="add a solver file/directory to the discovered demos",
    )
    parser.add_argument(
        "--only",
        action="append",
        default=[],
        help="run only the named discovered or added candidate (repeatable)",
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    profile_path = args.profile.resolve()
    profile = load_profile(profile_path)
    manifest_path = (REPO_ROOT / profile["manifest"]).resolve()
    problems = load_manifest(manifest_path)
    counts = validate_balance(problems, profile)
    candidates = discover_demo_solvers(REPO_ROOT / profile["demo_root"])
    candidates.extend(parse_candidate(value) for value in args.candidate)
    names = [candidate.name for candidate in candidates]
    if len(names) != len(set(names)):
        raise ValueError("candidate names must be unique")
    if args.only:
        requested = set(args.only)
        candidates = [candidate for candidate in candidates if candidate.name in requested]
        missing = requested - {candidate.name for candidate in candidates}
        if missing:
            raise ValueError(f"unknown --only candidates: {sorted(missing)}")
    if not candidates:
        raise ValueError("benchmark selected no solvers")

    print(f"Marathon benchmark: {profile['name']}")
    print(f"  manifest: {manifest_path.relative_to(REPO_ROOT)} ({len(problems)} problems)")
    print(f"  balance: {dict(sorted(counts.items()))}")
    print(f"  budget: {profile['budget_seconds']}s / {profile['budget_tokens']} tokens per solver")
    for candidate in candidates:
        print(f"  solver: {candidate.name} <- {candidate.source.relative_to(REPO_ROOT)}")
    if args.dry_run:
        return 0

    stamp = time.strftime("%Y%m%d_%H%M%S")
    batch_directory = REPO_ROOT / profile["output_directory"] / stamp
    batch_directory.mkdir(parents=True, exist_ok=True)
    results = []
    for candidate in candidates:
        print(f"\nRunning {candidate.name}...", flush=True)
        result = run_candidate(
            candidate,
            profile_path=profile_path,
            profile=profile,
            manifest_path=manifest_path,
            problems=problems,
            batch_directory=batch_directory,
        )
        results.append(result)
        print(
            f"  score={result['score']}/{len(problems)} "
            f"wall={result['wall_seconds']:.1f}s status={result['by_status']}"
        )

    results.sort(key=lambda item: (-int(item["score"]), float(item["wall_seconds"])))
    aggregate = {
        "profile": profile,
        "manifest": manifest_path.relative_to(REPO_ROOT).as_posix(),
        "results": results,
    }
    (batch_directory / "summary.json").write_text(
        json.dumps(aggregate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print("\nScoreboard")
    for rank, result in enumerate(results, 1):
        print(f"  {rank}. {result['name']}: {result['score']}/{len(problems)} ({result['wall_seconds']:.1f}s)")
    print(f"  results: {batch_directory.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
