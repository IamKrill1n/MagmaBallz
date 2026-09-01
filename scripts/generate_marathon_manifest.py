"""Deterministic Marathon manifest generator.

Reproduces the documented selection algorithm used by
``benchmarks/marathon_hard100.json``:

* per-tier seeded sampling with exact false/true quotas,
* global alternating false/true ordering after sampling,
* solver-visible rows stripped of the ``answer`` field.

Usage:

    python3 scripts/generate_marathon_manifest.py \
        --profile benchmarks/marathon_hard100.json

Writes the manifest referenced by the profile's ``manifest`` field and
validates the invariants (unique ids, expected difficulty counts, 50/50
alternating labels, no exposed answers). Exits non-zero on any violation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from collections import Counter
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]

SOLVER_VISIBLE_FIELDS = ("id", "index", "difficulty", "eq1_id", "eq2_id",
                         "equation1", "equation2")


def _tier_seed(profile_seed: int, difficulty: str) -> int:
    digest = hashlib.sha256(f"{profile_seed}:{difficulty}".encode("utf-8"))
    return int.from_bytes(digest.digest()[:8], "big")


def _shuffle(rows: list[dict[str, Any]], profile_seed: int,
             difficulty: str) -> list[dict[str, Any]]:
    rng = random.Random(_tier_seed(profile_seed, difficulty))
    out = list(rows)
    rng.shuffle(out)
    return out


def sample_source(
    profile_seed: int,
    source: dict[str, Any],
    source_rows: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    difficulty = str(source["difficulty"])
    rows = [row for row in source_rows if str(row.get("difficulty")) == difficulty]
    false_rows = [row for row in rows if row.get("answer") is False]
    true_rows = [row for row in rows if row.get("answer") is True]
    false_count = int(source["false"])
    true_count = int(source["true"])
    if len(false_rows) < false_count or len(true_rows) < true_count:
        raise ValueError(
            f"source {source['path']} has insufficient rows for "
            f"{difficulty} quotas ({false_count} false / {true_count} true)"
        )
    selected_false = _shuffle(false_rows, profile_seed, difficulty)[:false_count]
    selected_true = _shuffle(true_rows, profile_seed, difficulty)[:true_count]
    return selected_false + selected_true


def interleave_alternating(
    selected_by_difficulty: dict[str, list[dict[str, Any]]],
) -> list[dict[str, Any]]:
    false_pool: list[dict[str, Any]] = []
    true_pool: list[dict[str, Any]] = []
    for difficulty in sorted(selected_by_difficulty):
        for row in selected_by_difficulty[difficulty]:
            (true_pool if row.get("answer") is True else false_pool).append(row)
    if len(false_pool) != len(true_pool):
        raise ValueError(
            f"alternating interleave needs equal false/true pools, got "
            f"{len(false_pool)}/{len(true_pool)}"
        )
    out: list[dict[str, Any]] = []
    for false_row, true_row in zip(false_pool, true_pool):
        out.extend((false_row, true_row))
    return out


def load_source_rows(profile_root: Path, path: str) -> list[dict[str, Any]]:
    rows = [
        json.loads(line)
        for line in (profile_root / path).read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    ids = [str(row.get("id")) for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError(f"source {path} contains duplicate ids")
    return rows


def make_solver_visible(row: dict[str, Any]) -> dict[str, Any]:
    visible = {field: row[field] for field in SOLVER_VISIBLE_FIELDS}
    if any(field not in visible for field in SOLVER_VISIBLE_FIELDS):
        raise ValueError("solver-visible row missing a required field")
    if any(visible.get(field) is None for field in SOLVER_VISIBLE_FIELDS):
        raise ValueError("solver-visible row has a null required field")
    return visible


def validate_manifest(
    manifest_path: Path, profile: dict[str, Any]
) -> Counter[str]:
    rows = [
        json.loads(line)
        for line in manifest_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    ids = [str(row.get("id")) for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("manifest contains duplicate problem ids")
    if any("answer" in row for row in rows):
        raise ValueError("manifest must not expose answer labels")
    actual = Counter(str(row.get("difficulty")) for row in rows)
    expected = Counter(
        {str(key): int(value)
         for key, value in profile["expected_difficulty_counts"].items()}
    )
    if actual != expected:
        raise ValueError(
            f"manifest difficulty counts {dict(actual)} != {dict(expected)}"
        )
    return actual


def generate(profile_path: Path) -> Path:
    profile_root = REPO_ROOT
    profile = json.loads(profile_path.read_text(encoding="utf-8"))
    if profile.get("schema_version") != 1 or profile.get("mode") != "marathon":
        raise ValueError("profile must use schema_version=1 and mode=marathon")
    selection = profile["selection"]
    profile_seed = int(selection["seed"])
    selected_by_difficulty: dict[str, list[dict[str, Any]]] = {}
    for source in selection["sources"]:
        source_rows = load_source_rows(profile_root, str(source["path"]))
        difficulty = str(source["difficulty"])
        selected_by_difficulty[difficulty] = sample_source(
            profile_seed, source, source_rows
        )
    ordered = interleave_alternating(selected_by_difficulty)
    manifest_path = (profile_root / str(profile["manifest"])).resolve()
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with manifest_path.open("w", encoding="utf-8") as handle:
        for row in ordered:
            handle.write(json.dumps(make_solver_visible(row)) + "\n")
    counts = validate_manifest(manifest_path, profile)
    return manifest_path, counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile", type=Path,
        default=REPO_ROOT / "benchmarks" / "marathon_hard100.json",
    )
    args = parser.parse_args()
    manifest_path, counts = generate(args.profile)
    print(f"wrote {manifest_path.relative_to(REPO_ROOT)}")
    print(f"  counts: {dict(sorted(counts.items()))}")
    print(f"  total: {sum(counts.values())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())