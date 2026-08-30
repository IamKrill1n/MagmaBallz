from __future__ import annotations

import json
import unittest
from collections import Counter
from pathlib import Path

from pipeline.marathon_benchmark import (
    REPO_ROOT,
    discover_demo_solvers,
    load_manifest,
    load_profile,
    validate_balance,
)


class MarathonBenchmarkTest(unittest.TestCase):
    def setUp(self) -> None:
        self.profile = load_profile(REPO_ROOT / "benchmarks" / "marathon.json")
        self.problems = load_manifest(REPO_ROOT / self.profile["manifest"])

    def test_manifest_is_balanced_and_label_free(self) -> None:
        counts = validate_balance(self.problems, self.profile)
        self.assertEqual(len(self.problems), 24)
        self.assertEqual(Counter(counts.values()), Counter({6: 4}))
        self.assertTrue(all("answer" not in problem for problem in self.problems))

    def test_manifest_round_robins_difficulties(self) -> None:
        expected = ["normal", "hard", "extra_hard", "order5_normal"]
        for offset in range(0, len(self.problems), 4):
            self.assertEqual(
                [problem["difficulty"] for problem in self.problems[offset : offset + 4]],
                expected,
            )

    def test_manifest_matches_locked_source_rows(self) -> None:
        selected_by_source = []
        for raw_path in self.profile["selection"]["source_files"]:
            source_rows = [
                json.loads(line)
                for line in (REPO_ROOT / raw_path).read_text(encoding="utf-8").splitlines()
                if line.strip()
            ]
            selected_by_source.append(
                [
                    source_rows[index - 1]
                    for index in self.profile["selection"]["one_based_indices_per_source"]
                ]
            )

        expected = []
        for offset in range(len(selected_by_source[0])):
            for source_rows in selected_by_source:
                problem = dict(source_rows[offset])
                problem.pop("answer", None)
                expected.append(problem)
        self.assertEqual(self.problems, expected)

    def test_demo_discovery_includes_directory_and_file_solvers(self) -> None:
        candidates = discover_demo_solvers(REPO_ROOT / self.profile["demo_root"])
        names = {candidate.name for candidate in candidates}
        self.assertTrue({"baseline", "fewshot", "triage"}.issubset(names))
        self.assertIn("EQT02-M00010", names)
        self.assertTrue(all(candidate.source.name == "solver.py" or candidate.source.suffix == ".py" for candidate in candidates))


class Hard100MarathonBenchmarkTest(unittest.TestCase):
    def setUp(self) -> None:
        self.profile = load_profile(REPO_ROOT / "benchmarks" / "marathon_hard100.json")
        self.problems = load_manifest(REPO_ROOT / self.profile["manifest"])

    def test_manifest_is_hard_focused_balanced_and_label_free(self) -> None:
        counts = validate_balance(self.problems, self.profile)
        self.assertEqual(len(self.problems), 100)
        self.assertEqual(counts["normal"], 10)
        self.assertEqual(counts["hard"] + counts["extra_hard"], 55)
        self.assertEqual(counts["order5_normal"], 35)
        self.assertTrue(all("answer" not in problem for problem in self.problems))

    def test_manifest_provenance_has_alternating_source_labels(self) -> None:
        source_by_id = {}
        for source in self.profile["selection"]["sources"]:
            for raw in (REPO_ROOT / source["path"]).read_text(encoding="utf-8").splitlines():
                if raw.strip():
                    row = json.loads(raw)
                    source_by_id[row["id"]] = row

        source_rows = [source_by_id[problem["id"]] for problem in self.problems]
        self.assertEqual(
            [row["answer"] for row in source_rows],
            [label for _ in range(50) for label in (False, True)],
        )
        for source in self.profile["selection"]["sources"]:
            selected = [
                row
                for row in source_rows
                if row["difficulty"] == source["difficulty"]
            ]
            self.assertEqual(sum(row["answer"] is False for row in selected), source["false"])
            self.assertEqual(sum(row["answer"] is True for row in selected), source["true"])


if __name__ == "__main__":
    unittest.main()
