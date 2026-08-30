from __future__ import annotations

import unittest
from pathlib import Path

from pipeline.solo_benchmark import (
    _benchmark_fingerprint,
    _summarize,
    load_profile,
    selected_problem_entries,
    timeout_for,
)


class SoloBenchmarkTimeoutTest(unittest.TestCase):
    def setUp(self) -> None:
        self.profile = {
            "timeouts_seconds": {
                "normal": 120,
                "hard_or_order5": 300,
                "hard_markers": ["hard", "order5"],
            }
        }

    def test_normal_problem_gets_two_minutes(self) -> None:
        problem = {"difficulty": "normal"}
        self.assertEqual(timeout_for(problem, Path("normal.jsonl"), self.profile), 120)

    def test_hard_metadata_gets_five_minutes(self) -> None:
        problem = {"difficulty": "extra_hard"}
        self.assertEqual(timeout_for(problem, Path("set.jsonl"), self.profile), 300)

    def test_order5_path_gets_five_minutes(self) -> None:
        problem = {}
        self.assertEqual(
            timeout_for(problem, Path("evaluation_order5.jsonl"), self.profile),
            300,
        )


class SoloBenchmarkSelectionTest(unittest.TestCase):
    def test_selection_profile_can_be_fingerprinted(self) -> None:
        profile_path = Path("benchmarks/solo_hard_100.json").resolve()
        profile = load_profile(profile_path)

        fingerprint = _benchmark_fingerprint(
            profile_path,
            profile,
            Path("my_submission").resolve(),
            Path("pipeline/config.json").resolve(),
            [Path("examples/problems/hard1.jsonl").resolve()],
        )

        self.assertEqual(len(fingerprint), 64)

    def test_solver_file_can_be_fingerprinted(self) -> None:
        profile_path = Path("benchmarks/solo_hard_100.json").resolve()
        profile = load_profile(profile_path)

        fingerprint = _benchmark_fingerprint(
            profile_path,
            profile,
            Path("my_submission/solver.py").resolve(),
            Path("pipeline/config.json").resolve(),
            [Path("examples/problems/hard1.jsonl").resolve()],
        )

        self.assertEqual(len(fingerprint), 64)

    def test_exact_ids_are_loaded_in_profile_order(self) -> None:
        source = Path("examples/problems/hard1.jsonl").resolve()
        profile = {
            "problems": {
                "selections": [
                    {
                        "path": "examples/problems/hard1.jsonl",
                        "ids": ["hard1_0003", "hard1_0001"],
                    }
                ]
            }
        }

        entries = selected_problem_entries(source, profile)

        self.assertEqual([problem["id"] for _, problem in entries], ["hard1_0003", "hard1_0001"])
        self.assertEqual([index for index, _ in entries], [3, 1])

    def test_missing_selected_id_is_rejected(self) -> None:
        source = Path("examples/problems/hard1.jsonl").resolve()
        profile = {
            "problems": {
                "selections": [
                    {
                        "path": "examples/problems/hard1.jsonl",
                        "ids": ["missing"],
                    }
                ]
            }
        }

        with self.assertRaisesRegex(ValueError, "selected id not found"):
            selected_problem_entries(source, profile)


class SoloBenchmarkSummaryTest(unittest.TestCase):
    def test_accuracy_counts_only_correct_accepted_answers(self) -> None:
        source = Path("hard.jsonl")
        jobs = [object(), object(), object()]
        completed = {
            source: {
                "correct": {"solved": True, "label_match": True},
                "wrong": {"solved": True, "label_match": False},
                "missing": {"solved": False, "label_match": None},
            }
        }

        summary = _summarize(jobs, completed)  # type: ignore[arg-type]

        self.assertEqual(summary["correct"], 1)
        self.assertEqual(summary["accuracy"], 0.333333)


if __name__ == "__main__":
    unittest.main()
