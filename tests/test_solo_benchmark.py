from __future__ import annotations

import unittest
from pathlib import Path

from pipeline.solo_benchmark import timeout_for


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


if __name__ == "__main__":
    unittest.main()
