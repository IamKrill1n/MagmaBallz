from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SOLVER_PATH = ROOT / "my_submission" / "marathon" / "solverV3.py"
SPEC = importlib.util.spec_from_file_location("marathon_solver_v3", SOLVER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {SOLVER_PATH}")
solver = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = solver
SPEC.loader.exec_module(solver)


class MarathonSolverV3Test(unittest.TestCase):
    def test_nonabsorption_closure_precedes_constraint_search(self) -> None:
        problem = {
            "id": "ordering_probe",
            "equation1": "x * y = y * x",
            "equation2": "x * (y * z) = (x * y) * z",
        }
        with (
            patch.object(solver, "is_reflexive_problem", return_value=False),
            patch.object(solver, "singleton_route", return_value=None),
            patch.object(solver, "DISTILLED_CERTS", {}),
            patch.object(solver, "TRUE_ROUTES", ()),
            patch.object(solver, "_engine_gate", return_value=False),
            patch.object(solver, "find_counterexample", return_value=None),
            patch.object(solver, "absorption_hypothesis", return_value=False),
            patch.object(
                solver,
                "equational_closure_route",
                return_value=("true:test_closure", solver.reflexive_true_certificate()),
            ),
            patch.object(
                solver,
                "constraint_countermodel",
                side_effect=AssertionError("constraint search ran before closure"),
            ),
        ):
            result = solver.solve_problem_pass(problem, false_time_budget=0.01)

        self.assertIsNotNone(result)
        self.assertEqual(result["route"], "true:test_closure")


if __name__ == "__main__":
    unittest.main()
