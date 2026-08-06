"""Focused regression tests for the generalized zero-LLM Solo solver."""

from __future__ import annotations

import importlib.util
import sys
import time
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOLVER_PATH = ROOT / "examples/solo/demos/generalized/solver.py"
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("generalized_solver", SOLVER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {SOLVER_PATH}")
solver = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = solver
SPEC.loader.exec_module(solver)


def problem(equation1: str, equation2: str) -> solver.Problem:
    return solver.parse_problem(
        {"equation1": equation1, "equation2": equation2}
    )


class KernelTests(unittest.TestCase):
    def test_parser_alpha_normalizes_scopes_and_first_occurrence(self) -> None:
        parsed = problem("y = x ◇ y", "b ◇ a = a")
        self.assertEqual(
            [(variable.scope, variable.slot) for variable in parsed.premise.variables],
            [("premise", 0), ("premise", 1)],
        )
        self.assertEqual(
            [(variable.scope, variable.slot) for variable in parsed.goal.variables],
            [("goal", 0), ("goal", 1)],
        )

    def test_two_hop_joint_unification_builds_the_plain_trans_chain(self) -> None:
        parsed = problem(
            "x ◇ y = (y ◇ x) ◇ y",
            "a ◇ b = (b ◇ (b ◇ a)) ◇ b",
        )
        proofs = list(solver._chain_derivations(parsed))
        self.assertTrue(proofs)
        admission = solver.admit(
            parsed,
            solver.Candidate("derivation", proofs[0]),
            solver.Limits(100_000, 20_000),
            solver.SeenCandidates(),
        )
        self.assertEqual(admission.status, "judge_request")
        self.assertEqual(admission.verdict, "true")
        self.assertIn(".trans", admission.source or "")

    def test_nested_direct_rewrite_renders_congruence(self) -> None:
        parsed = problem("x ◇ x = y ◇ x", "(a ◇ a) ◇ c = (b ◇ a) ◇ c")
        proof = solver._lift_matching_context(
            parsed,
            parsed.goal.lhs,
            parsed.goal.rhs,
            solver._direct_between,
        )
        self.assertIsNotNone(proof)
        admission = solver.admit(
            parsed,
            solver.Candidate("derivation", proof),
            solver.Limits(100_000, 20_000),
            solver.SeenCandidates(),
        )
        self.assertEqual(admission.status, "judge_request")
        self.assertIn("congrArg", admission.source or "")

    def test_countermodel_is_rechecked_and_rendered(self) -> None:
        parsed = problem("x ◇ y = x", "x ◇ y = y")
        left_projection = solver.FiniteMagma(2, (0, 0, 1, 1))
        admission = solver.admit(
            parsed,
            solver.Candidate("countermodel", left_projection),
            solver.Limits(100_000, 20_000),
            solver.SeenCandidates(),
        )
        self.assertEqual(admission.status, "judge_request")
        self.assertEqual(admission.verdict, "false")
        self.assertIn('finOpTable "[[0,0],[1,1]]"', admission.source or "")

    def test_admission_deduplicates_evidence_before_judging(self) -> None:
        parsed = problem("x = x", "y = y")
        candidate = solver.Candidate("derivation", solver.refl(parsed.goal.lhs))
        seen = solver.SeenCandidates()
        first = solver.admit(
            parsed, candidate, solver.Limits(100_000, 20_000), seen
        )
        second = solver.admit(
            parsed, candidate, solver.Limits(100_000, 20_000), seen
        )
        self.assertEqual(first.status, "judge_request")
        self.assertEqual(second.status, "duplicate")
        self.assertEqual(second.reason, "evidence_duplicate")

    def test_controlled_lean_body_rejects_submission_scaffolding(self) -> None:
        parsed = problem("x = x", "y = y")
        admission = solver.admit(
            parsed,
            solver.Candidate("lean_body", "def submission : Goal := by\n  rfl"),
            solver.Limits(100_000, 20_000),
            solver.SeenCandidates(),
        )
        self.assertEqual(admission.status, "rejected")


class StrategyAndCaseTests(unittest.TestCase):
    def test_countermodel_prefix_is_deterministic_across_fresh_sessions(self) -> None:
        parsed = problem("x ◇ y = x", "x ◇ y = y")
        strategy = solver.registered_strategies()[0]
        deadline = time.monotonic() + 10
        first = strategy.open(parsed).advance(solver.EffortBudget(1, deadline))
        second = strategy.open(parsed).advance(solver.EffortBudget(1, deadline))
        self.assertEqual(first.status, "yielded")
        self.assertEqual(second.status, "yielded")
        self.assertEqual(first.candidate, second.candidate)

    def test_bidirectional_rewrite_retains_a_three_step_derivation(self) -> None:
        parsed = problem("x = x ◇ y", "a = ((a ◇ b) ◇ c) ◇ d")
        candidate = next(
            event for event in solver._rewrite_events(parsed) if event is not None
        )
        admission = solver.admit(
            parsed,
            candidate,
            solver.Limits(100_000, 20_000),
            solver.SeenCandidates(),
        )
        self.assertEqual(admission.status, "judge_request")
        self.assertGreaterEqual((admission.source or "").count(".trans"), 3)

    def test_disabled_oracle_does_not_touch_artifact_or_pair_ids(self) -> None:
        class Poison:
            def __getattribute__(self, name: str) -> object:
                raise AssertionError(f"artifact touched through {name}")

        parsed = problem("x = x", "y = y")
        result = solver.OracleSubsystem("disabled", Poison()).consult(
            parsed, Poison(), Poison()
        )
        self.assertEqual(result.disposition, "disabled")
        self.assertIsNone(result.cached_candidate)
        self.assertIsNone(result.preferred_lane)

    def test_case_engine_is_countermodel_first_then_accepts_proof(self) -> None:
        traces: list[dict[str, object]] = []
        judge_calls: list[tuple[str, str]] = []

        def judge(verdict: str, source: str) -> dict[str, object]:
            judge_calls.append((verdict, source))
            return {"status": "accepted"}

        startup = {
            "problem": {
                "id": "unit_reflexive",
                "eq1_id": 1,
                "eq2_id": 2,
                "equation1": "x = x",
                "equation2": "y = y",
            },
            "budget": {
                "timeout_seconds": 5,
                "max_code_length": 100_000,
                "max_false_cert_bytes": 20_000,
            },
        }
        outcome = solver.run_case(startup, judge, traces.append)
        self.assertEqual(outcome.status, "accepted")
        self.assertEqual([call[0] for call in judge_calls], ["true"])
        grants = [trace for trace in traces if trace.get("event") == "strategy_grant"]
        self.assertGreaterEqual(len(grants), 2)
        self.assertEqual(grants[0]["lane"], solver.LANE_COUNTERMODEL)
        self.assertEqual(grants[1]["lane"], solver.LANE_PROOF)

    def test_registry_order_matches_the_resolved_architecture(self) -> None:
        self.assertEqual(
            [strategy.id for strategy in solver.registered_strategies()],
            [
                "countermodel.portfolio",
                "proof.closed_form",
                "proof.short_chain",
                "proof.specialized",
                "proof.rewrite",
            ],
        )

    def test_submission_is_single_file_zero_llm_and_under_size_cap(self) -> None:
        source = SOLVER_PATH.read_text(encoding="utf-8")
        self.assertEqual(solver.PROMPT, "")
        self.assertNotIn('{"call": "llm"', source)
        self.assertLessEqual(len(source.encode("utf-8")), 500_000)
        siblings = [path.name for path in SOLVER_PATH.parent.iterdir()]
        self.assertEqual(siblings, ["solver.py"])


if __name__ == "__main__":
    unittest.main()
