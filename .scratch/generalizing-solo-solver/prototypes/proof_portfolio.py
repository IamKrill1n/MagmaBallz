#!/usr/bin/env python3
"""PROTOTYPE — explore an ordered deterministic TRUE-proof portfolio.

Question: which ordering of closed-form synthesis, substitution/short-chain
unification, specialized algebraic tactics, and bidirectional subterm rewriting
adds complementary judge-accepted coverage, and which accepted candidates can
be reconstructed through the shared Derivation representation?

This is throwaway instrumentation for the Wayfinder ticket "Choose the proof
search portfolio". It imports existing demo mechanisms instead of becoming a
production solver. Run it from the repository root with:

    python3 .scratch/generalizing-solo-solver/prototypes/proof_portfolio.py

The terminal state is fully redrawn after every action. Batch mode provides a
small, reproducible comparison without navigating the terminal:

    python3 .scratch/generalizing-solo-solver/prototypes/proof_portfolio.py \
        --batch --suite normal --limit 3
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
import time
from dataclasses import dataclass, replace
from pathlib import Path
from types import ModuleType
from typing import Callable, Sequence


ORDERINGS = {
    "deepening": (
        "closed_form",
        "short_chain",
        "specialized_algebra",
        "subterm_rewrite",
    ),
    "rewrite_early": (
        "closed_form",
        "short_chain",
        "subterm_rewrite",
        "specialized_algebra",
    ),
}

REPRESENTATIONS = {
    "true_reflexivity": "derivation",
    "true_singleton": "derivation",
    "true_simple_constancy": "derivation",
    "true_direct_substitution": "derivation",
    "true_direct_substitution_compound": "derivation",
    "true_calc_chain_1": "derivation",
    "true_calc_chain_2": "derivation",
    "true_one_congr_calc_chain": "derivation",
    "true_constancy_term_pool": "derivation",
    "bidirectional_subterm_rewrite": "rewrite_trace_to_derivation",
    "specialized_simp": "lean_body",
    "simp_constancy": "lean_body",
    "rw_chain": "lean_body",
    "hybrid_calc": "lean_body",
}


@dataclass(frozen=True)
class Attempt:
    strategy: str
    representation: str
    status: str
    elapsed_seconds: float
    code: str


@dataclass(frozen=True)
class LaneObservation:
    lane: str
    attempts: tuple[Attempt, ...]
    elapsed_seconds: float
    fault: str | None = None

    @property
    def accepted(self) -> Attempt | None:
        return next((attempt for attempt in self.attempts if attempt.status == "accepted"), None)


@dataclass(frozen=True)
class ExplorerState:
    problem_index: int
    ordering_name: str
    next_lane_index: int = 0
    observations: tuple[LaneObservation, ...] = ()

    @property
    def ordering(self) -> tuple[str, ...]:
        return ORDERINGS[self.ordering_name]

    @property
    def accepted(self) -> Attempt | None:
        for observation in self.observations:
            if observation.accepted is not None:
                return observation.accepted
        return None


def apply_observation(state: ExplorerState, observation: LaneObservation) -> ExplorerState:
    """Pure transition used by the throwaway TUI shell."""
    if state.accepted is not None or state.next_lane_index >= len(state.ordering):
        return state
    if observation.lane != state.ordering[state.next_lane_index]:
        raise ValueError("observation does not match the next portfolio lane")
    return replace(
        state,
        next_lane_index=state.next_lane_index + 1,
        observations=state.observations + (observation,),
    )


def load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load prototype adapter from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_true_problems(paths: Sequence[Path]) -> list[dict[str, object]]:
    problems: list[dict[str, object]] = []
    for path in paths:
        with path.open(encoding="utf-8") as source:
            for line in source:
                record = json.loads(line)
                if record.get("answer") is True:
                    record["equation1"] = str(record["equation1"]).replace("*", "◇")
                    record["equation2"] = str(record["equation2"]).replace("*", "◇")
                    problems.append(record)
    return problems


class RecordingJudge:
    def __init__(
        self,
        problem: dict[str, object],
        verify_answer: Callable[..., dict[str, object]],
    ):
        self.problem = problem
        self.verify_answer = verify_answer
        self.strategy = "unknown"
        self.attempts: list[Attempt] = []

    @property
    def calls(self) -> int:
        return len(self.attempts)

    def check(self, verdict: str, code: str, strategy: str | None = None) -> dict[str, object]:
        strategy = strategy or self.strategy
        started = time.monotonic()
        result = self.verify_answer(
            self.problem,
            json.dumps({"verdict": verdict, "code": code}),
        )
        elapsed = time.monotonic() - started
        self.attempts.append(
            Attempt(
                strategy=strategy,
                representation=REPRESENTATIONS.get(strategy, "lean_body"),
                status=str(result.get("status", "error")),
                elapsed_seconds=elapsed,
                code=code,
            )
        )
        return result


class PrototypeAdapters:
    def __init__(self, root: Path):
        self.root = root
        if str(root) not in sys.path:
            sys.path.insert(0, str(root))
        self.suii = load_module(
            "proof_portfolio_suii",
            root / "examples/solo/demos/suii0x/EQT02-S00006.py",
        )
        self.suii.log = lambda _message: None
        self.euler = load_module(
            "proof_portfolio_euler",
            root / "examples/solo/demos/eulerv5/solver.py",
        )
        from judge.verify import verify_answer

        self.verify_answer = verify_answer

    def run_lane(self, lane: str, problem: dict[str, object]) -> LaneObservation:
        started = time.monotonic()
        judge = RecordingJudge(problem, self.verify_answer)
        eq1 = str(problem["equation1"])
        eq2 = str(problem["equation2"])

        fault = None
        try:
            self._execute_lane(lane, problem, eq1, eq2, judge)
        except Exception as error:  # Prototype isolates faults at the strategy seam.
            fault = f"{type(error).__name__}: {error}"

        return LaneObservation(
            lane=lane,
            attempts=tuple(judge.attempts),
            elapsed_seconds=time.monotonic() - started,
            fault=fault,
        )

    def _execute_lane(
        self,
        lane: str,
        problem: dict[str, object],
        eq1: str,
        eq2: str,
        judge: RecordingJudge,
    ) -> None:
        if lane == "closed_form":
            variables, lhs, rhs = self.suii.parse_equation(eq2)
            if self.suii.norm_tree(lhs) == self.suii.norm_tree(rhs):
                proof = f"intro {' '.join(variables)}\nrfl"
                judge.check("true", self.suii.make_true_code(problem, proof), "true_reflexivity")
            else:
                for strategy in (self.suii.try_singleton, self.suii.try_simple_constancy):
                    if strategy(problem, eq1, eq2, judge):
                        break
        elif lane == "short_chain":
            strategies = (
                self.suii.try_direct_substitution,
                self.suii.try_direct_substitution_compound,
                self.suii.try_calc_chain,
                self.suii.try_one_congr_calc_chain,
                self.suii.try_constancy_term_pool,
            )
            for strategy in strategies:
                if strategy(problem, eq1, eq2, judge):
                    break
        elif lane == "specialized_algebra":
            strategies = (
                ("specialized_simp", self.euler.specialized_simp_v5),
                ("simp_constancy", self.euler.simp_constancy_v5),
                ("rw_chain", self.euler.rw_chain_v5),
                ("hybrid_calc", self.euler.hybrid_calc_v5),
            )
            original_call_judge = self.euler.call_judge
            try:
                for strategy_name, strategy in strategies:
                    judge.strategy = strategy_name
                    self.euler.call_judge = lambda verdict, code: judge.check(verdict, code)
                    if strategy(eq1, eq2):
                        break
            finally:
                self.euler.call_judge = original_call_judge
        elif lane == "subterm_rewrite":
            proof = self.euler.proof_bfs_v5(eq1, eq2, max_depth=5, time_limit=5.0)
            if proof:
                judge.check(
                    "true",
                    self.euler.lean_true(proof, high_heartbeats=True),
                    "bidirectional_subterm_rewrite",
                )
        else:
            raise ValueError(f"unknown lane: {lane}")


def advance(
    state: ExplorerState,
    problems: Sequence[dict[str, object]],
    adapters: PrototypeAdapters,
) -> ExplorerState:
    if state.accepted is not None or state.next_lane_index >= len(state.ordering):
        return state
    problem = problems[state.problem_index]
    lane = state.ordering[state.next_lane_index]
    return apply_observation(state, adapters.run_lane(lane, problem))


def reset_state(
    state: ExplorerState,
    *,
    problem_index: int | None = None,
    ordering_name: str | None = None,
) -> ExplorerState:
    return ExplorerState(
        problem_index=state.problem_index if problem_index is None else problem_index,
        ordering_name=state.ordering_name if ordering_name is None else ordering_name,
    )


def render(state: ExplorerState, problems: Sequence[dict[str, object]]) -> str:
    problem = problems[state.problem_index]
    lines = [
        "\033[1mPROTOTYPE — deterministic TRUE-proof portfolio\033[0m",
        f"\033[2mProblem {state.problem_index + 1}/{len(problems)}: {problem['id']}\033[0m",
        "",
        f"\033[1mpremise\033[0m: {problem['equation1']}",
        f"\033[1mgoal\033[0m:    {problem['equation2']}",
        f"\033[1morder\033[0m:   {state.ordering_name} -> {' -> '.join(state.ordering)}",
        "",
        "\033[1mLane state\033[0m",
    ]
    observed = {observation.lane: observation for observation in state.observations}
    for index, lane in enumerate(state.ordering):
        observation = observed.get(lane)
        if observation is None:
            marker = ">" if index == state.next_lane_index and state.accepted is None else " "
            lines.append(f"{marker} {lane}: pending")
            continue
        accepted = observation.accepted
        if accepted:
            detail = f"accepted by {accepted.strategy} [{accepted.representation}]"
        elif observation.fault:
            detail = f"fault; {observation.fault}"
        elif observation.attempts:
            statuses = ", ".join(attempt.status for attempt in observation.attempts)
            detail = f"exhausted; judge={statuses}"
        else:
            detail = "exhausted; no candidate"
        lines.append(
            f"  {lane}: {detail}; attempts={len(observation.attempts)}; "
            f"elapsed={observation.elapsed_seconds:.2f}s"
        )
    lines.extend(["", "\033[1mAccepted candidate\033[0m"])
    if state.accepted is None:
        lines.append("none")
    else:
        lines.extend(
            [
                f"strategy: {state.accepted.strategy}",
                f"representation: {state.accepted.representation}",
                f"judge status: {state.accepted.status}",
                "\033[2m" + state.accepted.code[-900:] + "\033[0m",
            ]
        )
    lines.extend(
        [
            "",
            "\033[1m[a]\033[0m advance lane  \033[1m[p]\033[0m run portfolio  "
            "\033[1m[n]\033[0m next problem  \033[1m[o]\033[0m toggle order  "
            "\033[1m[r]\033[0m reset  \033[1m[q]\033[0m quit",
        ]
    )
    return "\n".join(lines)


def run_tui(
    problems: Sequence[dict[str, object]],
    adapters: PrototypeAdapters,
    start_index: int,
) -> None:
    state = ExplorerState(problem_index=start_index, ordering_name="deepening")
    while True:
        print("\033[2J\033[H" + render(state, problems), flush=True)
        command = input("\n> ").strip().lower()
        if command == "q":
            return
        if command == "a":
            state = advance(state, problems, adapters)
        elif command == "p":
            while state.accepted is None and state.next_lane_index < len(state.ordering):
                state = advance(state, problems, adapters)
        elif command == "n":
            state = reset_state(state, problem_index=(state.problem_index + 1) % len(problems))
        elif command == "o":
            names = tuple(ORDERINGS)
            next_name = names[(names.index(state.ordering_name) + 1) % len(names)]
            state = reset_state(state, ordering_name=next_name)
        elif command == "r":
            state = reset_state(state)


def run_batch(
    problems: Sequence[dict[str, object]],
    adapters: PrototypeAdapters,
    limit: int,
) -> None:
    summary: dict[str, object] = {}
    for ordering_name in ORDERINGS:
        results = []
        for problem_index in range(min(limit, len(problems))):
            state = ExplorerState(problem_index=problem_index, ordering_name=ordering_name)
            while state.accepted is None and state.next_lane_index < len(state.ordering):
                state = advance(state, problems, adapters)
            results.append(state)
        accepted = [state for state in results if state.accepted is not None]
        summary[ordering_name] = {
            "cases": len(results),
            "accepted": len(accepted),
            "accepting_strategy": {
                strategy: sum(
                    state.accepted is not None
                    and state.accepted.strategy == strategy
                    for state in accepted
                )
                for strategy in sorted(
                    {state.accepted.strategy for state in accepted if state.accepted}
                )
            },
            "accepting_representation": {
                representation: sum(
                    state.accepted is not None and state.accepted.representation == representation
                    for state in accepted
                )
                for representation in sorted(
                    {state.accepted.representation for state in accepted if state.accepted}
                )
            },
            "unresolved": [
                problems[state.problem_index]["id"]
                for state in results
                if state.accepted is None
            ],
            "faults": {
                problems[state.problem_index]["id"]: [
                    f"{observation.lane}: {observation.fault}"
                    for observation in state.observations
                    if observation.fault
                ]
                for state in results
                if any(observation.fault for observation in state.observations)
            },
        }
    print(json.dumps(summary, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", action="store_true")
    parser.add_argument("--limit", type=int, default=5)
    parser.add_argument("--suite", choices=("development", "normal"), default="development")
    parser.add_argument("--start", type=int, default=1, help="one-based TUI problem index")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[3]
    paths = (
        [root / "examples/problems/hard1.jsonl", root / "examples/problems/hard2.jsonl"]
        if args.suite == "development"
        else [root / "examples/problems/normal.jsonl"]
    )
    problems = load_true_problems(paths)
    adapters = PrototypeAdapters(root)
    if args.batch or not sys.stdin.isatty():
        run_batch(problems, adapters, args.limit)
    else:
        start_index = max(0, min(len(problems) - 1, args.start - 1))
        run_tui(problems, adapters, start_index)


if __name__ == "__main__":
    main()
