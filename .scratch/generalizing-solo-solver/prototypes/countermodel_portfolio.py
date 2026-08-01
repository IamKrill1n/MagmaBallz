#!/usr/bin/env python3
"""PROTOTYPE — compare deterministic countermodel-search portfolios.

This is throwaway instrumentation for the Wayfinder ticket "Choose the
countermodel search portfolio". It is deliberately independent of production
solver code. Run from the repository root:

    python3 .scratch/generalizing-solo-solver/prototypes/countermodel_portfolio.py

The prototype reports the complete relevant state after each portfolio: solved
FALSE cases, first-hit lane, table and assignment-check credits, duplicate
tables, retained premise-models, and unresolved case IDs.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Term = tuple[str, object, object] | tuple[str, int]
Table = tuple[int, ...]


@dataclass(frozen=True)
class Equation:
    variables: tuple[str, ...]
    lhs: Term
    rhs: Term


@dataclass(frozen=True)
class Problem:
    problem_id: str
    premise: Equation
    goal: Equation


@dataclass
class SearchState:
    seen_tables: set[tuple[int, Table]] = field(default_factory=set)
    premise_models: list[tuple[int, Table]] = field(default_factory=list)
    tables_considered: int = 0
    assignment_checks: int = 0
    duplicates: int = 0
    backtrack_nodes: int = 0
    hit_lane: str | None = None
    hit_order: int | None = None


def parse_variables(text: str) -> tuple[str, ...]:
    return tuple(dict.fromkeys(ch for ch in text if "a" <= ch <= "z"))


def strip_outer_parentheses(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        closes_at_end = True
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            if depth == 0 and index != len(text) - 1:
                closes_at_end = False
                break
        if not closes_at_end:
            break
        text = text[1:-1].strip()
    return text


def parse_term(text: str, variable_slots: dict[str, int]) -> Term:
    text = strip_outer_parentheses(text.replace("*", "◇"))
    depth = 0
    split_at = -1
    for index, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "◇" and depth == 0:
            split_at = index
    if split_at >= 0:
        return (
            "app",
            parse_term(text[:split_at], variable_slots),
            parse_term(text[split_at + 1 :], variable_slots),
        )
    return ("var", variable_slots[text.strip()])


def parse_equation(text: str) -> Equation:
    variables = parse_variables(text)
    slots = {variable: index for index, variable in enumerate(variables)}
    lhs, rhs = text.split("=", 1)
    return Equation(variables, parse_term(lhs, slots), parse_term(rhs, slots))


def evaluate(term: Term, assignment: tuple[int, ...], order: int, table: Table) -> int:
    if term[0] == "var":
        return assignment[term[1]]  # type: ignore[index]
    left = evaluate(term[1], assignment, order, table)  # type: ignore[arg-type]
    right = evaluate(term[2], assignment, order, table)  # type: ignore[arg-type]
    return table[left * order + right]


def evaluate_partial(
    term: Term, assignment: tuple[int, ...], order: int, table: Sequence[int]
) -> int | None:
    if term[0] == "var":
        return assignment[term[1]]  # type: ignore[index]
    left = evaluate_partial(term[1], assignment, order, table)  # type: ignore[arg-type]
    right = evaluate_partial(term[2], assignment, order, table)  # type: ignore[arg-type]
    if left is None or right is None:
        return None
    value = table[left * order + right]
    return None if value < 0 else value


def holds(equation: Equation, order: int, table: Table, state: SearchState) -> bool:
    for assignment in itertools.product(range(order), repeat=len(equation.variables)):
        state.assignment_checks += 1
        if evaluate(equation.lhs, assignment, order, table) != evaluate(
            equation.rhs, assignment, order, table
        ):
            return False
    return True


def exhaustive_tables(order: int) -> Iterator[Table]:
    yield from itertools.product(range(order), repeat=order * order)


def rectangular_bands(order: int) -> Iterator[Table]:
    for left_size in range(2, order):
        if order % left_size:
            continue
        right_size = order // left_size
        yield tuple(
            (left // right_size) * right_size + right % right_size
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            (right // right_size) * right_size + left % right_size
            for left in range(order)
            for right in range(order)
        )


def product_affine_tables(order: int) -> Iterator[Table]:
    for left_order in range(2, order):
        if order % left_order:
            continue
        right_order = order // left_order
        for coefficients in itertools.product(
            range(left_order), range(left_order), range(left_order),
            range(right_order), range(right_order), range(right_order),
        ):
            a1, b1, c1, a2, b2, c2 = coefficients
            if not any(coefficients):
                continue
            cells = []
            for left in range(order):
                for right in range(order):
                    lx, ly = divmod(left, right_order)
                    rx, ry = divmod(right, right_order)
                    x = (a1 * lx + b1 * rx + c1) % left_order
                    y = (a2 * ly + b2 * ry + c2) % right_order
                    cells.append(x * right_order + y)
            yield tuple(cells)


def projection_exceptions(order: int) -> Iterator[Table]:
    bases = (
        tuple(left for left in range(order) for _ in range(order)),
        tuple(right for _ in range(order) for right in range(order)),
    )
    for base in bases:
        for cell, old_value in enumerate(base):
            for value in range(order):
                if value != old_value:
                    changed = list(base)
                    changed[cell] = value
                    yield tuple(changed)
        for row in range(order):
            for value in range(order):
                changed = list(base)
                changed[row * order : (row + 1) * order] = [value] * order
                yield tuple(changed)
        for column in range(order):
            for value in range(order):
                changed = list(base)
                for row in range(order):
                    changed[row * order + column] = value
                yield tuple(changed)


def structured_tables(order: int) -> Iterator[Table]:
    for constant in range(order):
        yield (constant,) * (order * order)
    yield tuple(left for left in range(order) for _ in range(order))
    yield tuple(right for _ in range(order) for right in range(order))
    yield tuple(min(left, right) for left in range(order) for right in range(order))
    yield tuple(max(left, right) for left in range(order) for right in range(order))
    yield tuple((left + right) % order for left in range(order) for right in range(order))
    yield tuple((left - right) % order for left in range(order) for right in range(order))
    for a, b, constant in itertools.product(range(order), repeat=3):
        yield tuple(
            (a * left + b * right + constant) % order
            for left in range(order)
            for right in range(order)
        )
    for constant in range(order):
        yield tuple(
            left if left == right else constant
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else left
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else right
            for left in range(order)
            for right in range(order)
        )
        yield tuple(
            left if left == right else (left + right + constant) % order
            for left in range(order)
            for right in range(order)
        )
    yield from rectangular_bands(order)
    yield from product_affine_tables(order)
    yield from projection_exceptions(order)


def pseudo_random_tables(problem: Problem, order: int, count: int) -> Iterator[Table]:
    """A reproducible diagnostic only; sampling violates the settled contract."""
    seed = problem.problem_id.encode("utf-8")
    for index in range(count):
        cells = bytearray()
        block = 0
        while len(cells) < order * order:
            digest = hashlib.sha256(seed + index.to_bytes(8, "big") + block.to_bytes(4, "big")).digest()
            cells.extend(value % order for value in digest)
            block += 1
        yield tuple(cells[: order * order])


def consider_table(
    problem: Problem,
    state: SearchState,
    lane: str,
    order: int,
    table: Table,
    retain_model: bool,
) -> bool:
    key = (order, table)
    if key in state.seen_tables:
        state.duplicates += 1
        return False
    state.seen_tables.add(key)
    state.tables_considered += 1
    if not holds(problem.premise, order, table, state):
        return False
    retained_at_order = sum(1 for model_order, _ in state.premise_models if model_order == order)
    if retain_model and retained_at_order < 4:
        state.premise_models.append(key)
    if holds(problem.goal, order, table, state):
        return False
    state.hit_lane = lane
    state.hit_order = order
    return True


def run_table_lane(
    problem: Problem,
    state: SearchState,
    lane: str,
    sources: Iterable[tuple[int, Iterable[Table]]],
    retain_models: bool = False,
) -> bool:
    for order, tables in sources:
        for table in tables:
            if consider_table(problem, state, lane, order, table, retain_models):
                return True
    return False


def premise_consistent(
    equation: Equation, order: int, table: Sequence[int], state: SearchState
) -> bool:
    for assignment in itertools.product(range(order), repeat=len(equation.variables)):
        state.assignment_checks += 1
        left = evaluate_partial(equation.lhs, assignment, order, table)
        right = evaluate_partial(equation.rhs, assignment, order, table)
        if left is not None and right is not None and left != right:
            return False
    return True


def backtrack(
    problem: Problem,
    state: SearchState,
    max_nodes: int,
    seeded: bool,
) -> bool:
    order = 4
    table = [-1] * (order * order)
    seed_tables = [table for model_order, table in state.premise_models if model_order == order]

    def value_order(cell: int) -> tuple[int, ...]:
        if not seeded:
            return tuple(range(order))
        preferred = [model[cell] for model in seed_tables]
        return tuple(dict.fromkeys(preferred + list(range(order))))

    def visit(cell: int) -> bool:
        if state.backtrack_nodes >= max_nodes:
            return False
        if cell == len(table):
            return consider_table(
                problem, state, "backtrack_seeded" if seeded else "backtrack_cold",
                order, tuple(table), False
            )
        for value in value_order(cell):
            state.backtrack_nodes += 1
            if state.backtrack_nodes > max_nodes:
                break
            table[cell] = value
            if premise_consistent(problem.premise, order, table, state) and visit(cell + 1):
                return True
        table[cell] = -1
        return False

    return visit(0)


def run_problem(
    problem: Problem,
    portfolio: str,
    max_backtrack_nodes: int,
    pseudo_random_count: int,
) -> SearchState:
    state = SearchState()
    lanes: dict[str, object] = {
        "exhaustive_2": lambda: run_table_lane(
            problem, state, "exhaustive_2", [(2, exhaustive_tables(2))]
        ),
        "exhaustive_3": lambda: run_table_lane(
            problem, state, "exhaustive_3", [(3, exhaustive_tables(3))]
        ),
        "structured": lambda: run_table_lane(
            problem,
            state,
            "structured",
            ((order, structured_tables(order)) for order in range(2, 8)),
            retain_models=True,
        ),
        "backtrack_cold": lambda: backtrack(problem, state, max_backtrack_nodes, False),
        "backtrack_seeded": lambda: backtrack(problem, state, max_backtrack_nodes, True),
        "pseudo_random": lambda: run_table_lane(
            problem,
            state,
            "pseudo_random_diagnostic",
            ((order, pseudo_random_tables(problem, order, pseudo_random_count)) for order in range(4, 8)),
        ),
    }
    orders = {
        "legacy": ("exhaustive_2", "exhaustive_3", "structured", "backtrack_cold", "pseudo_random"),
        "exhaustive_first_seeded": (
            "exhaustive_2", "exhaustive_3", "structured", "backtrack_seeded", "pseudo_random"
        ),
        "structured_first": ("structured", "exhaustive_2", "exhaustive_3", "backtrack_seeded", "pseudo_random"),
        "hybrid_cold": ("exhaustive_2", "structured", "exhaustive_3", "backtrack_cold", "pseudo_random"),
        "hybrid": ("exhaustive_2", "structured", "exhaustive_3", "backtrack_seeded", "pseudo_random"),
    }
    for lane in orders[portfolio]:
        if lanes[lane]():  # type: ignore[operator]
            break
    return state


def load_problems(paths: Sequence[Path], limit: int | None) -> list[Problem]:
    problems = []
    for path in paths:
        with path.open(encoding="utf-8") as source:
            for line in source:
                record = json.loads(line)
                if record["answer"] is not False:
                    continue
                problems.append(
                    Problem(
                        record["id"],
                        parse_equation(record["equation1"]),
                        parse_equation(record["equation2"]),
                    )
                )
                if limit is not None and len(problems) >= limit:
                    return problems
    return problems


def print_summary(portfolio: str, results: list[tuple[Problem, SearchState]]) -> None:
    solved = [(problem, state) for problem, state in results if state.hit_lane]
    lanes: dict[str, int] = {}
    orders: dict[int, int] = {}
    for _, state in solved:
        lanes[state.hit_lane or "unknown"] = lanes.get(state.hit_lane or "unknown", 0) + 1
        orders[state.hit_order or 0] = orders.get(state.hit_order or 0, 0) + 1
    unresolved = [problem.problem_id for problem, state in results if not state.hit_lane]
    full_state = {
        "portfolio": portfolio,
        "false_cases": len(results),
        "solved": len(solved),
        "first_hit_lane": lanes,
        "witness_order": orders,
        "tables_considered": sum(state.tables_considered for _, state in results),
        "assignment_checks": sum(state.assignment_checks for _, state in results),
        "duplicates_skipped": sum(state.duplicates for _, state in results),
        "backtrack_nodes": sum(state.backtrack_nodes for _, state in results),
        "retained_premise_models": sum(len(state.premise_models) for _, state in results),
        "unresolved": unresolved,
    }
    print(json.dumps(full_state, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--portfolio",
        choices=(
            "legacy", "exhaustive_first_seeded", "structured_first",
            "hybrid_cold", "hybrid", "all",
        ),
        default="all",
    )
    parser.add_argument("--limit", type=int)
    parser.add_argument("--max-backtrack-nodes", type=int, default=2_000)
    parser.add_argument("--pseudo-random-count", type=int, default=250)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[3]
    paths = [root / "examples/problems/hard1.jsonl", root / "examples/problems/hard2.jsonl"]
    problems = load_problems(paths, args.limit)
    portfolios = (
        ("legacy", "exhaustive_first_seeded", "structured_first", "hybrid_cold", "hybrid")
        if args.portfolio == "all"
        else (args.portfolio,)
    )
    for portfolio in portfolios:
        results = [
            (problem, run_problem(problem, portfolio, args.max_backtrack_nodes, args.pseudo_random_count))
            for problem in problems
        ]
        print_summary(portfolio, results)


if __name__ == "__main__":
    main()
