
import json
import os
import re
import sys
import urllib.request
from itertools import product
from typing import Callable, cast


API_BASE = os.environ.get("PIPELINE_API_BASE", "http://localhost:8000")

PROMPT = """You are a Lean 4 assistant for equational theories on magmas.
Return JSON only:
{"verdict":"false","counterexample_table":[[...], ...]}
or
{"verdict":"true","proof":"<Lean tactic body>"}
Do not include prose."""


Expression = Callable[[dict[str, int | Callable[[int, int], int]]], int]


def api_request(method: str, path: str, body: dict[str, object] | None = None) -> dict[str, object]:
    data = json.dumps(body).encode("utf-8") if body is not None else None
    request = urllib.request.Request(
        f"{API_BASE}{path}",
        data=data,
        method=method,
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(request, timeout=300) as response:
        payload = json.loads(response.read())
    data_payload = payload.get("data")
    if not isinstance(data_payload, dict):
        raise RuntimeError("API response is missing data object")
    return data_payload


def create_session(problem: dict[str, object]) -> str:
    result = api_request("POST", "/api/stage2/pipeline/sessions", {"problem": problem})
    session_id = result.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        raise RuntimeError("API response is missing session_id")
    return session_id


def close_session(session_id: str) -> None:
    api_request("DELETE", f"/api/stage2/pipeline/sessions/{session_id}")


def judge_answer(session_id: str, verdict: str, code: str) -> dict[str, object]:
    return api_request("POST", f"/api/stage2/pipeline/sessions/{session_id}/judge", {"verdict": verdict, "code": code})


def read_problem() -> dict[str, object]:
    raw_problem = os.environ.get("PROBLEM_JSON")
    if raw_problem:
        problem = json.loads(raw_problem)
    else:
        startup = json.loads(sys.stdin.readline())
        problem = startup.get("problem")
    if not isinstance(problem, dict):
        raise RuntimeError("Problem payload is missing")
    return problem


def strip_outer_parens(text: str) -> str:
    current = text.strip()
    while current.startswith("(") and current.endswith(")"):
        depth = 0
        wraps_all = True
        for index, char in enumerate(current):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            if depth == 0 and index < len(current) - 1:
                wraps_all = False
                break
        if not wraps_all:
            return current
        current = current[1:-1].strip()
    return current


def parse_equation(text: str) -> tuple[list[str], Expression, Expression]:
    normalized = text.replace("*", "◇")
    variables: list[str] = []
    seen: set[str] = set()
    for variable in re.findall(r"\b([a-z])\b", normalized):
        if variable not in seen:
            seen.add(variable)
            variables.append(variable)
    lhs_text, rhs_text = normalized.split("=", 1)

    def to_expr(source: str) -> Expression:
        term = strip_outer_parens(source)
        depth = 0
        operator_index = -1
        for index, char in enumerate(term):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            elif char == "◇" and depth == 0:
                operator_index = index
        if operator_index >= 0:
            left_expr = to_expr(term[:operator_index])
            right_expr = to_expr(term[operator_index + 1 :])
            return lambda env: cast(Callable[[int, int], int], env["op"])(left_expr(env), right_expr(env))
        variable = term.strip()
        if variable in seen:
            return lambda env: int(env[variable])
        raise ValueError(f"Cannot parse term: {variable}")

    return variables, to_expr(lhs_text), to_expr(rhs_text)


def equation_holds(variables: list[str], lhs_expr: Expression, rhs_expr: Expression, size: int, table: list[list[int]]) -> bool:
    def op(left: int, right: int) -> int:
        return table[left][right]

    for values in product(range(size), repeat=len(variables)):
        env: dict[str, int | Callable[[int, int], int]] = {"op": op}
        for variable, value in zip(variables, values):
            env[variable] = value
        if lhs_expr(env) != rhs_expr(env):
            return False
    return True


def iter_tables(size: int, limit: int | None = None):
    count = 0
    total_slots = size * size
    for encoding in range(size**total_slots):
        if limit is not None and count >= limit:
            break
        count += 1
        yield [[(encoding // (size ** (row * size + col))) % size for col in range(size)] for row in range(size)]


def find_counterexample(problem: dict[str, object]) -> list[list[int]] | None:
    lhs_text = str(problem.get("lhsText") or problem.get("lhs_text") or problem.get("equation1") or "")
    rhs_text = str(problem.get("rhsText") or problem.get("rhs_text") or problem.get("equation2") or "")
    lhs_variables, lhs_left, lhs_right = parse_equation(lhs_text)
    rhs_variables, rhs_left, rhs_right = parse_equation(rhs_text)

    for size, limit in ((1, None), (2, None), (3, None), (4, 120000)):
        for table in iter_tables(size, limit):
            lhs_ok = equation_holds(lhs_variables, lhs_left, lhs_right, size, table)
            rhs_ok = equation_holds(rhs_variables, rhs_left, rhs_right, size, table)
            if lhs_ok and not rhs_ok:
                return table
    return None


def main() -> None:
    session_id = ""
    try:
        problem = read_problem()
        session_id = create_session(problem)
        table = find_counterexample(problem)
        if table is None:
            print(json.dumps({"solved": False, "reason": "no small counterexample found"}))
            return
        result = judge_answer(session_id, "false", json.dumps(table))
        solved = result.get("status") == "accepted"
        print(json.dumps({"solved": solved, "verdict": "false", "answer": {"counterexample_table": table}, "judge": result}))
    except Exception as exc:
        print(json.dumps({"solved": False, "error": str(exc)}))
    finally:
        if session_id:
            try:
                close_session(session_id)
            except Exception:
                pass


if __name__ == "__main__":
    main()
