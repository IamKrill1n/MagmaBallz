"""Stage 2 solver for SAIR Equational Theories.

The deterministic core now handles:
1. reflexive TRUE implications;
2. singleton/collapse TRUE implications;
3. direct substitution, bounded rewrite chains, and subterm congruence TRUE implications;
4. finite FALSE witnesses from named small magmas, structured table families,
   affine/quadratic families, and bounded Fin n search.

LLM escalation is available only through the official Solo/Marathon
proxies. Unsupported cases are skipped rather than answered speculatively.
"""

from __future__ import annotations

import json
import importlib
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import lru_cache
from itertools import product
from typing import Any


PROMPT = """You are helping produce Lean 4 certificates for magma equation implications.

Return exactly one JSON object. The first character must be { and the last
character must be }. Do not include markdown, commentary, analysis, or <think>
blocks. Prefer the solver-owned DSL over raw Lean.

Problem {problem.id}: does Equation{problem.eq1_id} imply Equation{problem.eq2_id}?
Hypothesis: {problem.equation1}
Goal: {problem.equation2}

Deterministic analysis:
{solver.analysis}

Previous judge attempts:
{history.attempts}

Accepted JSON shapes:
1. TRUE rewrite chain, checked and rendered by the solver:
   {"verdict":"true","proof_kind":"rewrite_chain","chain":["<goal lhs>","<middle>","<goal rhs>"]}
   Use proof_kind "guided_chain" when a step may need a short solver-owned
   congruence or closure proof.
2. TRUE Lean body fallback, checked by the judge after sanitizer checks:
   {"verdict":"true","proof":"intro x y\n  exact ..."}
3. TRUE full Lean fallback, checked by the judge after sanitizer checks:
   {"verdict":"true","code":"import JudgeProblem\n\ndef submission : Goal := by\n  ..."}
4. FALSE finite countermodel, verified locally before Lean is emitted:
   {"verdict":"false","counterexample_table":[[0,1],[1,0]]}

Do not use sorry, admit, axioms, unsafe/meta commands, unsupported imports,
or Teorth theorem names. Marathon accepts only solver-verified DSL certificates,
so raw Lean/proof bodies are mainly a Solo debugging fallback. If you are unsure,
return a TRUE chain whose adjacent terms are solver-provable, or a finite table DSL.
"""

MAX_SUBMISSION_BYTES = 500_000
MAX_LEAN_CODE_BYTES = 100_000
MAX_FALSE_CERT_BYTES = 20_000
VALID_VERDICTS = {"true", "false"}
AFFINE_LINEAR_SIZES = (2, 3, 4, 5, 7, 8, 9)
AFFINE_QUADRATIC_SIZES = (2, 3, 5, 7)
ENUMERATION_MAX_N = 3
STRUCTURED_MAX_N = 7
REWRITE_CHAIN_MAX_DEPTH = 2
ABSORPTION_CHAIN_MAX_DEPTH = 3
ABSORPTION_POOL_LIMIT = 10
ABSORPTION_FRONTIER_LIMIT = 220
ABSORPTION_MAX_FILLS = 180
ABSORPTION_TERM_SLACK = 6
ABSORPTION_TIME_BUDGET = 0.05
ABSORPTION_DEEP_CHAIN_MAX_DEPTH = 3
ABSORPTION_DEEP_POOL_LIMIT = 12
ABSORPTION_DEEP_FRONTIER_LIMIT = 260
ABSORPTION_DEEP_MAX_FILLS = 120
ABSORPTION_DEEP_TERM_SLACK = 8
ABSORPTION_DEEP_TIME_BUDGET = 1.25
ABSORPTION_CONTEXT_BRIDGE_POOL_LIMIT = 16
ABSORPTION_CONTEXT_BRIDGE_SEED_LIMIT = 8
ABSORPTION_CONTEXT_BRIDGE_MAX_FILLS = 5000
ABSORPTION_CONTEXT_BRIDGE_TERM_SLACK = 12
ABSORPTION_CONTEXT_BRIDGE_DEPTH_SLACK = 4
ABSORPTION_CONTEXT_BRIDGE_TIME_BUDGET = 1.5
EQUATIONAL_CLOSURE_CHAIN_MAX_DEPTH = 4
EQUATIONAL_CLOSURE_POOL_LIMIT = 18
EQUATIONAL_CLOSURE_FRONTIER_LIMIT = 900
EQUATIONAL_CLOSURE_MAX_FILLS = 350
EQUATIONAL_CLOSURE_TERM_SLACK = 10
EQUATIONAL_CLOSURE_DEPTH_SLACK = 3
EQUATIONAL_CLOSURE_TIME_BUDGET = 0.45
GUIDED_CHAIN_MAX_DEPTH = 3
GUIDED_CHAIN_CLOSURE_TIME_BUDGET = 0.08
KNOWN_ORDER4_MAX_EQ_ID = 4694
CP_LEMMA_BUDGET_ORDER5 = 24
CP_GAP_TIME_BUDGET = 0.35
CP_LEMMA_TERM_SLACK = 4
CP_RAW_PAIR_CAP = 400
CP_CANONICAL_VARS = ("x", "y", "z", "w", "u", "v", "p", "q", "r", "s")
CP_HOP_CACHE_LIMIT = 4096
CP_SATURATION_ROUNDS = 10
CP_SATURATION_TIME_BUDGET = 20.0
CP_SATURATION_LEMMA_BUDGET = 200
CP_SATURATION_RAW_PAIR_CAP = 2500
CP_SATURATION_GAP_TIME = 2.5
CP_SATURATION_TERM_SLACK = 8
LLM_MAX_ROUNDS = 2
MARATHON_LLM_MAX_CALLS = 24
MARATHON_LLM_BATCH_SIZE = 10
MARATHON_REF_SECONDS_DEFAULT = 600.0
LLM_MAX_TABLE_N = 8
LLM_MAX_OUTPUT_TOKENS = 4096
LLM_HTTP_TIMEOUT_SECONDS = 45.0

LLM_CONFIG = {
    "model": "openai/gpt-oss-120b",
    "provider": "deepinfra/bf16",
    "max_output_tokens": LLM_MAX_OUTPUT_TOKENS,
    "temperature": 0.0,
    "reasoning_effort": "low",
    "use_seed": True,
    "seed": 0,
    "http_timeout_seconds": LLM_HTTP_TIMEOUT_SECONDS,
}

ALLOWED_IMPORTS = {
    "JudgeProblem",
    "JudgeDecide.DecideBang",
    "JudgeFinOp.MemoFinOp",
    "JudgeMagma.Magma",
}

BANNED_LEAN_RE = re.compile(
    r"\b(?:sorry|admit|sorryAx|dbg_trace|dbgTrace|run_tac|mkSorry|"
    r"initialize|builtin_initialize|axiom|unsafe|opaque|macro|elab|syntax)\b"
    r"|#(?:eval|check|print|reduce)|\b(?:Teorth|teorth|EquationalTheories)\b"
    r"|\bEquation(?!LHS\b|RHS\b)\d+\b",
    re.IGNORECASE,
)

WITNESS_TABLES = (
    ("LP", [[0, 0], [1, 1]]),
    ("RP", [[0, 1], [0, 1]]),
    ("C0", [[0, 0], [0, 0]]),
    ("XOR", [[0, 1], [1, 0]]),
    ("AND", [[0, 0], [0, 1]]),
    ("OR", [[0, 1], [1, 1]]),
    ("XNOR", [[1, 0], [0, 1]]),
    ("NAND", [[1, 1], [1, 0]]),
    ("NOR", [[1, 0], [0, 0]]),
    ("IMP", [[1, 0], [1, 1]]),
    ("NIMP", [[0, 1], [0, 0]]),
    ("A2", [[0, 0], [1, 0]]),
    ("Z3A", [[0, 1, 2], [1, 2, 0], [2, 0, 1]]),
    ("Z3B", [[0, 2, 1], [2, 1, 0], [1, 0, 2]]),
    ("T3L", [[0, 0, 0], [0, 0, 0], [0, 1, 0]]),
    ("T3R", [[0, 0, 0], [0, 0, 0], [0, 0, 1]]),
    ("S4A", [[3, 1, 1, 3], [0, 3, 2, 3], [3, 1, 3, 3], [0, 1, 2, 3]]),
    ("S5A", [[1, 2, 3, 4, 0], [0, 4, 3, 4, 1], [4, 2, 2, 1, 0], [2, 0, 2, 3, 2], [3, 1, 3, 0, 4]]),
    ("S4B", [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 1, 0]]),
    ("S5B", [[4, 3, 2, 2, 2], [2, 3, 2, 2, 3], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]]),
    ("S5C", [[0, 0, 0, 2, 2], [4, 1, 1, 4, 1], [1, 2, 2, 1, 2], [2, 3, 3, 3, 2], [2, 4, 4, 2, 4]]),
    ("S4C", [[3, 3, 2, 2], [1, 1, 0, 0], [3, 3, 2, 2], [1, 1, 0, 0]]),
    ("S4D", [[3, 2, 3, 3], [3, 3, 3, 3], [2, 3, 3, 3], [1, 2, 3, 3]]),
    ("S4E", [[2, 2, 2, 3], [3, 3, 2, 3], [2, 2, 2, 3], [3, 3, 2, 3]]),
    ("S4F", [[0, 2, 3, 1], [3, 1, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3]]),
    ("S5D", [[3, 3, 2, 2, 3], [4, 4, 2, 4, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]]),
    # CG9: a NON-natural central groupoid of order 9 (0-1 matrix A with
    # A^2 = J, Knuth 1970), found by exhaustive A^2=J search. Satisfies
    # Equation 168 `x = (y ◇ x) ◇ (x ◇ z)` while falsifying high-numbered
    # consequences that hold in every *natural* central groupoid
    # ((a,b)◇(c,d) = (b,c)) of any size — which is why n ≤ 8 table search
    # and the natural family both miss these witnesses entirely (finite
    # central groupoids exist only at orders n^2: 1, 4, 9, 16, ...).
    ("CG9", [[0, 0, 0, 1, 1, 1, 2, 2, 2], [3, 3, 3, 4, 4, 4, 5, 5, 5],
             [6, 6, 6, 7, 8, 8, 8, 7, 7], [0, 0, 0, 1, 1, 1, 2, 2, 2],
             [3, 3, 3, 4, 4, 4, 5, 5, 5], [6, 6, 6, 7, 8, 8, 8, 7, 7],
             [0, 0, 0, 1, 1, 1, 2, 2, 2], [3, 3, 3, 7, 8, 8, 8, 7, 7],
             [6, 6, 6, 4, 4, 4, 5, 5, 5]]),
)


def reflexive_true_certificate() -> str:
    return """import JudgeProblem

def submission : Goal := by
  intro G _ h
  exact h
"""


def false_certificate(n: int, table: list[list[int]]) -> str:
    table_str = json.dumps(table, separators=(",", ":"))
    max_rec_depth = "set_option maxRecDepth 20000\n" if n >= 7 else ""
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n"
        f"{max_rec_depth}\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        "  }\n"
        f"  refine Exists.intro (Fin {n}) ?_\n"
        "  refine Exists.intro m ?_\n"
        "  decideFin!\n"
    )


def singleton_true_certificate(
    eq1_vars: list[str],
    eq2_vars: list[str],
    singleton_var: str,
    singleton_on_lhs: bool,
) -> str:
    if not eq1_vars:
        return reflexive_true_certificate()

    args_a: list[str] = []
    args_b: list[str] = []
    for var in eq1_vars:
        if var == singleton_var:
            args_a.append("a")
            args_b.append("b")
        else:
            args_a.append("b")
            args_b.append("b")

    call_a = "h" if not args_a else "h " + " ".join(args_a)
    call_b = "h" if not args_b else "h " + " ".join(args_b)
    if singleton_on_lhs:
        collapse = f"({call_a}).trans ({call_b}).symm"
    else:
        collapse = f"({call_a}).symm.trans ({call_b})"
    intro_vars = " ".join(eq2_vars)
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""

    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hall : ∀ a b : G, a = b := by\n"
        "    intro a b\n"
        f"    exact {collapse}\n"
        f"{intro_line}"
        "  exact hall _ _\n"
    )


def substitution_true_certificate(
    eq2_vars: list[str],
    call_expr: str,
) -> str:
    intro_vars = " ".join(eq2_vars)
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  exact {call_expr}\n"
    )


def projection_true_certificate(eq2_vars: list[str], proof_expr: str) -> str:
    intro_vars = " ".join(eq2_vars)
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )


Term = tuple[Any, ...]


def is_reflexive_problem(problem: dict[str, Any]) -> bool:
    return problem.get("eq1_id") == problem.get("eq2_id")


def make_true_answer(problem: dict[str, Any], code: str) -> dict[str, Any]:
    return {
        "id": str(problem.get("id", "")),
        "verdict": "true",
        "code": code,
    }


def make_false_answer(problem: dict[str, Any], n: int, table: list[list[int]]) -> dict[str, Any]:
    return {
        "id": str(problem.get("id", "")),
        "verdict": "false",
        "code": false_certificate(n, table),
    }


def judge_answer_payload(answer: dict[str, Any]) -> dict[str, str] | None:
    verdict = answer.get("verdict")
    code = answer.get("code")
    if verdict not in VALID_VERDICTS or not isinstance(code, str):
        return None
    code_bytes = len(code.encode("utf-8"))
    if code_bytes > MAX_LEAN_CODE_BYTES:
        return None
    if verdict == "false" and code_bytes > MAX_FALSE_CERT_BYTES:
        return None
    return {"verdict": verdict, "code": code}


def marathon_answer_payload(answer: dict[str, Any]) -> dict[str, str] | None:
    pid = answer.get("id")
    if not isinstance(pid, str) or not pid:
        return None
    payload = judge_answer_payload(answer)
    if payload is None:
        return None
    return {"id": pid, **payload}


def strip_outer_parens(text: str) -> str:
    s = text.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        wraps = True
        for idx, char in enumerate(s):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            if depth == 0 and idx < len(s) - 1:
                wraps = False
                break
        if not wraps:
            break
        s = s[1:-1].strip()
    return s


def parse_term(text: str, variables: set[str]) -> Term:
    s = strip_outer_parens(text)
    depth = 0
    last_op = -1
    for idx, char in enumerate(s):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char in {"◇", "*"} and depth == 0:
            last_op = idx
    if last_op >= 0:
        return ("op", parse_term(s[:last_op], variables), parse_term(s[last_op + 1 :], variables))
    if len(s) == 1 and s in variables:
        return ("var", s)
    raise ValueError(f"cannot parse term: {text!r}")


def parse_equation(text: str) -> dict[str, Any]:
    if "=" not in text:
        raise ValueError(f"cannot parse equation: {text!r}")
    variables = []
    seen: set[str] = set()
    for var in re.findall(r"\b([a-z])\b", text):
        if var not in seen:
            seen.add(var)
            variables.append(var)
    lhs_text, rhs_text = text.split("=", 1)
    lhs_text = lhs_text.strip()
    rhs_text = rhs_text.strip()
    return {
        "variables": variables,
        "lhs": parse_term(lhs_text, seen),
        "rhs": parse_term(rhs_text, seen),
        "lhs_text": lhs_text,
        "rhs_text": rhs_text,
        "text": text.strip(),
    }


@lru_cache(maxsize=None)
def term_vars_tuple(term: Term) -> tuple[str, ...]:
    if term[0] == "var":
        return (str(term[1]),)
    return tuple(set(term_vars_tuple(term[1])) | set(term_vars_tuple(term[2])))


def term_vars(term: Term) -> set[str]:
    return set(term_vars_tuple(term))


@lru_cache(maxsize=None)
def term_size(term: Term) -> int:
    if term[0] == "var":
        return 1
    return 1 + term_size(term[1]) + term_size(term[2])


@lru_cache(maxsize=None)
def term_depth(term: Term) -> int:
    if term[0] == "var":
        return 0
    return 1 + max(term_depth(term[1]), term_depth(term[2]))


@lru_cache(maxsize=None)
def term_to_lean(term: Term) -> str:
    if term[0] == "var":
        return str(term[1])
    return f"({term_to_lean(term[1])} ◇ {term_to_lean(term[2])})"


@lru_cache(maxsize=None)
def dual_term(term: Term) -> Term:
    if term[0] == "var":
        return term
    return ("op", dual_term(term[2]), dual_term(term[1]))


def dual_equation(equation: dict[str, Any]) -> dict[str, Any]:
    out = dict(equation)
    out["lhs"] = dual_term(equation["lhs"])
    out["rhs"] = dual_term(equation["rhs"])
    out["lhs_text"] = term_to_lean(out["lhs"])
    out["rhs_text"] = term_to_lean(out["rhs"])
    out["text"] = f"{out['lhs_text']} = {out['rhs_text']}"
    return out


@lru_cache(maxsize=None)
def term_subterms_tuple(term: Term) -> tuple[Term, ...]:
    out: list[Term] = [term]
    if term[0] == "op":
        out.extend(term_subterms_tuple(term[1]))
        out.extend(term_subterms_tuple(term[2]))
    return tuple(out)


def term_subterms(term: Term) -> list[Term]:
    return list(term_subterms_tuple(term))


@lru_cache(maxsize=None)
def boundary_vars(term: Term) -> tuple[str | None, str | None]:
    if term[0] == "var":
        return str(term[1]), str(term[1])
    left = boundary_vars(term[1])
    right = boundary_vars(term[2])
    return left[0], right[1]


@lru_cache(maxsize=None)
def subterm_paths_tuple(term: Term, prefix: tuple[int, ...] = ()) -> tuple[tuple[int, ...], ...]:
    paths: list[tuple[int, ...]] = [prefix]
    if term[0] == "op":
        paths.extend(subterm_paths_tuple(term[1], prefix + (0,)))
        paths.extend(subterm_paths_tuple(term[2], prefix + (1,)))
    return tuple(paths)


def subterm_paths(term: Term, prefix: tuple[int, ...] = ()) -> list[tuple[int, ...]]:
    return list(subterm_paths_tuple(term, prefix))


@lru_cache(maxsize=None)
def term_at_path(term: Term, path: tuple[int, ...]) -> Term:
    cur = term
    for part in path:
        cur = cur[1] if part == 0 else cur[2]
    return cur


@lru_cache(maxsize=None)
def replace_subterm(term: Term, path: tuple[int, ...], replacement: Term) -> Term:
    if not path:
        return replacement
    if term[0] != "op":
        return term
    head, tail = path[0], path[1:]
    if head == 0:
        return ("op", replace_subterm(term[1], tail, replacement), term[2])
    return ("op", term[1], replace_subterm(term[2], tail, replacement))


@lru_cache(maxsize=None)
def context_to_lean(term: Term, path: tuple[int, ...], placeholder: str = "t") -> str:
    if not path:
        return placeholder
    if term[0] == "var":
        return term_to_lean(term)
    head, tail = path[0], path[1:]
    if head == 0:
        left = context_to_lean(term[1], tail, placeholder)
        right = term_to_lean(term[2])
    else:
        left = term_to_lean(term[1])
        right = context_to_lean(term[2], tail, placeholder)
    return f"({left} ◇ {right})"


def eval_term(term: Term, env: dict[str, Any]) -> int:
    if term[0] == "var":
        return env[term[1]]
    return env["op"](eval_term(term[1], env), eval_term(term[2], env))


def instantiate_term(term: Term, subst: dict[str, Term]) -> Term:
    if term[0] == "var":
        return subst[term[1]]
    return ("op", instantiate_term(term[1], subst), instantiate_term(term[2], subst))


def instantiate_term_if_bound(term: Term, subst: dict[str, Term]) -> Term | None:
    if term[0] == "var":
        return subst.get(term[1])
    left = instantiate_term_if_bound(term[1], subst)
    if left is None:
        return None
    right = instantiate_term_if_bound(term[2], subst)
    if right is None:
        return None
    return ("op", left, right)


def match_term(pattern: Term, target: Term, subst: dict[str, Term]) -> bool:
    if pattern[0] == "var":
        name = pattern[1]
        bound = subst.get(name)
        if bound is None:
            subst[name] = target
            return True
        return bound == target
    if target[0] != "op":
        return False
    return match_term(pattern[1], target[1], subst) and match_term(pattern[2], target[2], subst)


def equation_holds(equation: dict[str, Any], table: list[list[int]]) -> bool:
    n = len(table)

    def op(a: int, b: int) -> int:
        return table[a][b]

    for values in product(range(n), repeat=len(equation["variables"])):
        env: dict[str, Any] = {"op": op}
        env.update(zip(equation["variables"], values))
        if eval_term(equation["lhs"], env) != eval_term(equation["rhs"], env):
            return False
    return True


def table_is_counterexample(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    table: list[list[int]],
) -> bool:
    return equation_holds(eq1, table) and not equation_holds(eq2, table)


def enumerate_tables(n: int):
    total = n ** (n * n)
    for encoding in range(total):
        yield [[(encoding // (n ** (row * n + col))) % n for col in range(n)] for row in range(n)]


def table_key(table: list[list[int]]) -> str:
    return json.dumps(table, separators=(",", ":"))


def transpose_table(table: list[list[int]]) -> list[list[int]]:
    n = len(table)
    return [[table[y][x] for y in range(n)] for x in range(n)]


def structured_family_tables(max_n: int = STRUCTURED_MAX_N):
    seen: set[str] = set()

    def emit(route: str, table: list[list[int]]):
        if not table or len(table) > max_n:
            return None
        key = table_key(table)
        if key in seen:
            return None
        seen.add(key)
        return route, table

    for n in range(2, max_n + 1):
        candidates: list[tuple[str, list[list[int]]]] = [
            (f"false:semilattice:min:z{n}", [[min(x, y) for y in range(n)] for x in range(n)]),
            (f"false:semilattice:max:z{n}", [[max(x, y) for y in range(n)] for x in range(n)]),
            (f"false:spine:leftsucc:z{n}", [[(x + 1) % n for _y in range(n)] for x in range(n)]),
            (f"false:spine:rightsucc:z{n}", [[(y + 1) % n for y in range(n)] for _x in range(n)]),
            (f"false:spine:ifleft0:z{n}", [[y if x == 0 else x for y in range(n)] for x in range(n)]),
            (f"false:spine:ifright0:z{n}", [[x if y == 0 else y for y in range(n)] for x in range(n)]),
            (f"false:central:neg_sum:z{n}", [[(-x - y) % n for y in range(n)] for x in range(n)]),
            (f"false:central:one_neg_sum:z{n}", [[(1 - x - y) % n for y in range(n)] for x in range(n)]),
        ]
        for route, table in candidates:
            item = emit(route, table)
            if item is not None:
                yield item

    for rows in range(2, max_n + 1):
        for cols in range(2, max_n + 1):
            n = rows * cols
            if n > max_n:
                continue

            def idx(row: int, col: int) -> int:
                return row * cols + col

            table = []
            for a in range(n):
                ar, _ac = divmod(a, cols)
                row = []
                for b in range(n):
                    _br, bc = divmod(b, cols)
                    row.append(idx(ar, bc))
                table.append(row)
            item = emit(f"false:rectband:{rows}x{cols}", table)
            if item is not None:
                yield item


def affine_family_tables(max_n: int = 5):
    seen: set[str] = set()
    for n in AFFINE_LINEAR_SIZES:
        if n > max_n:
            continue
        for a in range(n):
            for b in range(n):
                for c in range(n):
                    table = [[(a * x + b * y + c) % n for y in range(n)] for x in range(n)]
                    key = json.dumps(table, separators=(",", ":"))
                    if key in seen:
                        continue
                    seen.add(key)
                    if c == 0:
                        route = f"false:linear:z{n}:{a},{b}"
                    else:
                        route = f"false:affine:z{n}:{a},{b},{c}"
                    yield route, table


def quadratic_family_tables(max_n: int = STRUCTURED_MAX_N):
    seen: set[str] = set()
    for n in AFFINE_QUADRATIC_SIZES:
        if n > max_n:
            continue
        coeffs = tuple(range(n)) if n <= 3 else tuple(dict.fromkeys((0, 1, 2 % n, n - 1)))
        nonzero = tuple(c for c in coeffs if c % n != 0) or (1,)

        for a in coeffs:
            for b in coeffs:
                for c in nonzero:
                    for d in coeffs:
                        table = [[(a * x + b * y + c * x * y + d) % n for y in range(n)] for x in range(n)]
                        key = table_key(table)
                        if key in seen:
                            continue
                        seen.add(key)
                        yield f"false:quadratic_xy:z{n}:{a},{b},{c},{d}", table

        for a in coeffs:
            for b in coeffs:
                for c in nonzero:
                    table_x = [[(a * x + b * y + c * x * x) % n for y in range(n)] for x in range(n)]
                    key_x = table_key(table_x)
                    if key_x not in seen:
                        seen.add(key_x)
                        yield f"false:quadratic_x2:z{n}:{a},{b},{c}", table_x
                    table_y = [[(a * x + b * y + c * y * y) % n for y in range(n)] for x in range(n)]
                    key_y = table_key(table_y)
                    if key_y not in seen:
                        seen.add(key_y)
                        yield f"false:quadratic_y2:z{n}:{a},{b},{c}", table_y


def singleton_route(eq1: dict[str, Any]) -> tuple[str, bool] | None:
    lhs = eq1["lhs"]
    rhs = eq1["rhs"]
    if lhs[0] == "var" and lhs[1] not in term_vars(rhs):
        return str(lhs[1]), True
    if rhs[0] == "var" and rhs[1] not in term_vars(lhs):
        return str(rhs[1]), False
    return None


def middle_self_collapse_source(eq1: dict[str, Any]) -> tuple[str, str, str, bool] | None:
    for swapped, variable_side, op_side in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if variable_side[0] != "var" or op_side[0] != "op" or op_side[1][0] != "op" or op_side[2][0] != "var":
            continue
        root = str(variable_side[1])
        inner = op_side[1]
        tail = op_side[2]
        if inner[1][0] != "var" or inner[2] != ("var", root):
            continue
        lead = str(inner[1][1])
        tail_name = str(tail[1])
        if len({root, lead, tail_name}) != 3:
            continue
        if set(eq1["variables"]) != {root, lead, tail_name}:
            continue
        return root, lead, tail_name, swapped
    return None


def middle_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = middle_self_collapse_source(eq1)
    if source is None:
        return None
    root, lead, tail, swapped = source
    call = call_expression_lean_args(eq1["variables"], {root: "a", lead: "b", tail: "c"})
    if swapped:
        call = f"({call}).symm"
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hc : ∀ a b c : G, a = (b ◇ a) ◇ c := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hright : ∀ a b c : G, b = a ◇ c := by\n"
        "    intro a b c\n"
        "    have h1 : a = (b ◇ a) ◇ b := hc a b b\n"
        "    have h2 : b = ((b ◇ a) ◇ b) ◇ c := hc b (b ◇ a) c\n"
        "    exact h2.trans (congrArg (fun t => t ◇ c) h1.symm)\n"
        "  have hall : ∀ a b : G, a = b := by\n"
        "    intro a b\n"
        "    have hb : b = a := by\n"
        "      exact (hright a b a).trans (hright a a a).symm\n"
        "    exact hb.symm\n"
        f"{intro_line}"
        "  exact hall _ _\n"
    )
    return "true:middle_self_collapse", code


def front_double_self_collapse_source(eq1: dict[str, Any]) -> tuple[str, str, str, bool] | None:
    for swapped, variable_side, op_side in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if variable_side[0] != "var" or op_side[0] != "op" or op_side[1][0] != "var":
            continue
        root = str(variable_side[1])
        lead = str(op_side[1][1])
        middle = op_side[2]
        if middle[0] != "op" or middle[1] != ("var", root):
            continue
        tail = middle[2]
        if tail[0] != "op" or tail[1] != ("var", root) or tail[2][0] != "var":
            continue
        tail_name = str(tail[2][1])
        if len({root, lead, tail_name}) != 3:
            continue
        if set(eq1["variables"]) != {root, lead, tail_name}:
            continue
        return root, lead, tail_name, swapped
    return None


def front_double_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = front_double_self_collapse_source(eq1)
    if source is None:
        return None
    root, lead, tail, swapped = source
    call = call_expression_lean_args(eq1["variables"], {root: "a", lead: "b", tail: "c"})
    if swapped:
        call = f"({call}).symm"
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hc : ∀ a b c : G, a = b ◇ (a ◇ (a ◇ c)) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hall : ∀ a b : G, a = b := by\n"
        "    have hrow : ∀ a b c : G, a ◇ b = a ◇ (a ◇ c) := by\n"
        "      intro a b c\n"
        "      have ha : a = (b ◇ (b ◇ c)) ◇ (a ◇ (a ◇ c)) := by\n"
        "        exact hc a (b ◇ (b ◇ c)) c\n"
        "      have ht : b ◇ (b ◇ c) = (a ◇ (a ◇ c)) ◇ ((b ◇ (b ◇ c)) ◇ a) := by\n"
        "        exact (hc (b ◇ (b ◇ c)) (a ◇ (a ◇ c)) (a ◇ (a ◇ c))).trans (congrArg (fun t => (a ◇ (a ◇ c)) ◇ ((b ◇ (b ◇ c)) ◇ t)) ha.symm)\n"
        "      have hb : b = (a ◇ (a ◇ c)) ◇ ((a ◇ (a ◇ c)) ◇ ((b ◇ (b ◇ c)) ◇ a)) := by\n"
        "        exact (hc b (a ◇ (a ◇ c)) c).trans (congrArg (fun t => (a ◇ (a ◇ c)) ◇ t) ht)\n"
        "      have hs : a ◇ (a ◇ c) = a ◇ b := by\n"
        "        exact (hc (a ◇ (a ◇ c)) a ((b ◇ (b ◇ c)) ◇ a)).trans (congrArg (fun t => a ◇ t) hb.symm)\n"
        "      exact hs.symm\n"
        "    intro a b\n"
        "    have ha : a = (b ◇ b) ◇ (a ◇ a) := by\n"
        "      exact (hc a (b ◇ b) b).trans (congrArg (fun t => (b ◇ b) ◇ t) (hrow a a b).symm)\n"
        "    have hb : b = (b ◇ b) ◇ (b ◇ b) := by\n"
        "      exact (hc b (b ◇ b) b).trans (congrArg (fun t => (b ◇ b) ◇ t) (hrow b b b).symm)\n"
        "    have hsame : (b ◇ b) ◇ (a ◇ a) = (b ◇ b) ◇ (b ◇ b) := by\n"
        "      exact (hrow (b ◇ b) (a ◇ a) b).trans (hrow (b ◇ b) (b ◇ b) b).symm\n"
        "    exact ha.trans (hsame.trans hb.symm)\n"
        f"{intro_line}"
        "  exact hall _ _\n"
    )
    return "true:front_double_self_collapse", code


def alternating_front_self_collapse_source(eq1: dict[str, Any]) -> tuple[str, str, str] | None:
    for variable_side, op_side in ((eq1["lhs"], eq1["rhs"]), (eq1["rhs"], eq1["lhs"])):
        if variable_side[0] != "var" or op_side[0] != "op" or op_side[1][0] != "var":
            continue
        root = str(variable_side[1])
        lead = str(op_side[1][1])
        middle = op_side[2]
        if middle[0] != "op" or middle[1] != ("var", root):
            continue
        tail = middle[2]
        if tail[0] != "op" or tail[1] != ("var", lead) or tail[2][0] != "var":
            continue
        tail_name = str(tail[2][1])
        if len({root, lead, tail_name}) != 3:
            continue
        if set(eq1["variables"]) != {root, lead, tail_name}:
            continue
        return root, lead, tail_name
    return None


def alternating_front_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = alternating_front_self_collapse_source(eq1)
    if source is None:
        return None
    root, lead, _tail = source
    singleton_goal = {
        "lhs": ("var", root),
        "rhs": ("var", lead),
        "variables": [root, lead],
        "lhs_text": root,
        "rhs_text": lead,
        "text": f"{root} = {lead}",
    }
    result = _closure_proof_expr_impl(
        eq1,
        singleton_goal,
        route_name="true:alternating_front_self_collapse:hall",
        chain_max_depth=EQUATIONAL_CLOSURE_CHAIN_MAX_DEPTH,
        pool_limit=EQUATIONAL_CLOSURE_POOL_LIMIT,
        frontier_limit=EQUATIONAL_CLOSURE_FRONTIER_LIMIT,
        max_fills=EQUATIONAL_CLOSURE_MAX_FILLS,
        term_slack=EQUATIONAL_CLOSURE_TERM_SLACK,
        depth_slack=EQUATIONAL_CLOSURE_DEPTH_SLACK,
        time_budget=0.08,
    )
    if result is None:
        return None
    _route, proof_expr = result
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"  have hall : ∀ {root} {lead} : G, {root} = {lead} := by\n"
        f"    intro {root} {lead}\n"
        f"    exact {proof_expr}\n"
        f"{intro_line}"
        "  exact hall _ _\n"
    )
    return "true:alternating_front_self_collapse", code


def mirrored_alternating_front_self_collapse_source(eq1: dict[str, Any]) -> tuple[str, str, str, bool] | None:
    for swapped, variable_side, op_side in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if variable_side[0] != "var" or op_side[0] != "op" or op_side[1][0] != "var":
            continue
        root = str(variable_side[1])
        lead = str(op_side[1][1])
        middle = op_side[2]
        if middle[0] != "op" or middle[1] != ("var", root):
            continue
        tail = middle[2]
        if tail[0] != "op" or tail[1][0] != "var" or tail[2] != ("var", lead):
            continue
        tail_name = str(tail[1][1])
        if len({root, lead, tail_name}) != 3:
            continue
        if set(eq1["variables"]) != {root, lead, tail_name}:
            continue
        return root, lead, tail_name, swapped
    return None


def mirrored_alternating_front_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = mirrored_alternating_front_self_collapse_source(eq1)
    if source is None:
        return None
    root, lead, tail, swapped = source
    call = call_expression_lean_args(eq1["variables"], {root: "a", lead: "b", tail: "c"})
    if swapped:
        call = f"({call}).symm"
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = b ◇ (a ◇ (c ◇ b)) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hall : ∀ a b : G, a = b := by\n"
        "    intro a b\n"
        "    have hc : ∀ x y z : G, x = (y ◇ x) ◇ z := by\n"
        "      intro x y z\n"
        "      exact (hsrc x (y ◇ x) z).trans (congrArg (fun t => (y ◇ x) ◇ t) (hsrc z x y).symm)\n"
        "    have hright : ∀ x y z : G, y = x ◇ z := by\n"
        "      intro x y z\n"
        "      have h1 : x = (y ◇ x) ◇ y := hc x y y\n"
        "      have h2 : y = ((y ◇ x) ◇ y) ◇ z := hc y (y ◇ x) z\n"
        "      exact h2.trans (congrArg (fun t => t ◇ z) h1.symm)\n"
        "    exact ((hright a b a).trans (hright a a a).symm).symm\n"
        f"{intro_line}"
        "  exact hall _ _\n"
    )
    return "true:mirrored_alternating_front_self_collapse", code


def sandwich_left_projection_source(eq1: dict[str, Any]) -> tuple[str, str, str, bool] | None:
    for swapped, variable_side, op_side in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if variable_side[0] != "var" or op_side[0] != "op":
            continue
        root = str(variable_side[1])
        root_term = ("var", root)
        if op_side[1] != root_term:
            continue
        tail = op_side[2]
        if tail[0] != "op" or tail[1][0] != "var":
            continue
        lead = str(tail[1][1])
        inner = tail[2]
        if inner[0] != "op" or inner[1][0] != "var" or inner[2] != ("var", lead):
            continue
        middle = str(inner[1][1])
        if len({root, lead, middle}) != 3:
            continue
        if set(eq1["variables"]) != {root, lead, middle}:
            continue
        return root, lead, middle, swapped
    return None


def projection_proof_expr_from_law(
    eq2: dict[str, Any],
    side: str,
    *,
    hypothesis_name: str,
) -> str | None:
    law = parse_equation("x = x ◇ y" if side == "left" else "x = y ◇ x")
    left = projection_term_proof(law, eq2["lhs"], side, hypothesis_name=hypothesis_name)
    right = projection_term_proof(law, eq2["rhs"], side, hypothesis_name=hypothesis_name)
    if left is None or right is None:
        return None
    left_proof, left_target = left
    right_proof, right_target = right
    if left_target != right_target:
        return None
    if left_proof == "rfl":
        return f"({right_proof}).symm" if right_proof != "rfl" else "rfl"
    if right_proof == "rfl":
        return left_proof
    return f"({left_proof}).trans ({right_proof}).symm"


def sandwich_left_projection_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = sandwich_left_projection_source(eq1)
    if source is None:
        return None
    proof_expr = projection_proof_expr_from_law(eq2, "left", hypothesis_name="hleft")
    if proof_expr is None:
        return None
    root, lead, middle, swapped = source
    call = call_expression_lean_args(eq1["variables"], {root: "a", lead: "b", middle: "c"})
    if swapped:
        call = f"({call}).symm"
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = a ◇ (b ◇ (c ◇ b)) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hleft : ∀ a b : G, a = a ◇ b := by\n"
        "    intro a b\n"
        "    exact\n"
        "      ((hsrc a b a).trans\n"
        "        (congrArg (fun t => a ◇ (b ◇ t)) (hsrc (a ◇ b) b a))).trans\n"
        "        ((congrArg (fun t => a ◇ t) (hsrc b (a ◇ b) b)).symm)\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:sandwich_left_projection", code


def square_twist_comm_source(eq1: dict[str, Any]) -> tuple[str, str, bool] | None:
    for swapped, source_lhs, source_rhs in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if source_lhs[0] != "op" or source_rhs[0] != "op" or source_rhs[1][0] != "op":
            continue
        if source_lhs[1][0] != "var" or source_lhs[2][0] != "var" or source_rhs[2][0] != "var":
            continue
        left_name = str(source_lhs[1][1])
        right_name = str(source_lhs[2][1])
        square = source_rhs[1]
        tail_name = str(source_rhs[2][1])
        if left_name == right_name or tail_name != left_name:
            continue
        if square != ("op", ("var", right_name), ("var", right_name)):
            continue
        if set(eq1["variables"]) != {left_name, right_name}:
            continue
        return left_name, right_name, swapped
    return None


@lru_cache(maxsize=None)
def commutative_term_key(term: Term) -> Term:
    if term[0] == "var":
        return term
    left = commutative_term_key(term[1])
    right = commutative_term_key(term[2])
    if repr(right) < repr(left):
        left, right = right, left
    return "op", left, right


def combine_binary_congr(
    left_src: Term,
    right_src: Term,
    left_dst: Term,
    left_proof: str,
    right_proof: str,
) -> str:
    proof_expr: str | None = None
    if left_proof != "rfl":
        proof_expr = f"congrArg (fun t => t ◇ {term_to_lean(right_src)}) ({left_proof})"
    if right_proof != "rfl":
        proof = f"congrArg (fun t => {term_to_lean(left_dst)} ◇ t) ({right_proof})"
        proof_expr = chain_trans(proof_expr, proof)
    return proof_expr or "rfl"


def commutative_term_proof(src: Term, dst: Term, *, hypothesis_name: str = "hcomm") -> str | None:
    if src == dst:
        return "rfl"
    if src[0] != "op" or dst[0] != "op":
        return None

    left_direct = commutative_term_proof(src[1], dst[1], hypothesis_name=hypothesis_name)
    if left_direct is not None:
        right_direct = commutative_term_proof(src[2], dst[2], hypothesis_name=hypothesis_name)
        if right_direct is not None:
            return combine_binary_congr(src[1], src[2], dst[1], left_direct, right_direct)

    left_swapped = commutative_term_proof(src[2], dst[1], hypothesis_name=hypothesis_name)
    if left_swapped is None:
        return None
    right_swapped = commutative_term_proof(src[1], dst[2], hypothesis_name=hypothesis_name)
    if right_swapped is None:
        return None
    swap_proof = f"{hypothesis_name} {term_to_lean(src[1])} {term_to_lean(src[2])}"
    rest = combine_binary_congr(src[2], src[1], dst[1], left_swapped, right_swapped)
    return chain_trans(swap_proof, rest)


def square_twist_comm_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = square_twist_comm_source(eq1)
    if source is None or commutative_term_key(eq2["lhs"]) != commutative_term_key(eq2["rhs"]):
        return None
    left_name, right_name, swapped = source
    call = call_expression_lean_args(eq1["variables"], {left_name: "a", right_name: "b"})
    if swapped:
        call = f"({call}).symm"
    proof_expr = commutative_term_proof(eq2["lhs"], eq2["rhs"])
    if proof_expr is None:
        return None
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hc : ∀ a b : G, a ◇ b = (b ◇ b) ◇ a := by\n"
        "    intro a b\n"
        f"    exact {call}\n"
        "  have hsq : ∀ a : G, a ◇ a = (a ◇ a) ◇ (a ◇ a) := by\n"
        "    intro a\n"
        "    exact (hc a a).trans (hc (a ◇ a) a)\n"
        "  have hcomm : ∀ a b : G, a ◇ b = b ◇ a := by\n"
        "    intro a b\n"
        "    have h1 : a ◇ b = (b ◇ b) ◇ a := hc a b\n"
        "    have h2 : (b ◇ b) ◇ a = (a ◇ a) ◇ (b ◇ b) := hc (b ◇ b) a\n"
        "    have h3 : (a ◇ a) ◇ (b ◇ b) = (b ◇ b) ◇ (a ◇ a) := by\n"
        "      exact (hc (a ◇ a) (b ◇ b)).trans (congrArg (fun t => t ◇ (a ◇ a)) (hsq b).symm)\n"
        "    have h4 : (b ◇ b) ◇ (a ◇ a) = (a ◇ a) ◇ b := (hc (a ◇ a) b).symm\n"
        "    exact h1.trans (h2.trans (h3.trans (h4.trans (hc b a).symm)))\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:square_twist_comm", code


def direct_substitution_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, dict[str, Term]] | None:
    for swapped in (False, True):
        source_lhs = eq1["rhs"] if swapped else eq1["lhs"]
        source_rhs = eq1["lhs"] if swapped else eq1["rhs"]
        subst: dict[str, Term] = {}
        if match_term(source_lhs, eq2["lhs"], subst) and match_term(source_rhs, eq2["rhs"], subst):
            return ("symm" if swapped else "direct"), subst
    return None


def bridge_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, dict[str, Term], dict[str, Term]] | None:
    eq1_sides = (eq1["lhs"], eq1["rhs"])
    for left_source in (0, 1):
        left_subst: dict[str, Term] = {}
        if not match_term(eq1_sides[left_source], eq2["lhs"], left_subst):
            continue
        left_other = instantiate_term_if_bound(eq1_sides[1 - left_source], left_subst)
        if left_other is None:
            continue
        for right_source in (0, 1):
            right_subst: dict[str, Term] = {}
            if not match_term(eq1_sides[right_source], eq2["rhs"], right_subst):
                continue
            right_other = instantiate_term_if_bound(eq1_sides[1 - right_source], right_subst)
            if right_other is None:
                continue
            if left_other != right_other:
                continue
            return (f"true:bridge:{left_source}{right_source}", left_subst, right_subst)
    return None


def projection_law_route(eq1: dict[str, Any]) -> str | None:
    for variable_side, op_side in ((eq1["lhs"], eq1["rhs"]), (eq1["rhs"], eq1["lhs"])):
        if variable_side[0] != "var" or op_side[0] != "op":
            continue
        projected = str(variable_side[1])
        left, right = op_side[1], op_side[2]
        if right == ("var", projected) and left[0] == "var" and left[1] != projected:
            return "right"
        if left == ("var", projected) and right[0] == "var" and right[1] != projected:
            return "left"
    return None


def goal_term_pool(eq2: dict[str, Any]) -> list[Term]:
    pool: list[Term] = []
    seen: set[Term] = set()
    lhs_subterms = term_subterms_tuple(eq2["lhs"])
    rhs_subterms = term_subterms_tuple(eq2["rhs"])
    for term in (eq2["lhs"], eq2["rhs"], *lhs_subterms[1:], *rhs_subterms[1:]):
        if term not in seen:
            seen.add(term)
            pool.append(term)
    for var in eq2["variables"]:
        term = ("var", var)
        if term not in seen:
            seen.add(term)
            pool.append(term)
    return pool or [("var", "x")]


def completed_bridge_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_trials: int = 2500,
) -> tuple[str, dict[str, Term], dict[str, Term]] | None:
    eq1_sides = (eq1["lhs"], eq1["rhs"])
    pool = goal_term_pool(eq2)
    for left_source in (0, 1):
        left_subst_base: dict[str, Term] = {}
        if not match_term(eq1_sides[left_source], eq2["lhs"], left_subst_base):
            continue
        for right_source in (0, 1):
            right_subst_base: dict[str, Term] = {}
            if not match_term(eq1_sides[right_source], eq2["rhs"], right_subst_base):
                continue
            missing: list[tuple[str, str]] = []
            for var in eq1["variables"]:
                if var not in left_subst_base:
                    missing.append(("L", var))
                if var not in right_subst_base:
                    missing.append(("R", var))
            if not missing:
                continue
            trials = 0
            for fills in product(pool, repeat=len(missing)):
                trials += 1
                if trials > max_trials:
                    break
                left_subst = dict(left_subst_base)
                right_subst = dict(right_subst_base)
                for (side, var), value in zip(missing, fills):
                    if side == "L":
                        left_subst[var] = value
                    else:
                        right_subst[var] = value
                left_other = instantiate_term(eq1_sides[1 - left_source], left_subst)
                right_other = instantiate_term(eq1_sides[1 - right_source], right_subst)
                if left_other == right_other:
                    return (f"true:constancy:{left_source}{right_source}", left_subst, right_subst)
    return None


def simple_true_proof_expr(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    hypothesis_name: str = "h",
) -> tuple[str, str] | None:
    direct = direct_substitution_route(eq1, eq2)
    if direct is not None:
        mode, subst = direct
        call_expr = call_expression(eq1["variables"], subst, hypothesis_name)
        if mode == "symm":
            call_expr = f"({call_expr}).symm"
        return "true:rewrite" if mode == "direct" else "true:rewrite:symm", call_expr

    bridge = bridge_route(eq1, eq2)
    if bridge is None:
        bridge = completed_bridge_route(eq1, eq2)
    if bridge is not None:
        bridge_name, left_subst, right_subst = bridge
        left_call = call_expression(eq1["variables"], left_subst, hypothesis_name)
        right_call = call_expression(eq1["variables"], right_subst, hypothesis_name)
        left_source = int(bridge_name[-2])
        right_source = int(bridge_name[-1])
        left_to_mid = left_call if left_source == 0 else f"({left_call}).symm"
        mid_to_right = f"({right_call}).symm" if right_source == 0 else right_call
        return bridge_name, f"({left_to_mid}).trans ({mid_to_right})"

    return None


def call_expression(eq1_vars: list[str], subst: dict[str, Term], name: str = "h") -> str:
    args = [term_to_lean(subst[var]) for var in eq1_vars]
    return name if not args else name + " " + " ".join(args)


def call_expression_lean_args(eq1_vars: list[str], subst: dict[str, str], name: str = "h") -> str:
    args = [subst[var] for var in eq1_vars]
    return name if not args else name + " " + " ".join(args)


def self_square_absorption_source(eq1: dict[str, Any]) -> tuple[str, str] | None:
    lhs = eq1["lhs"]
    rhs = eq1["rhs"]
    if lhs[0] != "var" or rhs[0] != "op" or rhs[1] != rhs[2]:
        return None
    root = str(lhs[1])
    square_root = rhs[1]
    if square_root[0] != "op" or square_root[2] != ("var", root) or square_root[1][0] != "var":
        return None
    square_var = str(square_root[1][1])
    if square_var == root or set(eq1["variables"]) != {root, square_var}:
        return None
    return root, square_var


def self_square_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = self_square_absorption_source(eq1)
    if source is None:
        return None
    root, square_var = source
    if eq2["lhs"] != ("var", root):
        return None
    rhs = eq2["rhs"]
    if rhs[0] != "op" or rhs[2][0] != "op" or rhs[2][2] != ("var", root):
        return None

    target_left = rhs[1]
    target_tail = rhs[2]
    tail_left = target_tail[1]
    root_term = ("var", root)
    first_call = call_expression_lean_args(
        eq1["variables"],
        {root: term_to_lean(root_term), square_var: term_to_lean(tail_left)},
    )
    second_call = call_expression_lean_args(eq1["variables"], {root: "B", square_var: "A"})
    third_call = call_expression_lean_args(eq1["variables"], {root: "C", square_var: "C"})
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  let A : G := {term_to_lean(target_left)}\n"
        f"  let B : G := {term_to_lean(target_tail)}\n"
        "  let C : G := A ◇ B\n"
        "  calc\n"
        f"    {root} = B ◇ B := {first_call}\n"
        f"    _ = (C ◇ C) ◇ (C ◇ C) := congrArg (fun t => t ◇ t) ({second_call})\n"
        f"    _ = C := ({third_call}).symm\n"
    )
    return "true:self_square_absorption", code


def repeat_tail_absorption_source(eq1: dict[str, Any]) -> tuple[str, str, str] | None:
    lhs = eq1["lhs"]
    rhs = eq1["rhs"]
    if lhs[0] != "var" or rhs[0] != "op":
        return None
    root_name = str(lhs[1])
    lead_term = rhs[1]
    tail = rhs[2]
    if lead_term[0] != "var" or tail[0] != "op":
        return None
    repeat_term = tail[1]
    repeated_tail = tail[2]
    if repeat_term[0] != "var" or repeated_tail[0] != "op":
        return None
    if repeated_tail[1] != repeat_term or repeated_tail[2] != ("var", root_name):
        return None
    lead_name = str(lead_term[1])
    repeat_name = str(repeat_term[1])
    if len({root_name, lead_name, repeat_name}) != 3:
        return None
    if set(eq1["variables"]) != {root_name, lead_name, repeat_name}:
        return None
    return root_name, lead_name, repeat_name


def repeat_tail_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = repeat_tail_absorption_source(eq1)
    if source is None:
        return None
    root_name, lead_name, repeat_name = source
    root_term = ("var", root_name)
    if eq2["lhs"] != root_term:
        return None
    rhs = eq2["rhs"]
    if rhs[0] != "op" or rhs[1] != ("op", root_term, root_term) or rhs[2][0] != "op" or rhs[2][1] != root_term:
        return None
    target_tail = rhs[2][2]
    if target_tail[0] != "op" or target_tail[2] != root_term:
        return None

    pivot_term = target_tail[1]
    pivot_lean = term_to_lean(pivot_term)
    root_lean = term_to_lean(root_term)
    root_square_lean = term_to_lean(("op", root_term, root_term))
    first_mid = ("op", pivot_term, ("op", pivot_term, ("op", pivot_term, root_term)))
    first_call = call_expression_lean_args(
        eq1["variables"],
        {root_name: root_lean, lead_name: pivot_lean, repeat_name: pivot_lean},
    )
    second_call = call_expression_lean_args(
        eq1["variables"],
        {root_name: term_to_lean(first_mid), lead_name: root_square_lean, repeat_name: root_lean},
    )
    third_call = call_expression_lean_args(
        eq1["variables"],
        {root_name: term_to_lean(target_tail), lead_name: root_lean, repeat_name: pivot_lean},
    )
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    context = f"(({root_lean} ◇ {root_lean}) ◇ ({root_lean} ◇ t))"
    proof_expr = f"(({first_call}).trans ({second_call})).trans (congrArg (fun t => {context}) ({third_call})).symm"
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:repeat_tail_absorption", code


def c9_e1072_shape_root(eq1: dict[str, Any]) -> str | None:
    lhs = eq1["lhs"]
    rhs = eq1["rhs"]
    if lhs[0] != "var" or rhs[0] != "op" or rhs[1][0] != "var":
        return None
    root = str(lhs[1])
    root_term = ("var", root)
    tail = ("op", ("op", root_term, ("op", root_term, root_term)), root_term)
    if rhs[2] != tail:
        return None
    return root


def c9_e1072_to_e19_lemma(eq1: dict[str, Any], root: str) -> str | None:
    lead = eq1["rhs"][1]
    if lead[0] != "var":
        return None
    lead_name = str(lead[1])
    if lead_name == root:
        return None
    a = ("var", "a")
    b = ("var", "b")
    c = ("var", "c")
    v0 = ("var", "v0")
    v0_tail = ("op", v0, ("op", v0, v0))
    first = call_expression(eq1["variables"], {root: a, lead_name: b})
    second = call_expression(eq1["variables"], {root: v0, lead_name: c})
    third = call_expression(eq1["variables"], {root: a, lead_name: v0_tail})
    return (
        "  have h19 : ∀ a b c : G, a = b ◇ (c ◇ a) := by\n"
        "    intro a b c\n"
        "    let v0 : G := ((a ◇ (a ◇ a)) ◇ a)\n"
        f"    exact ({first}).trans (congrArg (fun t => b ◇ t) "
        f"(({second}).trans (congrArg (fun t => c ◇ t) (({third}).symm))))\n"
    )


def c9_e1072_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    root = c9_e1072_shape_root(eq1)
    if root is None:
        return None
    lemma = c9_e1072_to_e19_lemma(eq1, root)
    if lemma is None:
        return None
    e19 = parse_equation("x = y ◇ (z ◇ x)")
    composed = simple_true_proof_expr(e19, eq2, hypothesis_name="h19")
    if composed is None:
        return None
    route, proof_expr = composed
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{lemma}"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return f"true:c9_e1072_collapse:{route}", code


def rewrite_steps_from_term(
    eq1: dict[str, Any],
    term: Term,
    *,
    hypothesis_name: str = "h",
    lemmas: tuple[dict[str, Any], ...] = (),
) -> list[tuple[Term, str, str]]:
    steps: list[tuple[Term, str, str]] = []
    rules = ((eq1, hypothesis_name), *((lemma, lemma["name"]) for lemma in lemmas))
    for path in subterm_paths(term):
        subterm = term_at_path(term, path)
        for rule, rule_name in rules:
            sides = (rule["lhs"], rule["rhs"])
            for source_idx in (0, 1):
                subst: dict[str, Term] = {}
                if not match_term(sides[source_idx], subterm, subst):
                    continue
                replacement = instantiate_term_if_bound(sides[1 - source_idx], subst)
                if replacement is None:
                    continue
                new_term = replace_subterm(term, path, replacement)
                if new_term == term:
                    continue
                call = call_expression(rule["variables"], subst, rule_name)
                proof = call if source_idx == 0 else f"({call}).symm"
                if path:
                    context = context_to_lean(term, path, "t")
                    proof = f"congrArg (fun t => {context}) ({proof})"
                steps.append((new_term, proof, f"rewrite:{source_idx}:{len(path)}"))
    return steps


def proof_between_terms(
    eq1: dict[str, Any],
    src: Term,
    dst: Term,
    *,
    hypothesis_name: str = "h",
    lemmas: tuple[dict[str, Any], ...] = (),
) -> tuple[str, str] | None:
    rules = ((eq1, hypothesis_name), *((lemma, lemma["name"]) for lemma in lemmas))
    for rule, rule_name in rules:
        sides = (rule["lhs"], rule["rhs"])
        for source_idx in (0, 1):
            subst: dict[str, Term] = {}
            if match_term(sides[source_idx], src, subst) and match_term(sides[1 - source_idx], dst, subst):
                call = call_expression(rule["variables"], subst, rule_name)
                proof = call if source_idx == 0 else f"({call}).symm"
                return proof, f"rewrite_whole:{source_idx}"
    for new_term, proof, route in rewrite_steps_from_term(eq1, src, hypothesis_name=hypothesis_name, lemmas=lemmas):
        if new_term == dst:
            return proof, route
    return None


def projection_term_proof(
    eq1: dict[str, Any],
    term: Term,
    side: str,
    *,
    hypothesis_name: str = "h",
) -> tuple[str, str] | None:
    if term[0] == "var":
        return "rfl", str(term[1])
    projected = term[2] if side == "right" else term[1]
    immediate = proof_between_terms(eq1, term, projected, hypothesis_name=hypothesis_name)
    if immediate is None:
        return None
    proof_expr = immediate[0]
    rest = projection_term_proof(eq1, projected, side, hypothesis_name=hypothesis_name)
    if rest is None:
        return None
    rest_proof, target_var = rest
    if rest_proof != "rfl":
        proof_expr = f"({proof_expr}).trans ({rest_proof})"
    return proof_expr, target_var


def projection_true_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    side = projection_law_route(eq1)
    if side is None:
        return None
    left = projection_term_proof(eq1, eq2["lhs"], side)
    right = projection_term_proof(eq1, eq2["rhs"], side)
    if left is None or right is None:
        return None
    left_proof, left_target = left
    right_proof, right_target = right
    if left_target != right_target:
        return None
    if left_proof == "rfl":
        proof_expr = f"({right_proof}).symm" if right_proof != "rfl" else "rfl"
    elif right_proof == "rfl":
        proof_expr = left_proof
    else:
        proof_expr = f"({left_proof}).trans ({right_proof}).symm"
    return f"true:projection:{side}", projection_true_certificate(eq2["variables"], proof_expr)


def find_rewrite_chain(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_depth: int = REWRITE_CHAIN_MAX_DEPTH,
    lemmas: tuple[dict[str, Any], ...] = (),
) -> tuple[list[str], str] | None:
    target = eq2["rhs"]
    queue: list[tuple[Term, list[str], list[str]]] = [(eq2["lhs"], [], [])]
    seen: set[Term] = {eq2["lhs"]}
    for _depth in range(max_depth):
        next_queue: list[tuple[Term, list[str], list[str]]] = []
        for term, proofs, routes in queue:
            for new_term, proof, route in rewrite_steps_from_term(eq1, term, lemmas=lemmas):
                if new_term in seen:
                    continue
                new_proofs = proofs + [proof]
                new_routes = routes + [route]
                if new_term == target:
                    expr = new_proofs[0]
                    for later in new_proofs[1:]:
                        expr = f"({expr}).trans ({later})"
                    return new_routes, expr
                seen.add(new_term)
                next_queue.append((new_term, new_proofs, new_routes))
        queue = next_queue
    return None


def proof_between_terms_guided(
    eq1: dict[str, Any],
    variables: list[str],
    src: Term,
    dst: Term,
    *,
    max_depth: int = GUIDED_CHAIN_MAX_DEPTH,
    closure_time_budget: float | None = GUIDED_CHAIN_CLOSURE_TIME_BUDGET,
    lemmas: tuple[dict[str, Any], ...] = (),
) -> tuple[str, str] | None:
    if src == dst:
        return "rfl", "guided:rfl"

    direct = proof_between_terms(eq1, src, dst, lemmas=lemmas)
    if direct is not None:
        proof, route = direct
        return proof, route

    edge_eq = {"lhs": src, "rhs": dst, "variables": variables}
    chain = find_rewrite_chain(eq1, edge_eq, max_depth=max_depth, lemmas=lemmas)
    if chain is not None:
        routes, proof_expr = chain
        return proof_expr, "guided:rewrite_chain:" + ",".join(routes)

    closure = _closure_proof_expr_impl(
        eq1,
        edge_eq,
        route_name="guided:equational_closure",
        chain_max_depth=2,
        pool_limit=12,
        frontier_limit=180,
        max_fills=80,
        term_slack=6,
        depth_slack=2,
        time_budget=closure_time_budget,
        lemmas=lemmas,
    )
    if closure is not None:
        route, proof_expr = closure
        return proof_expr, route
    return None


def absorption_hypothesis(eq1: dict[str, Any]) -> bool:
    lhs = eq1["lhs"]
    rhs = eq1["rhs"]
    if lhs[0] == "var" and lhs[1] in term_vars(rhs):
        return True
    if rhs[0] == "var" and rhs[1] in term_vars(lhs):
        return True
    return False


def absorption_term_pool(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    pool_limit: int = ABSORPTION_POOL_LIMIT,
) -> list[Term]:
    allowed_vars = set(eq2["variables"])
    seen: set[Term] = set()
    pool: list[Term] = []

    def add(term: Term) -> None:
        if term in seen or not term_vars(term).issubset(allowed_vars):
            return
        seen.add(term)
        pool.append(term)

    for var in eq2["variables"]:
        add(("var", var))
    eq2_lhs_subterms = term_subterms_tuple(eq2["lhs"])
    eq2_rhs_subterms = term_subterms_tuple(eq2["rhs"])
    for term in (eq2["lhs"], eq2["rhs"], *eq2_lhs_subterms[1:], *eq2_rhs_subterms[1:]):
        add(term)
    eq1_lhs_subterms = term_subterms_tuple(eq1["lhs"])
    eq1_rhs_subterms = term_subterms_tuple(eq1["rhs"])
    for term in (eq1["lhs"], eq1["rhs"], *eq1_lhs_subterms[1:], *eq1_rhs_subterms[1:]):
        add(term)

    small = list(pool)
    for left in small:
        for right in small:
            candidate = ("op", left, right)
            if term_size(candidate) <= 7 and term_depth(candidate) <= 3:
                add(candidate)

    pool.sort(key=lambda term: (term_size(term), term_depth(term), term_to_lean(term)))
    return pool[:pool_limit]


def absorption_context_bridge_pool(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    pool_limit: int = ABSORPTION_CONTEXT_BRIDGE_POOL_LIMIT,
    seed_limit: int = ABSORPTION_CONTEXT_BRIDGE_SEED_LIMIT,
) -> list[Term]:
    pool = absorption_term_pool(eq1, eq2, pool_limit=pool_limit)
    if not pool:
        return []
    allowed_vars = set(eq2["variables"])
    seen: set[Term] = set(pool)
    frontier = list(pool[:seed_limit])
    for left in frontier:
        for right in frontier:
            candidate = ("op", left, right)
            if candidate in seen or not term_vars(candidate).issubset(allowed_vars):
                continue
            if term_size(candidate) <= 7 and term_depth(candidate) <= 3:
                seen.add(candidate)
    extended = sorted(seen, key=lambda term: (term_size(term), term_depth(term), term_to_lean(term)))
    return extended[:pool_limit]


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def filled_absorption_steps(
    eq1: dict[str, Any],
    term: Term,
    pool: list[Term],
    *,
    max_size: int,
    max_depth: int,
    max_fills: int = ABSORPTION_MAX_FILLS,
    deadline: float | None = None,
    lemmas: tuple[dict[str, Any], ...] = (),
) -> list[tuple[Term, str, str]]:
    if not pool:
        return []

    steps: list[tuple[Term, str, str]] = []
    seen_terms: set[Term] = set()
    rules = ((eq1, "h"), *((lemma, lemma["name"]) for lemma in lemmas))
    default_term = pool[0]

    for path in subterm_paths(term):
        if deadline_expired(deadline):
            return steps
        subterm = term_at_path(term, path)
        for rule, rule_name in rules:
            sides = (rule["lhs"], rule["rhs"])
            for source_idx in (0, 1):
                if deadline_expired(deadline):
                    return steps
                subst: dict[str, Term] = {}
                if not match_term(sides[source_idx], subterm, subst):
                    continue

                replacement_pattern = sides[1 - source_idx]
                replacement_vars = term_vars(replacement_pattern)
                needed = [var for var in rule["variables"] if var not in subst and var in replacement_vars]
                if len(needed) > 3:
                    continue

                fill_count = 0
                fill_iter = product(pool, repeat=len(needed)) if needed else ((),)
                for fills in fill_iter:
                    if deadline_expired(deadline):
                        return steps
                    fill_count += 1
                    if fill_count > max_fills:
                        break

                    subst_full = dict(subst)
                    for var, value in zip(needed, fills):
                        subst_full[var] = value
                    for var in rule["variables"]:
                        if var not in subst_full:
                            subst_full[var] = default_term

                    replacement = instantiate_term(replacement_pattern, subst_full)
                    new_term = replace_subterm(term, path, replacement)
                    if new_term == term or new_term in seen_terms:
                        continue
                    if term_size(new_term) > max_size or term_depth(new_term) > max_depth:
                        continue

                    call = call_expression(rule["variables"], subst_full, rule_name)
                    proof = call if source_idx == 0 else f"({call}).symm"
                    if path:
                        context = context_to_lean(term, path, "t")
                        proof = f"congrArg (fun t => {context}) ({proof})"
                    seen_terms.add(new_term)
                    steps.append((new_term, proof, f"absorb:{source_idx}:{len(path)}:{len(needed)}"))

    steps.sort(key=lambda item: (term_size(item[0]), term_depth(item[0]), item[2], term_to_lean(item[0])))
    return steps


def chain_trans(prefix: str | None, proof: str) -> str:
    if prefix is None:
        return proof
    return f"({prefix}).trans ({proof})"


def combine_meeting_proofs(left_proof: str | None, right_proof: str | None) -> str:
    if left_proof is None and right_proof is None:
        return "rfl"
    if left_proof is None:
        return f"({right_proof}).symm"
    if right_proof is None:
        return left_proof
    return f"({left_proof}).trans ({right_proof}).symm"


# --- Critical-pair lemma engine (order-5 guided chains) ---------------------
#
# Derives new equations as critical pairs between known-true rules
# (Knuth-Bendix / superposition style overlaps), each carrying a complete
# Lean proof expression from birth: the peak term rewrites to one side via
# parent A and to the other via parent B, so the lemma's proof is always a
# two-step trans through the peak. Consumed by the guided-chain LLM route,
# demand-driven: lemmas are derived only when a specific hop fails, targeted
# at that hop. Gated by `guided_lemma_budget` — zero for the order <= 4 band,
# so the deterministic routes and their output are unchanged there.


def _resolve_walk(term: Term, subst: dict[str, Term]) -> Term:
    while term[0] == "var" and term[1] in subst:
        term = subst[term[1]]
    return term


def _occurs_in(name: str, term: Term, subst: dict[str, Term]) -> bool:
    term = _resolve_walk(term, subst)
    if term[0] == "var":
        return term[1] == name
    return _occurs_in(name, term[1], subst) or _occurs_in(name, term[2], subst)


def unify_terms(a: Term, b: Term, subst: dict[str, Term]) -> bool:
    a = _resolve_walk(a, subst)
    b = _resolve_walk(b, subst)
    if a == b:
        return True
    if a[0] == "var":
        if _occurs_in(str(a[1]), b, subst):
            return False
        subst[str(a[1])] = b
        return True
    if b[0] == "var":
        return unify_terms(b, a, subst)
    return unify_terms(a[1], b[1], subst) and unify_terms(a[2], b[2], subst)


def resolve_term(term: Term, subst: dict[str, Term]) -> Term:
    term = _resolve_walk(term, subst)
    if term[0] == "var":
        return term
    return ("op", resolve_term(term[1], subst), resolve_term(term[2], subst))


def _rename_term(term: Term, mapping: dict[str, str]) -> Term:
    if term[0] == "var":
        return ("var", mapping[str(term[1])])
    return ("op", _rename_term(term[1], mapping), _rename_term(term[2], mapping))


def _fill_vars(term: Term, mapping: dict[str, Term]) -> Term:
    if term[0] == "var":
        return mapping.get(str(term[1]), term)
    return ("op", _fill_vars(term[1], mapping), _fill_vars(term[2], mapping))


def _rule_renamed_apart(rule: dict[str, Any], prefix: str) -> tuple[dict[str, Any], dict[str, str]]:
    mapping = {var: f"{prefix}{idx}" for idx, var in enumerate(rule["variables"])}
    renamed = {
        "variables": [mapping[var] for var in rule["variables"]],
        "lhs": _rename_term(rule["lhs"], mapping),
        "rhs": _rename_term(rule["rhs"], mapping),
    }
    return renamed, mapping


def _first_occurrence_vars(*terms: Term) -> list[str]:
    ordered: list[str] = []
    seen: set[str] = set()

    def visit(term: Term) -> None:
        if term[0] == "var":
            name = str(term[1])
            if name not in seen:
                seen.add(name)
                ordered.append(name)
            return
        visit(term[1])
        visit(term[2])

    for term in terms:
        visit(term)
    return ordered


def lemma_statement_key(lhs: Term, rhs: Term) -> tuple[str, str]:
    left, right = term_to_lean(lhs), term_to_lean(rhs)
    return (left, right) if left <= right else (right, left)


def _statement_matches_rule(lhs: Term, rhs: Term, rule: dict[str, Any]) -> bool:
    for rule_lhs, rule_rhs in ((rule["lhs"], rule["rhs"]), (rule["rhs"], rule["lhs"])):
        subst: dict[str, Term] = {}
        if match_term(rule_lhs, lhs, subst) and match_term(rule_rhs, rhs, subst):
            if all(value[0] == "var" for value in subst.values()):
                return True
    return False


def _critical_pair_candidates(
    rule_a: dict[str, Any],
    name_a: str,
    rule_b: dict[str, Any],
    name_b: str,
    *,
    max_term_size: int,
    deadline: float,
    allow_var_overlap: bool = False,
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    renamed_a, map_a = _rule_renamed_apart(rule_a, "A")
    renamed_b, map_b = _rule_renamed_apart(rule_b, "B")
    orientations_a = ((renamed_a["lhs"], renamed_a["rhs"], 0), (renamed_a["rhs"], renamed_a["lhs"], 1))
    orientations_b = ((renamed_b["lhs"], renamed_b["rhs"], 0), (renamed_b["rhs"], renamed_b["lhs"], 1))
    for peak_side, other_a, ori_a in orientations_a:
        for path in subterm_paths(peak_side):
            overlap = term_at_path(peak_side, path)
            if overlap[0] != "op" and not allow_var_overlap:
                continue
            for inner_side, other_b, ori_b in orientations_b:
                if deadline_expired(deadline):
                    return out
                subst: dict[str, Term] = {}
                if not unify_terms(overlap, inner_side, subst):
                    continue
                peak = resolve_term(peak_side, subst)
                q1 = resolve_term(other_a, subst)
                q2 = replace_subterm(peak, path, resolve_term(other_b, subst))
                if q1 == q2:
                    continue
                if max(term_size(q1), term_size(q2), term_size(peak)) > max_term_size:
                    continue
                # Binders must be exactly the statement's variables: a variable
                # occurring only in the peak (hence only in the proof) is
                # universally quantified in its parent, so instantiate it with
                # the first statement variable instead of quantifying over it —
                # otherwise a whole-term match binds only statement variables
                # and call_expression has no image for the extra binder.
                free_vars = _first_occurrence_vars(q1, q2)
                if not free_vars or len(free_vars) > len(CP_CANONICAL_VARS):
                    continue
                filler: Term = ("var", free_vars[0])
                fill_map = {
                    var: filler
                    for var in _first_occurrence_vars(peak)
                    if var not in set(free_vars)
                }
                canon = dict(zip(free_vars, CP_CANONICAL_VARS))

                def canonize(term: Term) -> Term:
                    return _rename_term(_fill_vars(term, fill_map), canon)

                args_a = {
                    var: canonize(resolve_term(("var", map_a[var]), subst))
                    for var in rule_a["variables"]
                }
                args_b = {
                    var: canonize(resolve_term(("var", map_b[var]), subst))
                    for var in rule_b["variables"]
                }
                peak_c = canonize(peak)
                call_a = call_expression(rule_a["variables"], args_a, name_a)
                # proof_rev : q1 = peak (parent A read against its orientation)
                proof_rev = f"({call_a}).symm" if ori_a == 0 else call_a
                call_b = call_expression(rule_b["variables"], args_b, name_b)
                inner = call_b if ori_b == 0 else f"({call_b}).symm"
                if path:
                    context = context_to_lean(peak_c, path, "t")
                    inner = f"congrArg (fun t => {context}) ({inner})"
                out.append(
                    {
                        "variables": [canon[var] for var in free_vars],
                        "lhs": _rename_term(q1, canon),
                        "rhs": _rename_term(q2, canon),
                        "proof": f"({proof_rev}).trans ({inner})",
                        "cites": (name_a, name_b),
                    }
                )
    return out


def _gap_relevance(lemma: dict[str, Any], gap_subterms: tuple[Term, ...]) -> int:
    score = 0
    for side in (lemma["lhs"], lemma["rhs"]):
        for target in gap_subterms:
            subst: dict[str, Term] = {}
            if match_term(side, target, subst):
                score += 2
                break
    return score


def derive_gap_lemmas(
    eq1: dict[str, Any],
    pool: list[dict[str, Any]],
    src: Term,
    dst: Term,
    *,
    max_new: int,
    deadline: float,
    raw_pair_cap: int = CP_RAW_PAIR_CAP,
    term_slack: int = CP_LEMMA_TERM_SLACK,
    term_cap: int | None = None,
    allow_var_overlap: bool = False,
) -> list[dict[str, Any]]:
    if max_new <= 0:
        return []
    rules: list[tuple[dict[str, Any], str]] = [(eq1, "h")]
    rules.extend((lemma, lemma["name"]) for lemma in pool)
    seen_keys = {lemma_statement_key(eq1["lhs"], eq1["rhs"])}
    seen_keys.update(lemma_statement_key(lemma["lhs"], lemma["rhs"]) for lemma in pool)
    max_term_size = term_cap if term_cap is not None else (
        max(term_size(eq1["lhs"]), term_size(eq1["rhs"]), term_size(src), term_size(dst))
        + term_slack
    )

    candidates: list[dict[str, Any]] = []
    raw_count = 0
    for rule_a, name_a in rules:
        for rule_b, name_b in rules:
            if deadline_expired(deadline) or raw_count >= raw_pair_cap:
                break
            for candidate in _critical_pair_candidates(
                rule_a, name_a, rule_b, name_b, max_term_size=max_term_size,
                deadline=deadline, allow_var_overlap=allow_var_overlap,
            ):
                raw_count += 1
                key = lemma_statement_key(candidate["lhs"], candidate["rhs"])
                if key in seen_keys:
                    continue
                if any(
                    _statement_matches_rule(candidate["lhs"], candidate["rhs"], rule)
                    for rule, _name in rules
                ):
                    continue
                seen_keys.add(key)
                candidates.append(candidate)
        if deadline_expired(deadline) or raw_count >= raw_pair_cap:
            break

    gap_subterms = tuple({*term_subterms_tuple(src), *term_subterms_tuple(dst)})
    candidates.sort(
        key=lambda lemma: (
            -_gap_relevance(lemma, gap_subterms),
            term_size(lemma["lhs"]) + term_size(lemma["rhs"]),
            term_to_lean(lemma["lhs"]),
            term_to_lean(lemma["rhs"]),
        )
    )
    chosen = candidates[:max_new]
    for offset, lemma in enumerate(chosen):
        lemma["name"] = f"lem{len(pool) + offset + 1}"
    return chosen


def guided_lemma_budget(problem: dict[str, Any]) -> int:
    order5 = False
    for key in ("eq1_id", "eq2_id"):
        value = problem.get(key)
        if not isinstance(value, int) or not 1 <= value <= KNOWN_ORDER4_MAX_EQ_ID:
            order5 = True
    if not order5:
        try:
            for text_key in ("equation1", "equation2"):
                equation = parse_equation(str(problem[text_key]))
                op_count = (term_size(equation["lhs"]) - 1) // 2 + (term_size(equation["rhs"]) - 1) // 2
                if op_count >= 5:
                    order5 = True
                    break
        except (KeyError, ValueError):
            pass
    # Gate opened 2026-08-19: the order-<=4 restriction was retired after a
    # paired measurement showed +114/-0 on evaluation_normal+hard (and +50
    # more elsewhere) with the engine enabled everywhere. The original
    # byte-identity bar was superseded by the measured-gain bar; `order5`
    # detection is retained for telemetry only.
    _ = order5
    return CP_LEMMA_BUDGET_ORDER5


_CP_LEMMA_POOLS: dict[str, list[dict[str, Any]]] = {}
_CP_HOP_CACHE: dict[tuple[str, str, str], str] = {}


def _cited_lemmas(pool: list[dict[str, Any]], proofs: list[str]) -> list[dict[str, Any]]:
    by_name = {lemma["name"]: lemma for lemma in pool}
    cited: set[str] = set()
    frontier: list[str] = []
    for proof in proofs:
        frontier.extend(re.findall(r"\blem\d+\b", proof))
    while frontier:
        name = frontier.pop()
        if name in cited or name not in by_name:
            continue
        cited.add(name)
        frontier.extend(parent for parent in by_name[name]["cites"] if parent != "h")
    return [lemma for lemma in pool if lemma["name"] in cited]


def frontier_closest_pairs(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    lemmas: tuple[dict[str, Any], ...] = (),
    top: int = 3,
) -> list[tuple[Term, Term]]:
    """Expand one rewrite step from each goal side under the current rule set
    and rank cross-frontier pairs by shared-subterm structure (deliberately not
    string similarity). Empty list when the frontiers already meet."""
    left = [eq2["lhs"]] + [t for t, _p, _r in rewrite_steps_from_term(eq1, eq2["lhs"], lemmas=lemmas)][:12]
    right = [eq2["rhs"]] + [t for t, _p, _r in rewrite_steps_from_term(eq1, eq2["rhs"], lemmas=lemmas)][:12]
    if set(left) & set(right):
        return []
    scored: list[tuple[float, Term, Term]] = []
    for a in left:
        subs_a = set(term_subterms_tuple(a))
        for b in right:
            shared = subs_a.intersection(term_subterms_tuple(b))
            score = sum(term_size(s) for s in shared) / (1 + abs(term_size(a) - term_size(b)))
            scored.append((score, a, b))
    scored.sort(key=lambda item: (-item[0], term_to_lean(item[1]), term_to_lean(item[2])))
    return [(a, b) for _s, a, b in scored[:top]]


def frontier_bridge_hint(eq1: dict[str, Any], eq2: dict[str, Any], *, top: int = 3) -> str:
    """SearchState-lite for the LLM round-0 analysis."""
    pairs = frontier_closest_pairs(eq1, eq2, top=top)
    if not pairs:
        return ""  # already connected; deterministic routes handle it
    lines = ["Search frontier (one rewrite from each goal side; closest structural gaps):"]
    for a, b in pairs:
        lines.append(f"  bridge needed: {term_to_lean(a)} = {term_to_lean(b)}")
    lines.append(
        "A guided_chain that passes through either side of one of these gaps "
        "only needs the gap itself justified; hops are verified mechanically "
        "and failed hops trigger lemma derivation."
    )
    return "\n".join(lines)


def _cp_saturation_attempt(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    lemma_budget: int,
    rounds: int,
    deadline: float,
    beam: bool,
) -> tuple[str, str] | None:
    """One saturation attempt with its own pool.

    beam=False reproduces the pre-beam algorithm exactly (endpoint-targeted,
    slack-based term cap) plus the strictly-additive var-overlap fallback on
    dry rounds. beam=True targets the closest cross-frontier gap after round 0
    and explores with a wide term cap. The two run as SEPARATE attempts:
    sharing one pool measurably lost previously-solved cases in both mixes."""
    slice_size = max(12, lemma_budget // rounds)
    wide_cap = (
        2 * max(term_size(eq1["lhs"]), term_size(eq1["rhs"]),
                term_size(eq2["lhs"]), term_size(eq2["rhs"]))
        + CP_SATURATION_TERM_SLACK
    )
    pool: list[dict[str, Any]] = []
    for _round in range(rounds + 1):
        step = proof_between_terms_guided(
            eq1, eq2["variables"], eq2["lhs"], eq2["rhs"], lemmas=tuple(pool)
        )
        if step is not None:
            proof, _hop_route = step
            cited = _cited_lemmas(pool, [proof])
            if cited:
                code = guided_true_certificate_with_lemmas(eq2["variables"], cited, proof)
            else:
                code = substitution_true_certificate(eq2["variables"], proof)
            tag = "beam" if beam else "classic"
            return f"true:cp_saturation:{tag}:{len(cited)}", code
        if _round >= rounds or deadline_expired(deadline) or len(pool) >= lemma_budget:
            return None
        src, dst = eq2["lhs"], eq2["rhs"]
        cap_kwargs: dict[str, Any] = {}
        if beam:
            cap_kwargs["term_cap"] = wide_cap
            if _round > 0:
                pairs = frontier_closest_pairs(eq1, eq2, lemmas=tuple(pool), top=1)
                if pairs:
                    src, dst = pairs[0]
        new_lemmas: list[dict[str, Any]] = []
        for var_overlap in (False, True):
            new_lemmas = derive_gap_lemmas(
                eq1,
                pool,
                src,
                dst,
                max_new=min(slice_size, lemma_budget - len(pool)),
                deadline=min(deadline, time.monotonic() + CP_SATURATION_GAP_TIME),
                raw_pair_cap=CP_SATURATION_RAW_PAIR_CAP,
                term_slack=CP_SATURATION_TERM_SLACK,
                allow_var_overlap=var_overlap,
                **cap_kwargs,
            )
            if new_lemmas:
                break  # var-overlap only when the ordinary stream dries up
        if not new_lemmas:
            return None
        pool.extend(new_lemmas)
    return None


def cp_saturation_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    lemma_budget: int,
    rounds: int = CP_SATURATION_ROUNDS,
    time_budget: float = CP_SATURATION_TIME_BUDGET,
) -> tuple[str, str] | None:
    """Native (zero-LLM) targeted saturation. Two sequential attempts with
    independent pools: classic (pre-beam behavior, run first so every
    previously-solved case keeps its proof) then beam (frontier-guided, wide
    caps) only if classic fails. Gated by the lemma budget."""
    if lemma_budget <= 0:
        return None
    lemma_budget = max(lemma_budget, CP_SATURATION_LEMMA_BUDGET)
    for beam in (False, True):
        result = _cp_saturation_attempt(
            eq1,
            eq2,
            lemma_budget=lemma_budget,
            rounds=rounds,
            deadline=time.monotonic() + time_budget,
            beam=beam,
        )
        if result is not None:
            return result
    return None


def guided_true_certificate_with_lemmas(
    eq2_vars: list[str],
    lemmas: list[dict[str, Any]],
    chain_expr: str,
) -> str:
    lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]
    for lemma in lemmas:
        binders = " ".join(lemma["variables"])
        statement = f"{term_to_lean(lemma['lhs'])} = {term_to_lean(lemma['rhs'])}"
        lines.append(f"  have {lemma['name']} : ∀ {binders} : G, {statement} := by")
        lines.append(f"    intro {binders}")
        lines.append(f"    exact {lemma['proof']}")
    intro_vars = " ".join(eq2_vars)
    if intro_vars:
        lines.append(f"  intro {intro_vars}")
    lines.append(f"  exact {chain_expr}")
    return "\n".join(lines) + "\n"


def absorption_context_bridge_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    route_name: str = "true:absorption_context_bridge",
    pool_limit: int = ABSORPTION_CONTEXT_BRIDGE_POOL_LIMIT,
    seed_limit: int = ABSORPTION_CONTEXT_BRIDGE_SEED_LIMIT,
    max_fills: int = ABSORPTION_CONTEXT_BRIDGE_MAX_FILLS,
    term_slack: int = ABSORPTION_CONTEXT_BRIDGE_TERM_SLACK,
    depth_slack: int = ABSORPTION_CONTEXT_BRIDGE_DEPTH_SLACK,
    time_budget: float | None = None,
    max_goal_vars: int = 2,
) -> tuple[str, str] | None:
    if not absorption_hypothesis(eq1) or len(eq2["variables"]) > max_goal_vars:
        return None
    if time_budget is None:
        time_budget = ABSORPTION_CONTEXT_BRIDGE_TIME_BUDGET
    pool = absorption_context_bridge_pool(eq1, eq2, pool_limit=pool_limit, seed_limit=seed_limit)
    if not pool:
        return None
    deadline = time.monotonic() + time_budget if time_budget else None
    max_size = max(
        term_size(eq1["lhs"]),
        term_size(eq1["rhs"]),
        term_size(eq2["lhs"]),
        term_size(eq2["rhs"]),
    ) + term_slack
    max_depth = max(
        term_depth(eq1["lhs"]),
        term_depth(eq1["rhs"]),
        term_depth(eq2["lhs"]),
        term_depth(eq2["rhs"]),
    ) + depth_slack
    left_steps = filled_absorption_steps(
        eq1,
        eq2["lhs"],
        pool,
        max_size=max_size,
        max_depth=max_depth,
        max_fills=max_fills,
        deadline=deadline,
    )
    if deadline_expired(deadline):
        return None
    right_steps = filled_absorption_steps(
        eq1,
        eq2["rhs"],
        pool,
        max_size=max_size,
        max_depth=max_depth,
        max_fills=max_fills,
        deadline=deadline,
    )
    if deadline_expired(deadline):
        return None

    left_seen: dict[Term, str] = {}
    for term, proof, _route in left_steps:
        left_seen.setdefault(term, proof)
    right_seen: dict[Term, str] = {}
    for term, proof, _route in right_steps:
        right_seen.setdefault(term, proof)

    common = sorted(
        set(left_seen).intersection(right_seen),
        key=lambda term: (term_size(term), term_depth(term), term_to_lean(term)),
    )
    if not common:
        return None
    proof_expr = combine_meeting_proofs(left_seen[common[0]], right_seen[common[0]])
    return route_name, substitution_true_certificate(eq2["variables"], proof_expr)


def _closure_proof_expr_impl(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    route_name: str,
    chain_max_depth: int,
    pool_limit: int,
    frontier_limit: int,
    max_fills: int,
    term_slack: int,
    depth_slack: int,
    time_budget: float | None,
    lemmas: tuple[dict[str, Any], ...] = (),
) -> tuple[str, str] | None:
    deadline = time.monotonic() + time_budget if time_budget else None
    pool = absorption_term_pool(eq1, eq2, pool_limit=pool_limit)
    if not pool:
        return None

    max_size = max(
        term_size(eq1["lhs"]),
        term_size(eq1["rhs"]),
        term_size(eq2["lhs"]),
        term_size(eq2["rhs"]),
    ) + term_slack
    max_depth = max(
        term_depth(eq1["lhs"]),
        term_depth(eq1["rhs"]),
        term_depth(eq2["lhs"]),
        term_depth(eq2["rhs"]),
    ) + depth_slack

    left_start = eq2["lhs"]
    right_start = eq2["rhs"]
    left_seen: dict[Term, str | None] = {left_start: None}
    right_seen: dict[Term, str | None] = {right_start: None}
    left_frontier = [left_start]
    right_frontier = [right_start]

    def expand_frontier(
        frontier: list[Term],
        seen: dict[Term, str | None],
        other_seen: dict[Term, str | None],
        *,
        from_left: bool,
    ) -> tuple[list[Term], tuple[str, str] | None, bool]:
        next_frontier: list[Term] = []
        for term in frontier:
            if deadline_expired(deadline):
                return next_frontier, None, True
            prefix = seen[term]
            for new_term, proof, _route in filled_absorption_steps(
                eq1,
                term,
                pool,
                max_size=max_size,
                max_depth=max_depth,
                max_fills=max_fills,
                deadline=deadline,
                lemmas=lemmas,
            ):
                if deadline_expired(deadline):
                    return next_frontier, None, True
                if new_term in seen:
                    continue
                new_proof = chain_trans(prefix, proof)
                if new_term in other_seen:
                    if from_left:
                        proof_expr = combine_meeting_proofs(new_proof, other_seen[new_term])
                    else:
                        proof_expr = combine_meeting_proofs(other_seen[new_term], new_proof)
                    return next_frontier, (route_name, proof_expr), False
                seen[new_term] = new_proof
                next_frontier.append(new_term)
                if len(seen) >= frontier_limit:
                    break
            if len(seen) >= frontier_limit:
                break
        return next_frontier[:frontier_limit], None, False

    for _depth in range(chain_max_depth):
        if deadline_expired(deadline):
            return None
        left_frontier, result, timed_out = expand_frontier(left_frontier, left_seen, right_seen, from_left=True)
        if timed_out:
            return None
        if result is not None:
            return result

        right_frontier, result, timed_out = expand_frontier(right_frontier, right_seen, left_seen, from_left=False)
        if timed_out:
            return None
        if result is not None:
            return result

        if not left_frontier and not right_frontier:
            break

    return None


def _closure_route_impl(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    route_name: str,
    chain_max_depth: int,
    pool_limit: int,
    frontier_limit: int,
    max_fills: int,
    term_slack: int,
    depth_slack: int,
    time_budget: float | None,
) -> tuple[str, str] | None:
    result = _closure_proof_expr_impl(
        eq1,
        eq2,
        route_name=route_name,
        chain_max_depth=chain_max_depth,
        pool_limit=pool_limit,
        frontier_limit=frontier_limit,
        max_fills=max_fills,
        term_slack=term_slack,
        depth_slack=depth_slack,
        time_budget=time_budget,
    )
    if result is None:
        return None
    route, proof_expr = result
    return route, substitution_true_certificate(eq2["variables"], proof_expr)


def absorption_closure_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    route_name: str = "true:absorption_closure",
    chain_max_depth: int = ABSORPTION_CHAIN_MAX_DEPTH,
    pool_limit: int = ABSORPTION_POOL_LIMIT,
    frontier_limit: int = ABSORPTION_FRONTIER_LIMIT,
    max_fills: int = ABSORPTION_MAX_FILLS,
    term_slack: int = ABSORPTION_TERM_SLACK,
    time_budget: float | None = ABSORPTION_TIME_BUDGET,
) -> tuple[str, str] | None:
    if not absorption_hypothesis(eq1):
        return None
    return _closure_route_impl(
        eq1,
        eq2,
        route_name=route_name,
        chain_max_depth=chain_max_depth,
        pool_limit=pool_limit,
        frontier_limit=frontier_limit,
        max_fills=max_fills,
        term_slack=term_slack,
        depth_slack=2,
        time_budget=time_budget,
    )


def deep_absorption_closure_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    return absorption_closure_route(
        eq1,
        eq2,
        route_name="true:absorption_closure:deep",
        chain_max_depth=ABSORPTION_DEEP_CHAIN_MAX_DEPTH,
        pool_limit=ABSORPTION_DEEP_POOL_LIMIT,
        frontier_limit=ABSORPTION_DEEP_FRONTIER_LIMIT,
        max_fills=ABSORPTION_DEEP_MAX_FILLS,
        term_slack=ABSORPTION_DEEP_TERM_SLACK,
        time_budget=ABSORPTION_DEEP_TIME_BUDGET,
    )


def equational_closure_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    route_name: str = "true:equational_closure",
    chain_max_depth: int = EQUATIONAL_CLOSURE_CHAIN_MAX_DEPTH,
    pool_limit: int = EQUATIONAL_CLOSURE_POOL_LIMIT,
    frontier_limit: int = EQUATIONAL_CLOSURE_FRONTIER_LIMIT,
    max_fills: int = EQUATIONAL_CLOSURE_MAX_FILLS,
    term_slack: int = EQUATIONAL_CLOSURE_TERM_SLACK,
    depth_slack: int = EQUATIONAL_CLOSURE_DEPTH_SLACK,
    time_budget: float | None = EQUATIONAL_CLOSURE_TIME_BUDGET,
) -> tuple[str, str] | None:
    if eq2["lhs"] == eq2["rhs"]:
        return route_name, substitution_true_certificate(eq2["variables"], "rfl")
    return _closure_route_impl(
        eq1,
        eq2,
        route_name=route_name,
        chain_max_depth=chain_max_depth,
        pool_limit=pool_limit,
        frontier_limit=frontier_limit,
        max_fills=max_fills,
        term_slack=term_slack,
        depth_slack=depth_slack,
        time_budget=time_budget,
    )


def projection_cue(eq1: dict[str, Any], eq2: dict[str, Any]) -> bool:
    eq1_left, eq1_right = boundary_vars(eq1["lhs"])
    eq2_left, eq2_right = boundary_vars(eq2["rhs"])
    return eq1_left != eq2_left or eq1_right != eq2_right


def problem_priority(problem: dict[str, Any], eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[int, int, str]:
    if is_reflexive_problem(problem):
        return (0, len(eq2["text"]), "true:reflexive")
    if singleton_route(eq1):
        return (1, len(eq2["text"]), "true:singleton")
    if middle_self_collapse_source(eq1):
        return (1, len(eq2["text"]), "true:middle_self_collapse")
    if front_double_self_collapse_source(eq1):
        return (1, len(eq2["text"]), "true:front_double_self_collapse")
    if alternating_front_self_collapse_source(eq1):
        return (1, len(eq2["text"]), "true:alternating_front_self_collapse")
    if mirrored_alternating_front_self_collapse_source(eq1):
        return (1, len(eq2["text"]), "true:mirrored_alternating_front_self_collapse")
    if sandwich_left_projection_source(eq1) and projection_proof_expr_from_law(eq2, "left", hypothesis_name="hleft"):
        return (2, len(eq2["text"]), "true:sandwich_left_projection")
    if square_twist_comm_source(eq1) and commutative_term_key(eq2["lhs"]) == commutative_term_key(eq2["rhs"]):
        return (2, len(eq2["text"]), "true:square_twist_comm")
    if direct_substitution_route(eq1, eq2):
        return (2, len(eq2["text"]), "true:rewrite")
    if bridge_route(eq1, eq2):
        return (3, len(eq2["text"]), "true:bridge")
    if projection_cue(eq1, eq2):
        return (4, len(eq2["text"]), "false:projection_cue")
    if absorption_hypothesis(eq1):
        return (5, len(eq1["text"]) + len(eq2["text"]), "true:absorption")
    return (6, len(eq1["text"]) + len(eq2["text"]), "false:finite_search")


def find_counterexample(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_n: int = ENUMERATION_MAX_N,
    time_budget: float | None = None,
    allow_dual: bool = True,
) -> tuple[int, list[list[int]], str] | None:
    deadline = time.monotonic() + time_budget if time_budget else None
    named_max = max(max_n, STRUCTURED_MAX_N, 9)  # 9 admits CG9; vacuous otherwise (next-largest witness is 5x5)

    for name, table in WITNESS_TABLES:
        if len(table) <= named_max and table_is_counterexample(eq1, eq2, table):
            return len(table), table, f"false:witness:{name}"

    family_max = max(max_n, STRUCTURED_MAX_N)
    for route, table in structured_family_tables(max_n=family_max):
        if deadline is not None and time.monotonic() >= deadline:
            return None
        if table_is_counterexample(eq1, eq2, table):
            return len(table), table, route

    for route, table in affine_family_tables(max_n=max(max_n, max(AFFINE_LINEAR_SIZES))):
        if deadline is not None and time.monotonic() >= deadline:
            return None
        if table_is_counterexample(eq1, eq2, table):
            return len(table), table, route

    for route, table in quadratic_family_tables(max_n=family_max):
        if deadline is not None and time.monotonic() >= deadline:
            return None
        if table_is_counterexample(eq1, eq2, table):
            return len(table), table, route

    for n in range(2, max_n + 1):
        for table in enumerate_tables(n):
            if deadline is not None and time.monotonic() >= deadline:
                return None
            if table_is_counterexample(eq1, eq2, table):
                return n, table, f"false:enum_fin{n}"
    if allow_dual:
        remaining_budget = None
        if deadline is not None:
            remaining_budget = max(0.0, deadline - time.monotonic())
            if remaining_budget <= 0:
                return None
        dual = find_counterexample(
            dual_equation(eq1),
            dual_equation(eq2),
            max_n=max_n,
            time_budget=remaining_budget,
            allow_dual=False,
        )
        if dual is not None:
            n, table, route = dual
            return n, transpose_table(table), f"false:dual:{route}"
    return None


def solve_problem(
    problem: dict[str, Any],
    *,
    false_time_budget: float | None = None,
) -> dict[str, Any] | None:
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return None

    if is_reflexive_problem(problem):
        return {
            "answer": make_true_answer(problem, reflexive_true_certificate()),
            "route": "true:reflexive",
            "priority": problem_priority(problem, eq1, eq2),
        }

    singleton = singleton_route(eq1)
    if singleton is not None:
        singleton_var, singleton_on_lhs = singleton
        return {
            "answer": make_true_answer(
                problem,
                singleton_true_certificate(eq1["variables"], eq2["variables"], singleton_var, singleton_on_lhs),
            ),
            "route": "true:singleton",
            "priority": problem_priority(problem, eq1, eq2),
        }

    middle_self_collapse = middle_self_collapse_route(eq1, eq2)
    if middle_self_collapse is not None:
        route, code = middle_self_collapse
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    front_double_self_collapse = front_double_self_collapse_route(eq1, eq2)
    if front_double_self_collapse is not None:
        route, code = front_double_self_collapse
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    alternating_front_self_collapse = alternating_front_self_collapse_route(eq1, eq2)
    if alternating_front_self_collapse is not None:
        route, code = alternating_front_self_collapse
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    mirrored_alternating_front_self_collapse = mirrored_alternating_front_self_collapse_route(eq1, eq2)
    if mirrored_alternating_front_self_collapse is not None:
        route, code = mirrored_alternating_front_self_collapse
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    square_twist_comm = square_twist_comm_route(eq1, eq2)
    if square_twist_comm is not None:
        route, code = square_twist_comm
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    sandwich_left_projection = sandwich_left_projection_route(eq1, eq2)
    if sandwich_left_projection is not None:
        route, code = sandwich_left_projection
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    direct = direct_substitution_route(eq1, eq2)
    if direct is not None:
        mode, subst = direct
        call_expr = call_expression(eq1["variables"], subst)
        if mode == "symm":
            call_expr = f"({call_expr}).symm"
        return {
            "answer": make_true_answer(problem, substitution_true_certificate(eq2["variables"], call_expr)),
            "route": "true:rewrite" if mode == "direct" else "true:rewrite:symm",
            "priority": problem_priority(problem, eq1, eq2),
        }

    bridge = bridge_route(eq1, eq2)
    if bridge is not None:
        bridge_name, left_subst, right_subst = bridge
        left_call = call_expression(eq1["variables"], left_subst)
        right_call = call_expression(eq1["variables"], right_subst)
        left_source = int(bridge_name[-2])
        right_source = int(bridge_name[-1])
        left_to_mid = left_call if left_source == 0 else f"({left_call}).symm"
        mid_to_right = f"({right_call}).symm" if right_source == 0 else right_call
        return {
            "answer": make_true_answer(
                problem,
                substitution_true_certificate(eq2["variables"], f"({left_to_mid}).trans ({mid_to_right})"),
            ),
            "route": bridge_name,
            "priority": problem_priority(problem, eq1, eq2),
        }

    completed_bridge = completed_bridge_route(eq1, eq2)
    if completed_bridge is not None:
        bridge_name, left_subst, right_subst = completed_bridge
        left_call = call_expression(eq1["variables"], left_subst)
        right_call = call_expression(eq1["variables"], right_subst)
        left_source = int(bridge_name[-2])
        right_source = int(bridge_name[-1])
        left_to_mid = left_call if left_source == 0 else f"({left_call}).symm"
        mid_to_right = f"({right_call}).symm" if right_source == 0 else right_call
        return {
            "answer": make_true_answer(
                problem,
                substitution_true_certificate(eq2["variables"], f"({left_to_mid}).trans ({mid_to_right})"),
            ),
            "route": bridge_name,
            "priority": problem_priority(problem, eq1, eq2),
        }

    projection = projection_true_route(eq1, eq2)
    if projection is not None:
        route, code = projection
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    chain = find_rewrite_chain(eq1, eq2)
    if chain is not None:
        routes, proof_expr = chain
        return {
            "answer": make_true_answer(problem, substitution_true_certificate(eq2["variables"], proof_expr)),
            "route": "true:rewrite_chain:" + ",".join(routes),
            "priority": problem_priority(problem, eq1, eq2),
        }

    c9_collapse = c9_e1072_collapse_route(eq1, eq2)
    if c9_collapse is not None:
        route, code = c9_collapse
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    self_square = self_square_absorption_route(eq1, eq2)
    if self_square is not None:
        route, code = self_square
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    repeat_tail = repeat_tail_absorption_route(eq1, eq2)
    if repeat_tail is not None:
        route, code = repeat_tail
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    absorption_context_bridge = absorption_context_bridge_route(eq1, eq2)
    if absorption_context_bridge is not None:
        route, code = absorption_context_bridge
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    absorption = absorption_closure_route(eq1, eq2)
    if absorption is not None:
        route, code = absorption
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    counterexample = find_counterexample(eq1, eq2, time_budget=false_time_budget)
    if counterexample is None:
        closure_first = not absorption_hypothesis(eq1)
        if closure_first:
            closure = equational_closure_route(eq1, eq2)
            if closure is not None:
                route, code = closure
                return {
                    "answer": make_true_answer(problem, code),
                    "route": route,
                    "priority": problem_priority(problem, eq1, eq2),
                }

        deep_absorption = deep_absorption_closure_route(eq1, eq2)
        if deep_absorption is not None:
            route, code = deep_absorption
            return {
                "answer": make_true_answer(problem, code),
                "route": route,
                "priority": problem_priority(problem, eq1, eq2),
            }

        if not closure_first:
            closure = equational_closure_route(eq1, eq2)
            if closure is not None:
                route, code = closure
                return {
                    "answer": make_true_answer(problem, code),
                    "route": route,
                    "priority": problem_priority(problem, eq1, eq2),
                }
        saturation = cp_saturation_route(eq1, eq2, lemma_budget=guided_lemma_budget(problem))
        if saturation is not None:
            route, code = saturation
            return {
                "answer": make_true_answer(problem, code),
                "route": route,
                "priority": problem_priority(problem, eq1, eq2),
            }
        return None
    n, table, route = counterexample
    return {
        "answer": make_false_answer(problem, n, table),
        "route": route,
        "priority": problem_priority(problem, eq1, eq2),
    }


def load_json_line(stream: Any) -> dict[str, Any] | None:
    line = stream.readline()
    if not line:
        return None
    return json.loads(line)


def send_proxy_call(message: dict[str, Any]) -> dict[str, Any] | None:
    print(json.dumps(message, separators=(",", ":")), flush=True)
    return load_json_line(sys.stdin)


def judge_via_solo_proxy(answer: dict[str, Any]) -> dict[str, Any] | None:
    request = judge_answer_payload(answer)
    if request is None:
        log_stderr({"route": "output:skip_malformed_judge_answer"})
        return None
    request["call"] = "judge"
    return send_proxy_call(request)


def fallback_true_certificate() -> str:
    return reflexive_true_certificate()


def extract_json_object(text: str) -> dict[str, Any] | None:
    text = re.sub(r"<think>[\s\S]*?</think>", "", text or "").strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        obj = json.loads(text)
        return obj if isinstance(obj, dict) else None
    except json.JSONDecodeError:
        pass
    match = re.search(r"\{[\s\S]*\}", text)
    if not match:
        return None
    try:
        obj = json.loads(match.group())
    except json.JSONDecodeError:
        return None
    return obj if isinstance(obj, dict) else None


def sanitize_lean_code(code: str, *, verdict: str) -> bool:
    if not isinstance(code, str) or not code.strip():
        return False
    if len(code.encode("utf-8")) > MAX_LEAN_CODE_BYTES:
        return False
    if verdict == "false" and len(code.encode("utf-8")) > MAX_FALSE_CERT_BYTES:
        return False
    if BANNED_LEAN_RE.search(code):
        return False
    has_submission = bool(re.search(r"\b(?:def|theorem)\s+submission\b", code))
    if not has_submission:
        return False
    saw_judge_problem = False
    for raw_line in code.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("--"):
            continue
        if line.startswith("import "):
            modules = line.split()[1:]
            if not modules:
                return False
            for module in modules:
                if module not in ALLOWED_IMPORTS:
                    return False
                if module == "JudgeProblem":
                    saw_judge_problem = True
    return saw_judge_problem


def clean_proof_body(proof: str) -> str:
    proof = re.sub(r"<think>[\s\S]*?</think>", "", proof or "").strip()
    proof = re.sub(r"^```(?:lean)?\s*\n?", "", proof)
    proof = re.sub(r"\n?```\s*$", "", proof).strip()
    proof = re.sub(r"^\s*import\s+.*\n?", "", proof, flags=re.MULTILINE)
    match = re.search(r"\b(?:def|theorem)\s+submission\s*:\s*Goal\s*:=\s*by\s*(.*)", proof, re.DOTALL)
    if match:
        proof = match.group(1).strip()
    proof = re.sub(r"^\s*by\s+", "", proof).strip()
    proof = re.sub(r"^\s*intro\s+G\s+_\s+h\s*\n?", "", proof)
    return proof.strip()


def true_body_certificate(proof_body: str) -> str | None:
    body = clean_proof_body(proof_body)
    if not body or BANNED_LEAN_RE.search(body):
        return None
    indented = "\n".join(("  " + line if line.strip() else "") for line in body.splitlines())
    code = "import JudgeProblem\n\n" "def submission : Goal := by\n" "  intro G _ h\n" f"{indented}\n"
    if not sanitize_lean_code(code, verdict="true"):
        return None
    return code


def normalize_table(value: Any) -> list[list[int]] | None:
    if not isinstance(value, list) or not value:
        return None
    n = len(value)
    if n < 1 or n > LLM_MAX_TABLE_N:
        return None
    table: list[list[int]] = []
    for row in value:
        if not isinstance(row, list) or len(row) != n:
            return None
        out_row: list[int] = []
        for cell in row:
            if type(cell) is not int or cell < 0 or cell >= n:
                return None
            out_row.append(cell)
        table.append(out_row)
    return table


def parse_llm_chain_terms(chain: Any, variables: set[str]) -> list[Term] | None:
    if not isinstance(chain, list) or len(chain) < 2:
        return None
    terms: list[Term] = []
    for item in chain:
        if not isinstance(item, str):
            return None
        try:
            terms.append(parse_term(item, variables))
        except ValueError:
            return None
    return terms


def chain_certificate_from_terms(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    chain_terms: list[Term],
) -> str | None:
    if chain_terms[0] != eq2["lhs"] or chain_terms[-1] != eq2["rhs"]:
        return None
    proofs: list[str] = []
    for src, dst in zip(chain_terms, chain_terms[1:]):
        step = proof_between_terms(eq1, src, dst)
        if step is None:
            return None
        proofs.append(step[0])
    if not proofs:
        return None
    expr = proofs[0]
    for proof in proofs[1:]:
        expr = f"({expr}).trans ({proof})"
    return substitution_true_certificate(eq2["variables"], expr)


def guided_chain_certificate_from_terms_ex(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    chain_terms: list[Term],
    *,
    lemma_budget: int = 0,
) -> tuple[str | None, str | None]:
    """Returns (certificate, failed_hop_text). failed_hop_text is set only when
    a specific hop could not be verified (lemma widening enabled)."""
    if chain_terms[0] != eq2["lhs"] or chain_terms[-1] != eq2["rhs"]:
        return None, None
    pool = _CP_LEMMA_POOLS.setdefault(eq1["text"], []) if lemma_budget > 0 else []
    proofs: list[str] = []
    for src, dst in zip(chain_terms, chain_terms[1:]):
        hop_key = (eq1["text"], term_to_lean(src), term_to_lean(dst))
        cached = _CP_HOP_CACHE.get(hop_key) if lemma_budget > 0 else None
        if cached is not None:
            proofs.append(cached)
            continue
        step = proof_between_terms_guided(eq1, eq2["variables"], src, dst, lemmas=tuple(pool))
        if step is None and lemma_budget > 0 and len(pool) < lemma_budget:
            deadline = time.monotonic() + CP_GAP_TIME_BUDGET
            new_lemmas = derive_gap_lemmas(
                eq1, pool, src, dst, max_new=lemma_budget - len(pool), deadline=deadline
            )
            if new_lemmas:
                pool.extend(new_lemmas)
                step = proof_between_terms_guided(
                    eq1, eq2["variables"], src, dst, lemmas=tuple(pool)
                )
        if step is None:
            if lemma_budget > 0:
                return None, f"{term_to_lean(src)} = {term_to_lean(dst)}"
            return None, None
        if lemma_budget > 0 and len(_CP_HOP_CACHE) < CP_HOP_CACHE_LIMIT:
            _CP_HOP_CACHE[hop_key] = step[0]
        proofs.append(step[0])
    if not proofs:
        return None, None
    expr = proofs[0]
    for proof in proofs[1:]:
        expr = f"({expr}).trans ({proof})"
    cited = _cited_lemmas(pool, proofs)
    if cited:
        return guided_true_certificate_with_lemmas(eq2["variables"], cited, expr), None
    return substitution_true_certificate(eq2["variables"], expr), None


def guided_chain_certificate_from_terms(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    chain_terms: list[Term],
) -> str | None:
    code, _failed_hop = guided_chain_certificate_from_terms_ex(eq1, eq2, chain_terms)
    return code


def candidate_from_llm_text_with_reason(
    problem: dict[str, Any],
    text: str,
    *,
    allow_raw_true: bool = True,
) -> tuple[dict[str, Any] | None, str]:
    obj = extract_json_object(text)
    if obj is None:
        return None, "no_json_object"
    if isinstance(obj.get("answer"), dict):
        obj = obj["answer"]
    verdict = str(obj.get("verdict", "")).lower()
    if verdict not in {"true", "false"}:
        return None, "missing_or_invalid_verdict"
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return None, "problem_parse_failed"

    if verdict == "false":
        raw_table = obj.get("counterexample_table", obj.get("table"))
        table = normalize_table(raw_table)
        if table is None:
            return None, "false_table_invalid_shape"
        if not table_is_counterexample(eq1, eq2, table):
            return None, "false_table_not_counterexample"
        return {
            "answer": make_false_answer(problem, len(table), table),
            "route": "llm:false:table",
        }, "ok"

    chain = obj.get("chain")
    if chain is None and isinstance(obj.get("steps"), list):
        steps = obj["steps"]
        if steps and all(isinstance(step, dict) for step in steps):
            chain = [steps[0].get("from")]
            chain.extend(step.get("to") for step in steps)
    chain_reject_reason = "no_chain_supplied"
    if chain is not None:
        variables = set(eq2["variables"])
        chain_terms = parse_llm_chain_terms(chain, variables)
        if chain_terms is None:
            chain_reject_reason = "rewrite_chain_parse_failed"
        else:
            code = chain_certificate_from_terms(eq1, eq2, chain_terms)
            if code is not None:
                return {
                    "answer": make_true_answer(problem, code),
                    "route": "llm:true:rewrite_chain",
                }, "ok"
            code, failed_hop = guided_chain_certificate_from_terms_ex(
                eq1, eq2, chain_terms, lemma_budget=guided_lemma_budget(problem)
            )
            if code is not None:
                return {
                    "answer": make_true_answer(problem, code),
                    "route": "llm:true:guided_chain",
                }, "ok"
            if failed_hop is not None:
                chain_reject_reason = f"guided_chain_hop_unproved:{failed_hop}"
            else:
                chain_reject_reason = "guided_chain_unproved_or_bad_endpoints"

    if not allow_raw_true:
        if isinstance(obj.get("code", obj.get("lean")), str) or isinstance(obj.get("proof", obj.get("proof_body")), str):
            return None, "raw_true_disabled"
        return None, chain_reject_reason

    code = obj.get("code", obj.get("lean"))
    if isinstance(code, str) and sanitize_lean_code(code, verdict="true"):
        return {
            "answer": make_true_answer(problem, code),
            "route": "llm:true:raw_code",
        }, "ok"
    if isinstance(code, str):
        return None, "raw_code_sanitizer_rejected"

    proof = obj.get("proof", obj.get("proof_body"))
    if isinstance(proof, str):
        code = true_body_certificate(proof)
        if code is not None:
            return {
                "answer": make_true_answer(problem, code),
                "route": "llm:true:proof_body",
            }, "ok"
        return None, "proof_body_rejected"
    return None, chain_reject_reason


def candidate_from_llm_text(
    problem: dict[str, Any],
    text: str,
    *,
    allow_raw_true: bool = True,
) -> dict[str, Any] | None:
    candidate, _reason = candidate_from_llm_text_with_reason(problem, text, allow_raw_true=allow_raw_true)
    return candidate


def terms_preview(terms: list[Term] | tuple[Term, ...], *, limit: int = 10) -> str:
    rendered: list[str] = []
    seen: set[str] = set()
    for term in terms:
        text = term_to_lean(term)
        if text in seen:
            continue
        seen.add(text)
        rendered.append(text)
        if len(rendered) >= limit:
            break
    if not rendered:
        return "(none)"
    return ", ".join(rendered)


def solver_analysis(problem: dict[str, Any]) -> str:
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return "Could not parse one of the equations; prefer a finite-table DSL only if certain."
    hypothesis_subterms = list(term_subterms_tuple(eq1["lhs"]) + term_subterms_tuple(eq1["rhs"]))
    goal_subterms = list(term_subterms_tuple(eq2["lhs"]) + term_subterms_tuple(eq2["rhs"]))
    deterministic_status: list[str] = []
    deterministic_status.append("singleton: yes" if singleton_route(eq1) else "singleton: no")
    deterministic_status.append("direct substitution: yes" if direct_substitution_route(eq1, eq2) else "direct substitution: no")
    deterministic_status.append("two-instance bridge: yes" if bridge_route(eq1, eq2) else "two-instance bridge: no")
    deterministic_status.append(
        "completed bridge/constancy: yes"
        if completed_bridge_route(eq1, eq2, max_trials=300)
        else "completed bridge/constancy: no"
    )
    deterministic_status.append("projection law: yes" if projection_law_route(eq1) else "projection law: no")
    deterministic_status.append("absorption-like hypothesis: yes" if absorption_hypothesis(eq1) else "absorption-like hypothesis: no")
    cues: list[str] = [
        f"hypothesis variables: {' '.join(eq1['variables']) or '(none)'}",
        f"goal variables: {' '.join(eq2['variables']) or '(none)'}",
        f"goal lhs: {eq2['lhs_text']}",
        f"goal rhs: {eq2['rhs_text']}",
        f"hypothesis subterms: {terms_preview(hypothesis_subterms, limit=12)}",
        f"goal subterms: {terms_preview(goal_subterms, limit=12)}",
        "deterministic route cues: " + "; ".join(deterministic_status),
    ]
    if absorption_hypothesis(eq1):
        cues.append("This is a good TRUE candidate for absorption/collapse/congruence chaining.")
    elif projection_cue(eq1, eq2):
        cues.append("Boundary/projection cues can be FALSE; use TRUE only if the chain is explicit and solver-provable.")
    cues.append("Admissible term syntax: variables x y z w u v; binary products as a ◇ b; parentheses are allowed.")
    cues.append("A TRUE chain must start exactly with the goal lhs and end exactly with the goal rhs.")
    cues.append("Each adjacent TRUE chain step must be one explicit hypothesis rewrite, short rewrite chain, or bounded solver-owned closure/congruence step.")
    cues.append('Use {"proof_kind":"guided_chain"} when an adjacent chain edge needs more than one direct rewrite.')
    cues.append("Raw Lean/proof bodies may be judged in Solo, but Marathon will reject raw TRUE and append only solver-verified DSL certificates.")
    cues.append("For FALSE, provide a square finite table; the solver will test it before emitting Lean.")
    return "\n".join(cues)


def llm_problem_priority(priority: tuple[int, int, str], problem: dict[str, Any]) -> tuple[int, int, int, str]:
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return (9, priority[0], priority[1], str(problem.get("id", "")))

    score = 4
    if absorption_hypothesis(eq1):
        score -= 3
    if eq1["lhs"][0] == "var" or eq1["rhs"][0] == "var":
        score -= 1
    if eq2["lhs"][0] == "var" or eq2["rhs"][0] == "var":
        score -= 1
    if term_vars(eq2["lhs"]) == term_vars(eq2["rhs"]):
        score -= 1
    if projection_cue(eq1, eq2) and not absorption_hypothesis(eq1):
        score += 2
    if not term_vars(eq2["lhs"]).issubset(set(eq1["variables"])) or not term_vars(eq2["rhs"]).issubset(set(eq1["variables"])):
        score += 1
    score = max(0, score)
    size = term_size(eq1["lhs"]) + term_size(eq1["rhs"]) + term_size(eq2["lhs"]) + term_size(eq2["rhs"])
    return (score, priority[0], size, str(problem.get("id", "")))


def render_marathon_prompt(problem: dict[str, Any], analysis: str) -> str:
    replacements = {
        "problem.id": str(problem.get("id", "")),
        "problem.eq1_id": str(problem.get("eq1_id", "")),
        "problem.eq2_id": str(problem.get("eq2_id", "")),
        "problem.equation1": str(problem.get("equation1", "")),
        "problem.equation2": str(problem.get("equation2", "")),
        "solver.analysis": analysis,
        "history.attempts": "",
    }
    prompt = PROMPT
    for key, value in replacements.items():
        prompt = prompt.replace("{" + key + "}", value)
    return re.sub(r"\{(?:problem|solver|history)\.[a-zA-Z_]+\}", "", prompt)


def log_stderr(record: dict[str, Any]) -> None:
    print(json.dumps(record, separators=(",", ":")), file=sys.stderr, flush=True)


def text_preview(text: str, limit: int = 160) -> str:
    compact = re.sub(r"\s+", " ", text or "").strip()
    if len(compact) <= limit:
        return compact
    return compact[:limit]


def marathon_llm_attempt(
    call_llm: Any,
    problem: dict[str, Any],
    config: dict[str, Any],
    deadline: float,
) -> dict[str, Any]:
    pid = str(problem.get("id"))
    started = time.monotonic()
    max_seconds = min(float(config.get("http_timeout_seconds", LLM_HTTP_TIMEOUT_SECONDS)), max(1.0, deadline - started - 5.0))
    result: dict[str, Any] = {"id": pid}
    try:
        analysis = solver_analysis(problem)
        prompt = render_marathon_prompt(problem, analysis)
        response = call_llm(prompt, config=config, max_seconds=max_seconds)
    except Exception as exc:  # noqa: BLE001
        result["error"] = str(exc)
        result["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return result

    result["elapsed_seconds"] = round(time.monotonic() - started, 3)
    for key in ("tokens_used_call", "tokens_used_total", "budget_remaining"):
        if key in response:
            result[key] = response.get(key)
    if "error" in response:
        result["error"] = str(response.get("error", ""))
        return result

    response_text = str(response.get("response", ""))
    candidate, reject_reason = candidate_from_llm_text_with_reason(
        problem,
        response_text,
        allow_raw_true=False,
    )
    if candidate is None:
        result["reject_reason"] = reject_reason
        result["response_chars"] = len(response_text)
        if reject_reason == "no_json_object":
            result["response_preview"] = text_preview(response_text)
        return result
    result["candidate"] = candidate
    result["route"] = str(candidate.get("route", "llm:unknown"))
    return result


def solo_llm_rounds() -> int:
    raw = os.environ.get("MAGMA_SOLO_LLM_ROUNDS")
    if raw is None:
        return LLM_MAX_ROUNDS
    try:
        return max(0, int(raw))
    except ValueError:
        return LLM_MAX_ROUNDS

def run_solo() -> int:
    payload = load_json_line(sys.stdin)
    if not payload:
        return 0

    problem = payload.get("problem", payload)
    if not isinstance(problem, dict):
        return 0

    attempted: set[tuple[str, str]] = set()
    solved = solve_problem(problem)
    if solved is not None:
        answer = dict(solved["answer"])
        attempted.add((str(answer.get("verdict")), str(answer.get("code"))))
        response = judge_via_solo_proxy(answer)
        if response:
            print(
                json.dumps(
                    {
                        "judge_status": response.get("status"),
                        "route": solved["route"],
                    }
                ),
                file=sys.stderr,
            )
            if response.get("status") == "accepted":
                return 0

    analysis = solver_analysis(problem)
    if guided_lemma_budget(problem) > 0:
        try:
            hint = frontier_bridge_hint(
                parse_equation(str(problem["equation1"])),
                parse_equation(str(problem["equation2"])),
            )
        except (KeyError, ValueError):
            hint = ""
        if hint:
            analysis = f"{analysis}\n{hint}"
    if solved is None:
        print(
            json.dumps(
                {
                    "route": "skip:deterministic",
                    "reason": "No deterministic certificate available; escalating through proxy LLM.",
                }
            ),
            file=sys.stderr,
        )

    for round_idx in range(solo_llm_rounds()):
        llm_response = send_proxy_call(
            {
                "call": "llm",
                "context": {
                    "round": str(round_idx),
                    "analysis": analysis,
                },
            }
        )
        if not llm_response or "error" in llm_response:
            print(
                json.dumps(
                    {
                        "route": "llm:skip",
                        "round": round_idx,
                        "error": (llm_response or {}).get("error", "no response"),
                    }
                ),
                file=sys.stderr,
            )
            break
        candidate, reject_reason = candidate_from_llm_text_with_reason(problem, str(llm_response.get("response", "")))
        if candidate is None:
            print(json.dumps({"route": "llm:reject", "round": round_idx, "reason": reject_reason}), file=sys.stderr)
            if reject_reason.startswith("guided_chain_hop_unproved:"):
                gap = reject_reason.split(":", 1)[1]
                analysis = (
                    f"{solver_analysis(problem)}\n"
                    f"Guided-chain feedback: every hop of your previous chain verified except `{gap}`. "
                    f"Verified hops are cached and will be reused. Propose a chain that bridges exactly "
                    f"this gap through smaller intermediate steps (each hop provable from the hypothesis "
                    f"in at most a few rewrites), keeping the rest of your chain."
                )
            elif (
                reject_reason in ("false_table_not_counterexample", "false_table_invalid_shape")
                and guided_lemma_budget(problem) > 0
            ):
                analysis = (
                    f"{solver_analysis(problem)}\n"
                    f"Verdict feedback: your FALSE answer was refuted locally — the table either fails "
                    f"the hypothesis on some assignment or never falsifies the goal. Do not repeat it. "
                    f"If you remain confident the implication is FALSE, return a different table (size 3 "
                    f"or larger) that you have checked cell-by-cell against the hypothesis. Otherwise "
                    f"treat the implication as TRUE and return proof_kind guided_chain with a chain of "
                    f"intermediate terms from the goal's LHS to its RHS, using only the goal's variables; "
                    f"each consecutive pair should follow from the hypothesis in a few rewrites."
                )
            continue
        answer = dict(candidate["answer"])
        key = (str(answer.get("verdict")), str(answer.get("code")))
        if key in attempted:
            print(json.dumps({"route": "llm:duplicate", "round": round_idx}), file=sys.stderr)
            continue
        attempted.add(key)
        judge_response = judge_via_solo_proxy(answer)
        if judge_response:
            print(
                json.dumps(
                    {
                        "judge_status": judge_response.get("status"),
                        "route": candidate["route"],
                        "round": round_idx,
                    }
                ),
                file=sys.stderr,
            )
            if judge_response.get("status") == "accepted":
                return 0
    if guided_lemma_budget(problem) > 0 and not is_reflexive_problem(problem):
        # The reflexivity fallback typechecks only when the two laws coincide,
        # which the reflexive route already owns — for any other pair it is a
        # guaranteed-rejected submission. Skip it on the gated band.
        return 0
    fallback = make_true_answer(problem, fallback_true_certificate())
    judge_response = judge_via_solo_proxy(fallback)
    if judge_response:
        print(
            json.dumps(
                {
                    "judge_status": judge_response.get("status"),
                    "route": "fallback:final_judge_call",
                }
            ),
            file=sys.stderr,
        )
    return 0


def iter_manifest(path: str) -> list[dict[str, Any]]:
    problems: list[dict[str, Any]] = []
    with open(path, "r", encoding="utf-8") as manifest_file:
        for line in manifest_file:
            stripped = line.strip()
            if stripped:
                problems.append(json.loads(stripped))
    return problems


def append_answer(path: str, answer: dict[str, Any]) -> bool:
    payload = marathon_answer_payload(answer)
    if payload is None:
        log_stderr({"route": "output:skip_malformed_marathon_answer"})
        return False
    with open(path, "a", encoding="utf-8") as output_file:
        output_file.write(json.dumps(payload, separators=(",", ":")))
        output_file.write("\n")
        output_file.flush()
    return True


def marathon_reference_seconds() -> float:
    raw = os.environ.get("MAGMA_MARATHON_REF_SECONDS_PER_PROBLEM")
    if raw:
        try:
            value = float(raw)
            if value > 0:
                return value
        except ValueError:
            pass
    return MARATHON_REF_SECONDS_DEFAULT


def marathon_per_problem_budget(total_budget: float, problem_count: int, ref_seconds: float) -> float:
    if problem_count <= 0:
        return 0.25
    compression = total_budget / max(1.0, ref_seconds * problem_count)
    return max(0.2, min(4.0, 0.5 + 5.0 * compression))


def load_marathon_llm() -> tuple[Any | None, Any | None, Any | None]:
    lib_dir = os.environ.get("JUDGE_MARATHON_LIB_DIR")
    if not lib_dir:
        return None, None, None
    if lib_dir not in sys.path:
        sys.path.insert(0, lib_dir)
    try:
        marathon_llm = importlib.import_module("marathon_llm")
    except Exception:  # noqa: BLE001
        return None, None, None
    return marathon_llm.call_llm, marathon_llm.tokens_used, marathon_llm.budget_remaining


def run_marathon() -> int:
    manifest_path = os.environ.get("JUDGE_MARATHON_MANIFEST")
    output_path = os.environ.get("JUDGE_MARATHON_OUTPUT")
    if not manifest_path or not output_path:
        print("Missing Marathon manifest/output environment variables.", file=sys.stderr)
        return 2

    problems = iter_manifest(manifest_path)
    budget_seconds = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    budget_tokens = int(os.environ.get("JUDGE_MARATHON_BUDGET_TOKENS", "0"))
    deadline = time.monotonic() + budget_seconds
    ref_seconds = marathon_reference_seconds()
    per_problem_budget = marathon_per_problem_budget(budget_seconds, len(problems), ref_seconds)

    prioritized: list[tuple[tuple[int, int, str], dict[str, Any]]] = []
    for problem in problems:
        try:
            eq1 = parse_equation(str(problem["equation1"]))
            eq2 = parse_equation(str(problem["equation2"]))
            priority = problem_priority(problem, eq1, eq2)
        except (KeyError, ValueError):
            priority = (9, 0, "skip:parse_error")
        prioritized.append((priority, problem))
    prioritized.sort(key=lambda item: item[0])

    route_counts: dict[str, int] = {}
    solved = 0
    deterministic_submitted = 0
    solved_ids: set[str] = set()
    for priority, problem in prioritized:
        if time.monotonic() + 5.0 >= deadline:
            break
        answer_record = solve_problem(problem, false_time_budget=per_problem_budget)
        if answer_record is None:
            continue
        if not append_answer(output_path, answer_record["answer"]):
            continue
        route = str(answer_record["route"])
        route_counts[route] = route_counts.get(route, 0) + 1
        solved += 1
        deterministic_submitted += 1
        solved_ids.add(str(problem.get("id")))

    llm_calls = 0
    call_llm, tokens_used, budget_remaining = load_marathon_llm()
    unresolved_count = len(prioritized) - len(solved_ids)
    if unresolved_count > 0 and call_llm is None:
        print(
            json.dumps(
                {
                    "route": "llm:disabled",
                    "reason": "missing_marathon_proxy_library",
                    "unresolved": unresolved_count,
                    "budget_tokens": budget_tokens,
                }
            ),
            file=sys.stderr,
        )
    if unresolved_count > 0 and budget_tokens == 0:
        print(
            json.dumps(
                {
                    "route": "llm:disabled",
                    "reason": "zero_token_budget",
                    "unresolved": unresolved_count,
                    "budget_tokens": budget_tokens,
                }
            ),
            file=sys.stderr,
        )
    if call_llm is not None and budget_tokens != 0:
        unresolved = [
            (llm_problem_priority(priority, problem), problem)
            for priority, problem in prioritized
            if str(problem.get("id")) not in solved_ids
        ]
        unresolved.sort(key=lambda item: item[0])
        index = 0
        stop_llm = False
        with ThreadPoolExecutor(max_workers=MARATHON_LLM_BATCH_SIZE) as executor:
            while index < len(unresolved) and llm_calls < MARATHON_LLM_MAX_CALLS and not stop_llm:
                if time.monotonic() + 20.0 >= deadline:
                    break
                used = tokens_used() if tokens_used is not None else None
                if budget_tokens > 0 and used is not None and used >= budget_tokens:
                    log_stderr(
                        {
                            "route": "llm:disabled",
                            "reason": "token_budget_spent",
                            "tokens_used": used,
                            "budget_tokens": budget_tokens,
                        }
                    )
                    break
                remaining = budget_remaining() if budget_remaining is not None else None
                min_headroom = int(LLM_CONFIG["max_output_tokens"])
                if budget_tokens > 0 and remaining is not None and remaining >= 0 and remaining < min_headroom:
                    log_stderr(
                        {
                            "route": "llm:disabled",
                            "reason": "insufficient_remaining_token_headroom",
                            "budget_remaining": remaining,
                            "required_headroom": min_headroom,
                            "budget_tokens": budget_tokens,
                        }
                    )
                    break

                batch: list[dict[str, Any]] = []
                remaining_call_slots = MARATHON_LLM_MAX_CALLS - llm_calls
                while index < len(unresolved) and len(batch) < min(MARATHON_LLM_BATCH_SIZE, remaining_call_slots):
                    _priority, problem = unresolved[index]
                    index += 1
                    pid = str(problem.get("id"))
                    if pid not in solved_ids:
                        batch.append(problem)
                if not batch:
                    continue

                llm_calls += len(batch)
                log_stderr(
                    {
                        "route": "llm:batch_start",
                        "size": len(batch),
                        "ids": [str(problem.get("id")) for problem in batch],
                        "llm_calls": llm_calls,
                        "max_output_tokens": LLM_CONFIG["max_output_tokens"],
                        "reasoning_effort": LLM_CONFIG.get("reasoning_effort"),
                        "http_timeout_seconds": LLM_CONFIG.get("http_timeout_seconds"),
                        "budget_remaining": remaining,
                    }
                )
                futures = {
                    executor.submit(marathon_llm_attempt, call_llm, problem, LLM_CONFIG, deadline): problem
                    for problem in batch
                }
                for future in as_completed(futures):
                    problem = futures[future]
                    pid = str(problem.get("id"))
                    try:
                        result = future.result()
                    except Exception as exc:  # noqa: BLE001
                        log_stderr({"route": "llm:error", "id": pid, "error": str(exc)})
                        continue
                    if "error" in result:
                        error = str(result.get("error", ""))
                        log_stderr(
                            {
                                "route": "llm:error",
                                "id": pid,
                                "error": error,
                                "elapsed_seconds": result.get("elapsed_seconds"),
                                "budget_remaining": result.get("budget_remaining"),
                            }
                        )
                        if "exhausted" in error or "budget" in error:
                            stop_llm = True
                        continue
                    if "candidate" not in result:
                        log_stderr(
                            {
                                "route": "llm:reject",
                                "id": pid,
                                "reason": result.get("reject_reason", "unknown"),
                                "elapsed_seconds": result.get("elapsed_seconds"),
                                "tokens_used_call": result.get("tokens_used_call"),
                                "budget_remaining": result.get("budget_remaining"),
                                "response_chars": result.get("response_chars"),
                                "response_preview": result.get("response_preview"),
                            }
                        )
                        continue

                    candidate = result["candidate"]
                    if not append_answer(output_path, candidate["answer"]):
                        continue
                    route = str(candidate["route"])
                    route_counts[route] = route_counts.get(route, 0) + 1
                    solved += 1
                    solved_ids.add(pid)
                    log_stderr(
                        {
                            "route": "llm:accepted_candidate",
                            "id": pid,
                            "candidate_route": route,
                            "elapsed_seconds": result.get("elapsed_seconds"),
                            "tokens_used_call": result.get("tokens_used_call"),
                            "budget_remaining": result.get("budget_remaining"),
                        }
                    )

    print(
        json.dumps(
            {
                "submitted_deterministic": deterministic_submitted,
                "submitted_total": solved,
                "llm_calls": llm_calls,
                "budget_seconds": budget_seconds,
                "budget_tokens": budget_tokens,
                "reference_seconds_per_problem": ref_seconds,
                "per_problem_false_budget": round(per_problem_budget, 3),
                "routes": route_counts,
            }
        ),
        file=sys.stderr,
        flush=True,
    )
    return 0


def is_marathon_mode() -> bool:
    return bool(os.environ.get("JUDGE_MARATHON_MANIFEST") and os.environ.get("JUDGE_MARATHON_OUTPUT"))


def main() -> int:
    if is_marathon_mode():
        return run_marathon()
    return run_solo()


if __name__ == "__main__":
    raise SystemExit(main())
