from __future__ import annotations

import json
import importlib
import os
import random
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import lru_cache
from itertools import product
from typing import Any, Callable, NamedTuple


_PROCESS_START = time.monotonic()


PROMPT = """You produce proofs about magmas. A magma is a type G with one binary operation
written `a ◇ b`. You are given two equational laws and must prove the first
implies the second.

The deterministic solver already searched for a finite magma satisfying Equation1
but breaking Equation2 -- named tables, structured/affine/quadratic families,
every magma of order <= 3, duals, and a randomized order 4-6 search -- and found
none. So Equation1 very likely IMPLIES Equation2: prove it.

That search is NOT exhaustive. If you can actually exhibit a finite magma where
Equation1 HOLDS and Equation2 FAILS, send that instead of a proof:
{"verdict":"false","table":[[...],[...]]}
giving the full n x n Cayley table over {0,...,n-1} (rows = left argument).
The solver re-checks every table exhaustively before submitting, so a wrong
table is discarded harmlessly and a correct one wins the problem outright.
Only do this if you have actually verified both conditions on the table;
otherwise prove TRUE.

Problem {problem.id}: prove Equation{problem.eq1_id} implies Equation{problem.eq2_id}.
Hypothesis (Equation1):  {problem.equation1}
Goal       (Equation2):  {problem.equation2}

Deterministic solver hints:
{solver.analysis}

################  BEST WAY TO ANSWER: the rewrite chain  ################
Give the sequence of terms from the goal's left side to the goal's right side,
where EACH consecutive pair differs by exactly ONE use of the hypothesis on ONE
subterm. THE SOLVER computes the exact effect of each hypothesis application and
builds the Lean proof for you — so you never do term bookkeeping by hand (that is
the #1 source of mistakes). Use only the goal's variables.

CRITICAL: ◇ is NOT associative and NOT commutative unless the hypothesis itself
says so. Never reassociate `a ◇ (b ◇ c)` to `(a ◇ b) ◇ c`, and never reorder
`a ◇ b` to `b ◇ a`, as a chain step — those are not valid. Every step must change
exactly one subterm by matching (an instance of) one side of the hypothesis and
replacing it with the other side. Keep the full parenthesization explicit.

{"verdict":"true","proof_kind":"guided_chain","chain":["<goal-lhs>","<t1>","...","<goal-rhs>"],"key_terms":["<t>","..."]}

To design the chain, think of the hypothesis L = R as a two-way rewrite: anywhere
you see (an instance of) L you may replace it by R, and vice-versa. List the terms
you pass through. Make each step a single such replacement. Smaller steps are
safer — the solver proves each step by search, so many small steps beat few big
ones.

"key_terms" is optional but powerful: list up to 8 extra terms (goal variables
only, full parenthesization) that you believe appear somewhere in the derivation —
useful hypothesis instantiations, absorbing shapes, or halfway terms. Even if your
chain has a gap, the solver runs a bidirectional equational search SEEDED with your
chain terms and key_terms and can finish the proof. If you are unsure of the exact
chain, give your best chain AND generous key_terms.

Also optional: "peak_term" — many of these proofs EXPAND both sides to one big
common term and meet there. If you can name that single largest middle term, give
it as "peak_term":"<term>"; the solver then searches goal-lhs -> peak and
peak -> goal-rhs separately, which is much easier than the full jump.

################  OFTEN EASIER: name a lemma  ################
You do not have to prove the goal at all. If you can name a SMALL law that (a)
follows from the hypothesis and (b) makes the goal obvious, just say so:

{"verdict":"true","proof_kind":"lemma","lemma":"a ◇ b = a","lemmas":["<alt>","..."]}

Use fresh variables (a, b, c...) — the lemma is its own universally quantified
law, independent of the goal's variables. THE SOLVER proves the lemma from the
hypothesis itself and then derives the goal from it; you supply only the idea.

This is often far easier than a chain, because a small law is a much smaller
search target than the goal. Laws worth considering, strongest first:
  "a = b"            -- the hypothesis forces the magma to have one element
  "a ◇ b = a"        -- left projection      "a ◇ b = b"  -- right projection
  "a ◇ a = a"        -- idempotence
  "a ◇ b = a ◇ c"    -- the right argument never matters
  "a ◇ b = c ◇ b"    -- the left argument never matters
  "a ◇ b = b ◇ a"    -- commutativity
Any equation is allowed, not just these. Give "lemmas" as a list to offer
several; the solver tries each and keeps the first that works. A lemma that is
too strong to be true is discarded harmlessly, so guess boldly — but a lemma
must genuinely IMPLY the goal, or it is useless even if true.

################  FALLBACK: a full Lean proof  ################
Only if a chain is impossible. Return {"verdict":"true","code":"<full Lean file>"}
whose code field is exactly (newlines written as \\n inside the JSON string):

import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro <goal vars>
  <steps>

After `intro G _ h`, `h` is the hypothesis law (fully quantified) and the goal is
`<Eq2-LHS> = <Eq2-RHS>`. Use ONLY these tactics:
  rw [h a b ...]           -- replace <Eq1-LHS>[a,b,...] by <Eq1-RHS>; `rw [← h ...]` reverses
  calc ... := by rw [...]   -- an explicit equational chain
  Eq.trans, Eq.symm, congrArg (fun t => t ◇ c) / (fun t => c ◇ t), exact, rfl
DO NOT use `simp`, `simpa`, `simp_all`, `aesop`, or `grind`: on these laws `simp`
loops (maximum recursion depth) and is rejected. When you write `h a b c`, the
result is <Eq1-LHS> and <Eq1-RHS> with the variables literally replaced by a,b,c;
substitute carefully or you will get a type mismatch.

Import nothing except `import JudgeProblem`. No `sorry`/`admit`. No Mathlib.

################  Learn from previous attempts ################
{history.attempts}
{solver.feedback}
If a Lean error shows a type mismatch, your hypothesis instantiation was wrong —
recompute it or switch to the rewrite chain. If a chain step was unprovable,
split it into smaller single-rewrite steps.

Output exactly ONE JSON object (first char {, last char }). No markdown, no
<think>, no prose.
"""

JUDGE_MAX_CODE_LENGTH = 50_000
JUDGE_MAX_FALSE_CERT_BYTES = 10_000

MAX_LEAN_CODE_BYTES = JUDGE_MAX_CODE_LENGTH - 500
MAX_FALSE_CERT_BYTES = JUDGE_MAX_FALSE_CERT_BYTES - 500
VALID_VERDICTS = {"true", "false"}
AFFINE_LINEAR_SIZES = (2, 3, 4, 5, 7, 8, 9)
LARGE_LINEAR_SIZES = (11, 13, 16, 17, 19, 23, 25)
AFFINE_QUADRATIC_SIZES = (2, 3, 5, 7)
ENUMERATION_MAX_N = 3
STRUCTURED_MAX_N = 7
LOCAL_MODEL_SIZES = (4, 5)
LOCAL_MODEL_TIME_BUDGET = 6.0
LOCAL_MODEL_MAX_FLIPS = 4000
LOCAL_MODEL_NOISE = 0.25
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
ABSORPTION_DEEP_TIME_BUDGET = 1.6
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
LLM_GUIDED_CHAIN_MAX_DEPTH = 8
LLM_GUIDED_CHAIN_CLOSURE_TIME_BUDGET = 1.0
GUIDED_CHAIN_FRONTIER_LIMIT = 4000
DERIVED_CP_MAX_RULE_SIZE = 15
DERIVED_CP_MAX_RULES = 48
DERIVED_CP_CHAIN_MAX_DEPTH = 4
DERIVED_CP_POOL_LIMIT = 16
DERIVED_CP_FILL_POOL_CAP = 10
DERIVED_CP_FRONTIER_LIMIT = 2600
DERIVED_CP_MAX_FILLS = 1200
DERIVED_CP_TERM_SLACK = 10
DERIVED_CP_DEPTH_SLACK = 3
DERIVED_CP_TIME_BUDGET = 8.0
LLM_SEEDED_CLOSURE_CHAIN_MAX_DEPTH = 5
LLM_SEEDED_CLOSURE_POOL_LIMIT = 20
LLM_SEEDED_CLOSURE_FRONTIER_LIMIT = 3600
LLM_SEEDED_CLOSURE_MAX_FILLS = 3000
LLM_SEEDED_CLOSURE_TERM_SLACK = 10
LLM_SEEDED_CLOSURE_DEPTH_SLACK = 3
LLM_SEEDED_CLOSURE_TIME_BUDGET = 5.0
LLM_SEEDED_CLOSURE_MAX_SEEDS = 24
LLM_SEEDED_CLOSURE_FILL_POOL_CAP = 14
LLM_SEEDED_CLOSURE_WAYPOINT_BUDGET = 1.5
LLM_SEEDED_CLOSURE_MAX_WAYPOINTS = 5
LLM_SEEDED_CLOSURE_TOTAL_BUDGET = 14.0
LLM_MAX_ROUNDS = 6
SOLO_FALLBACK_RESERVE_SECONDS = 90.0
SOLO_DETERMINISTIC_SHARE = 0.55
SOLO_LLM_ROUND_MIN_SECONDS = 150.0
MARATHON_LLM_MAX_CALLS = 64
MARATHON_LLM_BATCH_SIZE = 8
MARATHON_REF_SECONDS_DEFAULT = 600.0
MARATHON_DETERMINISTIC_SHARE = 0.6
MARATHON_ROW_BORROW = 3.0
MARATHON_ROW_MIN_SECONDS = 1.0
LLM_MAX_TABLE_N = 8
LLM_MAX_OUTPUT_TOKENS = 16384
LLM_HTTP_TIMEOUT_SECONDS = 75.0

EFFORT_TIERS = {
    "fast": (1.0, 1.0, 1.0, 0, 0),
    "standard": (7.5, 4.6, 3.3, 6, 0),
    "deep": (22.0, 11.5, 6.6, 10, 1),
}
EFFORT_LADDER: tuple[str, ...] = ("fast", "standard", "deep")
_EFFORT = "fast"


def set_effort(tier: str) -> None:
    global _EFFORT
    if tier in EFFORT_TIERS:
        _EFFORT = tier


def effort_tier() -> str:
    return _EFFORT


def effort_for_seconds(per_problem_seconds: float) -> str:
    if per_problem_seconds >= 240.0:
        return "deep"
    if per_problem_seconds >= 45.0:
        return "standard"
    return "fast"


def effort_ladder_to(tier: str) -> tuple[str, ...]:
    if tier not in EFFORT_LADDER:
        return (tier,)
    return EFFORT_LADDER[: EFFORT_LADDER.index(tier) + 1]


_HARD_DEADLINE: float | None = None


def set_hard_deadline(deadline: float | None) -> None:
    global _HARD_DEADLINE
    _HARD_DEADLINE = deadline


def local_deadline(time_budget: float | None) -> float | None:
    local = time.monotonic() + time_budget if time_budget else None
    if _HARD_DEADLINE is None:
        return local
    if local is None:
        return _HARD_DEADLINE
    return min(local, _HARD_DEADLINE)


def hard_deadline_expired() -> bool:
    if memory_exceeded():
        return True
    return _HARD_DEADLINE is not None and time.monotonic() >= _HARD_DEADLINE


def _eff_time(base: float) -> float:
    return base * EFFORT_TIERS[_EFFORT][0]


def _eff_frontier(base: int) -> int:
    return int(base * EFFORT_TIERS[_EFFORT][1])


def _eff_fills(base: int) -> int:
    return int(base * EFFORT_TIERS[_EFFORT][2])


def _eff_pool(base: int) -> int:
    return base + EFFORT_TIERS[_EFFORT][3]


def _eff_depth(base: int) -> int:
    return base + EFFORT_TIERS[_EFFORT][4]

LLM_CONFIG = {
    "model": "openai/gpt-oss-120b",
    "provider": "deepinfra/bf16",
    "max_output_tokens": LLM_MAX_OUTPUT_TOKENS,
    "temperature": 0.0,
    "reasoning_effort": "medium",
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
    r"initialize|builtin_initialize|axiom|unsafe|opaque|macro|elab|syntax|"
    r"aesop|grind|simp_all)\b"
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
    ("S4G", [[0, 3, 2, 1], [0, 3, 2, 1], [2, 1, 0, 3], [2, 1, 0, 3]]),
    ("S6A", [[4, 4, 1, 1, 4, 2], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 5, 2, 0, 2, 5], [1, 1, 3, 3, 3, 2], [4, 2, 0, 1, 3, 0]]),
    ("S9A", [[2, 8, 7, 2, 8, 8, 2, 7, 7], [1, 1, 0, 6, 6, 6, 1, 0, 0], [3, 3, 0, 6, 6, 6, 3, 0, 0], [1, 1, 0, 6, 6, 6, 1, 0, 0], [3, 3, 5, 4, 4, 4, 3, 5, 5], [2, 8, 7, 2, 8, 8, 2, 7, 7], [3, 3, 5, 4, 4, 4, 3, 5, 5], [2, 8, 7, 2, 8, 8, 2, 7, 7], [1, 1, 5, 4, 4, 4, 1, 5, 5]]),
    ("S6B", [[2, 3, 4, 5, 0, 1], [2, 3, 0, 5, 4, 1], [2, 3, 4, 5, 0, 1], [4, 3, 2, 5, 0, 1], [2, 3, 4, 5, 0, 1], [0, 3, 4, 5, 2, 1]]),
)


def reflexive_true_certificate() -> str:
    return submission_certificate([], "  exact h\n")


DECIDE_MAX_REC_DEPTH_APPLICATIONS = 4_096


def false_certificate_memo(n: int, table: list[list[int]],
                           *, decide_applications: int | None = None) -> str:
    table_str = json.dumps(table, separators=(",", ":"))
    deep = n >= 7 or (decide_applications is not None
                      and decide_applications > DECIDE_MAX_REC_DEPTH_APPLICATIONS)
    max_rec_depth = "set_option maxRecDepth 20000\n" if deep else ""
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


def false_certificate_list(n: int, table: list[list[int]]) -> str:
    flat = ",".join(str(value) for row in table for value in row)
    op = (
        f"fun i j => Fin.mk (Nat.mod (List.getD [{flat}] "
        f"(Nat.add (Nat.mul (Fin.val i) {n}) (Fin.val j)) 0) {n}) "
        f"(Nat.mod_lt _ (Nat.succ_pos {n - 1}))"
    )
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        f"set_option maxRecDepth {max(40_000, 80 * n * n)}\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{ op := {op} }}\n"
        f"  refine Exists.intro (Fin {n}) ?_\n"
        "  refine Exists.intro m ?_\n"
        "  decideFin!\n"
    )


def false_certificate(n: int, table: list[list[int]],
                      *, decide_applications: int | None = None) -> str:
    if n <= LEGACY_MAX_WITNESS_ORDER and all(0 <= v <= 9 for row in table for v in row):
        return false_certificate_memo(
            n, table, decide_applications=decide_applications)
    return false_certificate_list(n, table)


def singleton_true_certificate(
    eq1_vars: list[str],
    eq2_vars: list[str],
    singleton_var: str,
    singleton_on_lhs: bool,
) -> str:
    if not eq1_vars:
        return reflexive_true_certificate()
    call_a = "h " + " ".join("a" if var == singleton_var else "b" for var in eq1_vars)
    call_b = "h " + " ".join("b" for _ in eq1_vars)
    collapse = (f"({call_a}).trans ({call_b}).symm" if singleton_on_lhs
                else f"({call_a}).symm.trans ({call_b})")
    return submission_certificate(
        eq2_vars, "  exact hall _ _\n",
        "  have hall : ∀ a b : G, a = b := by\n"
        "    intro a b\n"
        f"    exact {collapse}\n")


def substitution_true_certificate(eq2_vars: list[str], call_expr: str) -> str:
    return submission_certificate(eq2_vars, f"  exact {call_expr}\n")


def projection_true_certificate(eq2_vars: list[str], proof_expr: str) -> str:
    return submission_certificate(eq2_vars, f"  exact {proof_expr}\n")


def grind_true_certificate(eq2_vars: list[str], *, heartbeats: int = 100000) -> str:
    return submission_certificate(
        eq2_vars,
        f"  set_option maxHeartbeats {heartbeats} in\n"
        "  grind\n")


Term = tuple[Any, ...]


def is_reflexive_problem(problem: dict[str, Any]) -> bool:
    eq1_id = problem.get("eq1_id")
    eq2_id = problem.get("eq2_id")
    return eq1_id is not None and eq2_id is not None and eq1_id == eq2_id


def make_true_answer(problem: dict[str, Any], code: str) -> dict[str, Any]:
    return {
        "id": str(problem.get("id", "")),
        "verdict": "true",
        "code": code,
    }


def witness_decide_applications(n: int, *equations: dict[str, Any]) -> int:
    widest = max((len(eq.get("variables") or ()) for eq in equations), default=1)
    return n ** max(1, widest)


def make_false_answer(problem: dict[str, Any], n: int, table: list[list[int]],
                      *, equations: tuple[dict[str, Any], ...] = ()) -> dict[str, Any]:
    applications = (witness_decide_applications(n, *equations)
                    if equations else None)
    return {
        "id": str(problem.get("id", "")),
        "verdict": "false",
        "code": false_certificate(n, table, decide_applications=applications),
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


NARROW_GRIND_TRUE_SHAPES = (
    ("x = y * (y * (z * (w * x)))", "x = y * (z * (w * (u * x)))"),
    ("x = (((x * y) * y) * z) * y", "x = (((x * y) * y) * x) * z"),
    ("x * y = z * ((x * z) * y)", "x * y = (z * z) * (x * y)"),
    ("x * y = (y * x) * (y * z)", "x * y = y * (y * z)"),
    ("x * y = (y * y) * (z * x)", "x * y = ((y * z) * x) * z"),
    ("x = (y * y) * (x * y)", "x = (y * x) * (y * y)"),
    ("x = y * (y * (x * z))", "x * y = y * (x * (z * z))"),
    ("x = (y * (x * z)) * (z * z)", "x * y = x * ((x * y) * x)"),
    ("x = x * (y * (z * (x * y)))", "x = x * (((y * x) * z) * w)"),
)


def equation_shape_key(eq: dict[str, Any]) -> tuple[Term, Term]:
    return eq["lhs"], eq["rhs"]


def canonical_law_key(eq: dict[str, Any]) -> tuple[Term, Term]:
    names: dict[str, str] = {}
    return (
        canonical_term_shape(eq["lhs"], names),
        canonical_term_shape(eq["rhs"], names),
    )


def canonical_term_shape(term: Term, names: dict[str, str]) -> Term:
    if term[0] == "var":
        var = str(term[1])
        if var not in names:
            names[var] = f"v{len(names)}"
        return "var", names[var]
    return "op", canonical_term_shape(term[1], names), canonical_term_shape(term[2], names)


@lru_cache(maxsize=1)
def narrow_grind_true_shape_keys() -> frozenset[tuple[Term, Term, Term, Term]]:
    keys: set[tuple[Term, Term, Term, Term]] = set()
    for src_text, goal_text in NARROW_GRIND_TRUE_SHAPES:
        src = parse_equation(src_text)
        goal = parse_equation(goal_text)
        keys.add((*equation_shape_key(src), *equation_shape_key(goal)))
    return frozenset(keys)


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


def table_is_renderable(table: list[list[int]]) -> bool:
    n = len(table)
    if n < 1 or any(len(row) != n for row in table):
        return False
    if any(not (0 <= value < n) for row in table for value in row):
        return False
    return len(false_certificate(n, table).encode("utf-8")) <= MAX_FALSE_CERT_BYTES


def witness_decide_is_affordable(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    table: list[list[int]],
) -> bool:
    n = len(table)
    if n <= LEGACY_MAX_WITNESS_ORDER:
        return True
    widest = max(len(eq1.get("variables") or ()), len(eq2.get("variables") or ()))
    return n ** max(1, widest) <= MAX_WITNESS_DECIDE_APPLICATIONS


def table_is_counterexample(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    table: list[list[int]],
) -> bool:
    if not equation_holds(eq1, table) or equation_holds(eq2, table):
        return False
    return (
        table_is_renderable(table)
        and witness_decide_is_affordable(eq1, eq2, table)
    )


_HYPOTHESIS_MODELS_SEEN = 0


def reset_hypothesis_model_count() -> None:
    global _HYPOTHESIS_MODELS_SEEN
    _HYPOTHESIS_MODELS_SEEN = 0


def hypothesis_models_seen() -> int:
    return _HYPOTHESIS_MODELS_SEEN


def note_hypothesis_model() -> None:
    global _HYPOTHESIS_MODELS_SEEN
    _HYPOTHESIS_MODELS_SEEN += 1


def witness_check(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    table: list[list[int]],
) -> bool:
    if not equation_holds(eq1, table):
        return False
    note_hypothesis_model()
    if equation_holds(eq2, table):
        return False
    return (
        table_is_renderable(table)
        and witness_decide_is_affordable(eq1, eq2, table)
    )


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


def large_linear_family_tables():
    for n in LARGE_LINEAR_SIZES:
        for a in range(1, n):
            for b in range(1, n):
                yield (
                    f"false:linear:z{n}:{a},{b}",
                    [[(a * x + b * y) % n for y in range(n)] for x in range(n)],
                )


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


class LawMatch(NamedTuple):
    call: str
    """The `h ...` instance of eq1 that proves the family's law."""
    bound: dict[str, str]
    """eq1 variable -> the Lean argument it is instantiated with."""

    def var(self, arg: str) -> str:
        return next(name for name, value in self.bound.items() if value == arg)


def law_matcher(
    pattern: str,
    args: dict[str, str] | None = None,
    *,
    distinct: bool = False,
    symm: str = "({}).symm",
    both_orientations: bool = True,
) -> Callable[[dict[str, Any]], LawMatch | None]:
    law = parse_equation(pattern)
    lhs_pattern, rhs_pattern = law["lhs"], law["rhs"]
    lean_args = args if args is not None else {var: var for var in law["variables"]}
    orientations = (("lhs", "rhs"), ("rhs", "lhs"))[:2 if both_orientations else 1]

    def match(eq1: dict[str, Any]) -> LawMatch | None:
        for index, (left, right) in enumerate(orientations):
            subst: dict[str, Term] = {}
            if not match_term(lhs_pattern, eq1[left], subst):
                continue
            if not match_term(rhs_pattern, eq1[right], subst):
                continue
            bound: dict[str, str] = {}
            for var, image in subst.items():
                arg = lean_args[var]
                if image[0] != "var" or bound.setdefault(str(image[1]), arg) != arg:
                    break
            else:
                if distinct and len(bound) != len(subst):
                    continue
                if set(bound) != set(eq1["variables"]):
                    continue
                call = call_expression_lean_args(eq1["variables"], bound)
                return LawMatch(symm.format(call) if index else call, bound)
        return None

    return match


def law_have(hypothesis: str, binders: str, law: str, call: str) -> str:
    return (f"  have {hypothesis} : ∀ {binders} : G, {law} := by\n"
            f"    intro {binders}\n"
            f"    exact {call}\n")


def submission_certificate(
    eq2_vars: list[str],
    closing: str,
    prelude: str = "",
) -> str:
    intro_vars = " ".join(eq2_vars)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        + prelude
        + (f"  intro {intro_vars}\n" if intro_vars else "")
        + closing
    )


def singleton_from_1111_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M y y\n"
        "    let v1 := M y v0\n"
        f"    have h2 := {source_name} y y v1\n"
        "    have h3 := R x\n"
        "    let v4 := M x v0\n"
        f"    have h5 := {source_name} y x v4\n"
        "    have h6 := S h5\n"
        "    let v7 := M v4 x\n"
        "    let v8 := M (M x (M v7 v7)) x\n"
        "    let v9 := M x x\n"
        "    let v10 := M y v9\n"
        f"    have h11 := {source_name} x y v10\n"
        "    let v12 := M x v9\n"
        f"    have h13 := {source_name} x x v12\n"
        "    have h14 := S h13\n"
        "    let v15 := M v12 x\n"
        "    let v16 := M (M x (M v15 v15)) x\n"
        f"    exact T (T (T ({source_name} x x v8) (C h3 (T (T (T (C (T (T (T ({source_name} v12 x v16) (C h3 (T (T (T (C h14 (R v16)) (S ({source_name} v15 x x))) (C (C h3 (C h13 h13)) h3)) (C (T (T (C h3 (C h14 h14)) ({source_name} v12 x x)) (C h3 (C (T h14 h11) h11))) h3)))) (S ({source_name} (M y (M v10 v10)) x x))) (S h11)) (R v8)) (S ({source_name} v7 x x))) (C (C h3 (C h5 h5)) h3)) (C (T (T (C h3 (C h6 h6)) ({source_name} v4 x y)) (C h3 (C (T h6 h2) h2))) h3)))) (S ({source_name} (M y (M v1 v1)) x x))) (S h2)\n"
    )


def singleton_from_1283_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x x\n"
        "    let v1 := M (M v0 x) x\n"
        "    let v2 := M v1 v1\n"
        "    let v3 := M v2 y\n"
        "    let v4 := M (M v3 v3) x\n"
        "    let v5 := M (M (M y y) y) y\n"
        "    have h6 := R x\n"
        f"    have h7 := {source_name} x v1 x\n"
        "    have h8 := S h7\n"
        "    have h9 := R v2\n"
        "    let v10 := M (M v0 y) y\n"
        f"    have h11 := {source_name} x v10 y\n"
        "    have h12 := S h11\n"
        "    have h13 := T (C (T (C (C (T h12 h7) h12) h6) (C (C h9 h7) h6)) h6) (C (C (C h8 h8) h6) h6)\n"
        "    let v14 := M v10 v10\n"
        f"    have h15 := {source_name} v14 x x\n"
        "    have h16 := R v4\n"
        "    have h17 := R y\n"
        "    have h18 := S h15\n"
        "    have h19 := T (C (C (C h7 h7) h6) h6) (C (T (C (C h9 h8) h6) (C (C (T h8 h11) h11) h6)) h6)\n"
        f"    exact T (T (T ({source_name} x y x) (C h17 (T ({source_name} v1 v4 v1) (C h16 (T (T (C (T (T (C h8 h19) h18) h12) h19) h18) h12))))) (C h17 (T (C h16 (T (T h11 h15) (C (T (T h11 ({source_name} v14 y x)) (C ({source_name} y v5 y) h13)) h13))) (S ({source_name} v5 v4 v1))))) (S ({source_name} y y y))\n"
    )


def singleton_from_1906_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M y y\n"
        f"    have h1 := {source_name} y (M x v0) y\n"
        "    have h2 := S h1\n"
        "    have h3 := R v0\n"
        f"    have h4 := {source_name} y x y\n"
        "    have h5 := C h4 h3\n"
        f"    have h6 := S ({source_name} (M y v0) y x)\n"
        "    have h7 := R x\n"
        "    let v8 := M y x\n"
        f"    have h9 := {source_name} y (M x v8) x\n"
        "    have h10 := R v8\n"
        f"    have h11 := {source_name} y x x\n"
        f"    have h12 := {source_name} v8 y y\n"
        "    have h13 := T (T (S h12) (C (T h9 (C (S h11) h10)) h7)) (C (T (T (T (C h11 h10) (S h9)) h1) (C (S h4) h3)) h7)\n"
        "    have h14 := R y\n"
        "    have h15 := C (C h14 h13) h13\n"
        "    let v16 := M v8 y\n"
        f"    have h17 := {source_name} (M y v16) y v16\n"
        "    let v18 := M x x\n"
        "    have h19 := R v18\n"
        f"    have h20 := {source_name} x x x\n"
        f"    have h21 := {source_name} x (M x v18) x\n"
        "    have h22 := T h21 (C (S h20) h19)\n"
        "    let v23 := M x y\n"
        f"    have h24 := {source_name} x (M x v23) y\n"
        "    have h25 := R v23\n"
        f"    have h26 := {source_name} x x y\n"
        "    have h27 := S h21\n"
        "    have h28 := C h20 h19\n"
        "    let v29 := M v18 x\n"
        f"    have h30 := {source_name} v18 y x\n"
        f"    exact T (T (T (T (T (T (T (T (T (T h21 (C (T (C (T h28 h27) h19) (C h7 h30)) h30)) (S ({source_name} (M y v29) x v29))) (C h14 (T (C (T (T (C h22 h7) (C (T (T (T h28 h27) h24) (C (S h26) h25)) h7)) (C (T (C h26 h25) (S h24)) h22)) h22) (S ({source_name} x x v18))))) h12) (C (T (T (T (T h17 h15) h6) h5) h2) (R v16))) h17) h15) h6) h5) h2\n"
    )


def singleton_from_1773_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        f"    have h0 := S ({source_name} y x y)\n"
        "    have h1 := R x\n"
        "    let v2 := M x y\n"
        "    have h3 := R v2\n"
        f"    have h4 := {source_name} x x y\n"
        "    let v5 := M x x\n"
        "    let v6 := M v5 x\n"
        "    let v7 := M v2 x\n"
        f"    exact T (T h4 (C h3 (C (T (T ({source_name} v5 y y) (C (R (M y y)) (C (T (T ({source_name} (M y v5) x y) (C h3 (C (T (T (T (C ({source_name} x x x) (C ({source_name} y x x) (R v5))) (S ({source_name} v7 v5 v6))) ({source_name} v7 v2 v6)) (C (S h4) (C h0 h3))) h1))) (S ({source_name} (M y v2) x y))) (R y)))) (S ({source_name} v2 y y))) h1))) h0\n"
    )


def singleton_from_deep_repeat_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x (M y (M y x))\n"
        "    let v1 := M x (M v0 (M v0 x))\n"
        "    have h2 := R v1\n"
        f"    exact T (T (T ({source_name} x v1 v1) (C h2 (C h2 (T (C (R x) (S ({source_name} v0 x x))) (S ({source_name} y x x)))))) (C h2 (C h2 (T ({source_name} y y x) (C (R y) ({source_name} v0 y x)))))) (S ({source_name} y v1 v1))\n"
    )


def singleton_from_sandwich_repeat_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x x\n"
        "    have h1 := R x\n"
        f"    exact T (T ({source_name} x x x) (C h1 (C (C h1 ({source_name} v0 y x)) h1))) (S ({source_name} y x (M (M y (M v0 x)) y)))\n"
    )


_REPEATED_PREFIX_PRODUCT_LAW = "x = (y ◇ (y ◇ (x ◇ x))) ◇ z"
_repeated_prefix_product = law_matcher(_REPEATED_PREFIX_PRODUCT_LAW)


def repeated_prefix_product_constancy_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    found = _repeated_prefix_product(eq1)
    if found is None or eq2["lhs"][0] != "op" or eq2["rhs"][0] != "op":
        return None
    body = law_have("hsource", "x y z", _REPEATED_PREFIX_PRODUCT_LAW, found.call) + (
        "  have hconst : ∀ a b c d : G, a ◇ b = c ◇ d := by\n"
        "    intro a\n"
        "    repeat intro\n"
        "    try { rw [hsource a, ← hsource] }\n"
        "    try { rw [hsource a a, ← hsource] }\n"
    )
    return "true:repeated_prefix_product_constancy", submission_certificate(
        eq2["variables"], "  exact hconst _ _ _ _\n", body)


def singleton_from_reverse_deep_repeat_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M (M (M x x) x) x\n"
        "    let v1 := M (M (M x v0) v0) x\n"
        "    have h2 := R v1\n"
        f"    exact T (T (T ({source_name} x v1 v1) (C (C (T (C (S ({source_name} v0 x x)) (R x)) (S ({source_name} x x x))) h2) h2)) (C (C (T ({source_name} x x y) (C ({source_name} v0 x y) (R y))) h2) h2)) (S ({source_name} y v1 v1))\n"
    )


def singleton_from_outer_sandwich_block(source_name: str) -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x x\n"
        "    have h1 := R x\n"
        f"    exact T (T ({source_name} x x x) (C (C h1 (C ({source_name} v0 y x) h1)) h1)) (S ({source_name} y x (M y (M (M x v0) y))))\n"
    )


def singleton_from_forked_square_block() -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x y\n"
        "    let v1 := M x x\n"
        "    let v2 := M v1 v0\n"
        "    let v3 := M y y\n"
        "    have h4 := R v3\n"
        "    let v5 := M v1 v1\n"
        "    have h6 := hsource x v5 x\n"
        "    have h7 := S h6\n"
        "    let v8 := M v3 v3\n"
        "    have h9 := hsource x v5 (M v3 (M y x))\n"
        "    have h10 := S h9\n"
        "    have h11 := hsource y x x\n"
        "    have h12 := R v1\n"
        "    have h13 := R v5\n"
        "    have h14 := C h13 (C h12 h11)\n"
        "    have h15 := R y\n"
        "    have h16 := C h13 (C h12 (S h11))\n"
        "    have h17 := hsource x v5 v5\n"
        "    have h18 := S h17\n"
        "    have h19 := hsource x x x\n"
        "    have h20 := C h13 (C h12 h19)\n"
        "    have h21 := R x\n"
        "    have h22 := hsource v1 y x\n"
        "    have h23 := S h22\n"
        "    have h24 := C h12 (S h19)\n"
        "    have h25 := C h13 h24\n"
        "    have h26 := T h17 h25\n"
        "    have h27 := C h15 h26\n"
        "    have h28 := T h27 h23\n"
        "    have h29 := hsource x v2 y\n"
        "    have h30 := S h29\n"
        "    have h31 := C h30 h21\n"
        "    have h32 := R (M v2 v2)\n"
        "    have h33 := C h32 h30\n"
        "    have h34 := C (T h7 h29) h29\n"
        "    have h35 := R (M v5 v5)\n"
        "    have h36 := C h35 h7\n"
        "    have h37 := C (T (T h20 h18) h6) h6\n"
        "    have h38 := T h20 h18\n"
        "    have h39 := R (M v5 (M v1 x))\n"
        "    have h40 := C h39 h38\n"
        "    have h41 := T (T h7 h17) h25\n"
        "    have h42 := C h41 h7\n"
        "    have h43 := C h35 h6\n"
        "    have h44 := T h30 h6\n"
        "    have h45 := C h44 h30\n"
        "    have h46 := C h32 h29\n"
        "    have h47 := C h29 h21\n"
        "    have h48 := C h39 h26\n"
        "    have h49 := T (T (T (C (T (T (T (T (T (T (T h27 h23) h47) h46) h45) h43) h42) h48) (T (T (T (T (T (T h27 h23) h47) h46) h45) h43) h42)) (C (T h40 h37) (T h37 h36))) (C (T h36 h34) (T h34 h33))) (C (T h33 h31) h31)\n"
        "    have h50 := C h15 h38\n"
        "    have h51 := T h22 h50\n"
        "    have h52 := C h51 h21\n"
        "    have h53 := T (T (T (C (T h47 h46) h47) (C (T h45 h43) (T h46 h45))) (C (T h42 h48) (T h43 h42))) (C (T (T (T (T (T (T (T h40 h37) h36) h34) h33) h31) h22) h50) (T (T (T (T (T (T h37 h36) h34) h33) h31) h22) h50))\n"
        "    exact T (T (hsource x v1 v5) (C h12 (T (T (T (T (T (T h24 h52) (C h28 h6)) (S (hsource v1 v1 v1))) (hsource v1 v0 v1)) (C (T (T (T (T (T (T (T (C h29 h15) (C h44 h15)) (C h41 h15)) (C (T (T (T (T h20 h18) h9) h16) (C h53 (C h51 h15))) h15)) (C (T (T (T (T (T (C h49 (C h28 h15)) h14) h10) h17) h25) (C h53 h52)) h15)) (C (T (T (T (T (C h49 (C h28 h21)) h20) h18) h9) h16) h15)) (C (T h14 h10) (T (hsource y v8 v5) (C (R v8) (C h4 (S (hsource x y x))))))) (S (hsource v3 x x))) h7)) (C h4 (hsource x y y))))) (S (hsource y v1 v2))\n"
    )


def singleton_from_crossed_pair_block() -> str:
    return (
        "  have hall : ∀ x y : G, x = y := by\n"
        "    intro x y\n"
        "    let v0 := M x y\n"
        "    let v1 := M y x\n"
        "    have h2 := R y\n"
        "    let v3 := M x x\n"
        "    have h4 := hsource x x (M v3 x)\n"
        "    have h5 := hsource x x x\n"
        "    have h6 := R v3\n"
        "    have h7 := T (C h6 h5) (S h4)\n"
        "    have h8 := hsource y x (M v0 x)\n"
        "    have h9 := hsource x y x\n"
        "    have h10 := R v0\n"
        "    have h11 := T (C h10 h9) (S h8)\n"
        "    have h12 := T h4 (C h6 (S h5))\n"
        "    have h13 := T h8 (C h10 (S h9))\n"
        "    have h14 := hsource x y (M v1 x)\n"
        "    have h15 := hsource y x x\n"
        "    have h16 := R v1\n"
        "    have h17 := T (C h16 h15) (S h14)\n"
        "    have h18 := R (M y v1)\n"
        "    have h19 := T h14 (C h16 (S h15))\n"
        "    have h20 := C h2 h7\n"
        "    have h21 := C h11 h12\n"
        "    have h22 := C h13 h17\n"
        "    let v23 := M y y\n"
        "    have h24 := hsource y y (M v23 x)\n"
        "    have h25 := S h24\n"
        "    have h26 := hsource y y x\n"
        "    have h27 := R v23\n"
        "    have h28 := C h27 h26\n"
        "    have h29 := T h28 h25\n"
        "    have h30 := C h29 h19\n"
        "    have h31 := R x\n"
        "    have h32 := C h27 (S h26)\n"
        "    have h33 := hsource y v23 v23\n"
        "    have h34 := S h33\n"
        "    have h35 := hsource v23 y x\n"
        "    have h36 := T h24 h32\n"
        "    have h37 := C h13 h7\n"
        "    have h38 := C h2 h12\n"
        "    have h39 := R (M y v23)\n"
        "    have h40 := C h29 (T (C h39 (T (T (T h38 h37) (C h11 h19)) (C h36 h17))) (S h35))\n"
        "    have h41 := hsource y v23 v1\n"
        "    have h42 := C h36 (T (T (T (T h28 h25) h41) h40) (C (T h41 h40) h27))\n"
        "    have h43 := hsource y v1 v3\n"
        "    have h44 := hsource v1 y x\n"
        "    have h45 := T (C h19 (T h44 (C h18 (T (T (T (C h17 h19) (C h12 h17)) (C h7 h12)) (C h31 h7))))) (S h43)\n"
        "    have h46 := C h45 h36\n"
        "    have h47 := C h12 h7\n"
        "    have h48 := C h31 h12\n"
        "    have h49 := C h17 (T (C h18 (T (T (T h48 h47) (C h7 h19)) (C h19 h17))) (S h44))\n"
        "    have h50 := S h41\n"
        "    have h51 := C h36 (T h35 (C h39 (T (T (T h30 h22) h21) h20)))\n"
        "    have h52 := S (hsource v3 x x)\n"
        "    have h53 := T h48 h47\n"
        "    have h54 := C h7 (T (C (R (M x v3)) h53) h52)\n"
        "    have h55 := hsource x v3 v3\n"
        "    exact T (T (T (T (T (T h55 h54) (C (T h55 h54) h53)) h52) (C h31 (T (hsource x v0 v1) (C h11 (T (C (R (M x v0)) (T h38 h37)) (S (hsource v0 x x))))))) (C h19 (T (C (T (T (T h43 h49) (hsource (M x v1) y x)) (C (T (T (T (T (C (T (T h33 (C h29 (T (T (T (T (C (T h51 h50) h27) h51) h50) h24) h32))) (C (T h43 h49) h29)) h45) (C (T (T (T (T h46 h42) h34) h43) h49) h2)) h46) h42) h34) (T (T (T (T (C (T (T (T (T h46 h42) h34) h24) h32) h31) h30) h22) h21) h20))) (T (T (C h12 h2) (C h7 h13)) (C h19 h11))) (C h18 (T (T (C h17 h13) (C h12 h11)) (C h7 h2)))))) (S (hsource y v1 v0))\n"
    )


def collapse_family_route(
    label: str,
    hypothesis: str,
    law: str,
    block: str,
    *,
    binders: str = "x y z",
    pattern: str | None = None,
    args: dict[str, str] | None = None,
    distinct: bool = False,
    symm: str = "({}).symm",
) -> Callable[[dict[str, Any], dict[str, Any]], tuple[str, str] | None]:
    match = law_matcher(pattern or law, args, distinct=distinct, symm=symm)

    def route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
        found = match(eq1)
        if found is None:
            return None
        body = law_have(hypothesis, binders, law, found.call) + block
        return label, submission_certificate(
            eq2["variables"], "  exact hall _ _\n",
            right_projection_local_helpers() + body)

    route.match = match
    route.__name__ = route.__qualname__ = f"{label.split(':')[1]}_route"
    return route


nested_square_singleton_route = collapse_family_route(
    "true:nested_square_singleton", "h1111",
    "x = y ◇ ((y ◇ (x ◇ x)) ◇ z)",
    singleton_from_1111_block("h1111"))
tail_square_singleton_route = collapse_family_route(
    "true:tail_square_singleton", "h1283",
    "x = y ◇ (((x ◇ x) ◇ z) ◇ z)",
    singleton_from_1283_block("h1283"),
    pattern="x = y ◇ (((x ◇ x) ◇ z) ◇ w)",
    args={"x": "x", "y": "y", "z": "z", "w": "z"})
paired_tail_singleton_route = collapse_family_route(
    "true:paired_tail_singleton", "h1906",
    "x = (y ◇ (x ◇ z)) ◇ (x ◇ z)",
    singleton_from_1906_block("h1906"),
    pattern="x = (y ◇ (x ◇ z)) ◇ (x ◇ w)",
    args={"x": "x", "y": "y", "z": "z", "w": "z"}, distinct=True)
wrapped_tail_singleton_route = collapse_family_route(
    "true:wrapped_tail_singleton", "h1773",
    "x = (y ◇ z) ◇ ((y ◇ x) ◇ y)",
    singleton_from_1773_block("h1773"),
    pattern="x = y ◇ ((z ◇ x) ◇ z)",
    args={"x": "x", "y": "(y ◇ z)", "z": "y"})
deep_repeat_singleton_route = collapse_family_route(
    "true:deep_repeat_singleton", "hsource",
    "x = y ◇ (z ◇ (x ◇ (x ◇ z)))",
    singleton_from_deep_repeat_block("hsource"))
sandwich_repeat_singleton_route = collapse_family_route(
    "true:sandwich_repeat_singleton", "hsource",
    "x = y ◇ ((y ◇ (x ◇ z)) ◇ y)",
    singleton_from_sandwich_repeat_block("hsource"))
reverse_deep_repeat_singleton_route = collapse_family_route(
    "true:reverse_deep_repeat_singleton", "hsource",
    "x = (((y ◇ x) ◇ x) ◇ y) ◇ z",
    singleton_from_reverse_deep_repeat_block("hsource"))
outer_sandwich_singleton_route = collapse_family_route(
    "true:outer_sandwich_singleton", "hsource",
    "x = (y ◇ ((z ◇ x) ◇ y)) ◇ y",
    singleton_from_outer_sandwich_block("hsource"))
forked_square_singleton_route = collapse_family_route(
    "true:forked_square_singleton", "hsource",
    "x = y ◇ ((x ◇ x) ◇ (x ◇ z))",
    singleton_from_forked_square_block(), symm="S ({})")
crossed_pair_singleton_route = collapse_family_route(
    "true:crossed_pair_singleton", "hsource",
    "x = (y ◇ x) ◇ ((x ◇ y) ◇ z)",
    singleton_from_crossed_pair_block(), symm="S ({})")


def square_product_basis_goal(eq2: dict[str, Any]) -> tuple[Term, Term, Term, bool] | None:
    for swapped, square_side, product_side in (
        (False, eq2["lhs"], eq2["rhs"]),
        (True, eq2["rhs"], eq2["lhs"]),
    ):
        if square_side[0] != "op" or square_side[1] != square_side[2]:
            continue
        if product_side[0] != "op":
            continue
        return square_side[1], product_side[1], product_side[2], swapped
    return None


def square_product_from_double_tail_block() -> str:
    return (
        "  have h41 : ∀ x y z : G, x ◇ x = y ◇ z := by\n"
        "    intro x y z\n"
        "    let v0 := M x x\n"
        "    have h1 := R y\n"
        "    have h2 := S (hsource (M v0 z) y x)\n"
        "    have h3 := hsource v0 z z\n"
        "    have h4 := R v0\n"
        "    let v5 := M y z\n"
        "    have h6 := hsource z z v5\n"
        "    have h7 := R z\n"
        "    have h8 := hsource z z y\n"
        "    have h9 := S h8\n"
        "    have h10 := hsource v5 z x\n"
        "    have h11 := R v5\n"
        "    have h12 := hsource x z x\n"
        "    have h13 := S h12\n"
        "    have h14 := R x\n"
        "    let v15 := M x z\n"
        "    have h16 := hsource x x v15\n"
        "    have h17 := C (T h16 (C h13 h14)) h14\n"
        "    have h18 := hsource x x x\n"
        "    have h19 := C (S h18) h14\n"
        "    have h20 := hsource x x v0\n"
        "    have h21 := hsource v5 x x\n"
        "    have h22 := hsource z x v5\n"
        "    have h23 := hsource v0 x z\n"
        "    have h24 := T (T (T (T h20 h19) h23) (C (C (T (T (T h22 (C (T (C (T (T h21 (C (C (T (T (T h20 h19) h17) h13) h11) h11)) (S h10)) h7) h9) h7)) (C h8 h7)) (S h6)) h4) h4)) (S h3)\n"
        "    have h25 := C (C (T (T (T (T (T (T h20 h19) h17) h13) (hsource x z y)) (C (C (hsource y z x) h14) h14)) (S (hsource x y (M v15 y)))) h24) h24\n"
        "    have h26 := hsource v0 x x\n"
        "    exact T (T (T (T (T (T (T (hsource x x (M v5 x)) (C (S (hsource x x v5)) h14)) h26) h25) h2) (C (T (T h3 (C (C (T (T (T h6 (C h9 h7)) (C (T h8 (C (T (T h10 (C (C (T (T (T h12 (C (T (C h12 h14) (S h16)) h14)) (C h18 h14)) (S h20)) h11) h11)) (S h21)) h7)) h7)) (S h22)) h4) h4)) (S h23)) h1)) (C (T (T h26 h25) h2) h1)) (S (hsource y z v0))\n"
    )


_DOUBLE_TAIL_SQUARE_PRODUCT_LAW = "x ◇ y = ((z ◇ y) ◇ x) ◇ x"
_double_tail_square_product = law_matcher(
    _DOUBLE_TAIL_SQUARE_PRODUCT_LAW, symm="S ({})")


def double_tail_square_product_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    found = _double_tail_square_product(eq1)
    goal = square_product_basis_goal(eq2)
    if found is None or goal is None:
        return None
    square_arg, product_left, product_right, goal_swapped = goal
    proof_expr = (
        f"h41 {term_to_lean(square_arg)} {term_to_lean(product_left)} {term_to_lean(product_right)}"
    )
    if goal_swapped:
        proof_expr = f"S ({proof_expr})"
    body = (law_have("hsource", "x y z", _DOUBLE_TAIL_SQUARE_PRODUCT_LAW, found.call)
            + square_product_from_double_tail_block())
    return "true:double_tail_square_product", submission_certificate(
        eq2["variables"], f"  exact {proof_expr}\n",
        right_projection_local_helpers() + body)


_middle_self_collapse = law_matcher("a = (b ◇ a) ◇ c")


def middle_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _middle_self_collapse(eq1)
    if found is None:
        return None
    call = found.call
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


_front_double_self_collapse = law_matcher("a = b ◇ (a ◇ (a ◇ c))")


def front_double_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _front_double_self_collapse(eq1)
    if found is None:
        return None
    call = found.call
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


_alternating_front_self_collapse = law_matcher("a = b ◇ (a ◇ (b ◇ c))")


def alternating_front_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _alternating_front_self_collapse(eq1)
    if found is None:
        return None
    root, lead = found.var("a"), found.var("b")
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


_mirrored_alternating_front_self_collapse = law_matcher("a = b ◇ (a ◇ (c ◇ b))")


def mirrored_alternating_front_self_collapse_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _mirrored_alternating_front_self_collapse(eq1)
    if found is None:
        return None
    call = found.call
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


_sandwich_left_projection = law_matcher("a = a ◇ (b ◇ (c ◇ b))")


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
    found = _sandwich_left_projection(eq1)
    if found is None:
        return None
    proof_expr = projection_proof_expr_from_law(eq2, "left", hypothesis_name="hleft")
    if proof_expr is None:
        return None
    call = found.call
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


_left_row_constancy = law_matcher("a = ((a ◇ b) ◇ (b ◇ c)) ◇ d")


@lru_cache(maxsize=None)
def left_row_constancy_key(term: Term) -> Term:
    if term[0] == "var":
        return term
    return "op", left_row_constancy_key(term[1]), "_"


def left_row_constancy_term_proof(src: Term, dst: Term, *, hypothesis_name: str = "hrow") -> str | None:
    if src == dst:
        return "rfl"
    if left_row_constancy_key(src) != left_row_constancy_key(dst):
        return None
    if src[0] != "op" or dst[0] != "op":
        return None
    left_proof = left_row_constancy_term_proof(src[1], dst[1], hypothesis_name=hypothesis_name)
    if left_proof is None:
        return None
    proof_expr: str | None = None
    left_dst = dst[1]
    if left_proof != "rfl":
        proof_expr = f"congrArg (fun t => t ◇ {term_to_lean(src[2])}) ({left_proof})"
    row_step = f"{hypothesis_name} {term_to_lean(left_dst)} {term_to_lean(src[2])} {term_to_lean(dst[2])}"
    return chain_trans(proof_expr, row_step)


def left_row_constancy_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _left_row_constancy(eq1)
    if found is None:
        return None
    proof_expr = left_row_constancy_term_proof(eq2["lhs"], eq2["rhs"])
    if proof_expr is None:
        return None
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c d : G, a = ((a ◇ b) ◇ (b ◇ c)) ◇ d := by\n"
        "    intro a b c d\n"
        f"    exact {call}\n"
        "  have hrow : ∀ a b c : G, a ◇ b = a ◇ c := by\n"
        "    intro a b c\n"
        "    exact (hsrc (a ◇ b) (b ◇ a) a c).trans (congrArg (fun t => t ◇ c) (hsrc a b a ((b ◇ a) ◇ a))).symm\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:left_row_constancy", code


_product_constancy = law_matcher("a ◇ b = (b ◇ b) ◇ (c ◇ d)")


def product_constancy_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _product_constancy(eq1)
    if found is None or eq2["lhs"][0] != "op" or eq2["rhs"][0] != "op":
        return None
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    lhs_left = term_to_lean(eq2["lhs"][1])
    lhs_right = term_to_lean(eq2["lhs"][2])
    rhs_left = term_to_lean(eq2["rhs"][1])
    rhs_right = term_to_lean(eq2["rhs"][2])
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c d : G, a ◇ b = (b ◇ b) ◇ (c ◇ d) := by\n"
        "    intro a b c d\n"
        f"    exact {call}\n"
        "  have hprod : ∀ a b c d : G, a ◇ b = c ◇ d := by\n"
        "    intro a b c d\n"
        "    exact ((hsrc a b d d).trans (hsrc (b ◇ b) (d ◇ d) d d)).trans ((hsrc c d d d).trans (hsrc (d ◇ d) (d ◇ d) d d)).symm\n"
        f"{intro_line}"
        f"  exact hprod {lhs_left} {lhs_right} {rhs_left} {rhs_right}\n"
    )
    return "true:product_constancy", code


_square_twist_comm = law_matcher("a ◇ b = (b ◇ b) ◇ a")


@lru_cache(maxsize=None)
def commutative_term_key(term: Term) -> Term:
    if term[0] == "var":
        return term
    left = commutative_term_key(term[1])
    right = commutative_term_key(term[2])
    if repr(right) < repr(left):
        left, right = right, left
    return "op", left, right


_TERM_CACHE_FUNCS = (
    term_vars_tuple,
    term_size,
    term_depth,
    term_to_lean,
    dual_term,
    term_subterms_tuple,
    boundary_vars,
    subterm_paths_tuple,
    term_at_path,
    replace_subterm,
    context_to_lean,
    left_row_constancy_key,
    commutative_term_key,
)


def clear_term_caches() -> None:
    for cached in _TERM_CACHE_FUNCS:
        cached.cache_clear()


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
    found = _square_twist_comm(eq1)
    if found is None or commutative_term_key(eq2["lhs"]) != commutative_term_key(eq2["rhs"]):
        return None
    call = found.call
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


def projection_from_lemma_term_proof(
    term: Term,
    side: str,
    *,
    hypothesis_name: str,
) -> tuple[str, str] | None:
    if term[0] == "var":
        return "rfl", str(term[1])
    if term[0] != "op":
        return None
    projected = term[1] if side == "left" else term[2]
    step = f"{hypothesis_name} {term_to_lean(term[1])} {term_to_lean(term[2])}"
    rest = projection_from_lemma_term_proof(projected, side, hypothesis_name=hypothesis_name)
    if rest is None:
        return None
    rest_proof, target_var = rest
    if rest_proof != "rfl":
        step = f"({step}).trans ({rest_proof})"
    return step, target_var


def projection_from_lemma_goal_proof(eq2: dict[str, Any], side: str, *, hypothesis_name: str) -> str | None:
    left = projection_from_lemma_term_proof(eq2["lhs"], side, hypothesis_name=hypothesis_name)
    right = projection_from_lemma_term_proof(eq2["rhs"], side, hypothesis_name=hypothesis_name)
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


_tail_square_right_projection = law_matcher(
    "x = ((y ◇ z) ◇ z) ◇ x", {"x": "x", "y": "(y ◇ z)", "z": "z"})


_nested_tail_right_projection = law_matcher(
    "x = ((y ◇ (z ◇ w)) ◇ w) ◇ x",
    {"x": "x", "y": "y", "z": "x", "w": "z"}, distinct=True)


_left_pair_tail_right_projection = law_matcher("x = ((y ◇ z) ◇ (y ◇ x)) ◇ y")


_nested_left_projection = law_matcher(
    "x = x ◇ (y ◇ ((y ◇ z) ◇ w))",
    {"x": "x", "y": "y", "z": "x", "w": "z"}, distinct=True)


_right_nested_tail_left_projection = law_matcher(
    "x = x ◇ ((y ◇ (z ◇ w)) ◇ w)",
    {"x": "x", "y": "y", "z": "z", "w": "z"}, distinct=True)


_bracket_tail_left_projection = law_matcher(
    "x = x ◇ (((y ◇ z) ◇ w) ◇ u)",
    {"x": "x", "y": "y", "z": "z", "w": "z", "u": "z"}, distinct=True)


_pair_square_left_projection = law_matcher(
    "x = x ◇ ((y ◇ z) ◇ (w ◇ u))",
    {"x": "x", "y": "y", "z": "z", "w": "y", "u": "y"}, distinct=True)


_sandwich_tail_right_projection = law_matcher("x = (((y ◇ x) ◇ z) ◇ y) ◇ x")


def right_projection_local_helpers() -> str:
    return (
        "  let T := @Eq.trans\n"
        "  let S := @Eq.symm\n"
        "  let R := @Eq.refl\n"
        "  let M := @Magma.op\n"
        "  have C : {a b c d : G} -> a = b -> c = d -> a ◇ c = b ◇ d := by\n"
        "    intro a b c d h1 h2\n"
        "    rw [h1, h2]\n"
    )


def right_projection_from_3218_block() -> str:
    return (
        "  have hproj : ∀ x y : G, x = y ◇ x := by\n"
        "    intro x y\n"
        "    let v0 := M y x\n"
        "    have h1 := R y\n"
        "    have h2 := S (h3218 v0 v0 v0)\n"
        "    have h3 := R v0\n"
        "    have h4 := S (h3218 v0 v0 x)\n"
        "    have h5 := C (h3218 x y x) h3\n"
        "    have h6 := C (C (C (T h5 h4) h3) h3) h3\n"
        "    have h7 := h3218 v0 x v0\n"
        "    exact T (h3218 x y y) (C (T (C (C (C (T (h3218 y x v0) (C (T (C (T (T (T (C (T (T (T h5 h4) h7) h6) h3) h2) h7) h6) h3) h2) h1)) h1) h1) h1) (S (h3218 y v0 y))) (R x))\n"
    )


def left_projection_from_641_block(source_name: str) -> str:
    return (
        "  have hproj : ∀ x y : G, x = x ◇ y := by\n"
        "    intro x y\n"
        "    let v0 := M x y\n"
        f"    have h1 := {source_name} y x (M (M v0 x) x)\n"
        f"    have h2 := {source_name} x v0 x\n"
        "    have h3 := R y\n"
        "    have h4 := T (C h3 h2) (S h1)\n"
        "    have h5 := R x\n"
        f"    have h6 := {source_name} y v0 y\n"
        "    have h7 := C h3 (S h2)\n"
        f"    exact T (T ({source_name} x y (M (M y y) y)) (C h5 (T (C (T h1 h7) (C h4 (C (T (C h3 (T (T h1 h7) (C h6 h5))) (C h3 (C (S h6) h5))) h3))) (S ({source_name} (M y x) y y))))) (C h5 h4)\n"
    )


def left_projection_from_1065_block(source_name: str) -> str:
    return (
        "  have hproj : ∀ x y : G, x = x ◇ y := by\n"
        "    intro x y\n"
        f"    have h0 := S ({source_name} y x x)\n"
        "    let v1 := M (M x (M x x)) x\n"
        f"    exact T ({source_name} x y v1) (C (R x) (T (C (T (C (R y) (S ({source_name} v1 x x))) h0) (R v1)) h0))\n"
    )


def left_projection_from_1268_block(source_name: str) -> str:
    return (
        "  have hproj : ∀ x y : G, x = x ◇ y := by\n"
        "    intro x y\n"
        f"    have h0 := S ({source_name} y x x)\n"
        "    let v1 := M (M (M x x) x) x\n"
        "    have h2 := R v1\n"
        f"    exact T ({source_name} x y v1) (C (R x) (T (C (T (C h0 h2) h0) h2) h0))\n"
    )


def left_projection_from_857_block(source_name: str) -> str:
    return (
        "  have hproj : ∀ x y : G, x = x ◇ y := by\n"
        "    intro x y\n"
        "    let v0 := M x x\n"
        "    let v1 := M v0 v0\n"
        f"    have h2 := {source_name} v0 x x\n"
        "    let v3 := M x y\n"
        "    let v4 := M y y\n"
        "    let v5 := M y v3\n"
        f"    exact T ({source_name} x y v3) (C (R x) (T (T (T (C (R v5) (T ({source_name} v4 y y) (C ({source_name} v4 x x) (R (M v4 v4))))) (S ({source_name} v5 v4 v1))) (C (R y) (T ({source_name} v3 x x) (C (R v3) (T (C (R v0) (T h2 (C h2 (R v1)))) (S ({source_name} v0 v0 v1))))))) (S ({source_name} y x y))))\n"
    )


def right_projection_from_2927_block() -> str:
    return (
        "  have hproj : ∀ x y : G, x = y ◇ x := by\n"
        "    intro x y\n"
        "    have h0 := R x\n"
        "    let v1 := M y x\n"
        "    have h2 := h2927 y (M x (M x v1)) x\n"
        "    have h3 := S h2\n"
        "    have h4 := R y\n"
        "    have h5 := h2927 x x v1\n"
        "    have h6 := C h5 h4\n"
        "    have h7 := T h6 h3\n"
        "    have h8 := C (S h5) h4\n"
        "    have h9 := h2927 y v1 y\n"
        "    have h10 := S h9\n"
        "    have h11 := T (T (C h0 h10) h6) h3\n"
        "    have h12 := C h11 h4\n"
        "    have h13 := T (T h2 h8) (C h0 h9)\n"
        "    have h14 := C h13 h7\n"
        "    have h15 := T h2 h8\n"
        "    have h16 := C h11 h15\n"
        "    have h17 := C h13 h4\n"
        "    have h18 := C h4 h10\n"
        "    have h19 := C h4 h9\n"
        "    exact T (T (h2927 x (M y y) y) (C (T (T (T (T (C (T (C h19 h7) (C (T (T h18 h17) h16) h4)) h4) (C (T (C (T (T h14 h12) h19) h4) (C (T (T (T (T (T h18 h17) h16) (C (T (T h2 h8) (C h0 h15)) h7)) (h2927 (M (M x (M x y)) y) y x)) (C (C (C h4 (S (h2927 x x y))) h0) (T (T (C (T (T (C h0 h7) h6) h3) h15) h14) h12))) h4)) h4)) (S (h2927 y (M v1 x) y))) h2) h8) h0)) (C h7 h0)\n"
    )


def right_projection_from_3126_block(source_name: str) -> str:
    return (
        "  have hproj : ∀ x y : G, x = y ◇ x := by\n"
        "    intro x y\n"
        "    have h0 := R x\n"
        "    let v1 := M y x\n"
        "    let v2 := M v1 v1\n"
        f"    have h3 := {source_name} y v2 x\n"
        "    have h4 := R y\n"
        "    have h5 := R v2\n"
        f"    have h6 := {source_name} x y v1\n"
        "    let v7 := M v1 y\n"
        f"    have h8 := {source_name} y v7 x\n"
        "    have h9 := R v7\n"
        f"    have h10 := {source_name} x y y\n"
        "    let v11 := M v1 x\n"
        f"    have h12 := {source_name} y v11 x\n"
        "    have h13 := R v11\n"
        f"    have h14 := {source_name} x y x\n"
        "    let v15 := M (M (M x y) v1) x\n"
        f"    exact T (T (T (T ({source_name} x y v15) (C (T (T (T (C (C (C ({source_name} y x v1) h0) (R v15)) h4) (S ({source_name} y v15 x))) h12) (C (C (S h14) h13) h4)) h0)) (C (T (T (T (C (C h14 h13) h4) (S h12)) h8) (C (C (S h10) h9) h4)) h0)) (C (T (T (T (C (C h10 h9) h4) (S h8)) h3) (C (C (S h6) h5) h4)) h0)) (C (T (C (C h6 h5) h4) (S h3)) h0)\n"
    )


def right_projection_from_2788_block(source_name: str) -> str:
    return (
        "  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) = X0 := by\n"
        f"    exact ({source_name} X0 X1 X2).symm\n"
        "  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X3 := by\n"
        "    have hb : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X2 := eq9 X2 X0 X1\n"
        "    have hx : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X3 := eq9 X3 ((X0 ◇ X1) ◇ (X0 ◇ X2)) X0\n"
        "    exact (congrArg (fun t => (t ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) hb).symm.trans hx\n"
        "  have eq13 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := by\n"
        "    have hb : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = X2 := eq9 X2 X0 X1\n"
        "    have hx : ((X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := eq11 X0 X1 X2 X0\n"
        "    exact (congrArg (fun t => (X2 ◇ t) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) hb).symm.trans hx\n"
        "  have eq19 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := by\n"
        "    have h11 : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := eq11 X0 X1 (X0 ◇ X1) X2\n"
        "    have h9 : (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) = X0 ◇ (X0 ◇ X1)) := eq9 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X1) (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)\n"
        "    exact h9.symm.trans (congrArg (fun t => t ◇ (X0 ◇ X1)) h11)\n"
        "  have eq22 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by\n"
        "    have h19 : X1 ◇ (X1 ◇ X0) = (X1 ◇ X0) ◇ (X1 ◇ X0) := eq19 X1 X0 (X1 ◇ X0)\n"
        "    have h9 : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := eq9 X0 X1 X0\n"
        "    exact (congrArg (fun t => t ◇ X1) h19).trans h9\n"
        "  have eq25 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := by\n"
        "    have h19 : X0 ◇ (X0 ◇ X2) = (X0 ◇ X2) ◇ (X0 ◇ X2) := eq19 X0 X2 (X0 ◇ X2)\n"
        "    have h13 : ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := eq13 X0 X2 X2\n"
        "    exact (congrArg (fun t => (X2 ◇ X2) ◇ t) h19).trans h13\n"
        "  have eq33 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by\n"
        "    let P : G := X0 ◇ (X0 ◇ X1)\n"
        "    have hinner : P ◇ X0 = X1 := eq22 X1 X0\n"
        "    have hbase : (P ◇ (P ◇ X0)) ◇ P = X0 := eq22 X0 P\n"
        "    exact (congrArg (fun t => (P ◇ t) ◇ P) hinner).symm.trans hbase\n"
        "  have eq34 (X0 : G) : X0 ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by\n"
        "    let P : G := X0 ◇ (X0 ◇ X0)\n"
        "    have h22 : P ◇ X0 = X0 := eq22 X0 X0\n"
        "    have h33 : (P ◇ X0) ◇ P = X0 := eq33 X0 X0\n"
        "    exact (congrArg (fun t => t ◇ P) h22).symm.trans h33\n"
        "  have eq42 (X0 : G) : X0 ◇ (X0 ◇ X0) = X0 := by\n"
        "    have hstar : ∀ t : G, t ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by\n"
        "      intro t\n"
        "      exact (eq19 X0 (X0 ◇ X0) t).symm.trans (eq34 X0)\n"
        "    have hPP : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 :=\n"
        "      hstar (X0 ◇ (X0 ◇ X0))\n"
        "    have h22 := eq22 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))\n"
        "    have hrw := (congrArg\n"
        "      (fun t => ((X0 ◇ (X0 ◇ X0)) ◇ t) ◇ (X0 ◇ (X0 ◇ X0))) hPP).symm.trans h22\n"
        "    exact hrw.symm.trans (hstar ((X0 ◇ (X0 ◇ X0)) ◇ X0))\n"
        "  have eq43 (X0 : G) : X0 ◇ X0 = X0 := by\n"
        "    exact (congrArg (fun t => X0 ◇ t) (eq42 X0)).symm.trans (eq34 X0)\n"
        "  have hright : ∀ a b : G, a ◇ b = b := by\n"
        "    intro a b\n"
        "    have h19 : b ◇ (b ◇ b) = a ◇ (b ◇ b) := eq19 b b a\n"
        "    have hb : b ◇ (b ◇ b) = b := eq42 b\n"
        "    have hbb : b ◇ b = b := eq43 b\n"
        "    have hr : a ◇ (b ◇ b) = a ◇ b := congrArg (fun t => a ◇ t) hbb\n"
        "    exact hr.symm.trans (h19.symm.trans hb)\n"
    )


_RIGHT_PROJECTION_LEMMA = (
    "  have hright : ∀ a b : G, a ◇ b = b := by\n"
    "    intro a b\n"
    "    exact (hproj b a).symm\n"
)
_LEFT_PROJECTION_LEMMA = (
    "  have hleft : ∀ a b : G, a ◇ b = a := by\n"
    "    intro a b\n"
    "    exact (hproj a b).symm\n"
)


def projection_collapse_route(
    name: str,
    side: str,
    families: tuple[tuple[str, Any, str, str, str, bool], ...],
) -> Callable[[dict[str, Any], dict[str, Any]], tuple[str, str] | None]:
    def route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
        for label, match, hypothesis, law, block, helpers in families:
            found = match(eq1)
            if found is None:
                continue
            proof_expr = projection_from_lemma_goal_proof(
                eq2, side, hypothesis_name=f"h{side}")
            if proof_expr is None:
                return None
            prelude = right_projection_local_helpers() if helpers else ""
            return label, submission_certificate(
                eq2["variables"], f"  exact {proof_expr}\n",
                prelude + law_have(hypothesis, "x y z", law, found.call) + block)
        return None

    route.__name__ = route.__qualname__ = name
    return route


right_projection_collapse_route = projection_collapse_route(
    "right_projection_collapse_route", "right", (
        ("true:right_projection_collapse:tail_square", _tail_square_right_projection,
         "h3218", "x = (((y ◇ z) ◇ z) ◇ z) ◇ x",
         right_projection_from_3218_block() + _RIGHT_PROJECTION_LEMMA, True),
        ("true:right_projection_collapse:nested_tail", _nested_tail_right_projection,
         "h2927", "x = ((y ◇ (x ◇ z)) ◇ z) ◇ x",
         right_projection_from_2927_block() + _RIGHT_PROJECTION_LEMMA, True),
        ("true:right_projection_collapse:sandwich_tail", _sandwich_tail_right_projection,
         "h3126", "x = (((y ◇ x) ◇ z) ◇ y) ◇ x",
         right_projection_from_3126_block("h3126") + _RIGHT_PROJECTION_LEMMA, True),
        ("true:right_projection_collapse:left_pair_tail", _left_pair_tail_right_projection,
         "h2788", "x = ((y ◇ z) ◇ (y ◇ x)) ◇ y",
         right_projection_from_2788_block("h2788"), False),
    ))

nested_left_projection_route = projection_collapse_route(
    "nested_left_projection_route", "left", (
        ("true:nested_left_projection", _nested_left_projection,
         "h641", "x = x ◇ (y ◇ ((y ◇ x) ◇ z))",
         left_projection_from_641_block("h641") + _LEFT_PROJECTION_LEMMA, True),
    ))

specialized_left_projection_route = projection_collapse_route(
    "specialized_left_projection_route", "left", (
        ("true:left_projection_collapse:right_nested_tail", _right_nested_tail_left_projection,
         "h1065", "x = x ◇ ((y ◇ (z ◇ z)) ◇ z)",
         left_projection_from_1065_block("h1065") + _LEFT_PROJECTION_LEMMA, True),
        ("true:left_projection_collapse:bracket_tail", _bracket_tail_left_projection,
         "h1268", "x = x ◇ (((y ◇ z) ◇ z) ◇ z)",
         left_projection_from_1268_block("h1268") + _LEFT_PROJECTION_LEMMA, True),
        ("true:left_projection_collapse:pair_square", _pair_square_left_projection,
         "h857", "x = x ◇ ((y ◇ z) ◇ (y ◇ y))",
         left_projection_from_857_block("h857") + _LEFT_PROJECTION_LEMMA, True),
    ))


_derived_left_projection = law_matcher("a = a ◇ (b ◇ (a ◇ (b ◇ c)))")


def derived_left_projection_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _derived_left_projection(eq1)
    if found is None:
        return None
    left = projection_from_lemma_term_proof(eq2["lhs"], "left", hypothesis_name="hleft")
    right = projection_from_lemma_term_proof(eq2["rhs"], "left", hypothesis_name="hleft")
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
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = a ◇ (b ◇ (a ◇ (b ◇ c))) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hp : ∀ a b : G, a ◇ (b ◇ a) = a := by\n"
        "    intro a b\n"
        "    let T : G := a ◇ (b ◇ a)\n"
        "    have h1 : a = a ◇ (b ◇ T) := hsrc a b a\n"
        "    have h2 : a = a ◇ (b ◇ (a ◇ (b ◇ T))) := hsrc a b T\n"
        "    exact (congrArg (fun t => a ◇ (b ◇ t)) h1).trans h2.symm\n"
        "  have hmid : ∀ a b : G, a ◇ (b ◇ (a ◇ b)) = a := by\n"
        "    intro a b\n"
        "    have inner : b ◇ (a ◇ b) = b := hp b a\n"
        "    have hbig : a = a ◇ (b ◇ (a ◇ (b ◇ (a ◇ b)))) := hsrc a b (a ◇ b)\n"
        "    exact (hbig.trans (congrArg (fun t => a ◇ (b ◇ (a ◇ t))) inner)).symm\n"
        "  have hleft : ∀ a b : G, a ◇ b = a := by\n"
        "    intro a b\n"
        "    have inner : b ◇ (a ◇ b) = b := hp b a\n"
        "    exact (congrArg (fun t => a ◇ t) inner).symm.trans (hmid a b)\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:derived_left_projection", code


_derived_right_projection = law_matcher("a = ((b ◇ b) ◇ c) ◇ a")


def derived_right_projection_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _derived_right_projection(eq1)
    if found is None:
        return None
    left = projection_from_lemma_term_proof(eq2["lhs"], "right", hypothesis_name="hright")
    right = projection_from_lemma_term_proof(eq2["rhs"], "right", hypothesis_name="hright")
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
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = ((b ◇ b) ◇ c) ◇ a := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hright : ∀ a b : G, a ◇ b = b := by\n"
        "    intro a b\n"
        "    let E : G := (a ◇ a) ◇ b\n"
        "    have hEE : E ◇ E = E := (hsrc E a b).symm\n"
        "    have ha : a = E ◇ a := hsrc a a b\n"
        "    exact (congrArg (fun t => t ◇ b) ha).trans\n"
        "      ((congrArg (fun t => (t ◇ a) ◇ b) hEE.symm).trans\n"
        "        ((hsrc b E a).symm))\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:derived_right_projection", code


_square_to_right_product = law_matcher("a = (a ◇ b) ◇ (c ◇ c)")


def square_to_right_product_goal(eq2: dict[str, Any]) -> tuple[str, Term, Term, bool] | None:
    for swapped, square_side, product_side in (
        (False, eq2["lhs"], eq2["rhs"]),
        (True, eq2["rhs"], eq2["lhs"]),
    ):
        if square_side[0] != "op" or square_side[1][0] != "var" or square_side[2] != square_side[1]:
            continue
        root = str(square_side[1][1])
        if product_side[0] != "op" or product_side[1] != ("var", root) or product_side[2][0] != "op":
            continue
        return root, product_side[2][1], product_side[2][2], swapped
    return None


def square_to_right_product_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _square_to_right_product(eq1)
    goal = square_to_right_product_goal(eq2)
    if found is None or goal is None:
        return None
    root = found.var("a")
    goal_root, first, second, goal_swapped = goal
    if goal_root != root:
        return None
    call = found.call
    proof_expr = f"hprod {root} {term_to_lean(first)} {term_to_lean(second)}"
    if goal_swapped:
        proof_expr = f"({proof_expr}).symm"
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = (a ◇ b) ◇ (c ◇ c) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        "  have hprod : ∀ a b c : G, a ◇ a = a ◇ (b ◇ c) := by\n"
        "    intro a b c\n"
        "    exact ((congrArg (fun t => a ◇ t) (hsrc a a a)).trans\n"
        "      (congrArg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (hsrc a (b ◇ c) a))).trans\n"
        "      (hsrc (a ◇ (b ◇ c)) (a ◇ a) (a ◇ a)).symm\n"
        f"{intro_line}"
        f"  exact {proof_expr}\n"
    )
    return "true:square_to_right_product", code


_right_self_absorption = law_matcher("a = a ◇ (b ◇ (a ◇ (a ◇ c)))")


def right_self_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _right_self_absorption(eq1)
    if found is None:
        return None
    root = found.var("a")
    root_term = ("var", root)
    rhs = eq2["rhs"]
    if eq2["lhs"] != root_term or rhs[0] != "op" or rhs[1] != ("op", root_term, root_term):
        return None
    if rhs[2][0] != "op" or rhs[2][2] != root_term:
        return None
    goal_lead = rhs[2][1]
    if goal_lead[0] != "var":
        return None
    goal_lead_name = str(goal_lead[1])
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = a ◇ (b ◇ (a ◇ (a ◇ c))) := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        f"{intro_line}"
        f"  exact ((hsrc {root} {goal_lead_name} ({root} ◇ ({root} ◇ {root}))).trans "
        f"(congrArg (fun t => {root} ◇ ({goal_lead_name} ◇ t)) ((hsrc {root} {root} {root}).symm))).trans "
        f"((congrArg (fun t => (({root} ◇ t) ◇ ({goal_lead_name} ◇ {root}))) (hsrc {root} {root} {root})).trans "
        f"(congrArg (fun t => (t ◇ ({goal_lead_name} ◇ {root}))) ((hsrc {root} {root} ({root} ◇ {root})).symm))).symm\n"
    )
    return "true:right_self_absorption", code


_repeated_right_square = law_matcher(
    "a = ((a ◇ b) ◇ b) ◇ (b ◇ b)", both_orientations=False)


def repeated_right_square_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _repeated_right_square(eq1)
    if found is None:
        return None
    root = found.var("a")
    root_term = ("var", root)
    rhs = eq2["rhs"]
    if eq2["lhs"] != root_term or rhs[0] != "op" or rhs[2][0] != "var" or rhs[1][0] != "op":
        return None
    goal_param = str(rhs[2][1])
    if rhs[1] != ("op", ("op", root_term, ("op", ("var", goal_param), ("var", goal_param))), ("var", goal_param)):
        return None
    if root == goal_param:
        return None
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  let v0 : G := {goal_param} ◇ {goal_param}\n"
        f"  let v1 : G := {root} ◇ v0\n"
        "  have p1 : "
        f"{root} = (v1 ◇ v0) ◇ (v0 ◇ v0) := h {root} v0\n"
        "  have p2 : v1 = ((v1 ◇ "
        f"{goal_param}) ◇ {goal_param}) ◇ v0 := h v1 {goal_param}\n"
        "  have p3 : (v1 ◇ v0) ◇ (v0 ◇ v0) = ((((v1 ◇ "
        f"{goal_param}) ◇ {goal_param}) ◇ v0) ◇ v0) ◇ (v0 ◇ v0) :=\n"
        "    congrArg (fun t => (t ◇ v0) ◇ (v0 ◇ v0)) p2\n"
        "  have p4 : ((((v1 ◇ "
        f"{goal_param}) ◇ {goal_param}) ◇ v0) ◇ v0) ◇ (v0 ◇ v0) = (v1 ◇ {goal_param}) ◇ {goal_param} :=\n"
        f"    (h ((v1 ◇ {goal_param}) ◇ {goal_param}) v0).symm\n"
        "  exact p1.trans (p3.trans p4)\n"
    )
    return "true:repeated_right_square", code


_self_tail_triple = law_matcher(
    "a = ((b ◇ (b ◇ a)) ◇ a) ◇ a", both_orientations=False)


def self_tail_triple_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _self_tail_triple(eq1)
    if found is None:
        return None
    root = found.var("a")
    root_term = ("var", root)
    if eq2["lhs"] != root_term or eq2["rhs"] != ("op", ("op", root_term, root_term), root_term):
        return None
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{intro_line}"
        f"  let v2 : G := ({root} ◇ ({root} ◇ {root})) ◇ {root}\n"
        f"  have h1 : v2 ◇ {root} = {root} := (h {root} {root}).symm\n"
        f"  have p1 : v2 ◇ (v2 ◇ {root}) = {root} := (congrArg (fun t => v2 ◇ t) h1).trans h1\n"
        f"  have p2 : ((v2 ◇ (v2 ◇ {root})) ◇ {root}) ◇ {root} = (({root} ◇ {root}) ◇ {root}) :=\n"
        f"    congrArg (fun t => (t ◇ {root}) ◇ {root}) p1\n"
        f"  exact (h {root} v2).trans p2\n"
    )
    return "true:self_tail_triple", code


_nested_left_absorption = law_matcher("a = (b ◇ (b ◇ c)) ◇ a")


def nested_left_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _nested_left_absorption(eq1)
    if found is None:
        return None
    root = found.var("a")
    root_term = ("var", root)
    if eq2["lhs"] != root_term:
        return None
    rhs = eq2["rhs"]
    if rhs[0] != "op" or rhs[2] != root_term:
        return None
    tail1 = rhs[1]
    if tail1[0] != "op" or tail1[2] != root_term:
        return None
    tail2 = tail1[1]
    if tail2[0] != "op" or tail2[2] != root_term:
        return None
    tail3 = tail2[1]
    if tail3[0] != "op" or tail3[1] != root_term or tail3[2][0] != "var":
        return None
    goal_param = str(tail3[2][1])
    if goal_param == root:
        return None
    call = found.call
    intro_vars = " ".join(eq2["variables"])
    intro_line = f"  intro {intro_vars}\n" if intro_vars else ""
    code = (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  have hsrc : ∀ a b c : G, a = (b ◇ (b ◇ c)) ◇ a := by\n"
        "    intro a b c\n"
        f"    exact {call}\n"
        f"{intro_line}"
        f"  exact (hsrc {root} ({root} ◇ ({root} ◇ {goal_param})) ((({root} ◇ {goal_param}) ◇ {root}) ◇ {root})).trans "
        f"((congrArg (fun t => (t ◇ {root})) (hsrc ((({root} ◇ {goal_param}) ◇ {root}) ◇ {root}) {root} {goal_param})).trans "
        f"(congrArg (fun t => (t ◇ {root})) (hsrc (({root} ◇ ({root} ◇ {goal_param})) ◇ ((({root} ◇ {goal_param}) ◇ {root}) ◇ {root})) {root} {goal_param}))).symm\n"
    )
    return "true:nested_left_absorption", code


def narrow_grind_true_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    key = (*equation_shape_key(eq1), *equation_shape_key(eq2))
    if key not in narrow_grind_true_shape_keys():
        return None
    return "true:narrow_grind", grind_true_certificate(eq2["variables"])


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
    terms = (
        eq2["lhs"], eq2["rhs"],
        *term_subterms_tuple(eq2["lhs"])[1:],
        *term_subterms_tuple(eq2["rhs"])[1:],
        *(("var", var) for var in eq2["variables"]),
    )
    return list(dict.fromkeys(terms)) or [("var", "x")]


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


_self_square_absorption = law_matcher(
    "a = (b ◇ a) ◇ (b ◇ a)", both_orientations=False)


def self_square_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _self_square_absorption(eq1)
    if found is None:
        return None
    root, square_var = found.var("a"), found.var("b")
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


_repeat_tail_absorption = law_matcher(
    "a = b ◇ (c ◇ (c ◇ a))", both_orientations=False)


def repeat_tail_absorption_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    found = _repeat_tail_absorption(eq1)
    if found is None:
        return None
    root_name = found.var("a")
    lead_name, repeat_name = found.var("b"), found.var("c")
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
) -> list[tuple[Term, str, str]]:
    steps: list[tuple[Term, str, str]] = []
    sides = (eq1["lhs"], eq1["rhs"])
    for path in subterm_paths(term):
        subterm = term_at_path(term, path)
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
            call = call_expression(eq1["variables"], subst, hypothesis_name)
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
) -> tuple[str, str] | None:
    sides = (eq1["lhs"], eq1["rhs"])
    for source_idx in (0, 1):
        subst: dict[str, Term] = {}
        if match_term(sides[source_idx], src, subst) and match_term(sides[1 - source_idx], dst, subst):
            call = call_expression(eq1["variables"], subst, hypothesis_name)
            proof = call if source_idx == 0 else f"({call}).symm"
            return proof, f"rewrite_whole:{source_idx}"
    for new_term, proof, route in rewrite_steps_from_term(eq1, src, hypothesis_name=hypothesis_name):
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


UNIVERSAL_IDENTITY_MAX_PATTERN_VARS = 6
UNIVERSAL_IDENTITY_MAX_CODE = MAX_LEAN_CODE_BYTES


def universal_identity_source(eq1: dict[str, Any]) -> tuple[str, str, Term, bool] | None:
    for swapped, variable_side, op_side in (
        (False, eq1["lhs"], eq1["rhs"]),
        (True, eq1["rhs"], eq1["lhs"]),
    ):
        if variable_side[0] != "var" or op_side[0] != "op":
            continue
        root = str(variable_side[1])
        left, right = op_side[1], op_side[2]
        if left == ("var", root) and root not in term_vars(right):
            return "right", root, right, swapped
        if right == ("var", root) and root not in term_vars(left):
            return "left", root, left, swapped
    return None


class UniversalIdentityCalculus:
    def __init__(
        self,
        eq1: dict[str, Any],
        side: str,
        root: str,
        pattern: Term,
        swapped: bool,
        goal_vars: list[str],
    ) -> None:
        self.eq1 = eq1
        self.side = side
        self.root = root
        self.pattern = pattern
        self.swapped = swapped
        self.pattern_vars = sorted(term_vars(pattern))
        self.binder = next(
            (name for name in ("t", "s", "q", "tt", "ss", "zz") if name not in set(goal_vars)),
            "zz",
        )

    def hypothesis(self, carrier: Term, subst: dict[str, Term]) -> str:
        full: dict[str, Term] = {self.root: carrier}
        full.update(subst)
        for name in self.eq1["variables"]:
            full.setdefault(name, carrier)
        call = call_expression(self.eq1["variables"], full, "h")
        return f"({call})" if self.swapped else f"(({call}).symm)"

    def _congr(self, context: str, proof: str) -> str:
        return f"(congrArg (fun {self.binder} => {context}) {proof})"

    @staticmethod
    def _symm(proof: str) -> str:
        return f"(({proof}).symm)"

    @staticmethod
    def _trans(first: str | None, second: str) -> str:
        return second if first is None else f"(({first}).trans {second})"

    def _identity_instance(self, term: Term) -> dict[str, Term] | None:
        subst: dict[str, Term] = {}
        if match_term(self.pattern, term, subst):
            return subst
        return None

    def reduce(self, term: Term) -> tuple[Term, str | None]:
        if term[0] != "op":
            return term, None
        left, left_proof = self.reduce(term[1])
        right, right_proof = self.reduce(term[2])
        proof: str | None = None
        if left_proof is not None:
            proof = self._congr(f"{self.binder} ◇ {term_to_lean(term[2])}", left_proof)
        if right_proof is not None:
            proof = self._trans(
                proof, self._congr(f"{term_to_lean(left)} ◇ {self.binder}", right_proof))
        cut, keep = (right, left) if self.side == "right" else (left, right)
        subst = self._identity_instance(cut)
        if subst is None:
            return ("op", left, right), proof
        return keep, self._trans(proof, self.hypothesis(keep, subst))

    def projection_proof(self, left: Term, right: Term, identity: Term) -> str | None:
        target = right if self.side == "right" else left
        for choice in product((identity, target), repeat=len(self.pattern_vars)):
            subst = dict(zip(self.pattern_vars, choice))
            normal, proof = self.reduce(instantiate_term(self.pattern, subst))
            if normal != target:
                continue
            carrier = left if self.side == "right" else right
            applied = self.hypothesis(carrier, subst)
            if proof is None:
                return applied
            if self.side == "right":
                context = f"{term_to_lean(left)} ◇ {self.binder}"
            else:
                context = f"{self.binder} ◇ {term_to_lean(right)}"
            return self._trans(self._congr(context, self._symm(proof)), applied)
        return None


def universal_identity_term_proof(
    term: Term,
    keep_left: bool,
    projection: Callable[[Term, Term], str | None],
) -> tuple[str, str] | None:
    if term[0] == "var":
        return "rfl", str(term[1])
    if term[0] != "op":
        return None
    projected = term[1] if keep_left else term[2]
    step = projection(term[1], term[2])
    if step is None:
        return None
    rest = universal_identity_term_proof(projected, keep_left, projection)
    if rest is None:
        return None
    rest_proof, target_var = rest
    if rest_proof != "rfl":
        step = f"({step}).trans ({rest_proof})"
    return step, target_var


def universal_identity_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    source = universal_identity_source(eq1)
    if source is None:
        return None
    side, root, pattern, swapped = source
    goal_vars = list(eq2["variables"])
    if not goal_vars:
        return None
    calculus = UniversalIdentityCalculus(eq1, side, root, pattern, swapped, goal_vars)
    if len(calculus.pattern_vars) > UNIVERSAL_IDENTITY_MAX_PATTERN_VARS:
        return None
    seed: Term = ("var", goal_vars[0])
    identity = instantiate_term(pattern, {name: seed for name in calculus.pattern_vars})

    def projection(left: Term, right: Term) -> str | None:
        return calculus.projection_proof(left, right, identity)

    keep_left = side == "right"
    left = universal_identity_term_proof(eq2["lhs"], keep_left, projection)
    right = universal_identity_term_proof(eq2["rhs"], keep_left, projection)
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
    code = projection_true_certificate(goal_vars, proof_expr)
    if len(code) > UNIVERSAL_IDENTITY_MAX_CODE:
        return None
    law = "left" if keep_left else "right"
    return f"true:universal_identity:{law}", code


def find_rewrite_chain(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_depth: int = REWRITE_CHAIN_MAX_DEPTH,
    hypothesis_name: str = "h",
    deadline: float | None = None,
    frontier_limit: int | None = None,
) -> tuple[list[str], str] | None:
    target = eq2["rhs"]
    queue: list[tuple[Term, list[str], list[str]]] = [(eq2["lhs"], [], [])]
    seen: set[Term] = {eq2["lhs"]}
    for _depth in range(max_depth):
        next_queue: list[tuple[Term, list[str], list[str]]] = []
        for term, proofs, routes in queue:
            if deadline_expired(deadline):
                return None
            for new_term, proof, route in rewrite_steps_from_term(
                    eq1, term, hypothesis_name=hypothesis_name):
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
            if frontier_limit is not None and len(next_queue) >= frontier_limit:
                break
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
) -> tuple[str, str] | None:
    if src == dst:
        return "rfl", "guided:rfl"

    direct = proof_between_terms(eq1, src, dst)
    if direct is not None:
        proof, route = direct
        return proof, route

    edge_eq = {"lhs": src, "rhs": dst, "variables": variables}
    chain = find_rewrite_chain(
        eq1,
        edge_eq,
        max_depth=max_depth,
        deadline=local_deadline(closure_time_budget),
        frontier_limit=GUIDED_CHAIN_FRONTIER_LIMIT,
    )
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


MEMORY_CAP_MB_DEFAULT = 1600.0
_MEM_CHECK_EVERY = 4096
_mem_check_counter = 0
_mem_exceeded = False
_MEMORY_GUARD_ARMED = False


def arm_memory_guard(armed: bool = True) -> None:
    global _MEMORY_GUARD_ARMED, _mem_exceeded
    _MEMORY_GUARD_ARMED = armed
    _mem_exceeded = False


def _memory_cap_bytes() -> float:
    try:
        cap_mb = float(os.environ.get("MAGMA_MEMORY_CAP_MB", MEMORY_CAP_MB_DEFAULT))
    except ValueError:
        cap_mb = MEMORY_CAP_MB_DEFAULT
    return cap_mb * 1024 * 1024


def _process_rss_bytes() -> int | None:
    try:
        with open("/proc/self/statm", "rb") as statm:
            fields = statm.read().split()
        return int(fields[1]) * (os.sysconf("SC_PAGESIZE") if hasattr(os, "sysconf") else 4096)
    except (OSError, ValueError, IndexError):
        pass
    try:
        import ctypes

        class _PMC(ctypes.Structure):
            _fields_ = [
                ("cb", ctypes.c_uint32), ("PageFaultCount", ctypes.c_uint32),
                ("PeakWorkingSetSize", ctypes.c_size_t), ("WorkingSetSize", ctypes.c_size_t),
                ("QuotaPeakPagedPoolUsage", ctypes.c_size_t), ("QuotaPagedPoolUsage", ctypes.c_size_t),
                ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t), ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                ("PagefileUsage", ctypes.c_size_t), ("PeakPagefileUsage", ctypes.c_size_t),
            ]

        pmc = _PMC()
        pmc.cb = ctypes.sizeof(_PMC)
        kernel32 = ctypes.windll.kernel32
        get_info = getattr(kernel32, "K32GetProcessMemoryInfo", None)
        if get_info is None:
            get_info = ctypes.windll.psapi.GetProcessMemoryInfo
        current_process = ctypes.c_void_p(-1)
        if get_info(current_process, ctypes.byref(pmc), pmc.cb):
            return int(pmc.WorkingSetSize)
    except Exception:
        pass
    return None


def memory_exceeded() -> bool:
    global _mem_check_counter, _mem_exceeded
    if not _MEMORY_GUARD_ARMED:
        return False
    _mem_check_counter += 1
    if _mem_check_counter % _MEM_CHECK_EVERY:
        return _mem_exceeded
    rss = _process_rss_bytes()
    _mem_exceeded = rss is not None and rss > _memory_cap_bytes()
    return _mem_exceeded


_mem_reclaims_left = 3


def try_reclaim_memory() -> bool:
    global _mem_check_counter, _mem_exceeded, _mem_reclaims_left
    if not _MEMORY_GUARD_ARMED or not _mem_exceeded:
        return not _mem_exceeded
    if _mem_reclaims_left <= 0:
        return False
    _mem_reclaims_left -= 1
    clear_term_caches()
    import gc

    gc.collect()
    _mem_check_counter = -1
    return not memory_exceeded()


def reset_memory_reclaims() -> None:
    global _mem_reclaims_left, _mem_exceeded, _mem_check_counter
    _mem_reclaims_left = 3
    _mem_exceeded = False
    _mem_check_counter = 0


def deadline_expired(deadline: float | None) -> bool:
    if memory_exceeded():
        return True
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
    fill_pool: list[Term] | None = None,
) -> list[tuple[Term, str, str]]:
    if not pool:
        return []

    steps: list[tuple[Term, str, str]] = []
    seen_terms: set[Term] = set()
    sides = (eq1["lhs"], eq1["rhs"])
    default_term = pool[0]

    for path in subterm_paths(term):
        if deadline_expired(deadline):
            return steps
        subterm = term_at_path(term, path)
        for source_idx in (0, 1):
            if deadline_expired(deadline):
                return steps
            subst: dict[str, Term] = {}
            if not match_term(sides[source_idx], subterm, subst):
                continue

            replacement_pattern = sides[1 - source_idx]
            replacement_vars = term_vars(replacement_pattern)
            needed = [var for var in eq1["variables"] if var not in subst and var in replacement_vars]
            if len(needed) > 3:
                continue

            fill_count = 0
            fills_source = fill_pool if (fill_pool is not None and len(needed) > 1) else pool
            fill_iter = product(fills_source, repeat=len(needed)) if needed else ((),)
            for fills in fill_iter:
                if deadline_expired(deadline):
                    return steps
                fill_count += 1
                if fill_count > max_fills:
                    break

                subst_full = dict(subst)
                for var, value in zip(needed, fills):
                    subst_full[var] = value
                for var in eq1["variables"]:
                    if var not in subst_full:
                        subst_full[var] = default_term

                replacement = instantiate_term(replacement_pattern, subst_full)
                new_term = replace_subterm(term, path, replacement)
                if new_term == term or new_term in seen_terms:
                    continue
                if term_size(new_term) > max_size or term_depth(new_term) > max_depth:
                    continue

                call = call_expression(eq1["variables"], subst_full)
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
    deadline = local_deadline(time_budget)
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
    seed_terms: list[Term] | None = None,
) -> tuple[str, str] | None:
    if time_budget:
        time_budget = _eff_time(time_budget)
    frontier_limit = _eff_frontier(frontier_limit)
    max_fills = _eff_fills(max_fills)
    pool_limit = _eff_pool(pool_limit)

    deadline = local_deadline(time_budget)
    pool = absorption_term_pool(eq1, eq2, pool_limit=pool_limit)
    fill_pool: list[Term] | None = None
    if seed_terms:
        allowed_vars = set(eq2["variables"])
        seed_extra: list[Term] = []
        seed_seen: set[Term] = set()
        for seed in seed_terms:
            for term in term_subterms_tuple(seed):
                if term in seed_seen or not term_vars(term).issubset(allowed_vars):
                    continue
                seed_seen.add(term)
                seed_extra.append(term)
        seed_extra.sort(key=lambda term: (term_size(term), term_depth(term), term_to_lean(term)))
        seed_extra = seed_extra[:LLM_SEEDED_CLOSURE_MAX_SEEDS]
        var_terms = [term for term in pool if term[0] == "var"]
        rest = [term for term in pool if term[0] != "var" and term not in seed_seen]
        pool = var_terms + [term for term in seed_extra if term[0] != "var"] + rest
        fill_pool = pool[:LLM_SEEDED_CLOSURE_FILL_POOL_CAP]
    if not pool:
        return None

    size_basis = [
        term_size(eq1["lhs"]),
        term_size(eq1["rhs"]),
        term_size(eq2["lhs"]),
        term_size(eq2["rhs"]),
    ]
    depth_basis = [
        term_depth(eq1["lhs"]),
        term_depth(eq1["rhs"]),
        term_depth(eq2["lhs"]),
        term_depth(eq2["rhs"]),
    ]
    if seed_terms:
        size_basis.extend(term_size(term) for term in seed_terms)
        depth_basis.extend(term_depth(term) for term in seed_terms)
    max_size = max(size_basis) + term_slack
    max_depth = max(depth_basis) + depth_slack

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
                fill_pool=fill_pool,
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
        eq1, eq2, route_name=route_name, chain_max_depth=chain_max_depth,
        pool_limit=pool_limit, frontier_limit=frontier_limit,
        max_fills=max_fills, term_slack=term_slack, depth_slack=depth_slack,
        time_budget=time_budget)
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


def _kb_walk(term: Term, subst: dict[str, Term]) -> Term:
    while term[0] == "var" and term[1] in subst:
        term = subst[term[1]]
    return term


def _kb_occurs(name: str, term: Term, subst: dict[str, Term]) -> bool:
    term = _kb_walk(term, subst)
    if term[0] == "var":
        return term[1] == name
    return _kb_occurs(name, term[1], subst) or _kb_occurs(name, term[2], subst)


def _kb_unify(a: Term, b: Term, subst: dict[str, Term]) -> dict[str, Term] | None:
    a = _kb_walk(a, subst)
    b = _kb_walk(b, subst)
    if a == b:
        return subst
    if a[0] == "var":
        if _kb_occurs(a[1], b, subst):
            return None
        out = dict(subst)
        out[a[1]] = b
        return out
    if b[0] == "var":
        if _kb_occurs(b[1], a, subst):
            return None
        out = dict(subst)
        out[b[1]] = a
        return out
    out = _kb_unify(a[1], b[1], subst)
    if out is None:
        return None
    return _kb_unify(a[2], b[2], out)


def _kb_resolve(term: Term, subst: dict[str, Term]) -> Term:
    term = _kb_walk(term, subst)
    if term[0] == "var":
        return term
    return ("op", _kb_resolve(term[1], subst), _kb_resolve(term[2], subst))


def _kb_rename(term: Term, suffix: str) -> Term:
    if term[0] == "var":
        return ("var", term[1] + suffix)
    return ("op", _kb_rename(term[1], suffix), _kb_rename(term[2], suffix))


def _kb_nonvar_paths(term: Term, prefix: tuple[int, ...] = ()) -> list[tuple[int, ...]]:
    if term[0] != "op":
        return []
    out = [prefix]
    out.extend(_kb_nonvar_paths(term[1], prefix + (0,)))
    out.extend(_kb_nonvar_paths(term[2], prefix + (1,)))
    return out


class DerivedRule:
    __slots__ = ("lhs", "rhs", "vars", "proof_only_vars", "builder", "label")

    def __init__(self, lhs: Term, rhs: Term, builder: Any, label: str,
                 extra_vars: set[str] | None = None):
        self.lhs = lhs
        self.rhs = rhs
        pattern_vars = term_vars(lhs) | term_vars(rhs)
        self.proof_only_vars = sorted((extra_vars or set()) - pattern_vars)
        self.vars = sorted(pattern_vars)
        self.builder = builder
        self.label = label


def _equation_rules(
    equation: dict[str, Any], name: str, fwd_tag: str, bwd_tag: str
) -> list[DerivedRule]:
    binders = list(equation["variables"])

    def fwd(subst: dict[str, Term]) -> str:
        return call_expression(binders, subst, name)

    def bwd(subst: dict[str, Term]) -> str:
        return f"({call_expression(binders, subst, name)}).symm"

    return [
        DerivedRule(equation["lhs"], equation["rhs"], fwd, fwd_tag),
        DerivedRule(equation["rhs"], equation["lhs"], bwd, bwd_tag),
    ]


def _derived_base_rules(eq1: dict[str, Any], hyp_name: str = "h") -> list[DerivedRule]:
    return _equation_rules(eq1, hyp_name, "base_fwd", "base_bwd")


def _canonicalize_derived_rule(lhs: Term, rhs: Term) -> tuple[Term, Term, dict[str, str]]:
    mapping: dict[str, str] = {}

    def canon(term: Term) -> Term:
        if term[0] == "var":
            if term[1] not in mapping:
                mapping[term[1]] = f"v{len(mapping)}"
            return ("var", mapping[term[1]])
        return ("op", canon(term[1]), canon(term[2]))

    return canon(lhs), canon(rhs), mapping


_DERIVED_RULES_CACHE: dict[tuple[Term, Term, str, int, int], list[DerivedRule]] = {}


def critical_pair_rules(
    eq1: dict[str, Any],
    *,
    max_rule_size: int = DERIVED_CP_MAX_RULE_SIZE,
    max_rules: int = DERIVED_CP_MAX_RULES,
    hyp_name: str = "h",
) -> list[DerivedRule]:
    cache_key = (eq1["lhs"], eq1["rhs"], hyp_name, max_rule_size, max_rules)
    cached = _DERIVED_RULES_CACHE.get(cache_key)
    if cached is not None:
        return cached
    ev = list(eq1["variables"])
    L1 = _kb_rename(eq1["lhs"], "@1")
    R1 = _kb_rename(eq1["rhs"], "@1")
    L2 = _kb_rename(eq1["lhs"], "@2")
    R2 = _kb_rename(eq1["rhs"], "@2")

    rules: list[DerivedRule] = []
    seen: set[tuple[Term, Term]] = set()

    for s1, t1, s1_is_L in ((L1, R1, True), (R1, L1, False)):
        for s2, t2, s2_is_L in ((L2, R2, True), (R2, L2, False)):
            for p in _kb_nonvar_paths(s2):
                sub = term_at_path(s2, p)
                sigma = _kb_unify(s1, sub, {})
                if sigma is None:
                    continue
                new_lhs = _kb_resolve(t2, sigma)
                inner_repl = _kb_resolve(t1, sigma)
                expanded = _kb_resolve(s2, sigma)
                new_rhs = replace_subterm(expanded, p, inner_repl)
                if new_lhs == new_rhs:
                    continue
                if max(term_size(new_lhs), term_size(new_rhs)) > max_rule_size:
                    continue
                canon_l, canon_r, mapping = _canonicalize_derived_rule(new_lhs, new_rhs)
                if (canon_l, canon_r) in seen:
                    continue
                seen.add((canon_l, canon_r))

                def remap(term: Term) -> Term:
                    if term[0] == "var":
                        if term[1] not in mapping:
                            mapping[term[1]] = f"v{len(mapping)}"
                        return ("var", mapping[term[1]])
                    return ("op", remap(term[1]), remap(term[2]))

                tau2 = {v: remap(_kb_resolve(("var", v + "@2"), sigma)) for v in ev}
                tau1 = {v: remap(_kb_resolve(("var", v + "@1"), sigma)) for v in ev}
                expanded_pat = remap(expanded)

                def make_builder(tau1=tau1, tau2=tau2, expanded_pat=expanded_pat,
                                 p=p, s1_is_L=s1_is_L, s2_is_L=s2_is_L, ev=ev,
                                 hyp_name=hyp_name):
                    def build(subst: dict[str, Term]) -> str:
                        c2 = {v: instantiate_term(t, subst) for v, t in tau2.items()}
                        c1 = {v: instantiate_term(t, subst) for v, t in tau1.items()}
                        whole = instantiate_term(expanded_pat, subst)
                        call2 = call_expression(ev, c2, hyp_name)
                        step1 = f"({call2}).symm" if s2_is_L else call2
                        call1 = call_expression(ev, c1, hyp_name)
                        inner = call1 if s1_is_L else f"({call1}).symm"
                        if p:
                            ctx = context_to_lean(whole, p, "t")
                            step2 = f"congrArg (fun t => {ctx}) ({inner})"
                        else:
                            step2 = inner
                        return f"({step1}).trans ({step2})"
                    return build

                label = f"cp:{'L' if s1_is_L else 'R'}{'L' if s2_is_L else 'R'}:{'.'.join(map(str, p)) or 'root'}"
                all_vars: set[str] = set()
                for t in list(tau1.values()) + list(tau2.values()):
                    all_vars |= term_vars(t)
                fwd_rule = DerivedRule(canon_l, canon_r, make_builder(), label, extra_vars=all_vars)
                rules.append(fwd_rule)

                def make_rev(fwd_rule=fwd_rule):
                    def build(subst: dict[str, Term]) -> str:
                        return f"({fwd_rule.builder(subst)}).symm"
                    return build

                rules.append(DerivedRule(canon_r, canon_l, make_rev(), label + ":rev", extra_vars=all_vars))

    rules.sort(key=lambda r: (term_size(r.lhs) + term_size(r.rhs), r.label))
    rules = rules[:max_rules]
    _DERIVED_RULES_CACHE[cache_key] = rules
    if len(_DERIVED_RULES_CACHE) > 64:
        _DERIVED_RULES_CACHE.clear()
    return rules


def derived_rule_steps(
    rules: list[DerivedRule],
    term: Term,
    pool: list[Term],
    fill_pool: list[Term],
    *,
    max_size: int,
    max_depth: int,
    max_fills: int,
    deadline: float | None,
) -> list[tuple[Term, str]]:
    steps: list[tuple[Term, str]] = []
    seen: set[Term] = set()
    default_term = pool[0]
    for path in subterm_paths(term):
        if deadline_expired(deadline):
            break
        sub = term_at_path(term, path)
        for rule in rules:
            subst: dict[str, Term] = {}
            if not match_term(rule.lhs, sub, subst):
                continue
            needed = [v for v in rule.vars if v not in subst]
            if len(needed) > 3:
                continue
            fills_src = fill_pool if len(needed) > 1 else pool
            fill_iter = product(fills_src, repeat=len(needed)) if needed else ((),)
            count = 0
            for fills in fill_iter:
                count += 1
                if count > max_fills:
                    break
                full = dict(subst)
                for v, val in zip(needed, fills):
                    full[v] = val
                for v in rule.proof_only_vars:
                    full[v] = default_term
                replacement = instantiate_term(rule.rhs, full)
                new_term = replace_subterm(term, path, replacement)
                if new_term == term or new_term in seen:
                    continue
                if term_size(new_term) > max_size or term_depth(new_term) > max_depth:
                    continue
                proof = rule.builder(full)
                if path:
                    ctx = context_to_lean(term, path, "t")
                    proof = f"congrArg (fun t => {ctx}) ({proof})"
                seen.add(new_term)
                steps.append((new_term, proof))
    steps.sort(key=lambda item: (term_size(item[0]), term_depth(item[0])))
    return steps


def derived_cp_closure_proof_expr(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    chain_max_depth: int = DERIVED_CP_CHAIN_MAX_DEPTH,
    pool_limit: int = DERIVED_CP_POOL_LIMIT,
    fill_pool_cap: int = DERIVED_CP_FILL_POOL_CAP,
    frontier_limit: int = DERIVED_CP_FRONTIER_LIMIT,
    max_fills: int = DERIVED_CP_MAX_FILLS,
    term_slack: int = DERIVED_CP_TERM_SLACK,
    depth_slack: int = DERIVED_CP_DEPTH_SLACK,
    time_budget: float = DERIVED_CP_TIME_BUDGET,
    max_rules: int = DERIVED_CP_MAX_RULES,
    extra_rules: list[DerivedRule] | None = None,
) -> str | None:
    time_budget = _eff_time(time_budget)
    frontier_limit = _eff_frontier(frontier_limit)
    max_fills = _eff_fills(max_fills)
    pool_limit = _eff_pool(pool_limit)
    chain_max_depth = _eff_depth(chain_max_depth)

    deadline = local_deadline(time_budget)
    rules = (_derived_base_rules(eq1) + list(extra_rules or [])
             + critical_pair_rules(eq1, max_rules=max_rules))
    pool = absorption_term_pool(eq1, eq2, pool_limit=pool_limit)
    if not pool:
        return None
    fill_pool = pool[:fill_pool_cap]

    max_size = max(term_size(eq1["lhs"]), term_size(eq1["rhs"]),
                   term_size(eq2["lhs"]), term_size(eq2["rhs"])) + term_slack
    max_depth_t = max(term_depth(eq1["lhs"]), term_depth(eq1["rhs"]),
                      term_depth(eq2["lhs"]), term_depth(eq2["rhs"])) + depth_slack

    left_seen: dict[Term, str | None] = {eq2["lhs"]: None}
    right_seen: dict[Term, str | None] = {eq2["rhs"]: None}
    left_frontier = [eq2["lhs"]]
    right_frontier = [eq2["rhs"]]

    def expand(frontier: list[Term], seen: dict[Term, str | None],
               other: dict[Term, str | None], from_left: bool):
        nxt: list[Term] = []
        for term in frontier:
            if deadline_expired(deadline):
                return nxt, None, True
            prefix = seen[term]
            for new_term, proof in derived_rule_steps(
                rules, term, pool, fill_pool,
                max_size=max_size, max_depth=max_depth_t,
                max_fills=max_fills, deadline=deadline,
            ):
                if new_term in seen:
                    continue
                new_proof = chain_trans(prefix, proof)
                if new_term in other:
                    if from_left:
                        return nxt, combine_meeting_proofs(new_proof, other[new_term]), False
                    return nxt, combine_meeting_proofs(other[new_term], new_proof), False
                seen[new_term] = new_proof
                nxt.append(new_term)
                if len(seen) >= frontier_limit:
                    break
            if len(seen) >= frontier_limit:
                break
        return nxt[:frontier_limit], None, False

    for _ in range(chain_max_depth):
        if deadline_expired(deadline):
            return None
        left_frontier, result, timed_out = expand(left_frontier, left_seen, right_seen, True)
        if timed_out or result is not None:
            return result
        right_frontier, result, timed_out = expand(right_frontier, right_seen, left_seen, False)
        if timed_out or result is not None:
            return result
        if not left_frontier and not right_frontier:
            return None
    return None


def derived_cp_closure_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    proof_expr = derived_cp_closure_proof_expr(eq1, eq2)
    if proof_expr is None:
        return None
    return "true:derived_cp_closure", substitution_true_certificate(eq2["variables"], proof_expr)


PROJECTION_LEMMA_TEXT = {"left": "a ◇ b = a", "right": "a ◇ b = b"}

LEMMA_LIBRARY_TEXT = (
    ("trivial", "a = b"),
    ("idempotent", "a ◇ a = a"),
    ("left_row_constant", "a ◇ b = a ◇ c"),
    ("right_col_constant", "a ◇ b = c ◇ b"),
    ("product_constant", "a ◇ b = c ◇ d"),
    ("commutative", "a ◇ b = b ◇ a"),
)

LEMMA_APPLY_CHAIN_MAX_DEPTH = 3

LEMMA_LIBRARY_CLOSURE_TIME_BUDGET = 1.5
LLM_LEMMA_CLOSURE_TIME_BUDGET = 4.0

LEMMA_ENUM_MAX_RHS_OPS = 3
LEMMA_ENUM_VARS = ("a", "b", "c", "d")
LEMMA_ENUM_MAX_CANDIDATES = 600
LEMMA_BOOTSTRAP_TOTAL_BUDGET = 6.0


@lru_cache(maxsize=1)
def enumerated_lemma_library() -> tuple[tuple[str, str], ...]:
    def build_terms(max_ops: int) -> list[Term]:
        by_ops: list[list[Term]] = [[("var", v) for v in LEMMA_ENUM_VARS]]
        for ops in range(1, max_ops + 1):
            level: list[Term] = []
            for left_ops in range(ops):
                right_ops = ops - 1 - left_ops
                for left in by_ops[left_ops]:
                    for right in by_ops[right_ops]:
                        level.append(("op", left, right))
            by_ops.append(level)
        return [term for level in by_ops for term in level]

    rhs_terms = build_terms(LEMMA_ENUM_MAX_RHS_OPS)
    lhs_terms: tuple[Term, ...] = (
        ("var", "a"),
        ("op", ("var", "a"), ("var", "b")),
    )
    seen: set[tuple[Term, Term]] = set()
    laws: list[tuple[int, str, str]] = []
    for lhs in lhs_terms:
        for rhs in rhs_terms:
            if lhs == rhs:
                continue
            text = f"{term_to_lean(lhs)} = {term_to_lean(rhs)}"
            try:
                law = parse_equation(text)
            except ValueError:
                continue
            key = canonical_law_key(law)
            if key in seen:
                continue
            seen.add(key)
            size = term_size(lhs) + term_size(rhs)
            laws.append((size, f"enum{len(laws)}", text))
    laws.sort(key=lambda item: (item[0], item[2]))
    return tuple((name, text) for _, name, text in laws[:LEMMA_ENUM_MAX_CANDIDATES])


@lru_cache(maxsize=1)
def full_lemma_library() -> tuple[tuple[str, str], ...]:
    curated_shapes = set()
    curated: list[tuple[str, str]] = []
    for name, text in LEMMA_LIBRARY_TEXT:
        curated.append((name, text))
        curated_shapes.add(canonical_law_key(parse_equation(text)))
    extra = [
        (name, text)
        for name, text in enumerated_lemma_library()
        if canonical_law_key(parse_equation(text)) not in curated_shapes
    ]
    return tuple(curated + extra)


LEMMA_FILTER_FIN3_SAMPLES = 200
LEMMA_FILTER_SEED = 20260722


@lru_cache(maxsize=8)
def _lemma_filter_models(lhs: Term, rhs: Term, variables: tuple[str, ...]) -> tuple[tuple[tuple[int, ...], ...], ...]:
    eq1 = {"lhs": lhs, "rhs": rhs, "variables": list(variables)}
    models: list[tuple[tuple[int, ...], ...]] = []
    for encoding in product(range(2), repeat=4):
        table = [list(encoding[:2]), list(encoding[2:])]
        if equation_holds(eq1, table):
            models.append(tuple(tuple(row) for row in table))
    rng = random.Random(LEMMA_FILTER_SEED)
    for _ in range(LEMMA_FILTER_FIN3_SAMPLES):
        table = [[rng.randrange(3) for _ in range(3)] for _ in range(3)]
        if equation_holds(eq1, table):
            models.append(tuple(tuple(row) for row in table))
    return tuple(models)


def lemma_survives_models(eq1: dict[str, Any], lemma: dict[str, Any]) -> bool:
    models = _lemma_filter_models(
        eq1["lhs"], eq1["rhs"], tuple(eq1["variables"]))
    return all(equation_holds(lemma, [list(row) for row in table]) for table in models)


def lemma_closure_proof(
    eq1: dict[str, Any],
    lemma: dict[str, Any],
    *,
    time_budget: float = DERIVED_CP_TIME_BUDGET,
) -> str | None:
    if not lemma_survives_models(eq1, lemma):
        return None
    return derived_cp_closure_proof_expr(eq1, lemma, time_budget=time_budget)


@lru_cache(maxsize=2048)
def lemma_goal(text: str) -> dict[str, Any]:
    return parse_equation(text)


def lemma_certificate(
    lemma: dict[str, Any],
    lemma_proof: str,
    eq2_vars: list[str],
    proof_expr: str,
) -> str:
    binders = " ".join(lemma["variables"])
    statement = f"{term_to_lean(lemma['lhs'])} = {term_to_lean(lemma['rhs'])}"
    return submission_certificate(
        eq2_vars, f"  exact {proof_expr}\n",
        law_have("hlem", binders, statement, lemma_proof))


def lemma_applies_to_goal(lemma: dict[str, Any], eq2: dict[str, Any]) -> str | None:
    simple = simple_true_proof_expr(lemma, eq2, hypothesis_name="hlem")
    if simple is not None:
        return simple[1]
    chain = find_rewrite_chain(
        lemma, eq2, max_depth=LEMMA_APPLY_CHAIN_MAX_DEPTH, hypothesis_name="hlem")
    if chain is not None:
        return chain[1]
    return None


def projection_bootstrap_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    for side in ("left", "right"):
        proof_expr = projection_from_lemma_goal_proof(eq2, side, hypothesis_name="hlem")
        if proof_expr is None:
            continue
        lemma = lemma_goal(PROJECTION_LEMMA_TEXT[side])
        lemma_proof = lemma_closure_proof(eq1, lemma)
        if lemma_proof is None:
            continue
        return (
            f"true:projection_bootstrap:{side}",
            lemma_certificate(lemma, lemma_proof, eq2["variables"], proof_expr),
        )
    return None


def lemma_bootstrap_route(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    candidates: tuple[tuple[str, str], ...] | None = None,
) -> tuple[str, str] | None:
    if candidates is None:
        candidates = full_lemma_library()
    route_deadline = local_deadline(_eff_time(LEMMA_BOOTSTRAP_TOTAL_BUDGET))
    for name, text in candidates:
        if deadline_expired(route_deadline):
            return None
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            continue
        lemma_proof = lemma_closure_proof(
            eq1, lemma, time_budget=LEMMA_LIBRARY_CLOSURE_TIME_BUDGET)
        if lemma_proof is None:
            continue
        return (
            f"true:lemma_bootstrap:{name}",
            lemma_certificate(lemma, lemma_proof, eq2["variables"], proof_expr),
        )
    return None


LEMMA_CHAIN_MAX_HELPERS = 4
LEMMA_CHAIN_HARVEST_BUDGET = 0.4
LEMMA_CHAIN_TARGET_BUDGET = 2.5
LEMMA_CHAIN_TOTAL_BUDGET = 10.0


LEMMA_CHAIN_CP_HELPERS = 3
LEMMA_CHAIN_CP_RULES_EACH = 24
_CP_HELPER_LETTERS = "abcdefgh"


def cp_rule_helpers(
    eq1: dict[str, Any], limit: int
) -> list[tuple[dict[str, Any], str]]:
    out: list[tuple[dict[str, Any], str]] = []
    seen: set[tuple[Term, Term]] = set()
    for rule in critical_pair_rules(eq1):
        if len(out) >= limit:
            break
        if rule.label.endswith(":rev"):
            continue
        rule_vars = list(rule.vars)
        all_vars = rule_vars + [v for v in rule.proof_only_vars if v not in rule.vars]
        if not rule_vars or len(rule_vars) > len(_CP_HELPER_LETTERS):
            continue
        rename = {v: _CP_HELPER_LETTERS[i] for i, v in enumerate(rule_vars)}
        subst: dict[str, Term] = {v: ("var", rename[v]) for v in rule_vars}
        fallback = rename[rule_vars[0]] if rule_vars else "a"
        for v in all_vars:
            if v not in subst:
                subst[v] = ("var", fallback)
        lhs = instantiate_term(rule.lhs, subst)
        rhs = instantiate_term(rule.rhs, subst)
        if lhs == rhs:
            continue
        lemma = {
            "lhs": lhs,
            "rhs": rhs,
            "variables": [rename[v] for v in rule_vars],
            "text": f"{term_to_lean(lhs)} = {term_to_lean(rhs)}",
        }
        key = canonical_law_key(lemma)
        if key in seen:
            continue
        seen.add(key)
        out.append((lemma, rule.builder(subst)))
    return out


def _helper_lemma_rules(name: str, lemma: dict[str, Any]) -> list[DerivedRule]:
    return _equation_rules(lemma, name, f"{name}:fwd", f"{name}:bwd")


def _lemma_chain_goal_certificate(
    blocks: list[tuple[str, dict[str, Any], str]],
    eq2_vars: list[str],
    goal_expr: str,
) -> str:
    lines = ["import JudgeProblem", "", "def submission : Goal := by", "  intro G _ h"]
    for name, lemma, proof in blocks:
        binders = " ".join(lemma["variables"])
        statement = f"{term_to_lean(lemma['lhs'])} = {term_to_lean(lemma['rhs'])}"
        lines.append(f"  have {name} : ∀ {binders} : G, {statement} := by")
        lines.append(f"    intro {binders}")
        lines.append(f"    exact {proof}")
    if eq2_vars:
        lines.append(f"  intro {' '.join(eq2_vars)}")
    lines.append(f"  exact {goal_expr}")
    return "\n".join(lines) + "\n"


def lemma_chain_certificate(
    helpers: list[tuple[str, dict[str, Any], str]],
    final_lemma: dict[str, Any],
    final_proof: str,
    eq2_vars: list[str],
    goal_expr: str,
) -> str:
    return _lemma_chain_goal_certificate(
        helpers + [("hlem", final_lemma, final_proof)], eq2_vars, goal_expr)


def lemma_chain_bootstrap_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    route_budget = _eff_time(LEMMA_CHAIN_TOTAL_BUDGET)
    route_deadline = local_deadline(route_budget)
    harvest_deadline = local_deadline(0.5 * route_budget)

    targets: list[tuple[str, dict[str, Any], str]] = []
    for name, text in full_lemma_library():
        if deadline_expired(route_deadline):
            return None
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        targets.append((name, lemma, proof_expr))
    target_keys = {canonical_law_key(lemma) for _, lemma, _ in targets}

    helpers: list[tuple[str, dict[str, Any], str]] = []
    helper_keys: set[Any] = set()
    extra_rules: list[DerivedRule] = []

    for lemma, proof in cp_rule_helpers(eq1, LEMMA_CHAIN_CP_HELPERS):
        key = canonical_law_key(lemma)
        if key in target_keys or key in helper_keys:
            continue
        helper_keys.add(key)
        name = f"hlem{len(helpers)}"
        helpers.append((name, lemma, proof))
        extra_rules.extend(_helper_lemma_rules(name, lemma))
        extra_rules.extend(critical_pair_rules(
            lemma, hyp_name=name, max_rules=LEMMA_CHAIN_CP_RULES_EACH))

    harvested = 0
    for harvest_round in range(2):
        if harvest_round == 1 and not helpers:
            break
        for _, text in full_lemma_library():
            if harvested >= LEMMA_CHAIN_MAX_HELPERS or deadline_expired(harvest_deadline):
                break
            try:
                lemma = lemma_goal(text)
            except ValueError:
                continue
            key = canonical_law_key(lemma)
            if key in target_keys or key in helper_keys:
                continue
            if not lemma_survives_models(eq1, lemma):
                continue
            proof = derived_cp_closure_proof_expr(
                eq1, lemma, time_budget=LEMMA_CHAIN_HARVEST_BUDGET,
                extra_rules=extra_rules)
            if proof is None:
                continue
            helper_keys.add(key)
            name = f"hlem{len(helpers)}"
            helpers.append((name, lemma, proof))
            harvested += 1
            extra_rules.extend(_helper_lemma_rules(name, lemma))
        if harvested >= LEMMA_CHAIN_MAX_HELPERS or deadline_expired(harvest_deadline):
            break
    if not helpers:
        return None

    for name, lemma, goal_expr in targets:
        if deadline_expired(route_deadline):
            return None
        proof = derived_cp_closure_proof_expr(
            eq1, lemma,
            time_budget=LEMMA_CHAIN_TARGET_BUDGET, extra_rules=extra_rules)
        if proof is None:
            continue
        return (
            f"true:lemma_chain:{name}",
            lemma_chain_certificate(
                helpers, lemma, proof, eq2["variables"], goal_expr),
        )

    if deadline_expired(route_deadline):
        return None
    direct = derived_cp_closure_proof_expr(
        eq1, eq2, time_budget=LEMMA_CHAIN_TARGET_BUDGET, extra_rules=extra_rules)
    if direct is not None:
        return (
            "true:lemma_chain:direct_goal",
            _lemma_chain_goal_certificate(helpers, eq2["variables"], direct),
        )
    return None


EGG_TIME_BUDGET = 10.0
EGG_ROUNDS = 30
EGG_POOL_MAX = 36
EGG_EXPAND_CAP = 900
EGG_MAX_ENODES = 60_000
EGG_MAX_APPS = 200_000
EGG_MAX_PROOF_BYTES = 46_000
EGG_MAX_CERT_BYTES = MAX_LEAN_CODE_BYTES

_EGG_BINDER_CANDIDATES = ("t", "q", "p", "s", "r", "m", "n", "k")


class _EggProvenanceError(Exception):
    pass


def _egg_term_size(t: Term) -> int:
    if t[0] == "var":
        return 1
    return _egg_term_size(t[1]) + _egg_term_size(t[2]) + 1


def _egg_substitute(term: Term, subst: dict[str, Term]) -> Term:
    if term[0] == "var":
        return subst[term[1]]
    return ("op", _egg_substitute(term[1], subst), _egg_substitute(term[2], subst))


def _egg_subterms(t: Term, acc: list[Term]) -> list[Term]:
    acc.append(t)
    if t[0] == "op":
        _egg_subterms(t[1], acc)
        _egg_subterms(t[2], acc)
    return acc


def _egg_pattern_vars(t: Term, acc: set[str] | None = None) -> set[str]:
    if acc is None:
        acc = set()
    if t[0] == "var":
        acc.add(t[1])
    else:
        _egg_pattern_vars(t[1], acc)
        _egg_pattern_vars(t[2], acc)
    return acc


def _egg_subterm_at(t: Term, pos: tuple) -> Term:
    for step in pos:
        t = t[1] if step == "L" else t[2]
    return t


def _egg_replace_at(t: Term, pos: tuple, new: Term) -> Term:
    if not pos:
        return new
    if pos[0] == "L":
        return ("op", _egg_replace_at(t[1], pos[1:], new), t[2])
    return ("op", t[1], _egg_replace_at(t[2], pos[1:], new))


def _egg_upper_patterns(eq1: dict[str, Any]) -> tuple[Term, Term, list[str]]:
    def walk(t: Term) -> Term:
        if t[0] == "var":
            return ("var", t[1].upper())
        return ("op", walk(t[1]), walk(t[2]))
    return walk(eq1["lhs"]), walk(eq1["rhs"]), [v.upper() for v in eq1["variables"]]


class _EggProver:
    def __init__(self) -> None:
        self.parent: list[int] = []
        self.size_rep: list[int] = []
        self.enodes: dict[tuple, int] = {}
        self.witness: dict[tuple, Term] = {}
        self.term_class: dict[Term, int] = {}
        self.class_repr: dict[int, Term] = {}
        self.adj: dict[Term, list[tuple[Term, tuple, bool]]] = {}

    def find(self, a: int) -> int:
        while self.parent[a] != a:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def canon(self, node: tuple) -> tuple:
        if node[0] == "op":
            return ("op", self.find(node[1]), self.find(node[2]))
        return node

    def _register(self, t: Term, cid: int) -> None:
        if t not in self.term_class:
            self.term_class[t] = cid
        root = self.find(cid)
        best = self.class_repr.get(root)
        if best is None or _egg_term_size(t) < _egg_term_size(best):
            self.class_repr[root] = t

    def _add_edge(self, a: Term, b: Term, reason: tuple) -> None:
        self.adj.setdefault(a, []).append((b, reason, False))
        self.adj.setdefault(b, []).append((a, reason, True))

    def add_term(self, t: Term) -> int:
        known = self.term_class.get(t)
        if known is not None:
            return self.find(known)
        if t[0] == "var":
            key: tuple = t
            sz = 1
        else:
            a = self.add_term(t[1])
            b = self.add_term(t[2])
            key = ("op", self.find(a), self.find(b))
            sz = self.size_rep[self.find(a)] + self.size_rep[self.find(b)] + 1
        existing = self.enodes.get(key)
        if existing is not None:
            cid = self.find(existing)
            if sz < self.size_rep[cid]:
                self.size_rep[cid] = sz
            w = self.witness.get(key)
            if w is not None and w != t:
                self._add_edge(t, w, ("congr",))
            self._register(t, cid)
            return cid
        cid = len(self.parent)
        self.parent.append(cid)
        self.size_rep.append(sz)
        self.enodes[key] = cid
        self.witness[key] = t
        self._register(t, cid)
        return cid

    def merge_terms(self, a_term: Term, b_term: Term, reason: tuple) -> bool:
        a = self.find(self.term_class[a_term])
        b = self.find(self.term_class[b_term])
        if a_term != b_term:
            self._add_edge(a_term, b_term, reason)
        if a == b:
            return False
        self.parent[a] = b
        self.size_rep[b] = min(self.size_rep[b], self.size_rep[a])
        ra, rb = self.class_repr.get(a), self.class_repr.get(b)
        if ra is not None and (rb is None or _egg_term_size(ra) < _egg_term_size(rb)):
            self.class_repr[b] = ra
        return True

    def rebuild(self) -> None:
        changed = True
        while changed:
            changed = False
            fresh: dict[tuple, int] = {}
            fresh_wit: dict[tuple, Term] = {}
            for node, cid in self.enodes.items():
                node2 = self.canon(node)
                cid = self.find(cid)
                wit = self.witness.get(node)
                other = fresh.get(node2)
                if other is None:
                    fresh[node2] = cid
                    if wit is not None:
                        fresh_wit[node2] = wit
                elif self.find(other) != cid:
                    ow = fresh_wit.get(node2)
                    if wit is not None and ow is not None:
                        self.merge_terms(ow, wit, ("congr",))
                    else:
                        self.parent[self.find(other)] = cid
                    changed = True
            self.enodes = fresh
            self.witness = fresh_wit

    def class_of(self, t: Term) -> int:
        return self.find(self.term_class[t])

    def _tree_path(self, s: Term, t: Term) -> list[tuple[Term, Term, tuple, bool]]:
        if s == t:
            return []
        prev: dict[Term, tuple[Term, tuple, bool]] = {s: (s, (), False)}
        queue = [s]
        while queue:
            nxt: list[Term] = []
            for u in queue:
                for v, reason, flipped in self.adj.get(u, ()):
                    if v in prev:
                        continue
                    prev[v] = (u, reason, flipped)
                    if v == t:
                        path: list[tuple[Term, Term, tuple, bool]] = []
                        cur = t
                        while cur != s:
                            p, r, f = prev[cur]
                            path.append((p, cur, r, f))
                            cur = p
                        path.reverse()
                        return path
                    nxt.append(v)
            queue = nxt
        raise _EggProvenanceError("terms not connected in proof forest")

    def explain(self, s: Term, t: Term, *, depth: int = 0,
                budget: list[int] | None = None) -> list[tuple]:
        if depth > 300:
            raise _EggProvenanceError("explanation recursion too deep")
        if budget is None:
            budget = [200000]
        steps: list[tuple] = []
        cur = s
        for a, b, reason, flipped in self._tree_path(s, t):
            if a != cur:
                raise _EggProvenanceError("path does not chain")
            budget[0] -= 1
            if budget[0] < 0:
                raise _EggProvenanceError("explanation too long")
            if reason and reason[0] == "rule":
                _, subst_items = reason
                steps.append(((), dict(subst_items), flipped))
                cur = b
            elif reason and reason[0] == "congr":
                if a[0] != "op" or b[0] != "op":
                    raise _EggProvenanceError("congr edge on non-op terms")
                for sub in self.explain(a[1], b[1], depth=depth + 1, budget=budget):
                    steps.append((("L",) + sub[0], sub[1], sub[2]))
                for sub in self.explain(a[2], b[2], depth=depth + 1, budget=budget):
                    steps.append((("R",) + sub[0], sub[1], sub[2]))
                cur = b
            else:
                raise _EggProvenanceError(f"unknown reason {reason!r}")
        if cur != t:
            raise _EggProvenanceError("explanation does not reach target")
        return steps


def _egg_match_pattern(pattern: Term, term: Term,
                       subst: dict[str, Term]) -> dict[str, Term] | None:
    if pattern[0] == "var":
        bound = subst.get(pattern[1])
        if bound is None:
            s2 = dict(subst)
            s2[pattern[1]] = term
            return s2
        return subst if bound == term else None
    if term[0] != "op":
        return None
    s1 = _egg_match_pattern(pattern[1], term[1], subst)
    if s1 is None:
        return None
    return _egg_match_pattern(pattern[2], term[2], s1)


def _egg_diff_pos(a: Term, b: Term) -> tuple | None:
    if a == b:
        return None
    if a[0] == "op" and b[0] == "op":
        left = a[1] != b[1]
        right = a[2] != b[2]
        if left and not right:
            sub = _egg_diff_pos(a[1], b[1])
            return ("L",) + sub if sub is not None else ("L",)
        if right and not left:
            sub = _egg_diff_pos(a[2], b[2])
            return ("R",) + sub if sub is not None else ("R",)
    return ()


def _egg_one_step_between(s: Term, t: Term, lhs_p: Term, rhs_p: Term):
    if s == t:
        return None
    pos = _egg_diff_pos(s, t)
    if pos is None:
        return None
    sub_s = _egg_subterm_at(s, pos)
    sub_t = _egg_subterm_at(t, pos)
    for symm, (frm, to) in ((False, (lhs_p, rhs_p)), (True, (rhs_p, lhs_p))):
        subst = _egg_match_pattern(frm, sub_s, {})
        if subst is None:
            continue
        subst2 = _egg_match_pattern(to, sub_t, dict(subst))
        if subst2 is not None and _egg_substitute(frm, subst2) == sub_s:
            return (pos, subst2, symm)
    return None


def _egg_bridge_steps(start: Term, steps: list, lhs_p: Term, rhs_p: Term):
    states: list[Term] = [start]
    cur = start
    for pos, subst, symm in steps:
        to_t = _egg_substitute(lhs_p if symm else rhs_p, subst)
        cur = _egg_replace_at(cur, pos, to_t)
        states.append(cur)
    out: list = []
    i = 0
    while i < len(states) - 1:
        jumped = False
        for j in range(len(states) - 1, i, -1):
            if j == i + 1:
                break
            step = _egg_one_step_between(states[i], states[j], lhs_p, rhs_p)
            if step is not None:
                out.append(step)
                i = j
                jumped = True
                break
        if not jumped:
            if len(steps) != len(states) - 1:
                return None
            out.append(steps[i])
            i += 1
    return out


def _egg_shorten_steps(start: Term, steps: list, lhs_p: Term, rhs_p: Term):
    kept: list = []
    states: list[Term] = [start]
    index: dict[Term, int] = {start: 0}
    cur = start
    for pos, subst, symm in steps:
        from_t = _egg_substitute(rhs_p if symm else lhs_p, subst)
        try:
            if _egg_subterm_at(cur, pos) != from_t:
                return None
        except (IndexError, TypeError):
            return None
        to_t = _egg_substitute(lhs_p if symm else rhs_p, subst)
        nxt = _egg_replace_at(cur, pos, to_t)
        seen = index.get(nxt)
        if seen is not None:
            for t in states[seen + 1:]:
                index.pop(t, None)
            del kept[seen:]
            del states[seen + 1:]
        else:
            kept.append((pos, subst, symm))
            states.append(nxt)
            index[nxt] = len(states) - 1
        cur = nxt
    return kept


def _egg_balanced_trans(parts: list[str]) -> str:
    if len(parts) == 1:
        return parts[0]
    mid = len(parts) // 2
    return f"({_egg_balanced_trans(parts[:mid])}).trans ({_egg_balanced_trans(parts[mid:])})"


def _egg_render_steps(start: Term, target: Term, steps: list,
                      lhs_p: Term, rhs_p: Term, eq1_vars: list[str],
                      goal_vars: list[str]) -> str | None:
    binder = next((b for b in _EGG_BINDER_CANDIDATES if b not in goal_vars), None)
    if binder is None:
        return None
    cur = start
    parts: list[str] = []
    total = 0
    for pos, subst, symm in steps:
        from_t = _egg_substitute(rhs_p if symm else lhs_p, subst)
        to_t = _egg_substitute(lhs_p if symm else rhs_p, subst)
        try:
            if _egg_subterm_at(cur, pos) != from_t:
                return None
        except (IndexError, TypeError):
            return None
        args = " ".join(term_to_lean(subst[v]) for v in eq1_vars)
        inner = f"(h {args})" if args else "(h)"
        if symm:
            inner = f"{inner}.symm"
        if pos:
            ctx = _egg_replace_at(cur, pos, ("var", binder))
            step_proof = f"congrArg (fun {binder} => {term_to_lean(ctx)}) ({inner})"
        else:
            step_proof = inner
        cur = _egg_replace_at(cur, pos, to_t)
        parts.append(step_proof)
        total += len(step_proof.encode("utf-8")) + 10
        if total > EGG_MAX_PROOF_BYTES:
            return None
    if cur != target:
        return None
    if not parts:
        return "rfl"
    return _egg_balanced_trans(parts)


def _egg_ematch(egg: _EggProver, pattern: Term, cid: int, subst: dict,
                by_class: dict[int, list[tuple]]):
    cid = egg.find(cid)
    if pattern[0] == "var":
        v = pattern[1]
        bound = subst.get(v)
        if bound is not None:
            if egg.find(bound) == cid:
                yield subst
            return
        s2 = dict(subst)
        s2[v] = cid
        yield s2
        return
    for node in by_class.get(cid, ()):
        if node[0] != "op":
            continue
        for s1 in _egg_ematch(egg, pattern[1], node[1], subst, by_class):
            yield from _egg_ematch(egg, pattern[2], node[2], s1, by_class)


def egg_saturate_prove(eq1: dict[str, Any], eq2: dict[str, Any], *,
                       time_budget: float) -> str | None:
    lhs_p, rhs_p, eq1_vars = _egg_upper_patterns(eq1)
    goal_vars = list(eq2["variables"])
    L, R = eq2["lhs"], eq2["rhs"]

    egg = _EggProver()
    pool: list[int] = []
    for t in _egg_subterms(L, []) + _egg_subterms(R, []):
        cid = egg.add_term(t)
        if cid not in pool:
            pool.append(cid)

    orientations = []
    for symm, (a, b) in ((False, (lhs_p, rhs_p)), (True, (rhs_p, lhs_p))):
        free = sorted(_egg_pattern_vars(b) - _egg_pattern_vars(a))
        orientations.append((a, b, free, symm))

    deadline = local_deadline(time_budget)
    done: set = set()

    proved = egg.class_of(L) == egg.class_of(R)
    for rnd in range(EGG_ROUNDS):
        if proved or deadline_expired(deadline) or len(egg.enodes) > EGG_MAX_ENODES:
            break
        expand_targets = min(EGG_POOL_MAX, 10 + 6 * rnd)
        free_pool = min(18, 8 + 2 * rnd)

        cur_pool = sorted({egg.find(c) for c in pool},
                          key=lambda c: egg.size_rep[c])
        pool = cur_pool[:EGG_POOL_MAX]
        prods = []
        for p in pool[:expand_targets]:
            for q in pool[:expand_targets]:
                prods.append(egg.add_term(
                    ("op", egg.class_repr[egg.find(p)],
                     egg.class_repr[egg.find(q)])))
        for c in prods:
            c = egg.find(c)
            if c not in pool and len(pool) < EGG_POOL_MAX:
                pool.append(c)

        by_class: dict[int, list[tuple]] = {}
        for node, cid in egg.enodes.items():
            by_class.setdefault(egg.find(cid), []).append(egg.canon(node))

        apps = []
        out_of_time = False
        for oi, (a, b, free, symm) in enumerate(orientations):
            if out_of_time:
                break
            classes = pool[:expand_targets] if a[0] == "var" else list(by_class)
            for cid in classes:
                if deadline_expired(deadline):
                    out_of_time = True
                    break
                for subst in _egg_ematch(egg, a, cid, {}, by_class):
                    if len(apps) >= EGG_MAX_APPS or deadline_expired(deadline):
                        out_of_time = True
                        break
                    key = (oi, egg.find(cid),
                           tuple(sorted((v, egg.find(c)) for v, c in subst.items())))
                    if not free:
                        if key in done:
                            continue
                        apps.append((0, key, a, b, subst, symm))
                    else:
                        for combo in product(pool[:free_pool], repeat=len(free)):
                            key2 = key + (tuple(egg.find(c) for c in combo),)
                            if key2 in done:
                                continue
                            s2 = dict(subst)
                            s2.update(zip(free, combo))
                            cost = sum(egg.size_rep[egg.find(c)]
                                       for c in s2.values())
                            apps.append((cost, key2, a, b, s2, symm))
                if out_of_time:
                    break
        apps.sort(key=lambda x: x[0])

        merged_any = False
        capped = False
        applied_now = 0
        for cost, key, lhs_pat, rhs_pat, subst_cls, symm in apps:
            if applied_now > EGG_EXPAND_CAP and cost > 0:
                capped = True
                break
            if deadline_expired(deadline) or len(egg.enodes) > EGG_MAX_ENODES:
                capped = True
                break
            if key in done:
                continue
            done.add(key)
            applied_now += 1
            subst_terms = {v: egg.class_repr[egg.find(c)]
                           for v, c in subst_cls.items()}
            l_term = _egg_substitute(lhs_pat, subst_terms)
            r_term = _egg_substitute(rhs_pat, subst_terms)
            egg.add_term(l_term)
            egg.add_term(r_term)
            edge = (r_term, l_term) if symm else (l_term, r_term)
            subst_items = tuple(sorted(subst_terms.items()))
            if egg.merge_terms(edge[0], edge[1], ("rule", subst_items)):
                merged_any = True
            if egg.class_of(L) == egg.class_of(R):
                proved = True
                break
        egg.rebuild()
        if egg.class_of(L) == egg.class_of(R):
            proved = True
        if proved or (not merged_any and not capped):
            break

    if egg.class_of(L) != egg.class_of(R):
        return None
    try:
        steps = egg.explain(L, R)
    except (_EggProvenanceError, RecursionError):
        return None
    shortened = _egg_shorten_steps(L, steps, lhs_p, rhs_p)
    if shortened is None:
        return None
    for _ in range(4):
        before = len(shortened)
        bridged = _egg_bridge_steps(L, shortened, lhs_p, rhs_p)
        if bridged is None:
            break
        cut = _egg_shorten_steps(L, bridged, lhs_p, rhs_p)
        if cut is None:
            break
        shortened = cut
        if len(shortened) >= before:
            break
    return _egg_render_steps(L, R, shortened, lhs_p, rhs_p, eq1_vars, goal_vars)


def egg_closure_route(eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[str, str] | None:
    proof_expr = egg_saturate_prove(
        eq1, eq2, time_budget=_eff_time(EGG_TIME_BUDGET))
    if proof_expr is None:
        return None
    code = substitution_true_certificate(eq2["variables"], proof_expr)
    if len(code.encode("utf-8")) > EGG_MAX_CERT_BYTES:
        return None
    return "true:egg_closure", code


EGG_BOOTSTRAP_TOTAL_BUDGET = 24.0
EGG_BOOTSTRAP_LEMMA_BUDGET = 8.0
EGG_BOOTSTRAP_MAX_ATTEMPTS = 6

EGG_COLLAPSE_BUDGET = 40.0


def egg_collapse_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    collapse = lemma_goal("a = b")
    goal_expr = lemma_applies_to_goal(collapse, eq2)
    if goal_expr is None:
        return None
    if not lemma_survives_models(eq1, collapse):
        return None
    proof = egg_saturate_prove(
        eq1, collapse, time_budget=_eff_time(EGG_COLLAPSE_BUDGET))
    if proof is None:
        return None
    code = lemma_certificate(collapse, proof, eq2["variables"], goal_expr)
    if len(code.encode("utf-8")) > MAX_LEAN_CODE_BYTES:
        return None
    return "true:egg_collapse", code


EGG_PRIORITY_LEMMAS = (
    ("left_projection", "a ◇ b = a"),
    ("right_projection", "a ◇ b = b"),
    ("product_constant", "a ◇ b = c ◇ d"),
    ("left_row_constant", "a ◇ b = a ◇ c"),
    ("right_col_constant", "a ◇ b = c ◇ b"),
)


EGG_PROBE_COLLAPSE_BUDGET = 6.0
EGG_PROBE_LEMMA_BUDGET = 2.0
EGG_PROBE_LEMMAS = (
    ("left_row_constant", "a ◇ b = a ◇ c"),
    ("right_col_constant", "a ◇ b = c ◇ b"),
)


def egg_probe_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    collapse = lemma_goal("a = b")
    goal_expr = lemma_applies_to_goal(collapse, eq2)
    if goal_expr is not None and lemma_survives_models(eq1, collapse):
        proof = egg_saturate_prove(
            eq1, collapse, time_budget=EGG_PROBE_COLLAPSE_BUDGET)
        if proof is not None:
            code = lemma_certificate(collapse, proof, eq2["variables"], goal_expr)
            if len(code.encode("utf-8")) <= MAX_LEAN_CODE_BYTES:
                return "true:egg_collapse", code
    for name, text in EGG_PROBE_LEMMAS:
        lemma = lemma_goal(text)
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        proof = egg_saturate_prove(
            eq1, lemma, time_budget=EGG_PROBE_LEMMA_BUDGET)
        if proof is None:
            continue
        code = lemma_certificate(lemma, proof, eq2["variables"], proof_expr)
        if len(code.encode("utf-8")) <= MAX_LEAN_CODE_BYTES:
            return f"true:egg_bootstrap:{name}", code
    return None


def egg_priority_bootstrap_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    route_deadline = local_deadline(_eff_time(EGG_COLLAPSE_BUDGET * 2))
    for name, text in EGG_PRIORITY_LEMMAS:
        if deadline_expired(route_deadline):
            return None
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        proof = egg_saturate_prove(
            eq1, lemma, time_budget=_eff_time(EGG_COLLAPSE_BUDGET))
        if proof is None:
            continue
        code = lemma_certificate(lemma, proof, eq2["variables"], proof_expr)
        if len(code.encode("utf-8")) > MAX_LEAN_CODE_BYTES:
            continue
        return f"true:egg_bootstrap:{name}", code
    return None


def egg_bootstrap_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    route_deadline = local_deadline(_eff_time(EGG_BOOTSTRAP_TOTAL_BUDGET))
    attempts = 0
    for name, text in full_lemma_library():
        if attempts >= EGG_BOOTSTRAP_MAX_ATTEMPTS:
            return None
        if deadline_expired(route_deadline):
            return None
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        attempts += 1
        lemma_proof = egg_saturate_prove(
            eq1, lemma, time_budget=_eff_time(EGG_BOOTSTRAP_LEMMA_BUDGET))
        if lemma_proof is None:
            continue
        code = lemma_certificate(lemma, lemma_proof, eq2["variables"], proof_expr)
        if len(code.encode("utf-8")) > MAX_LEAN_CODE_BYTES:
            continue
        return f"true:egg_bootstrap:{name}", code
    return None


class _EggRule(NamedTuple):
    lhs: Term
    rhs: Term
    variables: tuple[str, ...]
    hyp: str


def _egg_rule_from(eq: dict[str, Any], hyp: str) -> _EggRule:
    lhs_p, rhs_p, names = _egg_upper_patterns(eq)
    return _EggRule(lhs_p, rhs_p, tuple(names), hyp)


EGG_MULTI_EXPLAIN_DEPTH = 400
EGG_MULTI_EXPLAIN_BUDGET = 20_000
EGG_MULTI_BRIDGE_MAX_STATES = 400


class _EggProverMulti(_EggProver):
    def explain_multi(self, s: Term, t: Term, *, depth: int = 0,
                      budget: list[int] | None = None,
                      deadline: float | None = None) -> list[tuple]:
        if depth > EGG_MULTI_EXPLAIN_DEPTH:
            raise _EggProvenanceError("explanation recursion too deep")
        if budget is None:
            budget = [EGG_MULTI_EXPLAIN_BUDGET]
        steps: list[tuple] = []
        cur = s
        for a, b, reason, flipped in self._tree_path(s, t):
            if a != cur:
                raise _EggProvenanceError("path does not chain")
            budget[0] -= 1
            if budget[0] < 0:
                raise _EggProvenanceError("explanation too long")
            if deadline_expired(deadline):
                raise _EggProvenanceError("explanation ran out of time")
            if reason and reason[0] == "rule":
                _, subst_items, rule_idx = reason
                steps.append(((), rule_idx, dict(subst_items), flipped))
                cur = b
            elif reason and reason[0] == "congr":
                if a[0] != "op" or b[0] != "op":
                    raise _EggProvenanceError("congr edge on non-op terms")
                for sub in self.explain_multi(a[1], b[1], depth=depth + 1,
                                              budget=budget, deadline=deadline):
                    steps.append((("L",) + sub[0], sub[1], sub[2], sub[3]))
                for sub in self.explain_multi(a[2], b[2], depth=depth + 1,
                                              budget=budget, deadline=deadline):
                    steps.append((("R",) + sub[0], sub[1], sub[2], sub[3]))
                cur = b
            else:
                raise _EggProvenanceError(f"unknown reason {reason!r}")
        if cur != t:
            raise _EggProvenanceError("explanation does not reach target")
        return steps


def _egg_step_sides(rule: _EggRule, subst: dict[str, Term],
                    symm: bool) -> tuple[Term, Term] | None:
    if not set(rule.variables) <= set(subst):
        return None
    frm = rule.rhs if symm else rule.lhs
    to = rule.lhs if symm else rule.rhs
    return _egg_substitute(frm, subst), _egg_substitute(to, subst)


def _egg_one_step_between_multi(s: Term, t: Term, rules: list[_EggRule]):
    if s == t:
        return None
    pos = _egg_diff_pos(s, t)
    if pos is None:
        return None
    sub_s = _egg_subterm_at(s, pos)
    sub_t = _egg_subterm_at(t, pos)
    for idx, rule in enumerate(rules):
        for symm, (frm, to) in ((False, (rule.lhs, rule.rhs)),
                                (True, (rule.rhs, rule.lhs))):
            subst = _egg_match_pattern(frm, sub_s, {})
            if subst is None:
                continue
            subst2 = _egg_match_pattern(to, sub_t, dict(subst))
            if subst2 is None or not set(rule.variables) <= set(subst2):
                continue
            if _egg_substitute(frm, subst2) == sub_s:
                return (pos, idx, subst2, symm)
    return None


def _egg_shorten_steps_multi(start: Term, steps: list, rules: list[_EggRule]):
    kept: list = []
    states: list[Term] = [start]
    index: dict[Term, int] = {start: 0}
    cur = start
    for pos, idx, subst, symm in steps:
        if not 0 <= idx < len(rules):
            return None
        sides = _egg_step_sides(rules[idx], subst, symm)
        if sides is None:
            return None
        from_t, to_t = sides
        try:
            if _egg_subterm_at(cur, pos) != from_t:
                return None
        except (IndexError, TypeError):
            return None
        nxt = _egg_replace_at(cur, pos, to_t)
        seen = index.get(nxt)
        if seen is not None:
            for term in states[seen + 1:]:
                index.pop(term, None)
            del kept[seen:]
            del states[seen + 1:]
        else:
            kept.append((pos, idx, subst, symm))
            states.append(nxt)
            index[nxt] = len(states) - 1
        cur = nxt
    return kept


def _egg_bridge_steps_multi(start: Term, steps: list, rules: list[_EggRule],
                            *, deadline: float | None = None):
    states: list[Term] = [start]
    cur = start
    for pos, idx, subst, symm in steps:
        sides = _egg_step_sides(rules[idx], subst, symm)
        if sides is None:
            return None
        cur = _egg_replace_at(cur, pos, sides[1])
        states.append(cur)
    if len(states) > EGG_MULTI_BRIDGE_MAX_STATES:
        return None
    out: list = []
    i = 0
    while i < len(states) - 1:
        if deadline_expired(deadline):
            return None
        jumped = False
        for j in range(len(states) - 1, i + 1, -1):
            step = _egg_one_step_between_multi(states[i], states[j], rules)
            if step is not None:
                out.append(step)
                i = j
                jumped = True
                break
        if not jumped:
            if len(steps) != len(states) - 1:
                return None
            out.append(steps[i])
            i += 1
    return out


def _egg_render_steps_multi(start: Term, target: Term, steps: list,
                            rules: list[_EggRule], goal_vars: list[str],
                            *, max_bytes: int) -> str | None:
    binder = next((b for b in _EGG_BINDER_CANDIDATES if b not in goal_vars), None)
    if binder is None:
        return None
    cur = start
    parts: list[str] = []
    total = 0
    for pos, idx, subst, symm in steps:
        if not 0 <= idx < len(rules):
            return None
        rule = rules[idx]
        sides = _egg_step_sides(rule, subst, symm)
        if sides is None:
            return None
        from_t, to_t = sides
        try:
            if _egg_subterm_at(cur, pos) != from_t:
                return None
        except (IndexError, TypeError):
            return None
        args = " ".join(term_to_lean(subst[v]) for v in rule.variables)
        inner = f"({rule.hyp} {args})" if args else f"({rule.hyp})"
        if symm:
            inner = f"{inner}.symm"
        if pos:
            ctx = _egg_replace_at(cur, pos, ("var", binder))
            step_proof = f"congrArg (fun {binder} => {term_to_lean(ctx)}) ({inner})"
        else:
            step_proof = inner
        cur = _egg_replace_at(cur, pos, to_t)
        parts.append(step_proof)
        total += len(step_proof.encode("utf-8")) + 10
        if total > max_bytes:
            return None
    if cur != target:
        return None
    if not parts:
        return "rfl"
    return _egg_balanced_trans(parts)


def _egg_run_saturation(rules: list[_EggRule], seed_terms: list[Term], *,
                        time_budget: float,
                        stop_pair: tuple[Term, Term] | None = None,
                        pool_max: int = EGG_POOL_MAX,
                        expand_cap: int = EGG_EXPAND_CAP) -> _EggProverMulti:
    egg = _EggProverMulti()
    pool: list[int] = []
    for term in seed_terms:
        cid = egg.add_term(term)
        if cid not in pool:
            pool.append(cid)

    orientations: list[tuple[int, Term, Term, list[str], bool]] = []
    for idx, rule in enumerate(rules):
        for symm, (a, b) in ((False, (rule.lhs, rule.rhs)),
                             (True, (rule.rhs, rule.lhs))):
            free = sorted(_egg_pattern_vars(b) - _egg_pattern_vars(a))
            orientations.append((idx, a, b, free, symm))

    deadline = local_deadline(time_budget)
    done: set = set()

    def reached() -> bool:
        if stop_pair is None:
            return False
        return egg.class_of(stop_pair[0]) == egg.class_of(stop_pair[1])

    if reached():
        return egg
    for rnd in range(EGG_ROUNDS):
        if deadline_expired(deadline) or len(egg.enodes) > EGG_MAX_ENODES:
            break
        expand_targets = min(pool_max, 10 + 6 * rnd)
        free_pool = min(18, 8 + 2 * rnd)

        cur_pool = sorted({egg.find(c) for c in pool},
                          key=lambda c: egg.size_rep[c])
        pool = cur_pool[:pool_max]
        prods = []
        for p in pool[:expand_targets]:
            for q in pool[:expand_targets]:
                prods.append(egg.add_term(
                    ("op", egg.class_repr[egg.find(p)],
                     egg.class_repr[egg.find(q)])))
        for c in prods:
            c = egg.find(c)
            if c not in pool and len(pool) < pool_max:
                pool.append(c)

        by_class: dict[int, list[tuple]] = {}
        for node, cid in egg.enodes.items():
            by_class.setdefault(egg.find(cid), []).append(egg.canon(node))

        apps = []
        out_of_time = False
        for oi, (ridx, a, b, free, symm) in enumerate(orientations):
            if out_of_time:
                break
            classes = pool[:expand_targets] if a[0] == "var" else list(by_class)
            for cid in classes:
                if deadline_expired(deadline):
                    out_of_time = True
                    break
                for subst in _egg_ematch(egg, a, cid, {}, by_class):
                    if deadline_expired(deadline):
                        out_of_time = True
                        break
                    key = (oi, egg.find(cid),
                           tuple(sorted((v, egg.find(c)) for v, c in subst.items())))
                    if not free:
                        if key in done:
                            continue
                        apps.append((0, key, ridx, a, b, subst, symm))
                    else:
                        for combo in product(pool[:free_pool], repeat=len(free)):
                            key2 = key + (tuple(egg.find(c) for c in combo),)
                            if key2 in done:
                                continue
                            s2 = dict(subst)
                            s2.update(zip(free, combo))
                            cost = sum(egg.size_rep[egg.find(c)]
                                       for c in s2.values())
                            apps.append((cost, key2, ridx, a, b, s2, symm))
        apps.sort(key=lambda x: x[0])

        merged_any = False
        capped = False
        applied_now = 0
        for cost, key, ridx, lhs_pat, rhs_pat, subst_cls, symm in apps:
            if applied_now > expand_cap and cost > 0:
                capped = True
                break
            if deadline_expired(deadline) or len(egg.enodes) > EGG_MAX_ENODES:
                capped = True
                break
            if key in done:
                continue
            done.add(key)
            applied_now += 1
            subst_terms = {v: egg.class_repr[egg.find(c)]
                           for v, c in subst_cls.items()}
            l_term = _egg_substitute(lhs_pat, subst_terms)
            r_term = _egg_substitute(rhs_pat, subst_terms)
            egg.add_term(l_term)
            egg.add_term(r_term)
            edge = (r_term, l_term) if symm else (l_term, r_term)
            subst_items = tuple(sorted(subst_terms.items()))
            if egg.merge_terms(edge[0], edge[1], ("rule", subst_items, ridx)):
                merged_any = True
            if reached():
                return egg
        egg.rebuild()
        if reached():
            return egg
        if not merged_any and not capped:
            break
    return egg


def _egg_extract_proof(egg: _EggProverMulti, rules: list[_EggRule],
                       lhs: Term, rhs: Term, goal_vars: list[str],
                       *, max_bytes: int,
                       deadline: float | None = None) -> str | None:
    if egg.class_of(lhs) != egg.class_of(rhs):
        return None
    try:
        steps = egg.explain_multi(lhs, rhs, deadline=deadline)
    except (_EggProvenanceError, RecursionError, KeyError):
        return None
    shortened = _egg_shorten_steps_multi(lhs, steps, rules)
    if shortened is None:
        return None
    for _ in range(4):
        if deadline_expired(deadline):
            break
        before = len(shortened)
        bridged = _egg_bridge_steps_multi(lhs, shortened, rules,
                                          deadline=deadline)
        if bridged is None:
            break
        cut = _egg_shorten_steps_multi(lhs, bridged, rules)
        if cut is None:
            break
        shortened = cut
        if len(shortened) >= before:
            break
    return _egg_render_steps_multi(lhs, rhs, shortened, rules, goal_vars,
                                   max_bytes=max_bytes)


def egg_saturate_prove_multi(rules: list[_EggRule], target: dict[str, Any], *,
                             time_budget: float,
                             max_proof_bytes: int = EGG_MAX_PROOF_BYTES
                             ) -> str | None:
    lhs, rhs = target["lhs"], target["rhs"]
    seeds = _egg_subterms(lhs, []) + _egg_subterms(rhs, [])
    egg = _egg_run_saturation(rules, seeds, time_budget=time_budget,
                              stop_pair=(lhs, rhs))
    return _egg_extract_proof(egg, rules, lhs, rhs, list(target["variables"]),
                              max_bytes=max_proof_bytes,
                              deadline=local_deadline(time_budget))


EGG_LADDER_MAX_LAW_BYTES = 8_000
EGG_LADDER_RUNG_BUDGET = 2.0
EGG_LADDER_RUNG_BUDGET_CAP = 6.0
EGG_LADDER_RUNG_SCAN_LIMIT = 200


def _egg_find_rung(eq1: dict[str, Any], rules: list[_EggRule], *,
                   skip: set, deadline: float | None
                   ) -> tuple[dict[str, Any], str] | None:
    scanned = 0
    for _name, text in full_lemma_library():
        if scanned >= EGG_LADDER_RUNG_SCAN_LIMIT or deadline_expired(deadline):
            return None
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        if canonical_law_key(lemma) in skip:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        scanned += 1
        proof = egg_saturate_prove_multi(
            rules, lemma,
            time_budget=min(_eff_time(EGG_LADDER_RUNG_BUDGET),
                            EGG_LADDER_RUNG_BUDGET_CAP),
            max_proof_bytes=EGG_LADDER_MAX_LAW_BYTES)
        if proof is None:
            continue
        skip.add(canonical_law_key(lemma))
        return lemma, proof
    return None


def lemma_closes_goal(lemma: dict[str, Any], eq2: dict[str, Any]) -> str | None:
    forward = lemma_applies_to_goal(lemma, eq2)
    if forward is not None:
        return forward
    reverse = {"lhs": eq2["rhs"], "rhs": eq2["lhs"],
               "variables": list(eq2["variables"]),
               "text": eq2.get("text", "")}
    simple = simple_true_proof_expr(lemma, reverse, hypothesis_name="hlem")
    if simple is not None:
        return f"({simple[1]}).symm"
    chain = find_rewrite_chain(
        lemma, reverse, max_depth=LEMMA_APPLY_CHAIN_MAX_DEPTH,
        hypothesis_name="hlem")
    if chain is not None:
        return f"({chain[1]}).symm"
    return None


GOAL_GENERALIZATION_MAX = 10
_GENERALIZATION_BINDERS = ("a", "b", "c", "d", "e", "f", "g")


def _term_positions(term: Term, prefix: tuple = ()) -> list[tuple[tuple, Term]]:
    out = [(prefix, term)]
    if term[0] == "op":
        out.extend(_term_positions(term[1], prefix + ("L",)))
        out.extend(_term_positions(term[2], prefix + ("R",)))
    return out


def _abstract_occurrences(lhs: Term, rhs: Term, targets: set[tuple],
                          hole: str) -> tuple[Term, Term]:
    def walk(term: Term, side: str, prefix: tuple) -> Term:
        if (side, prefix) in targets:
            return ("var", hole)
        if term[0] == "var":
            return term
        return ("op", walk(term[1], side, prefix + ("L",)),
                walk(term[2], side, prefix + ("R",)))
    return walk(lhs, "L", ()), walk(rhs, "R", ())


def _canonical_law(lhs: Term, rhs: Term,
                   holes: dict[str, Term]) -> tuple[dict[str, Any], dict[str, Term]] | None:
    order: list[str] = []

    def collect(term: Term) -> None:
        if term[0] == "var":
            if term[1] not in order:
                order.append(term[1])
            return
        collect(term[1])
        collect(term[2])
    collect(lhs)
    collect(rhs)
    if len(order) > len(_GENERALIZATION_BINDERS):
        return None
    rename = dict(zip(order, _GENERALIZATION_BINDERS))

    def apply(term: Term) -> Term:
        if term[0] == "var":
            return ("var", rename[term[1]])
        return ("op", apply(term[1]), apply(term[2]))
    new_lhs, new_rhs = apply(lhs), apply(rhs)
    subst = {rename[v]: holes.get(v, ("var", v)) for v in order}
    law = {
        "lhs": new_lhs,
        "rhs": new_rhs,
        "variables": [rename[v] for v in order],
        "text": f"{term_to_lean(new_lhs)} = {term_to_lean(new_rhs)}",
    }
    return law, subst


def goal_generalization_pivots(
    eq2: dict[str, Any]
) -> list[tuple[str, dict[str, Any], str]]:
    lhs, rhs = eq2["lhs"], eq2["rhs"]
    positions = ([("L", p, t) for p, t in _term_positions(lhs)]
                 + [("R", p, t) for p, t in _term_positions(rhs)])
    goal_vars = set(eq2["variables"])
    hole_names = [f"__g{i}" for i in range(len(_GENERALIZATION_BINDERS))]

    subterm_groups: dict[Term, set[tuple]] = {}
    for side, pos, term in positions:
        if term[0] == "var" or (term == lhs and side == "L") or (
                term == rhs and side == "R"):
            continue
        subterm_groups.setdefault(term, set()).add((side, pos))

    var_occurrences: dict[str, list[tuple]] = {}
    for side, pos, term in positions:
        if term[0] == "var":
            var_occurrences.setdefault(term[1], []).append((side, pos))
    var_singles = [(v, {occ}) for v, occs in var_occurrences.items()
                   if len(occs) > 1 for occ in occs]

    candidates: list[tuple[int, str, dict[tuple, Term]]] = []

    def add(label: str, groups: list[tuple[Term, set[tuple]]]) -> None:
        assignment: dict[tuple, Term] = {}
        for index, (term, occs) in enumerate(groups):
            for occ in occs:
                assignment[occ] = term
            _ = index
        candidates.append((len(assignment), label, assignment))

    scheme1 = sorted(subterm_groups.items(), key=lambda kv: term_size(kv[0]))
    scheme2 = [(("var", v), occs) for v, occs in var_singles]
    for term, occs in scheme1:
        add("sub", [(term, occs)])
    for term, occs in scheme2:
        add("var", [(term, occs)])
    for t1, o1 in scheme1:
        for t2, o2 in scheme2:
            if o1 & o2:
                continue
            add("sub+var", [(t1, o1), (t2, o2)])

    out: list[tuple[str, dict[str, Any], str]] = []
    seen: set = set()
    for _size, label, assignment in candidates:
        by_term: dict[Term, set[tuple]] = {}
        for occ, term in assignment.items():
            by_term.setdefault(term, set()).add(occ)
        if len(by_term) > len(hole_names):
            continue
        holes: dict[str, Term] = {}
        gen_lhs, gen_rhs = lhs, rhs
        for index, (term, occs) in enumerate(sorted(
                by_term.items(), key=lambda kv: term_to_lean(kv[0]))):
            hole = hole_names[index]
            if hole in goal_vars:
                break
            holes[hole] = term
            gen_lhs, gen_rhs = _abstract_occurrences(gen_lhs, gen_rhs, occs, hole)
        else:
            if gen_lhs == gen_rhs:
                continue
            built = _canonical_law(gen_lhs, gen_rhs, holes)
            if built is None:
                continue
            law, subst = built
            try:
                if (_egg_substitute(law["lhs"], subst) != lhs
                        or _egg_substitute(law["rhs"], subst) != rhs):
                    continue
            except KeyError:
                continue
            key = canonical_law_key(law)
            if key in seen:
                continue
            seen.add(key)
            proof = call_expression(law["variables"], subst, "hlem")
            out.append((f"goal_{label}{len(out)}", law, f"({proof})"))
            if len(out) >= GOAL_GENERALIZATION_MAX:
                break
    return out


EGG_LADDER_PIVOTS = (
    ("collapse", "a = b"),
    ("left_projection", "a ◇ b = a"),
    ("right_projection", "a ◇ b = b"),
    ("left_row_constant", "a ◇ b = a ◇ c"),
    ("right_col_constant", "a ◇ b = c ◇ b"),
    ("product_constant", "a ◇ b = c ◇ d"),
    ("left_sq_projection", "(a ◇ b) ◇ c = a"),
    ("right_sq_projection", "a ◇ (b ◇ c) = c"),
    ("triple_left", "((a ◇ b) ◇ c) ◇ d = a"),
    ("triple_right", "a ◇ (b ◇ (c ◇ d)) = d"),
)

EGG_LADDER_TOTAL_BUDGET = 60.0
EGG_LADDER_TARGET_BUDGET = 8.0
EGG_LADDER_FIRST_ROUND_BUDGET = 2.0
EGG_LADDER_GENERALIZATION_BUDGET = 4.0
EGG_LADDER_MAX_HELPERS = 4


def egg_ladder_route(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> tuple[str, str] | None:
    route_deadline = local_deadline(_eff_time(EGG_LADDER_TOTAL_BUDGET))
    targets: list[tuple[str, dict[str, Any], str]] = []
    for name, text in EGG_LADDER_PIVOTS:
        try:
            lemma = lemma_goal(text)
        except ValueError:
            continue
        goal_expr = lemma_closes_goal(lemma, eq2)
        if goal_expr is None:
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        targets.append((name, lemma, goal_expr))
    if not targets:
        return None

    rules = [_egg_rule_from(eq1, "h")]
    blocks: list[tuple[str, dict[str, Any], str]] = []
    seen: set = {canonical_law_key(eq1)}

    for depth in range(EGG_LADDER_MAX_HELPERS + 1):
        target_budget = _eff_time(
            EGG_LADDER_TARGET_BUDGET if depth else EGG_LADDER_FIRST_ROUND_BUDGET)
        for name, lemma, goal_expr in targets:
            if deadline_expired(route_deadline):
                return None
            proof = egg_saturate_prove_multi(
                rules, lemma, time_budget=target_budget)
            if proof is None:
                continue
            code = lemma_chain_certificate(
                blocks, lemma, proof, eq2["variables"], goal_expr)
            if len(code.encode("utf-8")) <= MAX_LEAN_CODE_BYTES:
                return f"true:egg_ladder:{name}:h{len(blocks)}", code
        if blocks and not deadline_expired(route_deadline):
            proof = egg_saturate_prove_multi(
                rules, eq2, time_budget=target_budget)
            if proof is not None:
                code = _lemma_chain_goal_certificate(
                    blocks, eq2["variables"], proof)
                if len(code.encode("utf-8")) <= MAX_LEAN_CODE_BYTES:
                    return f"true:egg_ladder:goal:h{len(blocks)}", code
        if depth == EGG_LADDER_MAX_HELPERS or deadline_expired(route_deadline):
            break
        rung = _egg_find_rung(eq1, rules, skip=seen, deadline=route_deadline)
        if rung is None:
            break
        law, rung_proof = rung
        hyp = f"hlem{len(blocks)}"
        blocks.append((hyp, law, rung_proof))
        rules.append(_egg_rule_from(law, hyp))

    for name, lemma, goal_expr in goal_generalization_pivots(eq2):
        if deadline_expired(route_deadline):
            break
        if any(canonical_law_key(lemma) == canonical_law_key(existing)
               for _n, existing, _e in targets):
            continue
        if not lemma_survives_models(eq1, lemma):
            continue
        proof = egg_saturate_prove_multi(
            rules, lemma,
            time_budget=_eff_time(EGG_LADDER_GENERALIZATION_BUDGET))
        if proof is None:
            continue
        code = lemma_chain_certificate(
            blocks, lemma, proof, eq2["variables"], goal_expr)
        if len(code.encode("utf-8")) <= MAX_LEAN_CODE_BYTES:
            return f"true:egg_ladder:{name}:h{len(blocks)}", code
    return None


def projection_cue(eq1: dict[str, Any], eq2: dict[str, Any]) -> bool:
    eq1_left, eq1_right = boundary_vars(eq1["lhs"])
    eq2_left, eq2_right = boundary_vars(eq2["rhs"])
    return eq1_left != eq2_left or eq1_right != eq2_right


_PRIORITY_CUES: tuple[tuple[int, str, tuple[Any, ...], Any], ...] = (
    (1, "true:deep_repeat_singleton", (deep_repeat_singleton_route.match,), None),
    (1, "true:reverse_deep_repeat_singleton", (reverse_deep_repeat_singleton_route.match,), None),
    (1, "true:sandwich_repeat_singleton", (sandwich_repeat_singleton_route.match,), None),
    (1, "true:outer_sandwich_singleton", (outer_sandwich_singleton_route.match,), None),
    (1, "true:forked_square_singleton", (forked_square_singleton_route.match,), None),
    (1, "true:crossed_pair_singleton", (crossed_pair_singleton_route.match,), None),
    (1, "true:nested_square_singleton", (nested_square_singleton_route.match,), None),
    (1, "true:tail_square_singleton", (tail_square_singleton_route.match,), None),
    (1, "true:paired_tail_singleton", (paired_tail_singleton_route.match,), None),
    (1, "true:wrapped_tail_singleton", (wrapped_tail_singleton_route.match,), None),
    (1, "true:middle_self_collapse", (_middle_self_collapse,), None),
    (1, "true:front_double_self_collapse", (_front_double_self_collapse,), None),
    (1, "true:alternating_front_self_collapse", (_alternating_front_self_collapse,), None),
    (1, "true:mirrored_alternating_front_self_collapse", (_mirrored_alternating_front_self_collapse,), None),
    (2, "true:sandwich_left_projection", (_sandwich_left_projection,),
     lambda eq2: projection_proof_expr_from_law(eq2, "left", hypothesis_name="hleft")),
    (2, "true:nested_left_projection", (_nested_left_projection,),
     lambda eq2: projection_from_lemma_goal_proof(eq2, "left", hypothesis_name="hleft")),
    (2, "true:left_projection_collapse",
     (_right_nested_tail_left_projection, _bracket_tail_left_projection,
      _pair_square_left_projection),
     lambda eq2: projection_from_lemma_goal_proof(eq2, "left", hypothesis_name="hleft")),
    (2, "true:left_row_constancy", (_left_row_constancy,),
     lambda eq2: left_row_constancy_term_proof(eq2["lhs"], eq2["rhs"])),
    (2, "true:product_constancy", (_product_constancy,),
     lambda eq2: eq2["lhs"][0] == "op" and eq2["rhs"][0] == "op"),
    (2, "true:repeated_prefix_product_constancy", (_repeated_prefix_product,),
     lambda eq2: eq2["lhs"][0] == "op" and eq2["rhs"][0] == "op"),
    (2, "true:double_tail_square_product", (_double_tail_square_product,),
     square_product_basis_goal),
    (2, "true:square_twist_comm", (_square_twist_comm,),
     lambda eq2: commutative_term_key(eq2["lhs"]) == commutative_term_key(eq2["rhs"])),
    (2, "true:square_to_right_product", (_square_to_right_product,),
     square_to_right_product_goal),
    (2, "true:right_projection_collapse",
     (_tail_square_right_projection, _nested_tail_right_projection,
      _sandwich_tail_right_projection, _left_pair_tail_right_projection),
     lambda eq2: projection_from_lemma_goal_proof(eq2, "right", hypothesis_name="hright")),
)


def problem_priority(problem: dict[str, Any], eq1: dict[str, Any], eq2: dict[str, Any]) -> tuple[int, int, str]:
    if is_reflexive_problem(problem):
        return (0, len(eq2["text"]), "true:reflexive")
    if singleton_route(eq1):
        return (1, len(eq2["text"]), "true:singleton")
    for tier, label, matchers, guard in _PRIORITY_CUES:
        if any(match(eq1) for match in matchers) and (guard is None or guard(eq2)):
            return (tier, len(eq2["text"]), label)
    if (*equation_shape_key(eq1), *equation_shape_key(eq2)) in narrow_grind_true_shape_keys():
        return (2, len(eq2["text"]), "true:narrow_grind")
    if direct_substitution_route(eq1, eq2):
        return (2, len(eq2["text"]), "true:rewrite")
    if bridge_route(eq1, eq2):
        return (3, len(eq2["text"]), "true:bridge")
    if projection_cue(eq1, eq2):
        return (4, len(eq2["text"]), "false:projection_cue")
    if absorption_hypothesis(eq1):
        return (5, len(eq1["text"]) + len(eq2["text"]), "true:absorption")
    return (6, len(eq1["text"]) + len(eq2["text"]), "false:finite_search")


def _false_witness_portfolio(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_n: int,
    deadline: float | None,
) -> tuple[int, list[list[int]], str] | None:
    for name, table in WITNESS_TABLES:
        if deadline_expired(deadline):
            return None
        if witness_check(eq1, eq2, table):
            return len(table), table, f"false:witness:{name}"

    family_max = max(max_n, STRUCTURED_MAX_N)
    for route, table in structured_family_tables(max_n=family_max):
        if deadline_expired(deadline):
            return None
        if witness_check(eq1, eq2, table):
            return len(table), table, route

    for route, table in affine_family_tables(max_n=max(max_n, max(AFFINE_LINEAR_SIZES))):
        if deadline_expired(deadline):
            return None
        if witness_check(eq1, eq2, table):
            return len(table), table, route

    for route, table in quadratic_family_tables(max_n=family_max):
        if deadline_expired(deadline):
            return None
        if witness_check(eq1, eq2, table):
            return len(table), table, route

    for n in range(2, max_n + 1):
        for table in enumerate_tables(n):
            if deadline_expired(deadline):
                return None
            if witness_check(eq1, eq2, table):
                return n, table, f"false:enum_fin{n}"
    return None


def find_counterexample(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    max_n: int = ENUMERATION_MAX_N,
    time_budget: float | None = None,
    allow_dual: bool = True,
) -> tuple[int, list[list[int]], str] | None:
    found = _false_witness_portfolio(
        eq1, eq2, max_n=max_n, deadline=local_deadline(time_budget))
    if found is not None:
        return found
    if not allow_dual:
        return None
    dual = _false_witness_portfolio(
        dual_equation(eq1), dual_equation(eq2), max_n=max_n,
        deadline=local_deadline(time_budget))
    if dual is not None:
        n, table, route = dual
        return n, transpose_table(table), f"false:dual:{route}"
    return None


def _lm_eval(term: Term, env: dict[str, int], table: list[list[int]]) -> int:
    if term[0] == "var":
        return env[term[1]]
    return table[_lm_eval(term[1], env, table)][_lm_eval(term[2], env, table)]


def _lm_envs(equation: dict[str, Any], n: int) -> list[dict[str, int]]:
    variables = list(equation["variables"])
    return [dict(zip(variables, values))
            for values in product(range(n), repeat=len(variables))]


def _lm_cells(term: Term, env: dict[str, int], table: list[list[int]],
              out: set[tuple[int, int]]) -> int:
    if term[0] == "var":
        return env[term[1]]
    a = _lm_cells(term[1], env, table, out)
    b = _lm_cells(term[2], env, table, out)
    out.add((a, b))
    return table[a][b]


_CONSTRAINT_EXHAUSTED = False


def reset_constraint_evidence() -> None:
    global _CONSTRAINT_EXHAUSTED
    _CONSTRAINT_EXHAUSTED = False


def constraint_search_exhausted() -> bool:
    return _CONSTRAINT_EXHAUSTED


MAX_WITNESS_ORDER = 25

LEGACY_MAX_WITNESS_ORDER = 10

MAX_WITNESS_DECIDE_APPLICATIONS = 20_000

CONSTRAINT_ORDERS = (8, 9, 6, 4, 10)
CONSTRAINT_TIME_BUDGET = 3.0
CONSTRAINT_MAX_NODES = 100_000_000
CONSTRAINT_WIDE_ORDERS = (8, 9, 10, 6, 5, 7, 4)
CONSTRAINT_WIDE_PER_ORDER_BUDGET = 45.0
CONSTRAINT_CHEAP_MAX_VARIABLES = 4
CONSTRAINT_WIDE_MAX_VARIABLES = 6
CONSTRAINT_MAX_INSTANCES = 20_000
_CELL_UNKNOWN = -1


def _cp_eval(term: Term, env: dict[str, int], table: list[int], n: int):
    if term[0] == "var":
        return env[term[1]], None, None
    lv, lr, _ = _cp_eval(term[1], env, table, n)
    rv, rr, _ = _cp_eval(term[2], env, table, n)
    if lv is None or rv is None:
        return None, (lr if lr is not None else rr), None
    idx = lv * n + rv
    val = table[idx]
    if val == _CELL_UNKNOWN:
        return None, idx, idx
    return val, None, None


def _cp_instances(eq: dict[str, Any], n: int) -> list[tuple[dict[str, int], Term, Term]]:
    variables = list(eq["variables"])
    lhs, rhs = eq["lhs"], eq["rhs"]
    return [(dict(zip(variables, values)), lhs, rhs)
            for values in product(range(n), repeat=len(variables))]


def _cp_propagate(table: list[int], n: int, instances, value_cap: int) -> bool:
    changed = True
    while changed:
        changed = False
        for env, lhs, rhs in instances:
            lv, _lr, lroot = _cp_eval(lhs, env, table, n)
            rv, _rr, rroot = _cp_eval(rhs, env, table, n)
            if lv is not None and rv is not None:
                if lv != rv:
                    return False
                continue
            if lv is not None and rroot is not None:
                if lv >= value_cap:
                    return False
                table[rroot] = lv
                changed = True
            elif rv is not None and lroot is not None:
                if rv >= value_cap:
                    return False
                table[lroot] = rv
                changed = True
    return True


def _cp_search(eq1: dict[str, Any], eq2: dict[str, Any], n: int,
               deadline: float | None, budget: list[int],
               value_cap: int | None = None) -> list[list[int]] | None:
    instances = _cp_instances(eq1, n)
    eq2_vars = list(eq2["variables"])
    eq2_lhs, eq2_rhs = eq2["lhs"], eq2["rhs"]
    cap = n if value_cap is None else min(n, value_cap)

    def branch(table: list[int]) -> list[list[int]] | None:
        budget[0] -= 1
        if budget[0] <= 0:
            return None
        if deadline is not None and time.monotonic() >= deadline:
            return None
        work = table[:]
        if not _cp_propagate(work, n, instances, cap):
            return None
        lv, _lr, _lroot = _cp_eval(eq2_lhs, tenv, work, n)
        rv, _rr, _rroot = _cp_eval(eq2_rhs, tenv, work, n)
        if lv is not None and rv is not None and lv == rv:
            return None
        blocking: dict[int, int] = {}
        for env, lhs, rhs in instances:
            for term in (lhs, rhs):
                _v, ready, _root = _cp_eval(term, env, work, n)
                if ready is not None:
                    blocking[ready] = blocking.get(ready, 0) + 1
        cell = -1
        if blocking:
            cell = max(blocking, key=lambda k: blocking[k])
        else:
            for term in (eq2_lhs, eq2_rhs):
                _v, ready, _root = _cp_eval(term, tenv, work, n)
                if ready is not None:
                    cell = ready
                    break
        if cell < 0:
            if lv is None or rv is None or lv == rv:
                return None
            filled = [0 if v == _CELL_UNKNOWN else v for v in work]
            return [filled[r * n:(r + 1) * n] for r in range(n)]
        for value in range(cap):
            trial = work[:]
            trial[cell] = value
            got = branch(trial)
            if got is not None:
                return got
        return None

    for target in product(range(cap), repeat=len(eq2_vars)):
        if budget[0] <= 0:
            return None
        if deadline is not None and time.monotonic() >= deadline:
            return None
        tenv = dict(zip(eq2_vars, target))
        found = branch([_CELL_UNKNOWN] * (n * n))
        if found is not None:
            return found
    return None


def constraint_countermodel(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    orders: tuple[int, ...] = CONSTRAINT_ORDERS,
    time_budget: float = CONSTRAINT_TIME_BUDGET,
    per_order: bool = False,
    max_variables: int = CONSTRAINT_CHEAP_MAX_VARIABLES,
    max_instances: int = CONSTRAINT_MAX_INSTANCES,
) -> tuple[int, list[list[int]], str] | None:
    global _CONSTRAINT_EXHAUSTED
    widest = max(len(eq1["variables"]), len(eq2["variables"]))
    if widest > max_variables:
        return None
    shared_deadline = None if per_order else local_deadline(_eff_time(time_budget))
    complete = True
    for n in orders:
        if n ** widest > max_instances:
            complete = False
            continue
        deadline = (local_deadline(_eff_time(time_budget)) if per_order
                    else shared_deadline)
        if deadline is not None and time.monotonic() >= deadline:
            complete = False
            break
        if memory_exceeded() and not try_reclaim_memory():
            complete = False
            break
        budget = [CONSTRAINT_MAX_NODES]
        table = _cp_search(eq1, eq2, n, deadline, budget)
        if budget[0] <= 0:
            complete = False
        if table is None:
            continue
        note_hypothesis_model()
        if table_is_counterexample(eq1, eq2, table):
            return n, table, f"false:constraint_fin{n}"
    if complete:
        _CONSTRAINT_EXHAUSTED = True
    return None


WIDE_DOMAIN_ORDERS = (13, 16, 20, 25, 30, 40, 50, 60)
WIDE_DOMAIN_VALUE_CAP = 10
WIDE_DOMAIN_PER_ORDER_BUDGET = 20.0


def _eq1_has_bare_variable_side(eq1: dict[str, Any]) -> bool:
    return eq1["lhs"][0] == "var" or eq1["rhs"][0] == "var"


def constraint_countermodel_wide_domain(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    orders: tuple[int, ...] = WIDE_DOMAIN_ORDERS,
    value_cap: int = WIDE_DOMAIN_VALUE_CAP,
    time_budget: float = WIDE_DOMAIN_PER_ORDER_BUDGET,
) -> tuple[int, list[list[int]], str] | None:
    if len(eq1["variables"]) > 3 or len(eq2["variables"]) > 3:
        return None
    if _eq1_has_bare_variable_side(eq1):
        return None
    for n in orders:
        deadline = local_deadline(_eff_time(time_budget))
        if deadline is not None and time.monotonic() >= deadline:
            return None
        if memory_exceeded() and not try_reclaim_memory():
            return None
        budget = [CONSTRAINT_MAX_NODES]
        table = _cp_search(eq1, eq2, n, deadline, budget, value_cap=value_cap)
        if table is None:
            continue
        note_hypothesis_model()
        if table_is_counterexample(eq1, eq2, table):
            return n, table, f"false:constraint_wide_fin{n}"
    return None


def local_model_counterexample(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    *,
    sizes: tuple[int, ...] = LOCAL_MODEL_SIZES,
    time_budget: float = LOCAL_MODEL_TIME_BUDGET,
    max_flips: int = LOCAL_MODEL_MAX_FLIPS,
    noise: float = LOCAL_MODEL_NOISE,
    seed: int = 0,
) -> tuple[int, list[list[int]], str] | None:
    deadline = local_deadline(_eff_time(time_budget))
    rng = random.Random(seed)
    lhs1, rhs1 = eq1["lhs"], eq1["rhs"]
    lhs2, rhs2 = eq2["lhs"], eq2["rhs"]
    if _EFFORT != "fast":
        sizes = sizes + (6,)
        max_flips = 800

    for n in sizes:
        envs1 = _lm_envs(eq1, n)
        envs2 = _lm_envs(eq2, n)

        def bad_envs(table: list[list[int]]) -> list[dict[str, int]]:
            return [env for env in envs1
                    if _lm_eval(lhs1, env, table) != _lm_eval(rhs1, env, table)]

        def breaks_goal(table: list[list[int]]) -> bool:
            return any(_lm_eval(lhs2, env, table) != _lm_eval(rhs2, env, table)
                       for env in envs2)

        while time.monotonic() < deadline:
            table = [[rng.randrange(n) for _ in range(n)] for _ in range(n)]
            for _ in range(max_flips):
                if time.monotonic() >= deadline:
                    break
                bad = bad_envs(table)
                if not bad:
                    note_hypothesis_model()
                    if breaks_goal(table) and table_is_counterexample(eq1, eq2, table):
                        return n, table, f"false:local_model{n}"
                    row, col = rng.randrange(n), rng.randrange(n)
                    table[row][col] = rng.randrange(n)
                    continue
                env = bad[rng.randrange(len(bad))]
                cells: set[tuple[int, int]] = set()
                _lm_cells(lhs1, env, table, cells)
                _lm_cells(rhs1, env, table, cells)
                if not cells:
                    break
                row, col = sorted(cells)[rng.randrange(len(cells))]
                if rng.random() < noise:
                    table[row][col] = rng.randrange(n)
                    continue
                best, best_score = table[row][col], len(bad) + 1
                for value in range(n):
                    previous, table[row][col] = table[row][col], value
                    score = len(bad_envs(table))
                    if score < best_score:
                        best, best_score = value, score
                    table[row][col] = previous
                table[row][col] = best
    return None


def _engine_gate() -> bool:
    if _HARD_DEADLINE is not None and time.monotonic() >= _HARD_DEADLINE:
        return True
    if memory_exceeded() and not try_reclaim_memory():
        return True
    return False


RouteResult = tuple[str, str]


def _direct_substitution_entry(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> RouteResult | None:
    direct = direct_substitution_route(eq1, eq2)
    if direct is None:
        return None
    mode, subst = direct
    call_expr = call_expression(eq1["variables"], subst)
    if mode == "symm":
        call_expr = f"({call_expr}).symm"
    route = "true:rewrite" if mode == "direct" else "true:rewrite:symm"
    return route, substitution_true_certificate(eq2["variables"], call_expr)


def _bridge_result(
    finder: Any, eq1: dict[str, Any], eq2: dict[str, Any]
) -> RouteResult | None:
    found = finder(eq1, eq2)
    if found is None:
        return None
    bridge_name, left_subst, right_subst = found
    left_call = call_expression(eq1["variables"], left_subst)
    right_call = call_expression(eq1["variables"], right_subst)
    left_source = int(bridge_name[-2])
    right_source = int(bridge_name[-1])
    left_to_mid = left_call if left_source == 0 else f"({left_call}).symm"
    mid_to_right = f"({right_call}).symm" if right_source == 0 else right_call
    return bridge_name, substitution_true_certificate(
        eq2["variables"], f"({left_to_mid}).trans ({mid_to_right})")


def _bridge_entry(eq1: dict[str, Any], eq2: dict[str, Any]) -> RouteResult | None:
    return _bridge_result(bridge_route, eq1, eq2)


def _completed_bridge_entry(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> RouteResult | None:
    return _bridge_result(completed_bridge_route, eq1, eq2)


def _rewrite_chain_entry(
    eq1: dict[str, Any], eq2: dict[str, Any]
) -> RouteResult | None:
    chain = find_rewrite_chain(eq1, eq2)
    if chain is None:
        return None
    routes, proof_expr = chain
    return ("true:rewrite_chain:" + ",".join(routes),
            substitution_true_certificate(eq2["variables"], proof_expr))


TRUE_ROUTES: tuple[Any, ...] = (
    deep_repeat_singleton_route,
    reverse_deep_repeat_singleton_route,
    sandwich_repeat_singleton_route,
    outer_sandwich_singleton_route,
    forked_square_singleton_route,
    crossed_pair_singleton_route,
    repeated_prefix_product_constancy_route,
    double_tail_square_product_route,
    nested_square_singleton_route,
    tail_square_singleton_route,
    paired_tail_singleton_route,
    wrapped_tail_singleton_route,
    middle_self_collapse_route,
    front_double_self_collapse_route,
    alternating_front_self_collapse_route,
    mirrored_alternating_front_self_collapse_route,
    square_twist_comm_route,
    sandwich_left_projection_route,
    nested_left_projection_route,
    specialized_left_projection_route,
    derived_left_projection_route,
    derived_right_projection_route,
    square_to_right_product_route,
    right_projection_collapse_route,
    right_self_absorption_route,
    repeated_right_square_route,
    self_tail_triple_route,
    nested_left_absorption_route,
    left_row_constancy_route,
    product_constancy_route,
    _direct_substitution_entry,
    _bridge_entry,
    _completed_bridge_entry,
    projection_true_route,
    _rewrite_chain_entry,
    c9_e1072_collapse_route,
    self_square_absorption_route,
    repeat_tail_absorption_route,
    universal_identity_route,
    absorption_context_bridge_route,
    absorption_closure_route,
)


def canonical_eq_text(eq: dict[str, Any]) -> str:
    names: dict[str, str] = {}
    lhs = canonical_term_shape(eq["lhs"], names)
    rhs = canonical_term_shape(eq["rhs"], names)
    return f"{term_to_lean(lhs)} = {term_to_lean(rhs)}"


DISTILLED_CERTS: dict[tuple[str, str], tuple[str, str, str]] = {
    ("v0 = (((v1 ◇ (v0 ◇ v2)) ◇ v0) ◇ v1)",
     "v0 = (v0 ◇ (((v1 ◇ v1) ◇ v0) ◇ v0))"): ("true", "e2920_e1248", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, (((a ◇ (b ◇ c)) ◇ b) ◇ a) = b := by
    intro a b c
    exact (h b a c).symm
  have hlem1 : ∀ a b c : G, ((a ◇ b) ◇ (a ◇ ((a ◇ b) ◇ c))) = a := by
    intro a b c
    exact ((congrArg (fun t => (t ◇ (a ◇ ((a ◇ b) ◇ c)))) (hlem0 a (a ◇ b) c)).symm).trans (hlem0 (a ◇ ((a ◇ b) ◇ c)) a b)
  have hlem2 : ∀ a b : G, ((a ◇ a) ◇ (a ◇ b)) = a := by
    intro a b
    exact ((congrArg (fun t => ((t ◇ a) ◇ (a ◇ b))) (hlem1 a b a)).symm).trans (hlem0 (a ◇ b) a ((a ◇ b) ◇ a))
  have hlem3 : ∀ a b : G, ((a ◇ b) ◇ (a ◇ a)) = a := by
    intro a b
    exact ((congrArg (fun t => ((a ◇ b) ◇ (a ◇ t))) (hlem1 a b a)).symm).trans (hlem1 a b (a ◇ ((a ◇ b) ◇ a)))
  have hlem4 : ∀ a b : G, (((a ◇ a) ◇ b) ◇ a) = (a ◇ a) := by
    intro a b
    exact ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ t)) (hlem2 a a)).symm).trans (hlem3 (a ◇ a) b)
  have hlem5 : ∀ a b : G, ((a ◇ b) ◇ (a ◇ b)) = a := by
    intro a b
    exact ((hlem4 (a ◇ b) a).symm).trans (hlem0 (a ◇ b) a b)
  have hlem6 : ∀ a b c : G, (((a ◇ b) ◇ c) ◇ a) = (a ◇ b) := by
    intro a b c
    exact ((congrArg (fun t => (((a ◇ b) ◇ c) ◇ t)) (hlem5 a b)).symm).trans (hlem3 (a ◇ b) c)
  have hlem7 : ∀ a b c : G, (a ◇ (b ◇ c)) = b := by
    intro a b c
    exact ((hlem6 a (b ◇ c) b).symm).trans (hlem0 a b c)
  have hlem8 : ∀ a b : G, a = b := by
    intro a b
    exact ((hlem7 (((a ◇ a) ◇ (b ◇ a)) ◇ b) a a).symm).trans (hlem0 (a ◇ a) b a)
  intro x y
  exact hlem8 x (x ◇ (((y ◇ y) ◇ x) ◇ x))
"""),
    ("v0 = (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v2))",
     "v0 = (((v0 ◇ v1) ◇ (v2 ◇ v3)) ◇ v1)"): ("true", "e2042_e2692", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, (a ◇ a) = (a ◇ ((a ◇ a) ◇ b)) := by
    intro a b
    exact (h (a ◇ a) (a ◇ a) b).trans (congrArg (fun t => (t ◇ ((a ◇ a) ◇ b))) ((h a (a ◇ a) a).symm))
  have hlem1 : ∀ a : G, ((a ◇ a) ◇ (a ◇ a)) = ((a ◇ a) ◇ a) := by
    intro a
    exact (hlem0 (a ◇ a) (a ◇ a)).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((h a (a ◇ a) a).symm))
  have hlem2 : ∀ a : G, a = (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) := by
    intro a
    exact (h a (a ◇ a) a).trans ((((hlem1 (a ◇ a)).symm).trans (congrArg (fun t => (t ◇ ((a ◇ a) ◇ (a ◇ a)))) (hlem1 a))).trans (congrArg (fun t => (((a ◇ a) ◇ a) ◇ t)) (hlem1 a)))
  have hlem3 : ∀ a b c : G, ((a ◇ a) ◇ a) = ((a ◇ b) ◇ (((a ◇ a) ◇ a) ◇ c)) := by
    intro a b c
    exact (h ((a ◇ a) ◇ a) b c).trans (congrArg (fun t => ((t ◇ b) ◇ (((a ◇ a) ◇ a) ◇ c))) ((hlem2 a).symm))
  have hlem4 : ∀ a b : G, ((a ◇ a) ◇ a) = ((a ◇ b) ◇ a) := by
    intro a b
    exact ((h ((a ◇ a) ◇ a) b ((a ◇ a) ◇ a)).trans (congrArg (fun t => (((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ b) ◇ t)) ((hlem2 a).symm))).trans (congrArg (fun t => ((t ◇ b) ◇ a)) ((hlem2 a).symm))
  have hlem5 : ∀ a b : G, (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) = a := by
    intro a b
    exact ((hlem4 (a ◇ b) (((a ◇ a) ◇ a) ◇ a)).trans (congrArg (fun t => (t ◇ (a ◇ b))) ((hlem3 a b a).symm))).trans ((h a a b).symm)
  have hlem6 : ∀ a b : G, (a ◇ b) = (a ◇ a) := by
    intro a b
    exact ((hlem2 (a ◇ b)).trans (congrArg (fun t => (t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)))) (hlem5 a b))).trans (congrArg (fun t => (a ◇ t)) (hlem5 a b))
  have hlem7 : ∀ a b c : G, (a ◇ b) = (a ◇ c) := by
    intro a b c
    exact (hlem6 a b).trans ((hlem6 a c).symm)
  intro x y z w
  exact (((h x x x).trans (congrArg (fun t => ((t ◇ x) ◇ (x ◇ x))) (hlem7 x x y))).trans (congrArg (fun t => (t ◇ (x ◇ x))) (hlem7 (x ◇ y) x (z ◇ w)))).trans (hlem7 ((x ◇ y) ◇ (z ◇ w)) (x ◇ x) y)
"""),
    ("v0 = (((v1 ◇ (v0 ◇ v2)) ◇ v1) ◇ v0)",
     "v0 = ((v1 ◇ v2) ◇ (v3 ◇ (v4 ◇ v0)))"): ("true", "e2923_e1623", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c d : G, ((a ◇ c) ◇ ((b ◇ ((a ◇ c) ◇ d)) ◇ b)) ◇ a = a := by
    intro a b c d
    exact (congrArg (fun t => (t ◇ ((b ◇ ((a ◇ c) ◇ d)) ◇ b)) ◇ a) (h (a ◇ c) b d)).trans (((h a ((b ◇ ((a ◇ c) ◇ d)) ◇ b) c).symm))
  have hlem1 : ∀ a b c d : G, ((b ◇ a) ◇ b) ◇ ((c ◇ (a ◇ d)) ◇ c) = (c ◇ (a ◇ d)) ◇ c := by
    intro a b c d
    exact (congrArg (fun t => ((b ◇ t) ◇ b) ◇ ((c ◇ (a ◇ d)) ◇ c)) (h a c d)).trans (((h ((c ◇ (a ◇ d)) ◇ c) b a).symm))
  have hlem2 : ∀ a b c d e : G, ((b ◇ ((c ◇ (a ◇ e)) ◇ c)) ◇ b) ◇ ((d ◇ a) ◇ d) = (d ◇ a) ◇ d := by
    intro a b c d e
    exact (congrArg (fun t => ((b ◇ t) ◇ b) ◇ ((d ◇ a) ◇ d)) ((hlem1 a d c e).symm)).trans (((h ((d ◇ a) ◇ d) b ((c ◇ (a ◇ e)) ◇ c)).symm))
  have hlem3 : ∀ a b c d : G, ((b ◇ (a ◇ d)) ◇ (((b ◇ (a ◇ d)) ◇ b) ◇ ((c ◇ a) ◇ c))) ◇ b = b := by
    intro a b c d
    exact (congrArg (fun t => ((b ◇ (a ◇ d)) ◇ (t ◇ ((c ◇ a) ◇ c))) ◇ b) ((hlem1 a c b d).symm)).trans ((hlem0 b ((c ◇ a) ◇ c) (a ◇ d) b))
  have hlem4 : ∀ a b c d : G, (((c ◇ (a ◇ d)) ◇ c) ◇ ((b ◇ a) ◇ b)) ◇ (c ◇ (a ◇ d)) = c ◇ (a ◇ d) := by
    intro a b c d
    exact (congrArg (fun t => (((c ◇ (a ◇ d)) ◇ c) ◇ ((b ◇ t) ◇ b)) ◇ (c ◇ (a ◇ d))) (h a c d)).trans ((hlem0 (c ◇ (a ◇ d)) b c a))
  have hlem5 : ∀ a b c d e : G, (((d ◇ a) ◇ d) ◇ ((b ◇ ((c ◇ (a ◇ e)) ◇ c)) ◇ b)) ◇ (d ◇ a) = d ◇ a := by
    intro a b c d e
    exact (congrArg (fun t => (((d ◇ a) ◇ d) ◇ ((b ◇ t) ◇ b)) ◇ (d ◇ a)) ((hlem1 a d c e).symm)).trans ((hlem0 (d ◇ a) b d ((c ◇ (a ◇ e)) ◇ c)))
  have hlem6 : ∀ a b c d e : G, (((b ◇ (a ◇ e)) ◇ b) ◇ ((d ◇ a) ◇ d)) ◇ ((c ◇ a) ◇ c) = (c ◇ a) ◇ c := by
    intro a b c d e
    exact (congrArg (fun t => (t ◇ ((d ◇ a) ◇ d)) ◇ ((c ◇ a) ◇ c)) ((hlem1 a d b e).symm)).trans ((hlem2 a ((d ◇ a) ◇ d) b c e))
  have hlem7 : ∀ a b c d e : G, (((c ◇ a) ◇ c) ◇ (((b ◇ (a ◇ e)) ◇ b) ◇ ((d ◇ a) ◇ d))) ◇ (c ◇ a) = c ◇ a := by
    intro a b c d e
    exact (congrArg (fun t => (((c ◇ a) ◇ c) ◇ (t ◇ ((d ◇ a) ◇ d))) ◇ (c ◇ a)) ((hlem1 a d b e).symm)).trans ((hlem5 a ((d ◇ a) ◇ d) b c e))
  have hlem8 : ∀ a b c d : G, ((b ◇ (b ◇ d)) ◇ b) ◇ ((a ◇ ((b ◇ (b ◇ d)) ◇ c)) ◇ a) = (a ◇ ((b ◇ (b ◇ d)) ◇ c)) ◇ a := by
    intro a b c d
    exact (congrArg (fun t => t ◇ ((a ◇ ((b ◇ (b ◇ d)) ◇ c)) ◇ a)) ((hlem1 b (b ◇ (b ◇ d)) b d).symm)).trans ((hlem1 (b ◇ (b ◇ d)) ((b ◇ (b ◇ d)) ◇ b) a c))
  have hlem9 : ∀ a b c d e : G, ((a ◇ ((c ◇ ((b ◇ (b ◇ d)) ◇ e)) ◇ c)) ◇ a) ◇ ((b ◇ (b ◇ d)) ◇ b) = (b ◇ (b ◇ d)) ◇ b := by
    intro a b c d e
    exact (congrArg (fun t => ((a ◇ t) ◇ a) ◇ ((b ◇ (b ◇ d)) ◇ b)) ((hlem8 c b e d).symm)).trans (((h ((b ◇ (b ◇ d)) ◇ b) a ((c ◇ ((b ◇ (b ◇ d)) ◇ e)) ◇ c)).symm))
  have hlem10 : ∀ a b c d : G, (((b ◇ ((a ◇ (a ◇ c)) ◇ d)) ◇ b) ◇ ((a ◇ (a ◇ c)) ◇ a)) ◇ ((a ◇ (a ◇ c)) ◇ a) = (a ◇ (a ◇ c)) ◇ a := by
    intro a b c d
    exact (congrArg (fun t => (t ◇ ((a ◇ (a ◇ c)) ◇ a)) ◇ ((a ◇ (a ◇ c)) ◇ a)) ((hlem8 b a d c).symm)).trans ((hlem9 ((a ◇ (a ◇ c)) ◇ a) a b c d))
  have hlem11 : ∀ a b c : G, ((((a ◇ (a ◇ c)) ◇ a) ◇ ((b ◇ a) ◇ b)) ◇ ((a ◇ (a ◇ c)) ◇ a)) ◇ ((a ◇ (a ◇ c)) ◇ a) = (a ◇ (a ◇ c)) ◇ a := by
    intro a b c
    exact (congrArg (fun t => ((t ◇ ((b ◇ a) ◇ b)) ◇ ((a ◇ (a ◇ c)) ◇ a)) ◇ ((a ◇ (a ◇ c)) ◇ a)) ((hlem1 a b a c).symm)).trans ((hlem10 a ((b ◇ a) ◇ b) c a))
  have hlem12 : ∀ a b : G, ((b ◇ (b ◇ b)) ◇ b) ◇ ((a ◇ (b ◇ b)) ◇ a) = (a ◇ (b ◇ b)) ◇ a := by
    intro a b
    exact (congrArg (fun t => t ◇ ((a ◇ (b ◇ b)) ◇ a)) ((hlem11 b b b).symm)).trans ((hlem6 (b ◇ b) ((b ◇ (b ◇ b)) ◇ b) a b b))
  have hlem13 : ∀ a b : G, (((a ◇ (b ◇ b)) ◇ a) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ (a ◇ (b ◇ b)) = a ◇ (b ◇ b) := by
    intro a b
    exact (congrArg (fun t => (((a ◇ (b ◇ b)) ◇ a) ◇ t) ◇ (a ◇ (b ◇ b))) ((hlem11 b b b).symm)).trans ((hlem7 (b ◇ b) ((b ◇ (b ◇ b)) ◇ b) a b b))
  have hlem14 : ∀ a : G, ((a ◇ (a ◇ a)) ◇ a) ◇ (a ◇ (a ◇ a)) = a ◇ (a ◇ a) := by
    intro a
    exact (congrArg (fun t => t ◇ (a ◇ (a ◇ a))) ((hlem12 a a).symm)).trans ((hlem13 a a))
  have hlem15 : ∀ a b c : G, ((a ◇ (b ◇ c)) ◇ (((a ◇ (b ◇ c)) ◇ a) ◇ (b ◇ (b ◇ b)))) ◇ a = a := by
    intro a b c
    exact (congrArg (fun t => ((a ◇ (b ◇ c)) ◇ (((a ◇ (b ◇ c)) ◇ a) ◇ t)) ◇ a) ((hlem14 b).symm)).trans ((hlem3 b a (b ◇ (b ◇ b)) c))
  have hlem16 : ∀ a b c : G, (((a ◇ (b ◇ c)) ◇ a) ◇ (b ◇ (b ◇ b))) ◇ (a ◇ (b ◇ c)) = a ◇ (b ◇ c) := by
    intro a b c
    exact (congrArg (fun t => (((a ◇ (b ◇ c)) ◇ a) ◇ t) ◇ (a ◇ (b ◇ c))) ((hlem14 b).symm)).trans ((hlem4 b (b ◇ (b ◇ b)) a c))
  have hlem17 : ∀ a : G, (a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)) = a ◇ (a ◇ a) := by
    intro a
    exact (congrArg (fun t => t ◇ (a ◇ (a ◇ a))) ((hlem14 a).symm)).trans ((hlem16 a a a))
  have hlem18 : ∀ a : G, (a ◇ (a ◇ a)) ◇ a = a := by
    intro a
    exact (congrArg (fun t => t ◇ a) ((hlem17 a).symm)).trans ((congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t) ◇ a) ((hlem14 a).symm)).trans ((hlem15 a a a)))
  have hlem19 : ∀ a : G, a ◇ a = a := by
    intro a
    exact (congrArg (fun t => t ◇ a) ((hlem18 a).symm)).trans (((h a a a).symm))
  have hlem20 : ∀ a b : G, (a ◇ b) ◇ a = a := by
    intro a b
    exact (congrArg (fun t => t ◇ a) ((hlem19 (a ◇ b)).symm)).trans ((congrArg (fun t => ((a ◇ b) ◇ t) ◇ a) ((hlem18 (a ◇ b)).symm)).trans ((hlem0 a (a ◇ b) b (a ◇ b))))
  have hlem21 : ∀ a b : G, a ◇ b = b := by
    intro a b
    exact (congrArg (fun t => t ◇ b) ((hlem20 a b).symm)).trans ((congrArg (fun t => ((a ◇ t) ◇ a) ◇ b) ((hlem19 b).symm)).trans (((h b a b).symm)))
  intro x y z w u
  exact ((hlem21 u x).symm).trans (((hlem21 w (u ◇ x)).symm).trans (((hlem21 (y ◇ z) (w ◇ (u ◇ x))).symm)))
"""),
    ("v0 = (v1 ◇ (v0 ◇ (v0 ◇ (v2 ◇ v0))))",
     "(v0 ◇ v0) = (((v1 ◇ v1) ◇ v0) ◇ v0)"): ("true", "e469_e4090", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, (a ◇ ((b ◇ (c ◇ b)) ◇ b)) = (b ◇ (c ◇ b)) := by
    intro a b c
    exact (((congrArg (fun t => (a ◇ ((b ◇ (c ◇ b)) ◇ t))) ((h b (b ◇ (c ◇ b)) c).symm))).symm).trans ((h (b ◇ (c ◇ b)) a b).symm)
  have hlem1 : ∀ a b c : G, (a ◇ b) = ((b ◇ (b ◇ (c ◇ b))) ◇ b) := by
    intro a b c
    exact (((congrArg (fun t => (a ◇ t)) ((h b ((b ◇ (b ◇ (c ◇ b))) ◇ b) c).symm)).symm)).trans ((((congrArg (fun t => (a ◇ (((b ◇ (b ◇ (c ◇ b))) ◇ t) ◇ (b ◇ (b ◇ (c ◇ b)))))) ((h b a c).symm)).symm)).trans (((hlem0 a (b ◇ (b ◇ (c ◇ b))) a)).trans (congrArg (fun t => ((b ◇ (b ◇ (c ◇ b))) ◇ t)) ((h b a c).symm))))
  have hlem2 : ∀ a b c : G, (a ◇ c) = (b ◇ c) := by
    intro a b c
    exact ((hlem1 a c c)).trans (((hlem1 b c c)).symm)
  intro x y
  exact hlem2 x ((y ◇ y) ◇ x) x
"""),
    ("v0 = ((v1 ◇ v0) ◇ ((v0 ◇ v2) ◇ v2))",
     "v0 = ((v1 ◇ (v2 ◇ (v1 ◇ v2))) ◇ v2)"): ("true", "e1689_e2391", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem1 : ∀ a b c : G, (a ◇ ((((a ◇ b) ◇ b) ◇ c) ◇ c)) = ((a ◇ b) ◇ b) := by
    intro a b c
    exact ((congrArg (fun t => (t ◇ ((((a ◇ b) ◇ b) ◇ c) ◇ c))) (h a a b)).trans ((h ((a ◇ b) ◇ b) (a ◇ a) c).symm))
  have hlem2 : ∀ a b c d : G, ((a ◇ (b ◇ c)) ◇ (c ◇ ((c ◇ d) ◇ d))) = (b ◇ c) := by
    intro a b c d
    exact ((congrArg (fun t => ((a ◇ (b ◇ c)) ◇ (t ◇ ((c ◇ d) ◇ d)))) (h c b d)).trans ((h (b ◇ c) a ((c ◇ d) ◇ d)).symm))
  have hlem3 : ∀ a b c : G, (a ◇ (b ◇ ((b ◇ c) ◇ c))) = ((a ◇ b) ◇ b) := by
    intro a b c
    exact ((congrArg (fun t => (a ◇ (t ◇ ((b ◇ c) ◇ c)))) (h b (a ◇ b) c)).trans (hlem1 a b ((b ◇ c) ◇ c)))
  have hlem4 : ∀ a b c d : G, ((a ◇ b) ◇ (b ◇ (c ◇ ((c ◇ d) ◇ d)))) = b := by
    intro a b c d
    exact ((congrArg (fun t => ((a ◇ b) ◇ t)) (hlem3 b c d)).trans ((h b a c).symm))
  have hlem5 : ∀ a b c : G, (((a ◇ (b ◇ c)) ◇ c) ◇ c) = (b ◇ c) := by
    intro a b c
    exact (((hlem3 (a ◇ (b ◇ c)) c a).symm).trans (hlem2 a b c a))
  have hlem6 : ∀ a b : G, (a ◇ ((a ◇ b) ◇ b)) = a := by
    intro a b
    exact ((((congrArg (fun t => (t ◇ ((a ◇ b) ◇ b))) (h a a b)).trans (congrArg (fun t => (((a ◇ t) ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ b))) (h a a b))).trans (hlem5 a (a ◇ a) ((a ◇ b) ◇ b))).trans ((h a a b).symm))
  have hlem7 : ∀ a b : G, (a ◇ b) = ((a ◇ b) ◇ b) := by
    intro a b
    exact ((congrArg (fun t => (a ◇ t)) ((hlem6 b a).symm)).trans (hlem3 a b a))
  have hlem8 : ∀ a b : G, (a ◇ (a ◇ b)) = a := by
    intro a b
    exact ((congrArg (fun t => (a ◇ t)) (hlem7 a b)).trans (hlem6 a b))
  have hlem9 : ∀ a b : G, ((a ◇ b) ◇ b) = b := by
    intro a b
    exact ((congrArg (fun t => ((a ◇ b) ◇ t)) ((hlem8 b ((b ◇ a) ◇ a)).symm)).trans (hlem4 a b b a))
  have hlem10 : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact (((hlem5 a a b).symm).trans (hlem9 (a ◇ (a ◇ b)) b))
  have hlem11 : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact ((congrArg (fun t => (a ◇ t)) ((hlem9 a b).symm)).trans (hlem6 a b))
  have hlem12 : ∀ a b : G, a = b := by
    intro a b
    exact (((hlem10 b a).symm).trans (hlem11 b a))
  intro x y z
  exact hlem12 x ((y ◇ (z ◇ (y ◇ z))) ◇ z)
"""),
    ("v0 = (v1 ◇ (v0 ◇ (((v2 ◇ v1) ◇ v1) ◇ v1)))",
     "v0 = (((v1 ◇ v2) ◇ (v0 ◇ v1)) ◇ (v0 ◇ v2))"): ("true", "e8502_e27144", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, a = ((((c ◇ a) ◇ a) ◇ a) ◇ ((b ◇ (((c ◇ a) ◇ a) ◇ a)) ◇ (((c ◇ a) ◇ a) ◇ a))) := by
    intro a b c
    exact (h a (((c ◇ a) ◇ a) ◇ a) b).trans ((congrArg (fun t => (((c ◇ a) ◇ a) ◇ a) ◇ t) (h ((b ◇ (((c ◇ a) ◇ a) ◇ a)) ◇ (((c ◇ a) ◇ a) ◇ a)) a c)).symm)
  have hlem1 : ∀ a b : G, (((b ◇ a) ◇ a) ◇ a) = ((((b ◇ a) ◇ a) ◇ a) ◇ a) := by
    intro a b
    exact (h (((b ◇ a) ◇ a) ◇ a) (((b ◇ a) ◇ a) ◇ a) a).trans (congrArg (fun t => (((b ◇ a) ◇ a) ◇ a) ◇ t) ((hlem0 a (a ◇ (((b ◇ a) ◇ a) ◇ a)) b).symm))
  have hlem2 : ∀ a b c : G, ((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) = (((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) := by
    intro a b c
    exact (h ((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) a b).trans ((congrArg (fun t => a ◇ t) (hlem1 (((b ◇ a) ◇ a) ◇ a) c)).trans ((h (((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) a b).symm))
  have hlem3 : ∀ a b c : G, (c ◇ (((b ◇ a) ◇ a) ◇ a)) = ((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) := by
    intro a b c
    exact (h (c ◇ (((b ◇ a) ◇ a) ◇ a)) a b).trans ((congrArg (fun t => a ◇ t) (hlem2 a b c)).trans ((h ((c ◇ (((b ◇ a) ◇ a) ◇ a)) ◇ (((b ◇ a) ◇ a) ◇ a)) a b).symm))
  have hlem4 : ∀ a b c : G, (c ◇ (((b ◇ a) ◇ a) ◇ a)) = c := by
    intro a b c
    exact (h (c ◇ (((b ◇ a) ◇ a) ◇ a)) a b).trans ((congrArg (fun t => a ◇ t) ((hlem3 a b c).symm)).trans ((h c a b).symm))
  have hlem5 : ∀ a b c : G, c = (a ◇ c) := by
    intro a b c
    exact (h c a b).trans (congrArg (fun t => a ◇ t) (hlem4 a b c))
  have hlem6 : ∀ a b : G, a = b := by
    intro a b
    exact ((hlem4 b b a).symm).trans ((congrArg (fun t => a ◇ t) ((congrArg (fun t => t ◇ b) (congrArg (fun t => t ◇ b) ((hlem5 b b b).symm))).trans ((congrArg (fun t => t ◇ b) ((hlem5 b b b).symm)).trans ((hlem5 b b b).symm)))).trans ((hlem5 a b b).symm))
  intro x y z
  exact hlem6 x (((y ◇ z) ◇ (x ◇ y)) ◇ (x ◇ z))
"""),
    ("v0 = (v0 ◇ (v1 ◇ ((v2 ◇ v1) ◇ (v3 ◇ v1))))",
     "v0 = ((v0 ◇ (((v1 ◇ v0) ◇ v2) ◇ v1)) ◇ v3)"): ("true", "e6605_e32838", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a p q r : G, (a ◇ (p ◇ ((q ◇ p) ◇ (r ◇ p)))) = a := by
    intro a p q r
    exact (h a p q r).symm
  have hlem1 : ∀ a p q r s : G, (a ◇ ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ s)) = a := by
    intro a p q r s
    exact (congrArg (fun t => (a ◇ ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ t))) ((((congrArg (fun t => ((s ◇ (p ◇ ((q ◇ p) ◇ (r ◇ p)))) ◇ t)) (hlem0 (p ◇ ((q ◇ p) ◇ (r ◇ p))) p q r)).trans ((hlem0 (s ◇ (p ◇ ((q ◇ p) ◇ (r ◇ p)))) p q r).trans (hlem0 s p q r)))).symm)).trans (hlem0 a (p ◇ ((q ◇ p) ◇ (r ◇ p))) s (p ◇ ((q ◇ p) ◇ (r ◇ p))))
  have hlem2 : ∀ a p q r y s : G, (a ◇ (((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y) ◇ s)) = a := by
    intro a p q r y s
    exact (congrArg (fun t => (a ◇ (((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y) ◇ t))) ((((congrArg (fun t => ((s ◇ ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y)) ◇ t)) (hlem1 ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y) p q r y)).trans ((hlem1 (s ◇ ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y)) p q r y).trans (hlem1 s p q r y)))).symm)).trans (hlem0 a ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y) s ((p ◇ ((q ◇ p) ◇ (r ◇ p))) ◇ y))
  have hlem3 : ∀ a y : G, (a ◇ y) = a := by
    intro a y
    exact (congrArg (fun t => (a ◇ t)) ((hlem2 y a a a y (a ◇ y)).symm)).trans (hlem0 a y (a ◇ ((a ◇ a) ◇ (a ◇ a))) a)
  intro x y z w
  exact ((hlem3 (x ◇ (((y ◇ x) ◇ z) ◇ y)) w).trans (hlem3 x (((y ◇ x) ◇ z) ◇ y))).symm
"""),
    ("v0 = ((v1 ◇ v2) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ v2))",
     "v0 = ((v0 ◇ (v0 ◇ v1)) ◇ (v2 ◇ (v2 ◇ v3)))"): ("true", "e20115_e21404", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem1 : ∀ a b c : G, ((a ◇ ((b ◇ (b ◇ c)) ◇ (c ◇ a))) ◇ b) = c := by
    intro a b c
    exact ((congrArg (fun t => ((a ◇ ((b ◇ (b ◇ c)) ◇ (c ◇ a))) ◇ t)) (h b c (c ◇ a))).trans ((h c a ((b ◇ (b ◇ c)) ◇ (c ◇ a))).symm))
  have hlem2 : ∀ a b : G, (((a ◇ a) ◇ b) ◇ (a ◇ b)) = (a ◇ (a ◇ a)) := by
    intro a b
    exact ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ b))) (h a a (a ◇ a))).trans ((h (a ◇ (a ◇ a)) (a ◇ a) b).symm))
  have hlem3 : ∀ a : G, ((((a ◇ a) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a)) = a := by
    intro a
    exact ((congrArg (fun t => ((((a ◇ a) ◇ a) ◇ t) ◇ (a ◇ a))) ((hlem2 a ((a ◇ a) ◇ a)).symm)).trans (hlem1 ((a ◇ a) ◇ a) (a ◇ a) a))
  have hlem4 : ∀ a b c : G, (((a ◇ b) ◇ c) ◇ ((((a ◇ a) ◇ b) ◇ (a ◇ (a ◇ a))) ◇ c)) = ((a ◇ a) ◇ b) := by
    intro a b c
    exact ((congrArg (fun t => (((a ◇ b) ◇ c) ◇ ((((a ◇ a) ◇ b) ◇ t) ◇ c))) ((hlem2 a b).symm)).trans ((h ((a ◇ a) ◇ b) (a ◇ b) c).symm))
  have hlem5 : ∀ a : G, (((a ◇ a) ◇ (a ◇ a)) ◇ a) = ((a ◇ a) ◇ a) := by
    intro a
    exact ((congrArg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ t)) ((hlem3 a).symm)).trans (hlem4 a a (a ◇ a)))
  have hlem6 : ∀ a b : G, (((a ◇ (a ◇ a)) ◇ b) ◇ ((a ◇ (a ◇ a)) ◇ b)) = ((a ◇ a) ◇ (a ◇ a)) := by
    intro a b
    exact ((congrArg (fun t => (((a ◇ (a ◇ a)) ◇ b) ◇ (t ◇ b))) ((hlem2 a (a ◇ a)).symm)).trans (hlem4 a (a ◇ a) b))
  have hlem7 : ∀ a b c : G, ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (((a ◇ (a ◇ a)) ◇ c) ◇ b)) = (((a ◇ (a ◇ a)) ◇ c) ◇ ((a ◇ a) ◇ (a ◇ a))) := by
    intro a b c
    exact (((congrArg (fun t => ((t ◇ b) ◇ (((a ◇ (a ◇ a)) ◇ c) ◇ b))) ((hlem6 a c).symm)).trans (hlem2 ((a ◇ (a ◇ a)) ◇ c) b)).trans (congrArg (fun t => (((a ◇ (a ◇ a)) ◇ c) ◇ t)) (hlem6 a c)))
  have hlem8 : ∀ a b c : G, ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (c ◇ b)) = (c ◇ ((a ◇ a) ◇ (a ◇ a))) := by
    intro a b c
    exact (((congrArg (fun t => ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (t ◇ b))) (h c a (a ◇ a))).trans (hlem7 a b ((c ◇ (c ◇ a)) ◇ (a ◇ a)))).trans (congrArg (fun t => (t ◇ ((a ◇ a) ◇ (a ◇ a)))) ((h c a (a ◇ a)).symm)))
  have hlem9 : ∀ a b : G, ((a ◇ (a ◇ ((b ◇ b) ◇ (b ◇ b)))) ◇ ((b ◇ b) ◇ (b ◇ b))) = a := by
    intro a b
    exact (((h a ((b ◇ b) ◇ (b ◇ b)) a).trans (hlem8 b a (a ◇ (a ◇ ((b ◇ b) ◇ (b ◇ b)))))).symm)
  have hlem10 : ∀ a b : G, ((a ◇ (a ◇ a)) ◇ (b ◇ (a ◇ (a ◇ a)))) = (b ◇ ((a ◇ a) ◇ (a ◇ a))) := by
    intro a b
    exact ((congrArg (fun t => (t ◇ (b ◇ (a ◇ (a ◇ a))))) ((hlem2 a (a ◇ a)).symm)).trans (hlem8 a (a ◇ (a ◇ a)) b))
  have hlem11 : ∀ a : G, (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) = ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) := by
    intro a
    exact (((congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem2 a (a ◇ a)).symm)).trans (hlem10 a ((a ◇ a) ◇ (a ◇ a)))).symm)
  have hlem12 : ∀ a b : G, (((a ◇ a) ◇ (a ◇ a)) ◇ ((b ◇ b) ◇ (b ◇ b))) = ((a ◇ a) ◇ ((b ◇ b) ◇ (b ◇ b))) := by
    intro a b
    exact ((((hlem8 b a (a ◇ a)).symm).trans ((congrArg (fun t => ((((b ◇ b) ◇ (b ◇ b)) ◇ a) ◇ t)) ((hlem5 a).symm)).trans (hlem8 b a ((a ◇ a) ◇ (a ◇ a))))).symm)
  have hlem13 : ∀ a : G, (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)) = (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) := by
    intro a
    exact ((congrArg (fun t => (t ◇ (a ◇ a))) ((hlem12 a a).symm)).trans (hlem5 (a ◇ a)))
  have hlem14 : ∀ a : G, (((a ◇ a) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) = (a ◇ a) := by
    intro a
    exact ((congrArg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ t)) ((hlem13 a).symm)).trans ((h (a ◇ a) (a ◇ a) (a ◇ a)).symm))
  have hlem15 : ∀ a b : G, (((a ◇ a) ◇ b) ◇ ((a ◇ a) ◇ b)) = ((a ◇ a) ◇ (a ◇ a)) := by
    intro a b
    exact ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ b))) ((hlem14 a).symm)).trans ((h ((a ◇ a) ◇ (a ◇ a)) (a ◇ a) b).symm))
  have hlem16 : ∀ a : G, ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) = ((a ◇ a) ◇ (a ◇ a)) := by
    intro a
    exact (((hlem11 a).symm).trans (hlem15 a (a ◇ a)))
  have hlem17 : ∀ a : G, (((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ a) = a := by
    intro a
    exact ((congrArg (fun t => (((a ◇ a) ◇ t) ◇ a)) ((hlem16 a).symm)).trans (hlem1 (a ◇ a) a a))
  have hlem18 : ∀ a : G, ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) = ((a ◇ a) ◇ (a ◇ a)) := by
    intro a
    exact (((hlem12 a a).symm).trans (hlem15 a (a ◇ a)))
  have hlem19 : ∀ a : G, ((a ◇ a) ◇ a) = a := by
    intro a
    exact (((hlem5 a).symm).trans ((congrArg (fun t => (t ◇ a)) ((hlem18 a).symm)).trans (hlem17 a)))
  have hlem20 : ∀ a b : G, (a ◇ ((b ◇ (b ◇ (a ◇ a))) ◇ a)) = b := by
    intro a b
    exact ((congrArg (fun t => (t ◇ ((b ◇ (b ◇ (a ◇ a))) ◇ a))) ((hlem19 a).symm)).trans ((h b (a ◇ a) a).symm))
  have hlem21 : ∀ a b : G, ((a ◇ b) ◇ (a ◇ b)) = (a ◇ a) := by
    intro a b
    exact (((congrArg (fun t => ((a ◇ b) ◇ (t ◇ b))) (hlem19 a)).symm).trans ((congrArg (fun t => ((a ◇ b) ◇ (((a ◇ a) ◇ t) ◇ b))) ((hlem19 a).symm)).trans ((h (a ◇ a) a b).symm)))
  have hlem22 : ∀ a b : G, ((a ◇ a) ◇ (a ◇ b)) = (a ◇ b) := by
    intro a b
    exact ((congrArg (fun t => (t ◇ (a ◇ b))) ((hlem21 a b).symm)).trans (hlem19 (a ◇ b)))
  have hlem23 : ∀ a b c : G, ((a ◇ a) ◇ ((a ◇ b) ◇ c)) = ((a ◇ b) ◇ c) := by
    intro a b c
    exact ((congrArg (fun t => (t ◇ ((a ◇ b) ◇ c))) ((hlem21 a b).symm)).trans (hlem22 (a ◇ b) c))
  have hlem24 : ∀ a b c : G, ((a ◇ a) ◇ ((b ◇ (b ◇ (a ◇ c))) ◇ (a ◇ c))) = b := by
    intro a b c
    exact ((congrArg (fun t => (t ◇ ((b ◇ (b ◇ (a ◇ c))) ◇ (a ◇ c)))) ((hlem21 a c).symm)).trans ((h b (a ◇ c) (a ◇ c)).symm))
  have hlem25 : ∀ a b : G, ((a ◇ a) ◇ b) = b := by
    intro a b
    exact (((congrArg (fun t => (t ◇ b)) (hlem21 a a)).symm).trans ((congrArg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ t)) ((hlem9 b a).symm)).trans (hlem24 (a ◇ a) b (a ◇ a))))
  have hlem26 : ∀ a b : G, ((a ◇ (a ◇ b)) ◇ b) = a := by
    intro a b
    exact (((h a b b).trans (hlem25 b ((a ◇ (a ◇ b)) ◇ b))).symm)
  have hlem27 : ∀ a b : G, ((a ◇ b) ◇ ((b ◇ (b ◇ (a ◇ a))) ◇ a)) = a := by
    intro a b
    exact ((congrArg (fun t => ((a ◇ t) ◇ ((b ◇ (b ◇ (a ◇ a))) ◇ a))) ((hlem20 a b).symm)).trans (hlem26 a ((b ◇ (b ◇ (a ◇ a))) ◇ a)))
  have hlem28 : ∀ a : G, ((a ◇ (a ◇ (a ◇ a))) ◇ a) = a := by
    intro a
    exact (((hlem23 a (a ◇ (a ◇ a)) a).symm).trans (hlem27 a a))
  have hlem29 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((congrArg (fun t => (a ◇ t)) ((hlem28 a).symm)).trans (hlem20 a a))
  have hlem30 : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact ((congrArg (fun t => (t ◇ b)) ((hlem29 a).symm)).trans (hlem25 a b))
  have hlem31 : ∀ a b : G, a = b := by
    intro a b
    exact (((hlem1 a b a).symm).trans (hlem30 (a ◇ ((b ◇ (b ◇ a)) ◇ (a ◇ a))) b))
  intro x y z w
  exact hlem31 x ((x ◇ (x ◇ y)) ◇ (z ◇ (z ◇ w)))
"""),
    ("v0 = (v0 ◇ ((v1 ◇ (v2 ◇ (v0 ◇ v0))) ◇ v2))",
     "v0 = (((v0 ◇ v1) ◇ v1) ◇ (v2 ◇ (v0 ◇ v3)))"): ("true", "e12716_e23224", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, (a ◇ (b ◇ (c ◇ ((a ◇ a) ◇ (b ◇ b))))) = a := by
    intro a b c
    exact ((h a b (c ◇ ((a ◇ a) ◇ (b ◇ b)))).trans (congrArg (fun t => (a ◇ (t ◇ (c ◇ ((a ◇ a) ◇ (b ◇ b)))))) ((h b c (a ◇ a)).symm))).symm
  have hlem1 : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact (((hlem0 a b (a ◇ (((a ◇ a) ◇ (b ◇ b)) ◇ (b ◇ b)))).symm).trans (congrArg (fun t => (a ◇ t)) ((h b a ((a ◇ a) ◇ (b ◇ b))).symm))).symm
  intro x y z w
  exact (((hlem1 ((x ◇ y) ◇ y) (z ◇ (x ◇ w))).trans (hlem1 (x ◇ y) y)).trans (hlem1 x y)).symm
"""),
    ("v0 = (v1 ◇ (((v2 ◇ v1) ◇ v0) ◇ v1))",
     "(v0 ◇ v1) = (v1 ◇ (v2 ◇ v3))"): ("true", "e1367_e341", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a (b ◇ a) a)).trans (congrArg (fun t => (t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (b ◇ a) a (a ◇ (b ◇ a)))))).trans ((congrArg (fun t => ((a ◇ (t ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b))).trans (congrArg (fun t => ((a ◇ ((a ◇ (t ◇ a)) ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h a (b ◇ a) a).symm)))).trans (((congrArg (fun t => ((a ◇ ((a ◇ (t ◇ a)) ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h a (a ◇ a) a))).trans (congrArg (fun t => ((a ◇ (t ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (((a ◇ (a ◇ a)) ◇ a) ◇ (a ◇ a)) a a).symm))).trans ((congrArg (fun t => (t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (a ◇ a) a (a ◇ (a ◇ a))).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ t)) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b))).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (t ◇ a)))) ((h a (b ◇ a) a).symm)))))).trans ((((congrArg (fun t => ((a ◇ a) ◇ (a ◇ t))) ((h (a ◇ a) a (a ◇ (a ◇ a))))).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ (t ◇ a))))) ((h (((a ◇ (a ◇ a)) ◇ a) ◇ (a ◇ a)) a a)))).trans ((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ ((a ◇ (t ◇ a)) ◇ a))))) ((h a (a ◇ a) a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ ((a ◇ (t ◇ a)) ◇ a))))) ((h a (b ◇ a) a))))).trans (((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ (t ◇ a))))) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ t))) ((h (b ◇ a) a (a ◇ (b ◇ a))).symm))).trans ((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (t ◇ a)))) ((h b (a ◇ a) a))).trans ((congrArg (fun t => ((a ◇ a) ◇ t)) ((h (((a ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a)) a a).symm)).trans ((h b (a ◇ a) a).symm)))))
  intro x y z w
  exact hlem (x ◇ y) (y ◇ (z ◇ w))
"""),
    ("v0 = (((v1 ◇ v0) ◇ (v1 ◇ v2)) ◇ v1)",
     "v0 = (((v1 ◇ v2) ◇ (v1 ◇ v3)) ◇ v4)"): ("true", "e2713_e2803", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((((h a a a)).trans (congrArg (fun t => (t ◇ a)) ((h ((a ◇ a) ◇ (a ◇ a)) (a ◇ a) ((b ◇ a) ◇ (b ◇ a)))))).trans ((congrArg (fun t => (((((t ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)) ◇ a)) ((h a a a))).trans (congrArg (fun t => ((((((((a ◇ a) ◇ (a ◇ a)) ◇ a) ◇ t) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)) ◇ a)) ((h a a a))))).trans (((congrArg (fun t => (((t ◇ ((a ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)) ◇ a)) ((h a ((a ◇ a) ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => (((a ◇ ((t ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)) ◇ a)) ((h a b a)))).trans ((congrArg (fun t => (((a ◇ (((((b ◇ a) ◇ (b ◇ a)) ◇ b) ◇ t) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)) ◇ a)) ((h a b a))).trans ((congrArg (fun t => (((a ◇ t) ◇ (a ◇ a)) ◇ a)) ((h b ((b ◇ a) ◇ (b ◇ a)) b).symm)).trans ((h b a a).symm))))
  intro x y z w u
  exact hlem x (((y ◇ z) ◇ (y ◇ w)) ◇ u)
"""),
    ("v0 = (((v1 ◇ v2) ◇ (v1 ◇ v0)) ◇ v1)",
     "v0 = (((v1 ◇ (v2 ◇ v3)) ◇ v1) ◇ v1)"): ("true", "e2788_e3030", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a ((a ◇ a) ◇ (a ◇ a)) a)).trans (congrArg (fun t => ((t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => ((a ◇ t) ◇ ((a ◇ a) ◇ (a ◇ a)))) ((h a a a).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ ((t ◇ a) ◇ (a ◇ a)))) ((h a ((a ◇ a) ◇ (a ◇ a)) a))).trans (congrArg (fun t => ((a ◇ a) ◇ ((((t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ a) ◇ (a ◇ a)))) ((h a a a).symm))))).trans (((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ t) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ a) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) ◇ (a ◇ a)))) ((h a ((a ◇ b) ◇ (a ◇ a)) a)))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((t ◇ (((a ◇ b) ◇ (a ◇ a)) ◇ a)) ◇ ((a ◇ b) ◇ (a ◇ a)))) ◇ (a ◇ a)))) ((h a a b).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ t) ◇ ((a ◇ b) ◇ (a ◇ a)))) ◇ (a ◇ a)))) ((h a a b).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((h ((a ◇ b) ◇ (a ◇ a)) (a ◇ a) ((a ◇ a) ◇ (a ◇ a))).symm)))))).trans ((((congrArg (fun t => ((a ◇ a) ◇ ((t ◇ b) ◇ (a ◇ a)))) ((h a ((a ◇ a) ◇ (a ◇ a)) a))).trans (congrArg (fun t => ((a ◇ a) ◇ ((((t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ t) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) ◇ (a ◇ a)))) ((h b ((b ◇ a) ◇ (b ◇ a)) b))).trans (congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((t ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ b)) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)))) ((h a b a).symm))))).trans (((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ ((a ◇ t) ◇ ((b ◇ a) ◇ (b ◇ a)))) ◇ (a ◇ a)))) ((h a b a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((h ((b ◇ a) ◇ (b ◇ a)) (a ◇ a) ((a ◇ a) ◇ (a ◇ a))).symm))).trans ((congrArg (fun t => ((t ◇ a) ◇ ((b ◇ a) ◇ (b ◇ a)))) ((h a b a))).trans ((congrArg (fun t => (((((b ◇ a) ◇ (b ◇ a)) ◇ b) ◇ t) ◇ ((b ◇ a) ◇ (b ◇ a)))) ((h a b a))).trans ((h b ((b ◇ a) ◇ (b ◇ a)) b).symm)))))
  intro x y z w
  exact hlem x (((y ◇ (z ◇ w)) ◇ y) ◇ y)
"""),
    ("v0 = (v1 ◇ ((v0 ◇ v1) ◇ (v2 ◇ v1)))",
     "(v0 ◇ v1) = ((v2 ◇ (v3 ◇ v3)) ◇ v3)"): ("true", "e886_e4057", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ x y : G, x = y := by
    intro x y
    exact (((((h x ((x ◇ x) ◇ (x ◇ x)) x)).trans (congrArg (fun t => (((x ◇ x) ◇ (x ◇ x)) ◇ (t ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))))) ((h x x x).symm))).trans ((congrArg (fun t => (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ t))) ((h x x x).symm)).trans ((congrArg (fun t => (((x ◇ x) ◇ (t ◇ x)) ◇ (x ◇ x))) ((h x ((x ◇ x) ◇ (y ◇ x)) x))).trans (congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (t ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ x)) ◇ (x ◇ x))) ((h x x y).symm))))).trans (((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ t)) ◇ x)) ◇ (x ◇ x))) ((h x x y).symm)).trans (congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) ◇ t)) ◇ (x ◇ x))) ((h x ((x ◇ x) ◇ (x ◇ x)) x)))).trans ((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (t ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ (x ◇ x))) ((h x x x).symm)).trans ((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ t)))) ◇ (x ◇ x))) ((h x x x).symm)).trans (congrArg (fun t => (t ◇ (x ◇ x))) ((h ((x ◇ x) ◇ (y ◇ x)) (x ◇ x) ((x ◇ x) ◇ (x ◇ x))).symm)))))).trans ((((congrArg (fun t => (((x ◇ x) ◇ (t ◇ x)) ◇ (x ◇ x))) ((h y ((x ◇ y) ◇ (x ◇ y)) y))).trans (congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ y) ◇ (x ◇ y)) ◇ (t ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y))))) ◇ x)) ◇ (x ◇ x))) ((h x y x).symm))).trans ((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ t)) ◇ x)) ◇ (x ◇ x))) ((h x y x).symm)).trans ((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ x)) ◇ t)) ◇ (x ◇ x))) ((h x ((x ◇ x) ◇ (x ◇ x)) x))).trans (congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (t ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ (x ◇ x))) ((h x x x).symm))))).trans (((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ t)))) ◇ (x ◇ x))) ((h x x x).symm)).trans (congrArg (fun t => (t ◇ (x ◇ x))) ((h ((x ◇ y) ◇ (x ◇ y)) (x ◇ x) ((x ◇ x) ◇ (x ◇ x))).symm))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (t ◇ x))) ((h x y x))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ ((x ◇ y) ◇ (x ◇ y))) ◇ t))) ((h x y x))).trans ((h y ((x ◇ y) ◇ (x ◇ y)) y).symm)))))
  intro x y z w
  exact hlem (x ◇ y) ((z ◇ (w ◇ w)) ◇ w)
"""),
    ("v0 = ((v1 ◇ v0) ◇ ((v0 ◇ v0) ◇ v2))",
     "(v0 ◇ v1) = (v0 ◇ ((v2 ◇ v0) ◇ v3))"): ("true", "e1683_e3531", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ x y z : G, (x ◇ y) = (x ◇ z) := by
    intro x y z
    exact (((((((h (x ◇ y) (x ◇ y) (x ◇ z))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h (x ◇ y) ((x ◇ x) ◇ ((x ◇ x) ◇ x)) (x ◇ y))))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (t ◇ y)) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x (x ◇ x) x))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((t ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h ((x ◇ x) ◇ x) (x ◇ x) y).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ t)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h (x ◇ y) (x ◇ y) x)))))).trans (((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ t) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h (x ◇ y) (x ◇ y) (((x ◇ y) ◇ (x ◇ y)) ◇ x)).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ (t ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x (x ◇ x) x)))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x y))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ ((t ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ t)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x y))))))).trans ((((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ ((x ◇ t) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x (x ◇ x) y).symm))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x (x ◇ x) x))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x y))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((t ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm))))).trans (((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ ((x ◇ x) ◇ t)) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x y))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ t) ◇ (x ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ (t ◇ y)) ◇ (x ◇ z)))) ((h x (x ◇ x) x))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ ((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ z)))) ((h x x y))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ ((t ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm))))))).trans (((((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ t)) ◇ y)) ◇ (x ◇ z)))) ((h x x y))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ x) ◇ ((x ◇ t) ◇ y)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)).symm))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (t ◇ (x ◇ z)))) ((h x x y).symm)).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (t ◇ (x ◇ z)))) ((h x ((x ◇ x) ◇ x) z))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((((x ◇ x) ◇ x) ◇ t) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y))))))).trans (((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x (x ◇ x) y)))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((t ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h ((x ◇ x) ◇ x) (x ◇ x) y))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((t ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x x).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (t ◇ y)) ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x (x ◇ x) x).symm)))))).trans ((((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (x ◇ y)) ◇ ((t ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ t) ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x y).symm))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ x) ◇ t) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (x ◇ y)) ◇ (t ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((((x ◇ (x ◇ y)) ◇ t) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h (x ◇ y) (x ◇ y) (((x ◇ y) ◇ (x ◇ y)) ◇ x))))))).trans (((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h (x ◇ y) x (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ x))).symm)).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ ((t ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)))).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ ((((x ◇ x) ◇ t) ◇ x) ◇ z)) ◇ (x ◇ z)))) ((h x x y).symm)))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ t) ◇ z)) ◇ (x ◇ z)))) ((h x x ((x ◇ x) ◇ y)))).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ (t ◇ z)) ◇ (x ◇ z)))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ (x ◇ z)) ◇ t))) ((h (x ◇ z) (x ◇ z) (((x ◇ z) ◇ (x ◇ z)) ◇ x)))))))))).trans ((((((congrArg (fun t => (((x ◇ y) ◇ (x ◇ y)) ◇ t)) ((h (x ◇ z) (x ◇ y) (((x ◇ z) ◇ (x ◇ z)) ◇ (((x ◇ z) ◇ (x ◇ z)) ◇ x))).symm)).trans (congrArg (fun t => ((t ◇ (x ◇ y)) ◇ (x ◇ z))) ((h (x ◇ y) ((x ◇ x) ◇ ((x ◇ x) ◇ x)) (x ◇ y))))).trans ((congrArg (fun t => ((((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (t ◇ y)) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x (x ◇ x) x))).trans ((congrArg (fun t => (((t ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h ((x ◇ x) ◇ x) (x ◇ x) y).symm)).trans (congrArg (fun t => (((((x ◇ x) ◇ x) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ t)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h (x ◇ y) (x ◇ y) x)))))).trans (((congrArg (fun t => (((((x ◇ x) ◇ x) ◇ t) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h (x ◇ y) (x ◇ y) (((x ◇ y) ◇ (x ◇ y)) ◇ x)).symm)).trans (congrArg (fun t => (((((x ◇ x) ◇ x) ◇ (t ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x (x ◇ x) x)))).trans ((congrArg (fun t => (((((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x y))).trans ((congrArg (fun t => (((((x ◇ x) ◇ x) ◇ ((t ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (((((x ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ t)) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x y))))))).trans ((((congrArg (fun t => (((((x ◇ x) ◇ x) ◇ ((x ◇ t) ◇ y)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => ((t ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x (x ◇ x) y).symm))).trans ((congrArg (fun t => ((t ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x (x ◇ x) x))).trans ((congrArg (fun t => (((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x y))).trans (congrArg (fun t => (((t ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm))))).trans (((congrArg (fun t => (((x ◇ ((x ◇ x) ◇ t)) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x y))).trans ((congrArg (fun t => (((x ◇ t) ◇ (x ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (((x ◇ x) ◇ (t ◇ y)) ◇ (x ◇ z))) ((h x (x ◇ x) x))))).trans ((congrArg (fun t => (((x ◇ x) ◇ ((((x ◇ x) ◇ t) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ z))) ((h x x y))).trans ((congrArg (fun t => (((x ◇ x) ◇ ((t ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (((x ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ t)) ◇ y)) ◇ (x ◇ z))) ((h x x y)))))))).trans (((((congrArg (fun t => (((x ◇ x) ◇ ((x ◇ t) ◇ y)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)).symm)).trans (congrArg (fun t => (t ◇ (x ◇ z))) ((h x x y).symm))).trans ((congrArg (fun t => (t ◇ (x ◇ z))) ((h x ((x ◇ x) ◇ x) z))).trans ((congrArg (fun t => (((((x ◇ x) ◇ x) ◇ t) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)))).trans (congrArg (fun t => ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm))))).trans (((congrArg (fun t => ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x (x ◇ x) y))).trans (congrArg (fun t => (((t ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h ((x ◇ x) ◇ x) (x ◇ x) y)))).trans ((congrArg (fun t => ((((t ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x x).symm)).trans ((congrArg (fun t => ((((x ◇ (t ◇ y)) ◇ ((x ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x (x ◇ x) x).symm)).trans (congrArg (fun t => ((((x ◇ (x ◇ y)) ◇ ((t ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)))))))).trans ((((congrArg (fun t => ((((x ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ t) ◇ x) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x y).symm)).trans (congrArg (fun t => ((((x ◇ (x ◇ y)) ◇ ((((x ◇ x) ◇ x) ◇ t) ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y))))).trans ((congrArg (fun t => ((((x ◇ (x ◇ y)) ◇ (t ◇ y)) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm)).trans ((congrArg (fun t => ((((x ◇ (x ◇ y)) ◇ t) ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h (x ◇ y) (x ◇ y) (((x ◇ y) ◇ (x ◇ y)) ◇ x)))).trans (congrArg (fun t => ((t ◇ ((x ◇ x) ◇ z)) ◇ (x ◇ z))) ((h (x ◇ y) x (((x ◇ y) ◇ (x ◇ y)) ◇ (((x ◇ y) ◇ (x ◇ y)) ◇ x))).symm))))).trans (((congrArg (fun t => (((x ◇ y) ◇ ((t ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)))).trans ((congrArg (fun t => (((x ◇ y) ◇ ((((x ◇ x) ◇ t) ◇ x) ◇ z)) ◇ (x ◇ z))) ((h x x y).symm)).trans (congrArg (fun t => (((x ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ t) ◇ z)) ◇ (x ◇ z))) ((h x x ((x ◇ x) ◇ y)))))).trans ((congrArg (fun t => (((x ◇ y) ◇ (t ◇ z)) ◇ (x ◇ z))) ((h x (x ◇ x) ((x ◇ x) ◇ ((x ◇ x) ◇ y))).symm)).trans ((congrArg (fun t => (((x ◇ y) ◇ (x ◇ z)) ◇ t)) ((h (x ◇ z) (x ◇ z) (((x ◇ z) ◇ (x ◇ z)) ◇ x)))).trans ((h (x ◇ z) (x ◇ y) (((x ◇ z) ◇ (x ◇ z)) ◇ (((x ◇ z) ◇ (x ◇ z)) ◇ x))).symm)))))))
  intro x y z w
  exact hlem x y ((z ◇ x) ◇ w)
"""),
    ("v0 = (v1 ◇ (v1 ◇ (v2 ◇ (v0 ◇ v1))))",
     "v0 = ((v1 ◇ v1) ◇ (v0 ◇ (v0 ◇ v0)))"): ("true", "e521_e1515", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((h a (a ◇ a) a)).trans (congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ (a ◇ (a ◇ t)))))) ((h a (b ◇ (a ◇ a)) a)))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ (a ◇ (a ◇ ((b ◇ (a ◇ a)) ◇ ((b ◇ (a ◇ a)) ◇ t)))))))) ((h a a b).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ t)))) ((h (b ◇ (a ◇ a)) a (b ◇ (a ◇ a))).symm)).trans ((h b (a ◇ a) a).symm)))
  intro x y
  exact hlem x ((y ◇ y) ◇ (x ◇ (x ◇ x)))
"""),
    ("v0 = ((v1 ◇ v1) ◇ (v0 ◇ (v0 ◇ v2)))",
     "v0 = (v1 ◇ (v1 ◇ ((v2 ◇ v3) ◇ v0)))"): ("true", "e1517_e735", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((((h a b a).trans (congrArg (fun w => ((b ◇ b) ◇ (a ◇ w))) ((((h ((a ◇ a)) b (((b ◇ b) ◇ ((b ◇ b) ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((a ◇ a) ◇ w))) ((h ((b ◇ b)) a b).symm))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) ((congrArg (fun w => ((a ◇ a) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) a (((b ◇ b) ◇ b))).symm)))).trans ((congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) b (((b ◇ b) ◇ b))).symm))))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) (h ((a ◇ (b ◇ b))) b a))).trans (((h ((b ◇ b)) b ((((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)) ◇ (b ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((b ◇ b) ◇ w))) (((h (((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a))) b (((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)))).trans (congrArg (fun w => ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)) ◇ w))) ((((h ((((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)) ◇ ((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)))) b (((b ◇ b) ◇ ((b ◇ b) ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)) ◇ ((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a))) ◇ w))) ((h ((b ◇ b)) (((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a))) b).symm))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) ((congrArg (fun w => ((((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a)) ◇ ((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a))) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) (((a ◇ (b ◇ b)) ◇ ((a ◇ (b ◇ b)) ◇ a))) (((b ◇ b) ◇ b))).symm)))).trans ((congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) b (((b ◇ b) ◇ b))).symm))))).symm))).symm)).trans (((((h b b b).trans (congrArg (fun w => ((b ◇ b) ◇ (b ◇ w))) ((((h ((b ◇ b)) b (((b ◇ b) ◇ ((b ◇ b) ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((b ◇ b) ◇ w))) ((h ((b ◇ b)) b b).symm))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) ((congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) b (((b ◇ b) ◇ b))).symm)))).trans ((congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) b (((b ◇ b) ◇ b))).symm))))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ (b ◇ b))) b b))).trans (((h ((b ◇ b)) b ((((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ (b ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((b ◇ b) ◇ w))) (((h (((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b))) b (((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ (((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ w))) ((((h ((((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)))) b (((b ◇ b) ◇ ((b ◇ b) ◇ b)))).trans (congrArg (fun w => ((b ◇ b) ◇ ((((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b))) ◇ w))) ((h ((b ◇ b)) (((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b))) b).symm))).trans (congrArg (fun w => ((b ◇ b) ◇ w)) ((congrArg (fun w => ((((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b))) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) (((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ b))) (((b ◇ b) ◇ b))).symm)))).trans ((congrArg (fun w => ((b ◇ b) ◇ w)) (h ((b ◇ b)) b b)).trans ((h ((b ◇ b)) b (((b ◇ b) ◇ b))).symm))))).symm))).symm)).symm)
  intro x y z w
  exact hlem x (y ◇ (y ◇ ((z ◇ w) ◇ x)))
"""),
    ("v0 = (v1 ◇ (v2 ◇ (v2 ◇ (v0 ◇ v2))))",
     "v0 = (v1 ◇ (v1 ◇ ((v1 ◇ v2) ◇ v0)))"): ("true", "e573_e719", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((h a a (a ◇ (a ◇ (a ◇ a)))).trans (congrArg (fun t => a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ t))) ((h a a a).symm))).trans (((h b a (a ◇ (a ◇ (a ◇ a)))).trans (congrArg (fun t => a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ t))) ((h a b a).symm))).symm)
  intro x y z
  exact hlem x (y ◇ (y ◇ ((y ◇ z) ◇ x)))
"""),
    ("v0 = (v1 ◇ (v0 ◇ ((v2 ◇ v1) ◇ v1)))",
     "v0 = (((v0 ◇ v0) ◇ v0) ◇ (v1 ◇ v1))"): ("true", "e691_e2038", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a b b)).trans (congrArg (fun t => (t ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b (b ◇ b) (b ◇ (a ◇ b)))))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ t)) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ t) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((a ◇ b) ◇ b)) b a)))))).trans (((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ t)))) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))))) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a)))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ t)) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (a ◇ b) (b ◇ ((a ◇ b) ◇ b)) b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ t))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((a ◇ b) ◇ b)) b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ t)))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))))))).trans ((((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ t)))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (a ◇ b) (b ◇ ((a ◇ b) ◇ b)) b).symm))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (t ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b (b ◇ (a ◇ b)) b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ t))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ b) (b ◇ ((b ◇ b) ◇ b)) b))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ ((b ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ (t ◇ (b ◇ ((b ◇ b) ◇ b)))))))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm))))).trans (((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ ((b ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ t))))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm)).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ t)) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((b ◇ b) ◇ b)) b b).symm))).trans ((congrArg (fun t => (((b ◇ b) ◇ t) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ b) ◇ t)) ((h (a ◇ ((b ◇ b) ◇ b)) b b))).trans ((h b ((b ◇ b) ◇ b) a).symm)))))
  intro x y
  exact hlem x (((x ◇ x) ◇ x) ◇ (y ◇ y))
"""),
    ("v0 = (v1 ◇ (v0 ◇ ((v2 ◇ v1) ◇ v1)))",
     "v0 = (((v1 ◇ v2) ◇ (v2 ◇ v2)) ◇ v0)"): ("true", "e691_e2812", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a b b)).trans (congrArg (fun t => (t ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b (b ◇ b) (b ◇ (a ◇ b)))))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ t)) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ t) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((a ◇ b) ◇ b)) b a)))))).trans (((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ t)))) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))))) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a)))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ t)) ◇ (b ◇ ((a ◇ b) ◇ b))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (a ◇ b) (b ◇ ((a ◇ b) ◇ b)) b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ t))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((a ◇ b) ◇ b)) b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ t)))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))))))).trans ((((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ ((a ◇ b) ◇ (t ◇ (b ◇ ((a ◇ b) ◇ b))))))))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b a))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (((b ◇ (a ◇ b)) ◇ (b ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ t)))) ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (a ◇ b) (b ◇ ((a ◇ b) ◇ b)) b).symm))).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (t ◇ (b ◇ b)))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b (b ◇ (a ◇ b)) b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ t))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ b) (b ◇ ((b ◇ b) ◇ b)) b))).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ ((b ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ (t ◇ (b ◇ ((b ◇ b) ◇ b)))))))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm))))).trans (((congrArg (fun t => (((b ◇ b) ◇ (b ◇ (b ◇ ((b ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ t))))) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm)).trans (congrArg (fun t => (((b ◇ b) ◇ (b ◇ t)) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h (b ◇ ((b ◇ b) ◇ b)) b b).symm))).trans ((congrArg (fun t => (((b ◇ b) ◇ t) ◇ (a ◇ ((b ◇ b) ◇ b)))) ((h b b b).symm)).trans ((congrArg (fun t => (((b ◇ b) ◇ b) ◇ t)) ((h (a ◇ ((b ◇ b) ◇ b)) b b))).trans ((h b ((b ◇ b) ◇ b) a).symm)))))
  intro x y z
  exact hlem x (((y ◇ z) ◇ (z ◇ z)) ◇ x)
"""),
    ("v0 = ((v1 ◇ ((v0 ◇ v2) ◇ v2)) ◇ v0)",
     "v0 = ((((v1 ◇ v2) ◇ v3) ◇ v1) ◇ v0)"): ("true", "e2521_e3232", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact (((((congrArg (fun t => (t ◇ b)) ((h a (a ◇ a) a))).trans (congrArg (fun t => ((((a ◇ a) ◇ (t ◇ a)) ◇ a) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a)))).trans ((congrArg (fun t => ((((a ◇ a) ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ a)) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => ((((a ◇ a) ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ a)) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)))).trans (((congrArg (fun t => ((((a ◇ a) ◇ ((t ◇ (a ◇ a)) ◇ a)) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm)).trans (congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ t) ◇ a)) ◇ a) ◇ b)) ((h (a ◇ a) a a)))).trans ((congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ ((a ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans ((congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ ((a ◇ t) ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)).trans (congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a))))))).trans ((((congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm))).trans ((congrArg (fun t => ((((a ◇ a) ◇ ((a ◇ ((t ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm)).trans ((congrArg (fun t => ((((a ◇ a) ◇ t) ◇ a) ◇ b)) ((h a a (a ◇ a)).symm)).trans (congrArg (fun t => (((t ◇ a) ◇ a) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a)))))).trans (((congrArg (fun t => (((((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ a) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => (((((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ a) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm))).trans ((congrArg (fun t => ((((t ◇ (a ◇ a)) ◇ a) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm)).trans ((congrArg (fun t => ((((a ◇ t) ◇ a) ◇ a) ◇ b)) ((h (a ◇ a) a a))).trans (congrArg (fun t => ((((a ◇ ((a ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a)))))))).trans (((((congrArg (fun t => ((((a ◇ ((a ◇ t) ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)).trans (congrArg (fun t => ((((a ◇ (t ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a)))).trans ((congrArg (fun t => ((((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans ((congrArg (fun t => ((((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)).trans (congrArg (fun t => ((((a ◇ ((t ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm))))).trans (((congrArg (fun t => ((t ◇ a) ◇ b)) ((h a a (a ◇ a)).symm)).trans (congrArg (fun t => ((a ◇ t) ◇ b)) ((h a b a)))).trans ((congrArg (fun t => ((a ◇ ((b ◇ (t ◇ a)) ◇ a)) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a))).trans ((congrArg (fun t => ((a ◇ ((b ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ a)) ◇ a)) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => ((a ◇ ((b ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ a)) ◇ a)) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)))))).trans ((((congrArg (fun t => ((a ◇ ((b ◇ ((t ◇ (a ◇ a)) ◇ a)) ◇ a)) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm)).trans (congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ t) ◇ a)) ◇ a)) ◇ b)) ((h (a ◇ a) a a)))).trans ((congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ ((a ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans ((congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ ((a ◇ t) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)).trans (congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h (a ◇ a) ((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) a)))))).trans (((congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ (((((a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ t) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm))).trans ((congrArg (fun t => ((a ◇ ((b ◇ ((a ◇ ((t ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ b) ◇ b)) a).symm)).trans ((congrArg (fun t => ((a ◇ ((b ◇ t) ◇ a)) ◇ b)) ((h a a (a ◇ a)).symm)).trans ((h b a a).symm))))))
  intro x y z w
  exact (hlem (((y ◇ z) ◇ w) ◇ y) x).symm
"""),
    ("v0 = ((v1 ◇ (v1 ◇ v0)) ◇ (v0 ◇ v2))",
     "(v0 ◇ v1) = (v0 ◇ (v0 ◇ (v1 ◇ v1)))"): ("true", "e1923_e3309", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c d : G, (a ◇ b) = (((c ◇ (c ◇ a)) ◇ a) ◇ ((a ◇ b) ◇ d)) := by
    intro a b c d
    exact (h (a ◇ b) (c ◇ (c ◇ a)) d).trans (congrArg (fun q => ((c ◇ (c ◇ a)) ◇ q) ◇ ((a ◇ b) ◇ d)) ((h a c b).symm))
  have hlem1 : ∀ a b c : G, (a ◇ (a ◇ b)) = ((c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ b) := by
    intro a b c
    exact (h (a ◇ (a ◇ b)) c (b ◇ b)).trans (congrArg (fun q => (c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ q) ((h b a b).symm))
  have hlem2 : ∀ a b c d : G, (((a ◇ (a ◇ (b ◇ (b ◇ c)))) ◇ (b ◇ (b ◇ c))) ◇ (c ◇ d)) = c := by
    intro a b c d
    exact (congrArg (fun q => ((a ◇ (a ◇ (b ◇ (b ◇ c)))) ◇ q) ◇ (c ◇ d)) (hlem1 b c a)).trans ((h c (a ◇ (a ◇ (b ◇ (b ◇ c)))) d).symm)
  have hlem3 : ∀ a b c d : G, ((a ◇ (a ◇ b)) ◇ b) = (((c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ (a ◇ (a ◇ b))) ◇ (b ◇ d)) := by
    intro a b c d
    exact (hlem0 (a ◇ (a ◇ b)) b c ((b ◇ d) ◇ d)).trans (congrArg (fun q => ((c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ (a ◇ (a ◇ b))) ◇ q) ((hlem0 b d a d).symm))
  have hlem4 : ∀ a b : G, ((a ◇ (a ◇ b)) ◇ b) = b := by
    intro a b
    exact (hlem3 a b a a).trans (hlem2 a a b a)
  have hlem5 : ∀ a b c : G, (a ◇ (a ◇ b)) = (((c ◇ (c ◇ a)) ◇ a) ◇ b) := by
    intro a b c
    exact (hlem0 a (a ◇ b) c (b ◇ b)).trans (congrArg (fun q => ((c ◇ (c ◇ a)) ◇ a) ◇ q) ((h b a b).symm))
  have hlem6 : ∀ a b : G, (a ◇ b) = (a ◇ (a ◇ b)) := by
    intro a b
    exact ((hlem5 a b b).trans (congrArg (fun q => q ◇ b) (hlem4 b a))).symm
  have hlem7 : ∀ a b c : G, ((a ◇ b) ◇ (b ◇ c)) = b := by
    intro a b c
    exact (congrArg (fun q => q ◇ (b ◇ c)) (hlem6 a b)).trans ((h b a c).symm)
  have hlem8 : ∀ a b : G, ((a ◇ b) ◇ b) = b := by
    intro a b
    exact (congrArg (fun q => q ◇ b) (hlem6 a b)).trans (hlem4 a b)
  have hlem9 : ∀ a b : G, (a ◇ (a ◇ b)) = a := by
    intro a b
    exact ((congrArg (fun q => q ◇ (a ◇ b)) (hlem8 b a)).symm).trans (hlem7 (b ◇ a) a b)
  have hlem10 : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact (hlem6 a b).trans (hlem9 a b)
  intro x y
  exact (hlem10 x y).trans ((hlem10 x (x ◇ (y ◇ y))).symm)
"""),
    ("(v0 ◇ v1) = (v1 ◇ ((v1 ◇ v2) ◇ v0))",
     "(v0 ◇ v1) = (((v2 ◇ v0) ◇ v1) ◇ v0)"): ("true", "e3561_e4195", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, (a ◇ b) = (b ◇ ((c ◇ b) ◇ a)) := by
    intro a b c
    exact (((h a b ((b ◇ (a ◇ b)) ◇ c)))).trans (congrArg (fun t => (b ◇ (t ◇ a))) ((h c b (a ◇ b)).symm))
  have hlem1 : ∀ a b c d : G, ((((a ◇ b) ◇ c) ◇ d) ◇ a) = (a ◇ (d ◇ (a ◇ b))) := by
    intro a b c d
    exact (((h (((a ◇ b) ◇ c) ◇ d) a b))).trans (congrArg (fun t => (a ◇ t)) ((h d (a ◇ b) c).symm))
  have hlem2 : ∀ a b c d : G, ((((a ◇ b) ◇ c) ◇ d) ◇ b) = (b ◇ (d ◇ (a ◇ b))) := by
    intro a b c d
    exact (((hlem0 (((a ◇ b) ◇ c) ◇ d) b a))).trans (congrArg (fun t => (b ◇ t)) ((h d (a ◇ b) c).symm))
  have hlem3 : ∀ a b c : G, (a ◇ b) = (b ◇ (a ◇ (b ◇ (a ◇ c)))) := by
    intro a b c
    exact ((((hlem0 a b (b ◇ (a ◇ c))))).trans (congrArg (fun t => (b ◇ t)) ((h ((b ◇ (a ◇ c)) ◇ b) a c)))).trans (congrArg (fun t => (b ◇ (a ◇ t))) ((hlem0 b (a ◇ c) b).symm))
  have hlem4 : ∀ a b : G, (a ◇ b) = (b ◇ (b ◇ a)) := by
    intro a b
    exact (((hlem3 a b (b ◇ a)))).trans (congrArg (fun t => (b ◇ t)) ((hlem3 b a a).symm))
  have hlem5 : ∀ a b c d : G, ((a ◇ ((b ◇ c) ◇ (a ◇ d))) ◇ b) = (b ◇ (a ◇ (b ◇ c))) := by
    intro a b c d
    exact (((h (a ◇ ((b ◇ c) ◇ (a ◇ d))) b c))).trans (congrArg (fun t => (b ◇ t)) ((hlem3 a (b ◇ c) d).symm))
  have hlem6 : ∀ a b c d : G, (a ◇ (b ◇ ((b ◇ c) ◇ a))) = ((b ◇ (d ◇ (b ◇ c))) ◇ a) := by
    intro a b c d
    exact (((hlem2 (b ◇ c) a d b).symm)).trans (congrArg (fun t => (t ◇ a)) ((hlem1 b c a d)))
  have hlem7 : ∀ a b c d : G, ((a ◇ (b ◇ (a ◇ c))) ◇ d) = (d ◇ (d ◇ a)) := by
    intro a b c d
    exact (((hlem6 d a c b).symm)).trans (congrArg (fun t => (d ◇ t)) ((h d a c).symm))
  have hlem8 : ∀ a b c d : G, (a ◇ b) = ((a ◇ (c ◇ (a ◇ d))) ◇ b) := by
    intro a b c d
    exact (((hlem4 a b))).trans ((hlem7 a c d b).symm)
  have hlem9 : ∀ a b c : G, (a ◇ b) = (b ◇ (a ◇ (b ◇ c))) := by
    intro a b c
    exact (((hlem8 a b (b ◇ c) (a ◇ b)))).trans ((hlem5 a b c (a ◇ b)))
  have hlem10 : ∀ a b c : G, (a ◇ b) = ((c ◇ a) ◇ b) := by
    intro a b c
    exact (((hlem8 a b c (c ◇ a)))).trans (congrArg (fun t => (t ◇ b)) ((hlem3 c a a).symm))
  have hlem11 : ∀ a b c : G, (a ◇ b) = (b ◇ (c ◇ a)) := by
    intro a b c
    exact (((h a b c))).trans (congrArg (fun t => (b ◇ t)) ((hlem10 c a b).symm))
  intro x y z
  exact (((((hlem11 x y z))).trans ((hlem9 y (z ◇ x) y))).trans ((hlem10 x (y ◇ ((z ◇ x) ◇ y)) z).symm)).trans ((hlem11 ((z ◇ x) ◇ y) x y).symm)
"""),
    ("v0 = ((v1 ◇ v0) ◇ ((v1 ◇ v1) ◇ v1))",
     "v0 = (v1 ◇ (v0 ◇ ((v1 ◇ v1) ◇ v1)))"): ("true", "e1695_e680", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, ((a ◇ a) ◇ a) = (b ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) := by
    intro a b
    exact (h ((a ◇ a) ◇ a) (a ◇ b)).trans (congrArg (fun t => (t ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)))) (h b a)).symm
  have hlem1 : ∀ a b : G, (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) = (((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b)) := by
    intro a b
    exact (h (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) b).trans (congrArg (fun t => (t ◇ ((b ◇ b) ◇ b))) (hlem0 a b)).symm
  have hlem2 : ∀ a b c : G, (((a ◇ b) ◇ c) ◇ (((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b))) = c := by
    intro a b c
    exact (congrArg (fun t => (((a ◇ b) ◇ c) ◇ t)) (hlem1 a b)).symm.trans (h c (a ◇ b)).symm
  have hlem3 : ∀ a b : G, (((a ◇ (a ◇ a)) ◇ b) ◇ a) = b := by
    intro a b
    exact (congrArg (fun t => (((a ◇ (a ◇ a)) ◇ b) ◇ t)) (h a (a ◇ a))).trans (hlem2 a (a ◇ a) b)
  have hlem4 : ∀ b a : G, (b ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a))) ◇ ((b ◇ b) ◇ b))) = a := by
    intro b a
    exact (congrArg (fun t => (t ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a))) ◇ ((b ◇ b) ◇ b)))) (hlem3 a b)).symm.trans (hlem2 (a ◇ (a ◇ a)) b a)
  have hlem5 : ∀ b a : G, (b ◇ ((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ ((b ◇ b) ◇ b))) = a := by
    intro b a
    exact (congrArg (fun t => (b ◇ (t ◇ ((b ◇ b) ◇ b)))) (hlem1 a (a ◇ a))).symm.trans (hlem4 b a)
  have hlem6 : ∀ b a : G, (b ◇ (a ◇ ((b ◇ b) ◇ b))) = a := by
    intro b a
    exact (congrArg (fun t => (b ◇ (t ◇ ((b ◇ b) ◇ b)))) (h a (a ◇ a))).trans (hlem5 b a)
  intro x y
  exact (hlem6 y x).symm
"""),
    ("v0 = ((v0 ◇ (v1 ◇ v2)) ◇ (v1 ◇ v3))",
     "(v0 ◇ v1) = (v0 ◇ ((v1 ◇ v2) ◇ v0))"): ("true", "e1874_e3524", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ x y z w : G, (x ◇ y) = (x ◇ ((y ◇ z) ◇ w)) := by
    intro x y z w
    exact ((congrArg (fun t => (x ◇ t)) ((h y (z ◇ (x ◇ y)) (x ◇ x) (x ◇ x)))).trans (congrArg (fun t => (x ◇ ((y ◇ t) ◇ ((z ◇ (x ◇ y)) ◇ (x ◇ x))))) ((h z x y x).symm))).trans ((congrArg (fun t => (x ◇ ((y ◇ z) ◇ t))) ((h z x y x).symm)).trans (((h (x ◇ ((y ◇ z) ◇ z)) (y ◇ z) x w)).trans (congrArg (fun t => (t ◇ ((y ◇ z) ◇ w))) ((h x (y ◇ z) z x).symm))))
  intro x y z
  exact hlem x y z x
"""),
    ("v0 = ((((v0 ◇ v1) ◇ v0) ◇ v0) ◇ v2)",
     "v0 = ((((v0 ◇ v1) ◇ v1) ◇ v2) ◇ v1)"): ("true", "e3067_e3082", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ u v : G, u = ((((u ◇ u) ◇ u) ◇ u) ◇ v) := by
    intro u v
    exact h u u v
  have hlem1 : ∀ a b c : G, (a ◇ b) = (a ◇ c) := by
    intro a b c
    exact ((((((hlem0 ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) b).trans (congrArg (fun q => (((q ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ b)) ((hlem0 (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).symm))).trans (congrArg (fun q => ((q ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ b)) (((hlem0 ((((a ◇ a) ◇ a) ◇ a)) ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).trans (congrArg (fun q => (((q ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))) ((hlem0 a ((((a ◇ a) ◇ a) ◇ a))).symm))).symm))).trans (congrArg (fun q => (q ◇ b)) ((hlem0 a ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).symm))).symm).trans ((((hlem0 ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) c).trans (congrArg (fun q => (((q ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ c)) ((hlem0 (((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).symm))).trans (congrArg (fun q => ((q ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)))) ◇ c)) (((hlem0 ((((a ◇ a) ◇ a) ◇ a)) ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).trans (congrArg (fun q => (((q ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))) ((hlem0 a ((((a ◇ a) ◇ a) ◇ a))).symm))).symm))).trans (congrArg (fun q => (q ◇ c)) ((hlem0 a ((((((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ a))))).symm))))
  intro x y z
  exact ((((hlem0 x y).trans (congrArg (fun q => (((q ◇ x) ◇ x) ◇ y)) (hlem1 x x y))).trans (congrArg (fun q => ((q ◇ x) ◇ y)) (hlem1 ((x ◇ y)) x y))).trans (congrArg (fun q => (q ◇ y)) (hlem1 (((x ◇ y) ◇ y)) x z)))
"""),
    ("v0 = ((v1 ◇ v0) ◇ ((v2 ◇ v0) ◇ v2))",
     "v0 = ((v1 ◇ v0) ◇ (v1 ◇ (v0 ◇ v0)))"): ("true", "e1703_e1488", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((((h a (a ◇ a) a)).trans (congrArg (fun t => (t ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a))))).trans ((congrArg (fun t => ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans (congrArg (fun t => ((a ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)))).trans (((congrArg (fun t => ((t ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) ((h a a b))).trans (congrArg (fun t => ((((a ◇ a) ◇ ((b ◇ a) ◇ b)) ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ a))) ((h a a b)))).trans ((congrArg (fun t => (t ◇ ((a ◇ a) ◇ a))) ((h ((b ◇ a) ◇ b) (a ◇ a) (a ◇ a)).symm)).trans ((congrArg (fun t => ((t ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (b ◇ a) a a))).trans (congrArg (fun t => (((t ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (a ◇ (b ◇ a)) ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a))))))).trans ((((congrArg (fun t => (((((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a b a))).trans (congrArg (fun t => ((((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm))).trans ((congrArg (fun t => ((((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans ((congrArg (fun t => (((((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans (congrArg (fun t => (((((a ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm))))).trans (((congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a))).trans (congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a b a)))).trans ((congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm)).trans ((congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans (congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm))))))).trans (((((congrArg (fun t => (((((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans (congrArg (fun t => (((t ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (a ◇ (a ◇ a)) a a).symm))).trans ((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (a ◇ (b ◇ a)) ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a))).trans (congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a b a))))).trans (((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ ((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm)).trans (congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ ((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a))))).trans ((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans ((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans (congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a))))))).trans ((((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a b a))).trans (congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm))).trans ((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans ((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm)).trans (congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h a a a).symm))))).trans (((congrArg (fun t => ((((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (a ◇ (a ◇ a)) a a).symm)).trans (congrArg (fun t => ((t ◇ b) ◇ ((a ◇ a) ◇ a))) ((h (a ◇ a) a a).symm))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ t)) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (a ◇ (t ◇ (a ◇ a))))) ((h a a a).symm)))))))).trans ((((((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ (a ◇ (a ◇ a))))) ((h a a (a ◇ a)))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))) ◇ (t ◇ (a ◇ a))))) ((h a a (a ◇ a))))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ t)) ((h (((a ◇ a) ◇ a) ◇ (a ◇ a)) (a ◇ a) (a ◇ a)).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))))).trans (((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ (a ◇ a)))) ((h a a b))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ a) ◇ ((b ◇ a) ◇ b)) ◇ (t ◇ (a ◇ a))) ◇ (a ◇ a)))) ((h a a b))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (t ◇ (a ◇ a)))) ((h ((b ◇ a) ◇ b) (a ◇ a) (a ◇ a)).symm)))))).trans ((((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((t ◇ b) ◇ (a ◇ a)))) ((h (b ◇ a) a a))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((t ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h (a ◇ (b ◇ a)) ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a)))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a b a))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a))))))).trans (((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a b a))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm))))))).trans (((((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ (((t ◇ ((a ◇ (b ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h (a ◇ (a ◇ a)) a a).symm)))).trans (((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h (a ◇ (b ◇ a)) ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a b a)))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ ((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm)).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ ((t ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a)))).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)))))).trans ((((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (t ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (a ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a)))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (t ◇ (b ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a b a))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (b ◇ a)).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ (t ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h ((a ◇ a) ◇ a) (a ◇ a) (a ◇ a))))))).trans (((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (t ◇ (a ◇ a))) ◇ a)) ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h a a a).symm))).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ b) ◇ (a ◇ a)))) ((h (a ◇ (a ◇ a)) a a).symm)).trans ((congrArg (fun t => (((a ◇ a) ◇ b) ◇ ((t ◇ b) ◇ (a ◇ a)))) ((h (a ◇ a) a a).symm)).trans ((h b (a ◇ a) (a ◇ a)).symm)))))))
  intro x y
  exact hlem x ((y ◇ x) ◇ (y ◇ (x ◇ x)))
"""),
    ("v0 = (((v1 ◇ v2) ◇ ((v1 ◇ v1) ◇ v2)) ◇ v0)",
     "v0 = (v1 ◇ (v0 ◇ ((v2 ◇ (v0 ◇ v1)) ◇ v0)))"): ("true", "e35120_e7607", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact (((h b a a).trans (congrArg (fun t => ((a ◇ a) ◇ t) ◇ b) (((((h a ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a).trans (congrArg (fun t => (t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ a)) ◇ a) ((h a a a).symm))).trans (congrArg (fun t => (a ◇ (t ◇ a)) ◇ a) ((h ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a a).symm))).trans (congrArg (fun t => (a ◇ t) ◇ a) ((h a a a).symm))).symm))).trans (congrArg (fun t => t ◇ b) (((((h a ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a).trans (congrArg (fun t => (t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ a)) ◇ a) ((h a a a).symm))).trans (congrArg (fun t => (a ◇ (t ◇ a)) ◇ a) ((h ((a ◇ a) ◇ ((a ◇ a) ◇ a)) a a).symm))).trans (congrArg (fun t => (a ◇ t) ◇ a) ((h a a a).symm))).symm))).symm
  intro x y z
  exact (((hlem y (x ◇ ((z ◇ (x ◇ y)) ◇ x))).trans (hlem x ((z ◇ (x ◇ y)) ◇ x))).trans (hlem (z ◇ (x ◇ y)) x)).symm
"""),
    ("v0 = ((v1 ◇ (v2 ◇ ((v1 ◇ v0) ◇ v2))) ◇ v1)",
     "v0 = (((v1 ◇ v2) ◇ (v0 ◇ v3)) ◇ (v2 ◇ v4))"): ("true", "e30719_e27190", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, ((a ◇ (a ◇ b)) ◇ a) = (c ◇ ((a ◇ b) ◇ c)) := by
    intro a b c
    exact ((h (c ◇ ((a ◇ b) ◇ c)) a a).trans (congrArg (fun t => (a ◇ (a ◇ t)) ◇ a) ((h b a c).symm))).symm
  have hlem1 : ∀ a c b : G, a = (c ◇ ((b ◇ ((b ◇ a) ◇ b)) ◇ c)) := by
    intro a c b
    exact (h a b b).trans (hlem0 b ((b ◇ a) ◇ b) c)
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((hlem1 a a (a ◇ a)).trans (congrArg (fun t => (a ◇ (t ◇ a))) (((hlem1 ((a ◇ ((a ◇ a) ◇ a)) ◇ a) (a ◇ a) a).trans (congrArg (fun t => ((a ◇ a) ◇ (t ◇ (a ◇ a)))) ((hlem1 ((a ◇ a) ◇ a) a a).symm))).symm))).trans (congrArg (fun t => (a ◇ (t ◇ a))) ((hlem1 ((a ◇ ((a ◇ a) ◇ a)) ◇ a) (b ◇ a) a).trans (congrArg (fun t => ((b ◇ a) ◇ ((a ◇ (t ◇ a)) ◇ (b ◇ a)))) ((hlem1 a a a).symm))))).trans ((hlem1 b a (b ◇ a)).trans (congrArg (fun t => (a ◇ (((b ◇ a) ◇ (t ◇ (b ◇ a))) ◇ a))) ((hlem1 ((b ◇ a) ◇ b) a b).trans (congrArg (fun t => (a ◇ (t ◇ a))) ((hlem1 a b b).symm))))).symm
  intro x y z w u
  exact hlem x (((y ◇ z) ◇ (x ◇ w)) ◇ (z ◇ u))
"""),
    ("v0 = (v1 ◇ ((v2 ◇ (v1 ◇ v1)) ◇ v0))",
     "v0 = ((v1 ◇ v2) ◇ ((v0 ◇ v2) ◇ v0))"): ("false_code", "e1167_e1763", """import JudgeProblem

def submission.op (a b : Nat) : Nat :=
  if b % 2 = a % 2 then b + 1 else b - 1

def submission.inst : Magma Nat := { op := submission.op }

theorem submission.crux (y w x : Nat) (hw : w % 2 = y % 2) :
    submission.op y (submission.op w x) = x := by
  by_cases hx : x % 2 = w % 2
  · have h1 : submission.op w x = x + 1 := by
      unfold submission.op
      exact if_pos hx
    rw [h1]
    unfold submission.op
    split <;> omega
  · have h1 : submission.op w x = x - 1 := by
      unfold submission.op
      exact if_neg hx
    rw [h1]
    unfold submission.op
    split <;> omega

theorem submission.hwpar (y z : Nat) :
    (submission.op z (submission.op y y)) % 2 = y % 2 := by
  have hsq : submission.op y y = y + 1 := by
    unfold submission.op
    exact if_pos rfl
  rw [hsq]
  unfold submission.op
  split <;> omega

theorem submission.lhs : @EquationLHS Nat submission.inst := by
  intro x y z
  exact (submission.crux y (submission.op z (submission.op y y)) x
    (submission.hwpar y z)).symm

theorem submission.rhs : ¬ @EquationRHS Nat submission.inst := by
  intro h
  exact absurd (h 0 1 0) (by decide)

def submission : Goal :=
  Exists.intro Nat (Exists.intro submission.inst
    (And.intro submission.lhs submission.rhs))
"""),
    ("v0 = (((v1 ◇ v0) ◇ v2) ◇ (v2 ◇ v1))",
     "v0 = ((v1 ◇ (v1 ◇ (v0 ◇ v0))) ◇ v0)"): ("false", "e2116_e2327", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp
set_option maxRecDepth 20000

def submission : Goal := by
  let m : Magma (Fin 8) := {
    op := finOpTable "[[0,2,4,6,3,1,7,5],[3,6,1,2,0,4,5,7],[6,3,7,0,2,5,4,1],[5,4,2,1,7,6,3,0],[7,1,6,4,5,2,0,3],[4,5,0,7,1,3,6,2],[1,7,3,5,4,0,2,6],[2,0,5,3,6,7,1,4]]"
  }
  refine Exists.intro (Fin 8) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = (v1 ◇ (((v2 ◇ v1) ◇ v0) ◇ v2))",
     "(v0 ◇ (v1 ◇ v2)) = (v0 ◇ (v2 ◇ v1))"): ("false", "e1368_e4358", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp
set_option maxRecDepth 20000

def submission : Goal := by
  let m : Magma (Fin 8) := {
    op := finOpTable "[[0,2,6,1,3,4,7,5],[4,1,5,2,7,0,3,6],[3,6,2,5,0,7,4,1],[5,7,4,3,1,6,2,0],[7,5,1,6,4,3,0,2],[6,3,0,7,2,5,1,4],[1,4,7,0,5,2,6,3],[2,0,3,4,6,1,5,7]]"
  }
  refine Exists.intro (Fin 8) ?_
  refine Exists.intro m ?_
  decideFin!
"""),

    ("v0 = ((v1 ◇ (v2 ◇ (v0 ◇ v3))) ◇ v4)",
     "(v0 ◇ (v0 ◇ v1)) = ((v2 ◇ v1) ◇ v3)"): ("true", "e2380_e4422", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w
  exact (h (x ◇ (x ◇ y)) z (w ◇ (w ◇ (y ◇ w))) w w).trans (congrArg (fun t => ((z ◇ t) ◇ w)) ((h y w w w ((x ◇ (x ◇ y)) ◇ w)).symm))
"""),
    ("v0 = (((v1 ◇ (v2 ◇ v2)) ◇ v0) ◇ v1)",
     "v0 = (v1 ◇ ((v1 ◇ (v2 ◇ v0)) ◇ v2))"): ("false", "e3008_e1131", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 5) := {
    op := finOpTable "[[1,2,4,3,0],[2,1,0,4,3],[3,0,1,2,4],[0,4,3,1,2],[4,3,2,0,1]]"
  }
  refine Exists.intro (Fin 5) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = (((v0 ◇ (v1 ◇ v2)) ◇ v2) ◇ v0)",
     "v0 = (((v0 ◇ v0) ◇ (v1 ◇ v1)) ◇ v0)"): ("false", "e2890_e2652", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 6) := {
    op := finOpTable "[[0,5,0,3,4,3],[2,1,2,2,1,2],[2,1,2,2,1,2],[0,3,0,3,4,3],[0,4,0,3,4,5],[5,4,5,5,4,5]]"
  }
  refine Exists.intro (Fin 6) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = ((v1 ◇ (v0 ◇ (v0 ◇ v2))) ◇ v1)",
     "v0 = ((((v0 ◇ v1) ◇ v2) ◇ v1) ◇ v0)"): ("true", "e2297_e3089", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact (((((congrArg (fun t => (a ◇ t)) ((h a a a))).trans ((congrArg (fun t => (a ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a))) ((h a a a))).trans (congrArg (fun t => (a ◇ ((((a ◇ t) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))))).trans (((congrArg (fun t => (a ◇ ((((a ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t)) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))).trans (congrArg (fun t => (a ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a))) ((h ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) a (a ◇ (a ◇ a))).symm))).trans ((congrArg (fun t => (a ◇ (t ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ t) ◇ a))) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a))))))).trans (((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))) ◇ t)) ◇ a))) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a)))).trans ((congrArg (fun t => (a ◇ t)) ((h ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))) a (a ◇ a)).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ t) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ (a ◇ a))))))).trans (((congrArg (fun t => (a ◇ ((a ◇ (t ◇ a)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h (a ◇ (a ◇ (a ◇ ((a ◇ a) ◇ (a ◇ a))))) a a))).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ ((a ◇ (a ◇ (a ◇ ((a ◇ a) ◇ (a ◇ a))))) ◇ t)) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ (a ◇ a))).symm))).trans ((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ t) ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ (a ◇ a))).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ t)) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ a)))))))).trans ((((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (t ◇ a))) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h (a ◇ (a ◇ (a ◇ ((a ◇ a) ◇ a)))) a a))).trans ((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ ((a ◇ (a ◇ (a ◇ ((a ◇ a) ◇ a)))) ◇ t)) ◇ a) ◇ a))) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ a)).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ t) ◇ a) ◇ a))) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))))) ((h a a ((a ◇ a) ◇ a)).symm)))).trans (((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ t))) ((h ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) a (a ◇ a)))).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ t)) ◇ a)))) ((h (a ◇ a) (a ◇ a) a).symm))).trans ((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((a ◇ t) ◇ a)))) ((h (a ◇ a) (a ◇ a) a).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ (t ◇ a)))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a)))))).trans (((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a)))) ((h ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) a (a ◇ (a ◇ a))))).trans ((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((((a ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t)) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a)))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((((a ◇ t) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a)))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm)))).trans (((congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a)))) ((h a a a).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) ◇ t))) ((h a a a).symm))).trans ((congrArg (fun t => (a ◇ t)) ((h ((a ◇ a) ◇ a) a a).symm)).trans (congrArg (fun t => (a ◇ ((a ◇ t) ◇ a))) ((h a a a)))))))).trans (((((congrArg (fun t => (a ◇ ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ t)) ◇ a))) ((h a a a))).trans ((congrArg (fun t => (a ◇ t)) ((h (a ◇ (a ◇ (a ◇ a))) a a).symm)).trans (congrArg (fun t => (a ◇ (t ◇ (a ◇ (a ◇ a))))) ((h a a a))))).trans (((congrArg (fun t => (a ◇ (((a ◇ t) ◇ a) ◇ (a ◇ (a ◇ a))))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))).trans (congrArg (fun t => (a ◇ (((a ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t)) ◇ a) ◇ (a ◇ (a ◇ a))))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a)))).trans ((congrArg (fun t => (a ◇ (t ◇ (a ◇ (a ◇ a))))) ((h ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) a (a ◇ (a ◇ a))).symm)).trans (congrArg (fun t => (a ◇ t)) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm))))).trans ((((h (a ◇ (a ◇ (a ◇ a))) a a)).trans ((congrArg (fun t => ((a ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ t)) ◇ a)) ((h a a a).symm)).trans (congrArg (fun t => ((a ◇ t) ◇ a)) ((h a a a).symm)))).trans (((congrArg (fun t => ((a ◇ a) ◇ t)) ((h a a a))).trans (congrArg (fun t => ((a ◇ a) ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a))) ((h a a a)))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ t) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))).trans (congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t)) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))))))).trans ((((congrArg (fun t => ((a ◇ a) ◇ ((t ◇ (a ◇ (a ◇ a))) ◇ a))) ((h ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) a (a ◇ (a ◇ a))).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ (t ◇ a))) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ ((a ◇ t) ◇ a))) ((h (a ◇ a) (a ◇ a) a))))).trans (((congrArg (fun t => ((a ◇ a) ◇ ((a ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) ◇ t)) ◇ a))) ((h (a ◇ a) (a ◇ a) a))).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((h ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) a (a ◇ a)).symm))).trans (((h ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))) a (a ◇ a))).trans (congrArg (fun t => ((a ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a)))) ◇ t)) ◇ a)) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a)).symm))))).trans (((congrArg (fun t => ((a ◇ t) ◇ a)) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a)).symm)).trans ((congrArg (fun t => (t ◇ a)) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a))).trans (congrArg (fun t => ((t ◇ (a ◇ (a ◇ a))) ◇ a)) ((h ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) a (a ◇ (a ◇ a))))))).trans (((congrArg (fun t => ((((a ◇ (((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ a))) ◇ t)) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a)) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => ((((a ◇ t) ◇ a) ◇ (a ◇ (a ◇ a))) ◇ a)) ((h (a ◇ (a ◇ a)) (a ◇ (a ◇ a)) a).symm))).trans ((congrArg (fun t => ((t ◇ (a ◇ (a ◇ a))) ◇ a)) ((h a a a).symm)).trans ((h a a a).symm))))))
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((((h a b a)).trans ((congrArg (fun t => ((b ◇ (a ◇ t)) ◇ b)) ((hlem0 a))).trans (congrArg (fun t => ((b ◇ t) ◇ b)) ((hlem0 a))))).trans (((congrArg (fun t => (t ◇ b)) ((h (b ◇ a) b (b ◇ a)))).trans (congrArg (fun t => (((b ◇ ((b ◇ a) ◇ t)) ◇ b) ◇ b)) ((hlem0 (b ◇ a))))).trans ((congrArg (fun t => (((b ◇ t) ◇ b) ◇ b)) ((hlem0 (b ◇ a)))).trans (congrArg (fun t => (((b ◇ (b ◇ t)) ◇ b) ◇ b)) ((h a (a ◇ b) a)))))).trans (((congrArg (fun t => (((b ◇ (b ◇ (((a ◇ t) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b)))) ◇ b) ◇ b)) ((hlem0 b).symm)).trans ((congrArg (fun t => (((b ◇ (b ◇ (((a ◇ (b ◇ t)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b)))) ◇ b) ◇ b)) ((hlem0 b).symm)).trans (congrArg (fun t => (((b ◇ (b ◇ (((a ◇ (b ◇ (b ◇ b))) ◇ (a ◇ t)) ◇ (a ◇ b)))) ◇ b) ◇ b)) ((hlem0 a))))).trans (((congrArg (fun t => (((b ◇ (b ◇ (((a ◇ (b ◇ (b ◇ b))) ◇ t) ◇ (a ◇ b)))) ◇ b) ◇ b)) ((hlem0 a))).trans (congrArg (fun t => (((b ◇ (b ◇ (t ◇ (a ◇ b)))) ◇ b) ◇ b)) ((h b a b).symm))).trans ((congrArg (fun t => (t ◇ b)) ((h b b (a ◇ b)).symm)).trans ((hlem0 b)))))
  intro x y z
  exact hlem x ((((x ◇ y) ◇ z) ◇ y) ◇ x)
"""),
    ("v0 = ((v1 ◇ ((v1 ◇ v0) ◇ v0)) ◇ v1)",
     "(v0 ◇ (v0 ◇ v1)) = (v2 ◇ (v2 ◇ v1))"): ("false", "e2531_e4307", """import JudgeProblem
import JudgeDecide.DecideBang
set_option maxRecDepth 40000

def submission : Goal := by
  let m : Magma (Fin 13) := { op := fun i j => Fin.mk (Nat.mod (List.getD [0,7,1,8,2,9,3,10,4,11,5,12,6,7,1,8,2,9,3,10,4,11,5,12,6,0,1,8,2,9,3,10,4,11,5,12,6,0,7,8,2,9,3,10,4,11,5,12,6,0,7,1,2,9,3,10,4,11,5,12,6,0,7,1,8,9,3,10,4,11,5,12,6,0,7,1,8,2,3,10,4,11,5,12,6,0,7,1,8,2,9,10,4,11,5,12,6,0,7,1,8,2,9,3,4,11,5,12,6,0,7,1,8,2,9,3,10,11,5,12,6,0,7,1,8,2,9,3,10,4,5,12,6,0,7,1,8,2,9,3,10,4,11,12,6,0,7,1,8,2,9,3,10,4,11,5,6,0,7,1,8,2,9,3,10,4,11,5,12] (Nat.add (Nat.mul (Fin.val i) 13) (Fin.val j)) 0) 13) (Nat.mod_lt _ (Nat.succ_pos 12)) }
  refine Exists.intro (Fin 13) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = ((v1 ◇ (v2 ◇ (v2 ◇ v0))) ◇ v0)",
     "v0 = ((v0 ◇ ((v1 ◇ v0) ◇ v0)) ◇ v0)"): ("true", "e2398_e2456", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((congrArg (fun t => (t ◇ a)) ((h a a a))).trans (congrArg (fun t => (((a ◇ (a ◇ (a ◇ a))) ◇ t) ◇ a)) ((h a a a)))).trans ((congrArg (fun t => (((a ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ (a ◇ a))) ◇ t)) ◇ a)) ((h a a a))).trans ((h a (a ◇ (a ◇ (a ◇ a))) (a ◇ (a ◇ (a ◇ a)))).symm))
  intro x y
  exact ((((hlem0 x).symm).trans (congrArg (fun t => (x ◇ t)) ((h x y x)))).trans ((congrArg (fun t => (x ◇ ((y ◇ (x ◇ t)) ◇ x))) ((hlem0 x))).trans ((congrArg (fun t => (x ◇ ((y ◇ t) ◇ x))) ((hlem0 x))).trans (congrArg (fun t => (t ◇ ((y ◇ x) ◇ x))) ((hlem0 x).symm))))).trans (((congrArg (fun t => ((x ◇ t) ◇ ((y ◇ x) ◇ x))) ((h x y x))).trans ((congrArg (fun t => ((x ◇ ((y ◇ (x ◇ t)) ◇ x)) ◇ ((y ◇ x) ◇ x))) ((hlem0 x))).trans (congrArg (fun t => ((x ◇ ((y ◇ t) ◇ x)) ◇ ((y ◇ x) ◇ x))) ((hlem0 x))))).trans ((congrArg (fun t => ((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ t) ◇ x))) ((hlem0 x).symm)).trans ((congrArg (fun t => ((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (x ◇ t)) ◇ x))) ((hlem0 x).symm)).trans (congrArg (fun t => ((x ◇ ((y ◇ x) ◇ x)) ◇ t)) ((h x y x).symm)))))
"""),
    ("v0 = ((v1 ◇ ((v0 ◇ v2) ◇ v2)) ◇ v0)",
     "v0 = ((v0 ◇ (v1 ◇ v2)) ◇ (v3 ◇ v0))"): ("true", "e2521_e1879", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((((congrArg (fun t => (t ◇ a)) ((h a a (a ◇ a)))).trans ((congrArg (fun t => (((a ◇ ((a ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a))).trans (congrArg (fun t => (((a ◇ ((a ◇ ((t ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a).symm)))).trans ((congrArg (fun t => (((a ◇ ((t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) a))).trans ((congrArg (fun t => (((a ◇ (((t ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a (a ◇ a)).symm)).trans (congrArg (fun t => (((a ◇ (((((a ◇ a) ◇ a) ◇ t) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a)))))).trans (((congrArg (fun t => (((a ◇ (((((a ◇ a) ◇ a) ◇ (t ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a).symm)).trans ((congrArg (fun t => (((a ◇ (((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((t ◇ a) ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => (((a ◇ (((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)))).trans ((congrArg (fun t => (((a ◇ (t ◇ (a ◇ a))) ◇ a) ◇ a)) ((h (a ◇ a) ((a ◇ a) ◇ a) a).symm)).trans ((congrArg (fun t => (((a ◇ ((a ◇ t) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a))).trans (congrArg (fun t => (((a ◇ ((a ◇ (t ◇ a)) ◇ (a ◇ a))) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a).symm)))))).trans ((((congrArg (fun t => (((a ◇ t) ◇ a) ◇ a)) ((h (a ◇ a) a a).symm)).trans ((congrArg (fun t => (((a ◇ (t ◇ a)) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a))).trans (congrArg (fun t => (((a ◇ ((t ◇ a) ◇ a)) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a).symm)))).trans ((congrArg (fun t => (((t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) a))).trans ((congrArg (fun t => ((((t ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a (a ◇ a)).symm)).trans (congrArg (fun t => ((((((a ◇ a) ◇ a) ◇ t) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a)))))).trans (((congrArg (fun t => ((((((a ◇ a) ◇ a) ◇ (t ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a).symm)).trans ((congrArg (fun t => ((((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((t ◇ a) ◇ a)) ◇ a) ◇ a)) ((h ((a ◇ a) ◇ a) a a))).trans (congrArg (fun t => ((((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ (t ◇ a)) ◇ a) ◇ a)) ((h a (a ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)))).trans ((congrArg (fun t => ((t ◇ a) ◇ a)) ((h (a ◇ a) ((a ◇ a) ◇ a) a).symm)).trans ((congrArg (fun t => (t ◇ a)) ((h ((a ◇ a) ◇ a) (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) a))).trans ((h a ((((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ a)) a).symm)))))
  have hlem : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact ((congrArg (fun t => (t ◇ b)) ((hlem0 a).symm)).trans (congrArg (fun t => ((a ◇ t) ◇ b)) ((h a b a)))).trans ((congrArg (fun t => ((a ◇ ((b ◇ (t ◇ a)) ◇ a)) ◇ b)) ((hlem0 a))).trans ((congrArg (fun t => ((a ◇ ((b ◇ t) ◇ a)) ◇ b)) ((hlem0 a))).trans ((h b a a).symm)))
  intro x y z w
  exact ((hlem w x).symm).trans ((hlem (x ◇ (y ◇ z)) (w ◇ x)).symm)
"""),
    ("v0 = (v0 ◇ ((v1 ◇ (v2 ◇ v0)) ◇ v2))",
     "v0 = ((v0 ◇ v1) ◇ (v1 ◇ (v1 ◇ v0)))"): ("true", "e1057_e1454", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact (congrArg (fun t => (a ◇ t)) (h b a (a ◇ b))).trans (((h a b ((a ◇ ((a ◇ b) ◇ b)) ◇ (a ◇ b))).trans (congrArg (fun t => (a ◇ (t ◇ ((a ◇ ((a ◇ b) ◇ b)) ◇ (a ◇ b))))) ((h b (a ◇ ((a ◇ b) ◇ b)) a).symm))).symm)
  intro x y
  exact ((hlem (x ◇ y) (y ◇ (y ◇ x))).trans (hlem x y)).symm
"""),
    ("v0 = ((v1 ◇ v0) ◇ ((v0 ◇ v2) ◇ v1))",
     "v0 = ((((v0 ◇ v1) ◇ v2) ◇ v3) ◇ v3)"): ("true", "e1688_e3100", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((((h (a ◇ a) (a ◇ (a ◇ a)) (a ◇ a))).trans ((congrArg (fun t => (((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) ((h a a a))).trans (congrArg (fun t => (t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) ((h (a ◇ a) a ((a ◇ a) ◇ a)).symm)))).trans (((congrArg (fun t => ((a ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (t ◇ (a ◇ a))))) ((h a a a))).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a)).symm))).trans ((congrArg (fun t => ((a ◇ a) ◇ t)) ((h (a ◇ a) (a ◇ a) a))).trans (congrArg (fun t => ((a ◇ a) ◇ ((t ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) ((h (a ◇ a) a ((a ◇ a) ◇ a))))))).trans ((((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ (a ◇ a)) ◇ (t ◇ a)) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) ((h a a a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) ((h (a ◇ a) (a ◇ a) ((a ◇ a) ◇ a))))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((((a ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (t ◇ (a ◇ a)))) ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) ((h a a a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ (t ◇ (((a ◇ a) ◇ a) ◇ (a ◇ a))))) ((h (a ◇ a) (a ◇ (a ◇ a)) (a ◇ a)).symm)))).trans (((congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ t)))) ((h (a ◇ a) a ((a ◇ a) ◇ a)))).trans (congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (t ◇ a)))))) ((h a a a).symm))).trans ((congrArg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ t))) ((h a (a ◇ a) (a ◇ a)).symm)).trans ((h a a a).symm))))
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a (a ◇ b) a)).trans ((congrArg (fun t => ((t ◇ a) ◇ ((a ◇ a) ◇ (a ◇ b)))) ((hlem0 (a ◇ b)).symm)).trans (congrArg (fun t => ((((a ◇ b) ◇ (a ◇ b)) ◇ t) ◇ ((a ◇ a) ◇ (a ◇ b)))) ((h a (a ◇ b) b))))).trans ((congrArg (fun t => ((((a ◇ b) ◇ (a ◇ b)) ◇ (((a ◇ b) ◇ a) ◇ t)) ◇ ((a ◇ a) ◇ (a ◇ b)))) ((hlem0 (a ◇ b)))).trans ((congrArg (fun t => (t ◇ ((a ◇ a) ◇ (a ◇ b)))) ((h (a ◇ b) (a ◇ b) a).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ t))) ((h (a ◇ b) (a ◇ b) a)))))).trans (((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (((a ◇ b) ◇ a) ◇ t))))) ((hlem0 (a ◇ b)).symm)).trans ((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ t)))) ((h a (a ◇ b) b).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((a ◇ a) ◇ (t ◇ a)))) ((hlem0 (a ◇ b)))))).trans (((congrArg (fun t => ((a ◇ b) ◇ t)) ((h a a b).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ t)) ((h a b b)))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (t ◇ b)))) ((hlem0 (a ◇ b)).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ ((t ◇ (a ◇ b)) ◇ b)))) ((h (a ◇ b) (a ◇ b) a))))))).trans ((((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (((((a ◇ b) ◇ (a ◇ b)) ◇ (((a ◇ b) ◇ a) ◇ t)) ◇ (a ◇ b)) ◇ b)))) ((hlem0 (a ◇ b)).symm)).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (((((a ◇ b) ◇ (a ◇ b)) ◇ t) ◇ (a ◇ b)) ◇ b)))) ((h a (a ◇ b) b).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (((t ◇ a) ◇ (a ◇ b)) ◇ b)))) ((hlem0 (a ◇ b)))))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ ((((a ◇ b) ◇ a) ◇ t) ◇ b)))) ((hlem0 (a ◇ b)).symm)).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (t ◇ b)))) ((h a (a ◇ b) b).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ t))) ((hlem0 (a ◇ b)).symm))))).trans (((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (t ◇ (a ◇ b))))) ((h (a ◇ b) (a ◇ b) a))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ ((((a ◇ b) ◇ (a ◇ b)) ◇ (((a ◇ b) ◇ a) ◇ t)) ◇ (a ◇ b))))) ((hlem0 (a ◇ b)).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ ((((a ◇ b) ◇ (a ◇ b)) ◇ t) ◇ (a ◇ b))))) ((h a (a ◇ b) b).symm)))).trans (((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ ((t ◇ a) ◇ (a ◇ b))))) ((hlem0 (a ◇ b)))).trans (congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ (((a ◇ b) ◇ a) ◇ t)))) ((hlem0 (a ◇ b)).symm))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((b ◇ a) ◇ t))) ((h a (a ◇ b) b).symm)).trans ((h b a a).symm)))))
  intro x y z w
  exact hlem x ((((x ◇ y) ◇ z) ◇ w) ◇ w)
"""),
    ("v0 = ((v1 ◇ ((v2 ◇ v0) ◇ v2)) ◇ v0)",
     "v0 = (((v1 ◇ v2) ◇ v3) ◇ (v3 ◇ v0))"): ("true", "e2575_e2227", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact (((congrArg (fun t => (t ◇ b)) ((h a (((a ◇ a) ◇ a) ◇ ((a ◇ (((a ◇ b) ◇ a) ◇ (a ◇ b))) ◇ a)) (a ◇ b)))).trans ((congrArg (fun t => ((t ◇ a) ◇ b)) ((h (((a ◇ b) ◇ a) ◇ (a ◇ b)) ((a ◇ a) ◇ a) a).symm)).trans (congrArg (fun t => (((t ◇ (a ◇ b)) ◇ a) ◇ b)) ((h ((a ◇ b) ◇ a) (a ◇ ((a ◇ b) ◇ a)) b))))).trans (((congrArg (fun t => ((((((a ◇ ((a ◇ b) ◇ a)) ◇ t) ◇ ((a ◇ b) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h b b a).symm)).trans (congrArg (fun t => ((((t ◇ ((a ◇ b) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h b a a).symm))).trans ((congrArg (fun t => ((((b ◇ t) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h ((a ◇ b) ◇ a) a (a ◇ b)))).trans (congrArg (fun t => ((((b ◇ ((a ◇ (((a ◇ t) ◇ ((a ◇ b) ◇ a)) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h b b a)))))).trans ((((congrArg (fun t => ((((b ◇ ((a ◇ (t ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h ((a ◇ b) ◇ a) a b).symm)).trans (congrArg (fun t => ((((b ◇ ((t ◇ (((a ◇ b) ◇ a) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h a ((a ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ ((a ◇ a) ◇ a)) ◇ a)) a)))).trans ((congrArg (fun t => ((((b ◇ (((t ◇ a) ◇ (((a ◇ b) ◇ a) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h ((a ◇ a) ◇ a) (a ◇ ((a ◇ a) ◇ a)) a).symm)).trans (congrArg (fun t => ((((b ◇ (((((a ◇ a) ◇ a) ◇ t) ◇ (((a ◇ b) ◇ a) ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h a a (a ◇ b)))))).trans (((congrArg (fun t => ((((b ◇ (t ◇ ((a ◇ b) ◇ a))) ◇ (a ◇ b)) ◇ a) ◇ b)) ((h (((a ◇ b) ◇ a) ◇ (a ◇ b)) ((a ◇ a) ◇ a) a).symm)).trans (congrArg (fun t => ((t ◇ a) ◇ b)) ((h (a ◇ b) b ((a ◇ b) ◇ a)).symm))).trans ((congrArg (fun t => (t ◇ b)) ((h ((a ◇ b) ◇ a) (a ◇ ((a ◇ b) ◇ a)) b))).trans ((h b ((a ◇ ((a ◇ b) ◇ a)) ◇ ((b ◇ ((a ◇ b) ◇ a)) ◇ b)) a).symm))))
  intro x y z w
  exact ((hlem w x).symm).trans ((hlem ((y ◇ z) ◇ w) (w ◇ x)).symm)
"""),
    ("v0 = (((v1 ◇ (v2 ◇ v1)) ◇ v2) ◇ v0)",
     "(v0 ◇ v0) = ((v0 ◇ (v1 ◇ v1)) ◇ v0)"): ("false", "e2998_e3870", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[1,2,3,0],[0,1,2,3],[3,0,3,2],[0,1,2,3]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = ((v0 ◇ v1) ◇ ((v2 ◇ v3) ◇ v0))",
     "(v0 ◇ v1) = (((v0 ◇ v2) ◇ v0) ◇ v1)"): ("false", "e1676_e4138", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[3,2,3,2],[1,2,1,2],[1,0,1,0],[3,0,3,0]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = (((v0 ◇ (v1 ◇ v1)) ◇ v2) ◇ v0)",
     "v0 = (((v0 ◇ (v1 ◇ v2)) ◇ v3) ◇ v0)"): ("false", "e2878_e2894", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[1,1,1,1],[2,2,2,3],[0,0,0,0],[0,0,0,1]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = (v1 ◇ ((v2 ◇ (v0 ◇ v0)) ◇ v1))",
     "v0 = (v0 ◇ (v1 ◇ ((v1 ◇ v0) ◇ v2)))"): ("true", "e1147_e641", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((((h a (b ◇ (b ◇ a)) a)).trans (congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (t ◇ (b ◇ (b ◇ a))))) ((h (a ◇ (a ◇ a)) (b ◇ b) (a ◇ (a ◇ a)))))).trans ((congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (((b ◇ b) ◇ (t ◇ (b ◇ b))) ◇ (b ◇ (b ◇ a))))) ((h a (a ◇ (a ◇ a)) a).symm)).trans (congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (((b ◇ b) ◇ t) ◇ (b ◇ (b ◇ a))))) ((h (a ◇ (b ◇ b)) b (a ◇ (b ◇ b))))))).trans (((congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (((b ◇ b) ◇ (b ◇ (t ◇ b))) ◇ (b ◇ (b ◇ a))))) ((h b (a ◇ (b ◇ b)) a).symm)).trans (congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (((b ◇ b) ◇ (t ◇ (b ◇ b))) ◇ (b ◇ (b ◇ a))))) ((h b (b ◇ (b ◇ b)) b)))).trans ((congrArg (fun t => ((b ◇ (b ◇ a)) ◇ (t ◇ (b ◇ (b ◇ a))))) ((h (b ◇ (b ◇ b)) (b ◇ b) (b ◇ (b ◇ b))).symm)).trans ((h b (b ◇ (b ◇ a)) b).symm)))
  intro x y z
  exact hlem x (x ◇ (y ◇ ((y ◇ x) ◇ z)))
"""),
    ("v0 = ((v1 ◇ (v0 ◇ (v2 ◇ v3))) ◇ v1)",
     "v0 = ((((v1 ◇ v2) ◇ v0) ◇ v1) ◇ v0)"): ("true", "e2323_e3180", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, a = ((b ◇ (a ◇ c)) ◇ b) := by
    intro a b c
    exact (h a b (a ◇ (c ◇ (a ◇ a))) a).trans (congrArg (fun t => ((b ◇ (a ◇ t)) ◇ b)) ((h c a a a).symm))
  have hlem1 : ∀ a b c d e f : G, a = (b ◇ ((a ◇ (c ◇ d)) ◇ (b ◇ (e ◇ f)))) := by
    intro a b c d e f
    exact (h a ((a ◇ (c ◇ d)) ◇ (b ◇ (e ◇ f))) c d).trans (congrArg (fun t => (t ◇ ((a ◇ (c ◇ d)) ◇ (b ◇ (e ◇ f))))) ((h b (a ◇ (c ◇ d)) e f).symm))
  have hlem2 : ∀ a b c d e f : G, ((a ◇ b) ◇ (c ◇ (d ◇ e))) = ((f ◇ c) ◇ f) := by
    intro a b c d e f
    exact (h ((a ◇ b) ◇ (c ◇ (d ◇ e))) f a b).trans (congrArg (fun t => ((f ◇ t) ◇ f)) ((h c (a ◇ b) d e).symm))
  have hlem3 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((hlem1 (a ◇ a) (a ◇ (a ◇ a)) a a ((a ◇ a) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem1 a ((a ◇ a) ◇ (a ◇ a)) a a a a).symm))).trans (hlem0 a a a).symm
  have hlem4 : ∀ a b c : G, (a ◇ b) = (a ◇ c) := by
    intro a b c
    exact ((hlem1 (a ◇ b) (a ◇ (a ◇ a)) a a ((a ◇ b) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem1 a ((a ◇ b) ◇ (a ◇ a)) a a a a).symm))).trans ((hlem1 (a ◇ c) (a ◇ (a ◇ a)) a a ((a ◇ c) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem1 a ((a ◇ c) ◇ (a ◇ a)) a a a a).symm))).symm
  have hlem5 : ∀ a b c : G, (a ◇ b) = (c ◇ b) := by
    intro a b c
    exact ((hlem1 (a ◇ b) (a ◇ (a ◇ a)) a a ((a ◇ b) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem1 a ((a ◇ b) ◇ (a ◇ a)) a a a a).symm))).trans ((hlem1 (c ◇ b) (a ◇ (a ◇ a)) a a ((c ◇ b) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (a ◇ a)) ◇ t)) ((hlem1 a ((c ◇ b) ◇ (a ◇ a)) a a a a).symm))).symm
  have hlem6 : ∀ a b c d : G, (a ◇ b) = (c ◇ d) := by
    intro a b c d
    exact (hlem5 a b c).trans (hlem4 c d b).symm
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((hlem1 a (a ◇ (b ◇ a)) a a (a ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => ((a ◇ (b ◇ a)) ◇ t)) ((hlem1 a (a ◇ (a ◇ a)) b a a a).symm))).trans (hlem0 b a a).symm
  intro x y z
  exact hlem x ((((y ◇ z) ◇ x) ◇ y) ◇ x)
"""),
    ("v0 = ((v1 ◇ v0) ◇ (v2 ◇ (v2 ◇ v0)))",
     "(v0 ◇ v0) = ((v0 ◇ v0) ◇ v0)"): ("true", "e1506_e359", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x
  exact ((((h (x ◇ x) x x)).trans (congrArg (fun t => (t ◇ (x ◇ (x ◇ (x ◇ x))))) ((h (x ◇ (x ◇ x)) (x ◇ x) (x ◇ x))))).trans ((congrArg (fun t => ((t ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) ◇ (x ◇ (x ◇ (x ◇ x))))) ((h x x x).symm)).trans (congrArg (fun t => ((x ◇ ((x ◇ x) ◇ t)) ◇ (x ◇ (x ◇ (x ◇ x))))) ((h x x x).symm)))).trans (((congrArg (fun t => ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ t))) ((h (x ◇ (x ◇ x)) (x ◇ x) (x ◇ x)))).trans (congrArg (fun t => ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (t ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))))))) ((h x x x).symm))).trans ((congrArg (fun t => ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ t))))) ((h x x x).symm)).trans ((h ((x ◇ x) ◇ x) x x).symm)))
"""),
    ("(v0 ◇ v1) = (v1 ◇ (v0 ◇ (v2 ◇ v1)))",
     "((v0 ◇ v1) ◇ v2) = ((v1 ◇ v3) ◇ v2)"): ("true", "e3349_e4682", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, (a ◇ b) = (b ◇ b) := by
    intro a b
    exact (((((h a b a)).trans ((h b (a ◇ (a ◇ b)) b))).trans ((congrArg (fun t => ((a ◇ (a ◇ b)) ◇ (b ◇ t))) ((h a b a).symm)).trans ((congrArg (fun t => ((a ◇ (a ◇ b)) ◇ t)) ((h b (a ◇ b) a))).trans ((h (a ◇ b) (a ◇ (a ◇ b)) b).symm)))).trans (((congrArg (fun t => ((a ◇ b) ◇ t)) ((h a (a ◇ b) a))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ t))) ((h a (a ◇ (a ◇ b)) b))).trans (congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ (a ◇ t))))) ((h a b a).symm)))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ t)))) ((h a (a ◇ b) a))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ t))) ((h (a ◇ b) (a ◇ (a ◇ b)) a).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ t))) ((h (a ◇ b) (a ◇ (a ◇ b)) b))))))).trans ((((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ t)))) ((h b (a ◇ b) a).symm)).trans (congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ t))))) ((h a b a)))).trans ((congrArg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ t))) ((h b (a ◇ (a ◇ b)) b).symm)).trans ((congrArg (fun t => ((a ◇ b) ◇ t)) ((h b (a ◇ b) a).symm)).trans ((h (a ◇ b) (b ◇ (a ◇ b)) (b ◇ b)))))).trans (((congrArg (fun t => ((b ◇ (a ◇ b)) ◇ t)) ((h (b ◇ b) (a ◇ b) b).symm)).trans ((congrArg (fun t => ((b ◇ (a ◇ b)) ◇ ((b ◇ b) ◇ t))) ((h a b b))).trans (congrArg (fun t => ((b ◇ (a ◇ b)) ◇ t)) ((h b (b ◇ b) a).symm)))).trans ((congrArg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ t))) ((h b b a))).trans (((h b (b ◇ (a ◇ b)) b).symm).trans ((h b b a).symm)))))
  intro x y z w
  exact (hlem (x ◇ y) z).trans ((hlem (y ◇ w) z).symm)
"""),
    ("v0 = ((v0 ◇ v1) ◇ (v0 ◇ (v1 ◇ v2)))",
     "v0 = ((v0 ◇ v1) ◇ (v0 ◇ (v2 ◇ v1)))"): ("false", "e1446_e1448", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[2,3,3,2],[3,3,3,3],[3,3,0,0],[2,0,0,1]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = (v0 ◇ (v1 ◇ ((v0 ◇ v2) ◇ v1)))",
     "v0 = (v0 ◇ ((v1 ◇ (v2 ◇ v3)) ◇ v3))"): ("true", "e636_e1070", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, a = (a ◇ (b ◇ (a ◇ b))) := by
    intro a b
    exact (h a b (a ◇ ((a ◇ a) ◇ a))).trans (congrArg (fun t => (a ◇ (b ◇ (t ◇ b)))) ((h a a a).symm))
  have hlem1 : ∀ a b c d : G, a = (a ◇ ((b ◇ (((a ◇ c) ◇ d) ◇ b)) ◇ (a ◇ c))) := by
    intro a b c d
    exact (h a (b ◇ (((a ◇ c) ◇ d) ◇ b)) c).trans (congrArg (fun t => (a ◇ ((b ◇ (((a ◇ c) ◇ d) ◇ b)) ◇ t))) ((h (a ◇ c) b d).symm))
  have hlem2 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact (congrArg (fun t => (a ◇ t)) ((hlem0 a (a ◇ (a ◇ a))).trans (congrArg (fun t => (a ◇ ((a ◇ (a ◇ a)) ◇ t))) ((hlem0 a a).symm)))).trans (h a a (a ◇ a)).symm
  have hlem3 : ∀ a : G, a = (a ◇ a) := by
    intro a
    exact (hlem2 a).symm
  have hlem4 : ∀ a : G, a = ((a ◇ a) ◇ a) := by
    intro a
    exact ((hlem2 a).symm).trans (congrArg (fun t => (t ◇ a)) (hlem2 a)).symm
  have hlem5 : ∀ a b : G, a = ((a ◇ a) ◇ b) := by
    intro a b
    exact (((hlem2 a).symm).trans (h (a ◇ a) b (b ◇ (a ◇ a)))).trans (congrArg (fun t => ((a ◇ a) ◇ t)) ((hlem0 b ((a ◇ a) ◇ (b ◇ (a ◇ a)))).trans (congrArg (fun t => (b ◇ (((a ◇ a) ◇ (b ◇ (a ◇ a))) ◇ t))) ((hlem0 b (a ◇ a)).symm)))).symm
  have hlem : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact (congrArg (fun t => (t ◇ b)) ((hlem2 a).symm)).trans (hlem5 a b).symm
  intro x y z w
  exact (hlem x ((y ◇ (z ◇ w)) ◇ w)).symm
"""),
    ("v0 = (v1 ◇ ((((v2 ◇ v3) ◇ v2) ◇ v0) ◇ v2))",
     "v0 = ((v1 ◇ (v0 ◇ v0)) ◇ ((v1 ◇ v2) ◇ v3))"): ("true", "e16886_e22457", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w
  exact (((h x (y ◇ (x ◇ x)) ((((w ◇ w) ◇ w) ◇ ((y ◇ z) ◇ w)) ◇ w) w).trans (congrArg (fun t => ((y ◇ (x ◇ x)) ◇ t)) ((h ((y ◇ z) ◇ w) (((((((w ◇ w) ◇ w) ◇ ((y ◇ z) ◇ w)) ◇ w) ◇ w) ◇ ((((w ◇ w) ◇ w) ◇ ((y ◇ z) ◇ w)) ◇ w)) ◇ x) w w).symm))).symm).symm
"""),
    ("v0 = (v1 ◇ (v0 ◇ ((v0 ◇ v2) ◇ (v2 ◇ v1))))",
     "v0 = (((v1 ◇ v2) ◇ v2) ◇ (v0 ◇ (v0 ◇ v3)))"): ("false", "e6681_e23774", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[2,0,1,3],[0,2,3,1],[1,3,2,0],[3,1,0,2]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ("v0 = ((v1 ◇ v2) ◇ (((v3 ◇ v0) ◇ v4) ◇ v4))",
     "v0 = ((v0 ◇ (v1 ◇ v1)) ◇ (v0 ◇ (v2 ◇ v0)))"): ("true", "e21241_e21453", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z
  exact (((h x x (y ◇ y) x (((x ◇ (x ◇ (z ◇ x))) ◇ x) ◇ x)).trans (congrArg (fun t => ((x ◇ (y ◇ y)) ◇ t)) ((h (x ◇ (z ◇ x)) (x ◇ x) (((x ◇ (x ◇ (z ◇ x))) ◇ x) ◇ x) x x).symm))).symm).symm
"""),
    ("v0 = ((v1 ◇ (v1 ◇ ((v2 ◇ v0) ◇ v1))) ◇ v2)",
     "v0 = ((v0 ◇ (v1 ◇ v2)) ◇ (v3 ◇ (v4 ◇ v4)))"): ("true", "e30562_e21559", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((((h a a (a ◇ (a ◇ b)))).trans ((congrArg (fun t => ((a ◇ (a ◇ (((a ◇ (a ◇ t)) ◇ a) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h b a a))).trans (congrArg (fun t => ((a ◇ (a ◇ (t ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h (a ◇ ((a ◇ b) ◇ a)) a a).symm)))).trans (((congrArg (fun t => ((a ◇ (a ◇ t)) ◇ (a ◇ (a ◇ b)))) ((h ((a ◇ ((a ◇ b) ◇ a)) ◇ a) b a))).trans (congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (t ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h (a ◇ ((a ◇ ((a ◇ b) ◇ a)) ◇ a)) a a)))).trans ((congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (((a ◇ (a ◇ t)) ◇ a) ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h ((a ◇ b) ◇ a) a a).symm)).trans (congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (t ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h b a a).symm))))).trans (((congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (t ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h b b a))).trans ((congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (((b ◇ (b ◇ t)) ◇ a) ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h ((a ◇ b) ◇ b) a b))).trans (congrArg (fun t => ((a ◇ (a ◇ ((b ◇ (b ◇ (t ◇ b))) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h (a ◇ ((b ◇ ((a ◇ b) ◇ b)) ◇ a)) b a).symm)))).trans (((congrArg (fun t => ((a ◇ (a ◇ t)) ◇ (a ◇ (a ◇ b)))) ((h ((b ◇ ((a ◇ b) ◇ b)) ◇ a) b a).symm)).trans (congrArg (fun t => ((a ◇ (a ◇ (t ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h (b ◇ ((a ◇ b) ◇ b)) a b)))).trans ((congrArg (fun t => ((a ◇ (a ◇ (((a ◇ (a ◇ t)) ◇ b) ◇ a))) ◇ (a ◇ (a ◇ b)))) ((h b b a).symm)).trans ((h b a (a ◇ (a ◇ b))).symm))))
  intro x y z w u
  exact hlem x ((x ◇ (y ◇ z)) ◇ (w ◇ (u ◇ u)))
"""),
    ("v0 = (v1 ◇ (((v2 ◇ v1) ◇ v0) ◇ v1))",
     "(v0 ◇ v1) = (v2 ◇ ((v1 ◇ v0) ◇ v0))"): ("true", "e1367_e3599", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((((h a (b ◇ a) a)).trans (congrArg (fun t => (t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (b ◇ a) a (a ◇ (b ◇ a)))))).trans ((congrArg (fun t => ((a ◇ (t ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b))).trans (congrArg (fun t => ((a ◇ ((a ◇ (t ◇ a)) ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h a (b ◇ a) a).symm)))).trans (((congrArg (fun t => ((a ◇ ((a ◇ (t ◇ a)) ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h a (a ◇ a) a))).trans (congrArg (fun t => ((a ◇ (t ◇ a)) ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (((a ◇ (a ◇ a)) ◇ a) ◇ (a ◇ a)) a a).symm))).trans ((congrArg (fun t => (t ◇ (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)))) ((h (a ◇ a) a (a ◇ (a ◇ a))).symm)).trans ((congrArg (fun t => ((a ◇ a) ◇ t)) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b))).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (t ◇ a)))) ((h a (b ◇ a) a).symm)))))).trans ((((congrArg (fun t => ((a ◇ a) ◇ (a ◇ t))) ((h (a ◇ a) a (a ◇ (a ◇ a))))).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ (t ◇ a))))) ((h (((a ◇ (a ◇ a)) ◇ a) ◇ (a ◇ a)) a a)))).trans ((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ ((a ◇ (t ◇ a)) ◇ a))))) ((h a (a ◇ a) a).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ ((a ◇ (t ◇ a)) ◇ a))))) ((h a (b ◇ a) a))))).trans (((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (a ◇ (t ◇ a))))) ((h (((a ◇ (b ◇ a)) ◇ a) ◇ (b ◇ a)) a b).symm)).trans (congrArg (fun t => ((a ◇ a) ◇ (a ◇ t))) ((h (b ◇ a) a (a ◇ (b ◇ a))).symm))).trans ((congrArg (fun t => ((a ◇ a) ◇ (a ◇ (t ◇ a)))) ((h b (a ◇ a) a))).trans ((congrArg (fun t => ((a ◇ a) ◇ t)) ((h (((a ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a)) a a).symm)).trans ((h b (a ◇ a) a).symm)))))
  intro x y z
  exact hlem (x ◇ y) (z ◇ ((y ◇ x) ◇ x))
"""),
    ("v0 = ((((v1 ◇ v0) ◇ (v2 ◇ v3)) ◇ v0) ◇ v1)",
     "v0 = ((v0 ◇ (v0 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0))"): ("true", "e39227_e22253", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, a = ((((b ◇ a) ◇ c) ◇ a) ◇ b) := by
    intro a b c
    exact (h a b (((a ◇ c) ◇ (a ◇ a)) ◇ c) a).trans (congrArg (fun t => ((((b ◇ a) ◇ t) ◇ a) ◇ b)) ((h c a a a).symm))
  have hlem1 : ∀ a b c d : G, (a ◇ b) = ((c ◇ d) ◇ ((a ◇ b) ◇ (c ◇ d))) := by
    intro a b c d
    exact (h (a ◇ b) ((a ◇ b) ◇ (c ◇ d)) c d).trans (congrArg (fun t => (t ◇ ((a ◇ b) ◇ (c ◇ d)))) ((h (c ◇ d) (a ◇ b) a b).symm))
  have hlem2 : ∀ a b c d e : G, a = ((a ◇ a) ◇ (((b ◇ c) ◇ a) ◇ (d ◇ e))) := by
    intro a b c d e
    exact (h a (((b ◇ c) ◇ a) ◇ (d ◇ e)) b c).trans (congrArg (fun t => ((t ◇ a) ◇ (((b ◇ c) ◇ a) ◇ (d ◇ e)))) ((h a (b ◇ c) d e).symm))
  have hlem3 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((hlem0 (a ◇ a) ((a ◇ a) ◇ (a ◇ a)) (a ◇ a)).trans (congrArg (fun t => (t ◇ ((a ◇ a) ◇ (a ◇ a)))) ((hlem0 (a ◇ a) (a ◇ a) (a ◇ a)).symm))).trans ((hlem0 a ((a ◇ a) ◇ (a ◇ a)) a).trans (congrArg (fun t => ((t ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))) ((hlem0 a a (a ◇ a)).symm))).symm
  have hlem4 : ∀ a : G, a = (a ◇ a) := by
    intro a
    exact (hlem3 a).symm
  have hlem5 : ∀ a : G, a = ((a ◇ a) ◇ a) := by
    intro a
    exact ((hlem3 a).symm).trans (congrArg (fun t => (t ◇ a)) (hlem3 a)).symm
  have hlem6 : ∀ a b : G, a = ((a ◇ a) ◇ b) := by
    intro a b
    exact (h a b a (b ◇ a)).trans (congrArg (fun t => ((t ◇ a) ◇ b)) ((hlem0 a (a ◇ (b ◇ a)) (b ◇ a)).trans (congrArg (fun t => (t ◇ (a ◇ (b ◇ a)))) ((hlem0 (b ◇ a) a a).symm)))).symm
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (hlem6 a b).trans (((((hlem3 b).symm).trans ((hlem0 (b ◇ b) ((b ◇ b) ◇ a) a).trans (congrArg (fun t => (t ◇ ((b ◇ b) ◇ a))) ((hlem0 a (b ◇ b) (b ◇ b)).symm)))).trans (congrArg (fun t => (a ◇ t)) ((hlem6 b a).symm))).trans (congrArg (fun t => (t ◇ b)) ((hlem3 a).symm))).symm
  intro x y
  exact hlem x ((x ◇ (x ◇ y)) ◇ ((x ◇ y) ◇ x))
"""),
    ("v0 = (v1 ◇ ((v2 ◇ (v0 ◇ (v3 ◇ v4))) ◇ v3))",
     "v0 = ((v1 ◇ v0) ◇ ((v0 ◇ (v2 ◇ v3)) ◇ v2))"): ("true", "e13167_e19841", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w
  exact (((h x (y ◇ x) w ((w ◇ (((x ◇ (z ◇ w)) ◇ z) ◇ (w ◇ w))) ◇ w) w).trans (congrArg (fun t => ((y ◇ x) ◇ t)) ((h ((x ◇ (z ◇ w)) ◇ z) (w ◇ (x ◇ (((w ◇ (((x ◇ (z ◇ w)) ◇ z) ◇ (w ◇ w))) ◇ w) ◇ w))) w w w).symm))).symm).symm
"""),
    ("v0 = (v1 ◇ ((v2 ◇ (v0 ◇ (v1 ◇ v1))) ◇ v1))",
     "v0 = (v1 ◇ ((v1 ◇ v2) ◇ (v0 ◇ (v3 ◇ v0))))"): ("true", "e13115_e9520", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, (a ◇ (b ◇ ((c ◇ c) ◇ (c ◇ c)))) = (c ◇ (b ◇ c)) := by
    intro a b c
    exact (h (a ◇ (b ◇ ((c ◇ c) ◇ (c ◇ c)))) c (c ◇ c)).trans (congrArg (fun t => (c ◇ (t ◇ c))) ((h b (c ◇ c) a).symm))
  have hlem1 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((h (a ◇ a) a (a ◇ a)).trans (congrArg (fun t => (a ◇ (t ◇ a))) (((hlem0 a (a ◇ a) (a ◇ a)).symm).trans (congrArg (fun t => (a ◇ t)) (hlem0 (a ◇ a) ((a ◇ a) ◇ (a ◇ a)) a))))).trans ((h a a (a ◇ a)).trans (congrArg (fun t => (a ◇ (t ◇ a))) (((hlem0 a a (a ◇ a)).symm).trans (congrArg (fun t => (a ◇ t)) (hlem0 a ((a ◇ a) ◇ (a ◇ a)) a))))).symm
  have hlem2 : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    exact ((h (a ◇ b) a (a ◇ a)).trans (congrArg (fun t => (a ◇ (t ◇ a))) (((hlem0 a (a ◇ b) (a ◇ a)).symm).trans (congrArg (fun t => (a ◇ t)) (hlem0 (a ◇ b) ((a ◇ a) ◇ (a ◇ a)) a))))).trans ((h a a (a ◇ a)).trans (congrArg (fun t => (a ◇ (t ◇ a))) (((hlem0 a a (a ◇ a)).symm).trans (congrArg (fun t => (a ◇ t)) (hlem0 a ((a ◇ a) ◇ (a ◇ a)) a))))).symm
  have hlem3 : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    exact (hlem2 a b).trans ((h b a a).trans (hlem2 a ((a ◇ (b ◇ (a ◇ a))) ◇ a))).symm
  have hlem4 : ∀ a : G, a = (a ◇ a) := by
    intro a
    exact (hlem1 a).symm
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact ((hlem3 b a).symm).trans ((hlem2 b a).symm).symm
  intro x y z w
  exact hlem x (y ◇ ((y ◇ z) ◇ (x ◇ (w ◇ x))))
"""),
    ("v0 = (v1 ◇ (v2 ◇ (((v0 ◇ v3) ◇ v2) ◇ v4)))",
     "v0 = ((((v1 ◇ v2) ◇ v0) ◇ v1) ◇ (v3 ◇ v4))"): ("true", "e8773_e28912", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z w u
  exact (((h x (((y ◇ z) ◇ x) ◇ y) u u ((((w ◇ u) ◇ u) ◇ ((x ◇ u) ◇ u)) ◇ u)).trans (congrArg (fun t => ((((y ◇ z) ◇ x) ◇ y) ◇ t)) ((h (w ◇ u) u ((x ◇ u) ◇ u) u u).symm))).symm).symm
"""),
    ("v0 = (v1 ◇ (v2 ◇ (((v3 ◇ v2) ◇ v0) ◇ v2)))",
     "v0 = ((v0 ◇ (v1 ◇ (v0 ◇ (v2 ◇ v1)))) ◇ v1)"): ("true", "e8993_e29328", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c d e : G, a = (b ◇ ((c ◇ (((d ◇ c) ◇ e) ◇ c)) ◇ e)) := by
    intro a b c d e
    exact (h a b (c ◇ (((d ◇ c) ◇ e) ◇ c)) a).trans (congrArg (fun t => (b ◇ ((c ◇ (((d ◇ c) ◇ e) ◇ c)) ◇ t))) ((h e ((a ◇ (c ◇ (((d ◇ c) ◇ e) ◇ c))) ◇ a) c d).symm))
  have hlem1 : ∀ a b c d e : G, (a ◇ (((b ◇ a) ◇ c) ◇ a)) = (d ◇ (e ◇ (c ◇ e))) := by
    intro a b c d e
    exact (h (a ◇ (((b ◇ a) ◇ c) ◇ a)) d e a).trans (congrArg (fun t => (d ◇ (e ◇ (t ◇ e)))) ((h c (a ◇ e) a b).symm))
  have hlem2 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact (hlem0 (a ◇ a) a a a a).trans ((hlem0 a a a a a).symm)
  have hlem3 : ∀ a b c : G, (a ◇ b) = (a ◇ c) := by
    intro a b c
    exact (hlem0 (a ◇ b) a a a a).trans ((hlem0 (a ◇ c) a a a a).symm)
  have hlem4 : ∀ a b c : G, (a ◇ b) = (c ◇ b) := by
    intro a b c
    exact (hlem0 (a ◇ b) a a a a).trans ((hlem0 (c ◇ b) a a a a).symm)
  have hlem5 : ∀ a b c d : G, (a ◇ b) = (c ◇ d) := by
    intro a b c d
    exact (hlem0 (a ◇ b) a a a a).trans ((hlem0 (c ◇ d) a a a a).symm)
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (hlem0 a a a a a).trans ((hlem0 b a a a a).symm)
  intro x y z
  exact hlem x ((x ◇ (y ◇ (x ◇ (z ◇ y)))) ◇ y)
"""),
    ("v0 = ((v1 ◇ ((v1 ◇ (v0 ◇ v1)) ◇ v2)) ◇ v1)",
     "v0 = (((v1 ◇ v2) ◇ v3) ◇ (v2 ◇ (v3 ◇ v1)))"): ("true", "e32253_e23916", """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, (a ◇ (b ◇ a)) = ((a ◇ b) ◇ a) := by
    intro a b
    exact (h (a ◇ (b ◇ a)) a a).trans (congrArg (fun t => ((a ◇ t) ◇ a)) ((h b a a).symm))
  have hlem1 : ∀ a b c d : G, (a ◇ ((a ◇ (b ◇ a)) ◇ c)) = ((a ◇ ((a ◇ b) ◇ d)) ◇ a) := by
    intro a b c d
    exact (h (a ◇ ((a ◇ (b ◇ a)) ◇ c)) a d).trans (congrArg (fun t => ((a ◇ ((a ◇ t) ◇ d)) ◇ a)) ((h b a c).symm))
  have hlem2 : ∀ a : G, (a ◇ a) = a := by
    intro a
    exact ((congrArg (fun t => (t ◇ a)) (h a a (a ◇ a))).trans (congrArg (fun t => (((a ◇ t) ◇ a) ◇ a)) (((hlem0 (a ◇ a) a).trans (congrArg (fun t => (t ◇ (a ◇ a))) ((hlem0 a a).symm))).symm))).trans ((h a a a).trans (congrArg (fun t => (t ◇ a)) (hlem1 a a a (a ◇ (a ◇ a))))).symm
  have hlem3 : ∀ a : G, a = (a ◇ a) := by
    intro a
    exact (hlem2 a).symm
  have hlem : ∀ a b : G, a = b := by
    intro a b
    exact (((h a a a).trans (congrArg (fun t => (t ◇ a)) (hlem1 a a a (b ◇ a)))).trans (congrArg (fun t => (((a ◇ (t ◇ (b ◇ a))) ◇ a) ◇ a)) (hlem2 a))).trans ((h b a a).trans (congrArg (fun t => (t ◇ a)) (hlem0 a (a ◇ (b ◇ a))))).symm
  intro x y z w
  exact hlem x (((y ◇ z) ◇ w) ◇ (z ◇ (w ◇ y)))
"""),
    ("v0 = (v1 ◇ (v0 ◇ ((v2 ◇ v2) ◇ v1)))",
     "(v0 ◇ v1) = (v1 ◇ (v0 ◇ (v0 ◇ v0)))"): ("false", "e695_e3342", """import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 4) := {
    op := finOpTable "[[1,0,2,3],[0,1,3,2],[2,3,1,0],[3,2,0,1]]"
  }
  refine Exists.intro (Fin 4) ?_
  refine Exists.intro m ?_
  decideFin!
"""),
    ('v0 = (((v0 ◇ (v0 ◇ v1)) ◇ v2) ◇ v2)',
     '(v0 ◇ v0) = (v0 ◇ ((v0 ◇ v1) ◇ v0))'): ("true", 'e2860_e3458', """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b c : G, a ◇ ((a ◇ (a ◇ c)) ◇ b) = a ◇ (a ◇ c) := by
    intro a b c
    exact (congrArg (fun t => t ◇ ((a ◇ (a ◇ c)) ◇ b)) (h a c ((a ◇ (a ◇ c)) ◇ b))).trans (((h (a ◇ (a ◇ c)) b ((a ◇ (a ◇ c)) ◇ b)).symm))
  have hlem1 : ∀ a b c d : G, ((((a ◇ (a ◇ b)) ◇ d) ◇ a) ◇ c) ◇ c = (a ◇ (a ◇ b)) ◇ d := by
    intro a b c d
    exact (congrArg (fun t => ((((a ◇ (a ◇ b)) ◇ d) ◇ t) ◇ c) ◇ c) (h a b d)).trans (((h ((a ◇ (a ◇ b)) ◇ d) d c).symm))
  have hlem2 : ∀ a b c : G, (a ◇ (a ◇ c)) ◇ a = (a ◇ (a ◇ c)) ◇ ((a ◇ (a ◇ c)) ◇ b) := by
    intro a b c
    exact (congrArg (fun t => (a ◇ (a ◇ c)) ◇ t) (h a c ((a ◇ (a ◇ c)) ◇ b))).trans ((hlem0 (a ◇ (a ◇ c)) ((a ◇ (a ◇ c)) ◇ b) b))
  have hlem3 : ∀ a b c d : G, (((a ◇ (a ◇ c)) ◇ a) ◇ d) ◇ d = a ◇ (a ◇ c) := by
    intro a b c d
    exact (congrArg (fun t => (t ◇ d) ◇ d) (hlem2 a b c)).trans (((h (a ◇ (a ◇ c)) b d).symm))
  have hlem4 : ∀ a b : G, b ◇ b = b ◇ (b ◇ a) := by
    intro a b
    exact (congrArg (fun t => t ◇ b) (h b a b)).trans ((hlem3 b a a b))
  have hlem5 : ∀ a b c : G, ((c ◇ c) ◇ b) ◇ b = c := by
    intro a b c
    exact (congrArg (fun t => (t ◇ b) ◇ b) (hlem4 a c)).trans (((h c a b).symm))
  have hlem6 : ∀ a b c : G, (c ◇ b) ◇ b = (c ◇ c) ◇ c := by
    intro a b c
    exact (congrArg (fun t => (t ◇ b) ◇ b) (h c a c)).trans ((hlem1 c a b c).trans ((congrArg (fun t => t ◇ c) ((hlem4 a c).symm))))
  have hlem7 : ∀ a b : G, b ◇ ((b ◇ b) ◇ a) = b ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ ((b ◇ b) ◇ a)) ((hlem5 a ((b ◇ b) ◇ a) b).symm)).trans (((h (b ◇ b) a ((b ◇ b) ◇ a)).symm))
  have hlem8 : ∀ a b : G, (b ◇ b) ◇ (b ◇ a) = (b ◇ b) ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ (b ◇ a)) (hlem4 a b)).trans ((hlem6 a (b ◇ a) b))
  have hlem9 : ∀ a b c : G, ((((b ◇ b) ◇ c) ◇ b) ◇ a) ◇ a = (b ◇ b) ◇ c := by
    intro a b c
    exact (congrArg (fun t => ((((b ◇ b) ◇ c) ◇ t) ◇ a) ◇ a) ((hlem5 a c b).symm)).trans (((h ((b ◇ b) ◇ c) c a).symm))
  have hlem10 : ∀ a b : G, ((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a) = ((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b) := by
    intro a b
    exact (congrArg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) ((hlem6 a b a).symm)).trans ((hlem8 b (a ◇ b)))
  have hlem11 : ∀ a b : G, (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b) = a ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ (a ◇ b)) (hlem10 a b)).trans ((hlem5 a (a ◇ b) (a ◇ b)))
  have hlem12 : ∀ a b c : G, ((b ◇ c) ◇ a) ◇ a = ((b ◇ c) ◇ (b ◇ c)) ◇ ((b ◇ b) ◇ b) := by
    intro a b c
    exact (congrArg (fun t => (t ◇ a) ◇ a) ((hlem11 b c).symm)).trans ((hlem9 a (b ◇ c) ((b ◇ b) ◇ b)))
  have hlem13 : ∀ a b : G, ((b ◇ b) ◇ b) ◇ a = ((b ◇ a) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b) := by
    intro a b
    exact (congrArg (fun t => t ◇ a) ((hlem6 a a b).symm)).trans ((hlem12 a b a))
  have hlem14 : ∀ a b : G, (((a ◇ a) ◇ a) ◇ b) ◇ (a ◇ b) = a ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ (a ◇ b)) (hlem13 b a)).trans ((congrArg (fun t => t ◇ (a ◇ b)) (hlem10 a b)).trans ((hlem5 a (a ◇ b) (a ◇ b))))
  have hlem15 : ∀ a b : G, (a ◇ b) ◇ ((a ◇ a) ◇ b) = (a ◇ a) ◇ b := by
    intro a b
    exact (congrArg (fun t => (t ◇ b) ◇ ((a ◇ a) ◇ b)) ((hlem5 a (a ◇ a) a).symm)).trans ((hlem14 (a ◇ a) b))
  have hlem16 : ∀ a b c : G, (((b ◇ b) ◇ c) ◇ a) ◇ a = b ◇ c := by
    intro a b c
    exact (congrArg (fun t => (t ◇ a) ◇ a) ((hlem15 b c).symm)).trans ((congrArg (fun t => (((b ◇ c) ◇ t) ◇ a) ◇ a) ((hlem15 b c).symm)).trans (((h (b ◇ c) ((b ◇ b) ◇ c) a).symm)))
  have hlem17 : ∀ a b : G, (a ◇ b) ◇ a = (a ◇ a) ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ a) ((hlem16 a a b).symm)).trans ((hlem9 a a b))
  have hlem18 : ∀ a b : G, a ◇ ((a ◇ b) ◇ a) = a ◇ a := by
    intro a b
    exact (congrArg (fun t => a ◇ t) (hlem17 a b)).trans ((hlem7 b a))
  intro x y
  exact ((hlem18 x y).symm)
"""),

    ('v0 = (((v1 ◇ v1) ◇ v1) ◇ (v0 ◇ v1))',
     'v0 = (((v1 ◇ v1) ◇ v0) ◇ (v1 ◇ v1))'): ("true", 'e2135_e2128', """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) ◇ a = (b ◇ b) ◇ b := by
    intro a b
    exact (congrArg (fun t => (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) ◇ t) (h a b)).trans (((h ((b ◇ b) ◇ b) (a ◇ b)).symm))
  have hlem1 : ∀ a b : G, ((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b) = ((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b) := by
    intro a b
    exact (congrArg (fun t => ((a ◇ a) ◇ a) ◇ t) ((hlem0 a b).symm)).trans (((h (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b)) a).symm))
  have hlem2 : ∀ a b c : G, (((b ◇ b) ◇ b) ◇ ((c ◇ c) ◇ c)) ◇ (a ◇ (b ◇ c)) = a := by
    intro a b c
    exact (congrArg (fun t => t ◇ (a ◇ (b ◇ c))) (hlem1 b c)).trans (((h a (b ◇ c)).symm))
  have hlem3 : ∀ a b : G, (b ◇ b) ◇ (a ◇ (b ◇ b)) = a := by
    intro a b
    exact (congrArg (fun t => t ◇ (a ◇ (b ◇ b))) (h (b ◇ b) b)).trans ((hlem2 a b b))
  have hlem4 : ∀ a b c d : G, (((b ◇ b) ◇ b) ◇ (((c ◇ c) ◇ c) ◇ ((d ◇ d) ◇ d))) ◇ (a ◇ (b ◇ (c ◇ d))) = a := by
    intro a b c d
    exact (congrArg (fun t => (((b ◇ b) ◇ b) ◇ t) ◇ (a ◇ (b ◇ (c ◇ d)))) (hlem1 c d)).trans ((hlem2 a b (c ◇ d)))
  have hlem5 : ∀ a b c : G, (((b ◇ b) ◇ b) ◇ (c ◇ c)) ◇ (a ◇ (b ◇ (c ◇ c))) = a := by
    intro a b c
    exact (congrArg (fun t => (((b ◇ b) ◇ b) ◇ t) ◇ (a ◇ (b ◇ (c ◇ c)))) (h (c ◇ c) c)).trans ((hlem4 a b c c))
  have hlem6 : ∀ a b : G, b ◇ (a ◇ (b ◇ (b ◇ b))) = a := by
    intro a b
    exact (congrArg (fun t => t ◇ (a ◇ (b ◇ (b ◇ b)))) (h b b)).trans ((hlem5 a b b))
  have hlem7 : ∀ a b : G, (((a ◇ a) ◇ a) ◇ (b ◇ b)) ◇ a = b ◇ b := by
    intro a b
    exact (congrArg (fun t => (((a ◇ a) ◇ a) ◇ (b ◇ b)) ◇ t) ((hlem3 a b).symm)).trans ((hlem5 (b ◇ b) a b))
  have hlem8 : ∀ a b c : G, ((((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ (c ◇ c)) ◇ (a ◇ b) = c ◇ c := by
    intro a b c
    exact (congrArg (fun t => (t ◇ (c ◇ c)) ◇ (a ◇ b)) (hlem1 a b)).trans ((hlem7 (a ◇ b) c))
  have hlem9 : ∀ a b : G, ((a ◇ a) ◇ (b ◇ b)) ◇ (a ◇ a) = b ◇ b := by
    intro a b
    exact (congrArg (fun t => (t ◇ (b ◇ b)) ◇ (a ◇ a)) (h (a ◇ a) a)).trans ((hlem8 a a b))
  have hlem10 : ∀ a b : G, (((a ◇ a) ◇ a) ◇ b) ◇ a = b := by
    intro a b
    exact (congrArg (fun t => (((a ◇ a) ◇ a) ◇ t) ◇ a) (h b b)).trans ((congrArg (fun t => (((a ◇ a) ◇ a) ◇ (((b ◇ b) ◇ b) ◇ t)) ◇ a) (h (b ◇ b) b)).trans ((congrArg (fun t => (((a ◇ a) ◇ a) ◇ (((b ◇ b) ◇ b) ◇ t)) ◇ a) (hlem1 b b)).trans ((congrArg (fun t => (((a ◇ a) ◇ a) ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b)))) ◇ t) ((hlem6 a b).symm)).trans ((hlem4 b a b (b ◇ b))))))
  have hlem11 : ∀ a b : G, ((b ◇ b) ◇ a) ◇ (b ◇ b) = a := by
    intro a b
    exact (congrArg (fun t => (t ◇ a) ◇ (b ◇ b)) ((hlem9 b b).symm)).trans ((hlem10 (b ◇ b) a))
  intro x y
  exact ((hlem11 x y).symm)
"""),

    ('v0 = (((v0 ◇ v1) ◇ v0) ◇ (v1 ◇ v2))',
     'v0 = (((v0 ◇ v0) ◇ (v1 ◇ v2)) ◇ v1)'): ("true", 'e2055_e2656', """import JudgeProblem

def submission : Goal := by
  intro G _ h
  have hlem0 : ∀ a b : G, b ◇ (b ◇ a) = b ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ (b ◇ a)) (h b b b)).trans (((h (b ◇ b) b a).symm))
  have hlem1 : ∀ a b c d : G, ((a ◇ ((b ◇ c) ◇ b)) ◇ a) ◇ b = a := by
    intro a b c d
    exact (congrArg (fun t => ((a ◇ ((b ◇ c) ◇ b)) ◇ a) ◇ t) (h b c d)).trans (((h a ((b ◇ c) ◇ b) (c ◇ d)).symm))
  have hlem2 : ∀ a b c : G, ((b ◇ b) ◇ b) ◇ ((b ◇ c) ◇ a) = b := by
    intro a b c
    exact (congrArg (fun t => (t ◇ b) ◇ ((b ◇ c) ◇ a)) ((hlem0 c b).symm)).trans (((h b (b ◇ c) a).symm))
  have hlem3 : ∀ a b : G, (a ◇ ((a ◇ a) ◇ a)) ◇ a = (a ◇ a) ◇ a := by
    intro a b
    exact (congrArg (fun t => (t ◇ ((a ◇ a) ◇ a)) ◇ a) ((hlem2 a a b).symm)).trans ((hlem1 ((a ◇ a) ◇ a) a b a))
  have hlem4 : ∀ a : G, ((a ◇ a) ◇ a) ◇ a = a := by
    intro a
    exact (congrArg (fun t => t ◇ a) ((hlem3 a a).symm)).trans ((hlem1 a a a a))
  have hlem5 : ∀ a b : G, (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = b ◇ a := by
    intro a b
    exact (congrArg (fun t => (t ◇ (b ◇ a)) ◇ b) ((hlem0 b (b ◇ a)).symm)).trans ((hlem1 (b ◇ a) b a a))
  have hlem6 : ∀ a b : G, (b ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a) = (b ◇ b) ◇ b := by
    intro a b
    exact (congrArg (fun t => (t ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ((hlem4 b).symm)).trans (((h ((b ◇ b) ◇ b) b a).symm))
  have hlem7 : ∀ a : G, a ◇ a = a ◇ ((a ◇ a) ◇ a) := by
    intro a
    exact (congrArg (fun t => t ◇ a) (h a a ((a ◇ a) ◇ a))).trans ((congrArg (fun t => (t ◇ (a ◇ ((a ◇ a) ◇ a))) ◇ a) ((hlem6 ((a ◇ a) ◇ a) a).symm)).trans ((hlem5 ((a ◇ a) ◇ a) a)))
  have hlem8 : ∀ a b : G, (b ◇ b) ◇ (b ◇ a) = (b ◇ b) ◇ b := by
    intro a b
    exact (congrArg (fun t => t ◇ (b ◇ a)) (hlem7 b)).trans ((congrArg (fun t => (t ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ((hlem4 b).symm)).trans (((h ((b ◇ b) ◇ b) b a).symm)))
  have hlem9 : ∀ a b c : G, b ◇ ((b ◇ c) ◇ a) = b ◇ b := by
    intro a b c
    exact (congrArg (fun t => t ◇ ((b ◇ c) ◇ a)) (h b b b)).trans ((congrArg (fun t => (t ◇ (b ◇ b)) ◇ ((b ◇ c) ◇ a)) ((hlem8 c b).symm)).trans (((h (b ◇ b) (b ◇ c) a).symm)))
  have hlem10 : ∀ a b c : G, (a ◇ a) ◇ c = (a ◇ (c ◇ b)) ◇ a := by
    intro a b c
    exact (congrArg (fun t => t ◇ c) ((hlem9 a a (c ◇ b)).symm)).trans ((congrArg (fun t => (t ◇ ((a ◇ (c ◇ b)) ◇ a)) ◇ c) (h a (c ◇ b) c)).trans ((hlem1 ((a ◇ (c ◇ b)) ◇ a) c b a)))
  have hlem11 : ∀ a b c d : G, ((a ◇ a) ◇ (b ◇ c)) ◇ b = a := by
    intro a b c d
    exact (congrArg (fun t => t ◇ b) (hlem10 a b (b ◇ c))).trans ((congrArg (fun t => ((a ◇ ((b ◇ c) ◇ b)) ◇ a) ◇ t) (h b c d)).trans (((h a ((b ◇ c) ◇ b) (c ◇ d)).symm)))
  intro x y z
  exact ((hlem11 x y z x).symm)
"""),
}


def solve_problem(
    problem: dict[str, Any],
    *,
    false_time_budget: float | None = None,
) -> dict[str, Any] | None:
    target = effort_tier()
    reset_hypothesis_model_count()
    reset_constraint_evidence()
    try:
        for tier in effort_ladder_to(target):
            set_effort(tier)
            record = solve_problem_pass(
                problem, false_time_budget=false_time_budget)
            if record is not None:
                return record
            if _HARD_DEADLINE is not None and time.monotonic() >= _HARD_DEADLINE:
                return None
            if memory_exceeded():
                return None
    finally:
        set_effort(target)
    return None


def solve_problem_pass(
    problem: dict[str, Any],
    *,
    false_time_budget: float | None = None,
) -> dict[str, Any] | None:
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return None

    def true_record(route: str, code: str) -> dict[str, Any]:
        return {
            "answer": make_true_answer(problem, code),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    def false_record(n: int, table: list[list[int]], route: str) -> dict[str, Any]:
        return {
            "answer": make_false_answer(problem, n, table,
                                        equations=(eq1, eq2)),
            "route": route,
            "priority": problem_priority(problem, eq1, eq2),
        }

    if is_reflexive_problem(problem):
        return true_record("true:reflexive", reflexive_true_certificate())

    singleton = singleton_route(eq1)
    if singleton is not None:
        singleton_var, singleton_on_lhs = singleton
        return true_record("true:singleton", singleton_true_certificate(
            eq1["variables"], eq2["variables"], singleton_var, singleton_on_lhs))

    distilled = DISTILLED_CERTS.get((canonical_eq_text(eq1), canonical_eq_text(eq2)))
    if distilled is not None:
        verdict, name, code = distilled
        if verdict == "true":
            return true_record(f"true:distilled:{name}", code)
        return {
            "answer": {
                "id": str(problem.get("id", "")),
                "verdict": "false",
                "code": code,
            },
            "route": f"false:distilled:{name}",
            "priority": problem_priority(problem, eq1, eq2),
        }

    for route_fn in TRUE_ROUTES:
        found = route_fn(eq1, eq2)
        if found is not None:
            return true_record(*found)

    if _engine_gate():
        return None
    counterexample = find_counterexample(eq1, eq2, time_budget=false_time_budget)
    if counterexample is not None:
        return false_record(*counterexample)

    closure_first = not absorption_hypothesis(eq1)
    if closure_first:
        if _engine_gate():
            return None
        closed = equational_closure_route(eq1, eq2)
        if closed is not None:
            return true_record(*closed)

    if _engine_gate():
        return None
    constrained = constraint_countermodel(eq1, eq2)
    if constrained is not None:
        return false_record(*constrained)

    engines: list[Any] = [
        egg_probe_route,
    ]
    engines.append(deep_absorption_closure_route)
    if not closure_first:
        engines.append(equational_closure_route)
    engines.extend((
        derived_cp_closure_route,
        projection_bootstrap_route,
        lemma_bootstrap_route,
        lemma_chain_bootstrap_route,
        egg_closure_route,
        egg_collapse_route,
        egg_priority_bootstrap_route,
        egg_bootstrap_route,
        egg_ladder_route,
        narrow_grind_true_route,
    ))

    for engine in engines:
        if _engine_gate():
            return None
        found = engine(eq1, eq2)
        if found is not None:
            return true_record(*found)

    if _engine_gate():
        return None
    late = local_model_counterexample(eq1, eq2)
    if late is not None:
        return false_record(*late)

    if _engine_gate():
        return None
    for index, (route, table) in enumerate(large_linear_family_tables()):
        if index % 128 == 0 and _engine_gate():
            return None
        if witness_check(eq1, eq2, table):
            return false_record(len(table), table, route)

    if _engine_gate():
        return None
    wide = constraint_countermodel(
        eq1, eq2, orders=CONSTRAINT_WIDE_ORDERS,
        time_budget=CONSTRAINT_WIDE_PER_ORDER_BUDGET, per_order=True,
        max_variables=CONSTRAINT_WIDE_MAX_VARIABLES)
    if wide is not None:
        return false_record(*wide)

    if _engine_gate():
        return None
    wide_domain = constraint_countermodel_wide_domain(eq1, eq2)
    if wide_domain is not None:
        return false_record(*wide_domain)
    return None


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


def guided_chain_certificate_from_terms(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    chain_terms: list[Term],
) -> str | None:
    if chain_terms[0] != eq2["lhs"] or chain_terms[-1] != eq2["rhs"]:
        return None
    proofs: list[str] = []
    for src, dst in zip(chain_terms, chain_terms[1:]):
        step = proof_between_terms_guided(
            eq1,
            eq2["variables"],
            src,
            dst,
            max_depth=_eff_depth(LLM_GUIDED_CHAIN_MAX_DEPTH),
            closure_time_budget=_eff_time(LLM_GUIDED_CHAIN_CLOSURE_TIME_BUDGET),
        )
        if step is None:
            return None
        proofs.append(step[0])
    if not proofs:
        return None
    expr = proofs[0]
    for proof in proofs[1:]:
        expr = f"({expr}).trans ({proof})"
    return substitution_true_certificate(eq2["variables"], expr)


def parse_llm_key_terms(raw: Any, variables: set[str]) -> list[Term]:
    terms: list[Term] = []
    if not isinstance(raw, list):
        return terms
    for item in raw:
        if not isinstance(item, str):
            continue
        try:
            terms.append(parse_term(item, variables))
        except ValueError:
            continue
    return terms


def _seeded_closure_expr(
    eq1: dict[str, Any],
    goal_eq: dict[str, Any],
    seed_terms: list[Term],
    *,
    time_budget: float,
) -> str | None:
    result = _closure_proof_expr_impl(
        eq1,
        goal_eq,
        route_name="llm:true:seeded_closure",
        chain_max_depth=LLM_SEEDED_CLOSURE_CHAIN_MAX_DEPTH,
        pool_limit=LLM_SEEDED_CLOSURE_POOL_LIMIT,
        frontier_limit=LLM_SEEDED_CLOSURE_FRONTIER_LIMIT,
        max_fills=LLM_SEEDED_CLOSURE_MAX_FILLS,
        term_slack=LLM_SEEDED_CLOSURE_TERM_SLACK,
        depth_slack=LLM_SEEDED_CLOSURE_DEPTH_SLACK,
        time_budget=time_budget,
        seed_terms=seed_terms,
    )
    if result is None:
        return None
    return result[1]


def seeded_closure_certificate_from_terms(
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    seed_terms: list[Term],
) -> str | None:
    if not seed_terms:
        return None
    total_deadline = local_deadline(LLM_SEEDED_CLOSURE_TOTAL_BUDGET)

    proof_expr = _seeded_closure_expr(
        eq1, eq2, seed_terms, time_budget=LLM_SEEDED_CLOSURE_TIME_BUDGET
    )
    if proof_expr is not None:
        return substitution_true_certificate(eq2["variables"], proof_expr)

    endpoints = (eq2["lhs"], eq2["rhs"])
    waypoints: list[Term] = []
    waypoint_seen: set[Term] = set(endpoints)
    for term in seed_terms:
        if term in waypoint_seen:
            continue
        waypoint_seen.add(term)
        waypoints.append(term)
    for waypoint in waypoints[:LLM_SEEDED_CLOSURE_MAX_WAYPOINTS]:
        remaining = total_deadline - time.monotonic()
        if remaining < 2.0 * LLM_SEEDED_CLOSURE_WAYPOINT_BUDGET:
            break
        left_eq = {"lhs": eq2["lhs"], "rhs": waypoint, "variables": eq2["variables"]}
        left_expr = _seeded_closure_expr(
            eq1, left_eq, seed_terms, time_budget=LLM_SEEDED_CLOSURE_WAYPOINT_BUDGET
        )
        if left_expr is None:
            continue
        right_eq = {"lhs": waypoint, "rhs": eq2["rhs"], "variables": eq2["variables"]}
        right_expr = _seeded_closure_expr(
            eq1, right_eq, seed_terms, time_budget=LLM_SEEDED_CLOSURE_WAYPOINT_BUDGET
        )
        if right_expr is None:
            continue
        glued = f"({left_expr}).trans ({right_expr})"
        return substitution_true_certificate(eq2["variables"], glued)
    return None


LLM_MAX_LEMMAS = 6
LLM_LEMMA_MAX_TERM_SIZE = 13


LLM_LEMMA_BINDER_PREFIX = re.compile(r"^\s*(?:∀|forall\b)[^,]*,\s*")


def usable_llm_lemma(text: str) -> dict[str, Any] | None:
    if not isinstance(text, str):
        return None
    text = LLM_LEMMA_BINDER_PREFIX.sub("", text).strip().rstrip(".")
    try:
        lemma = parse_equation(text)
    except (ValueError, TypeError):
        return None
    variables = list(lemma["variables"])
    if not 1 <= len(variables) <= 4:
        return None
    if any(len(name) != 1 or not name.isalpha() or not name.islower() for name in variables):
        return None
    if "h" in variables:
        return None
    if max(term_size(lemma["lhs"]), term_size(lemma["rhs"])) > LLM_LEMMA_MAX_TERM_SIZE:
        return None
    return lemma


def llm_lemma_candidate(
    problem: dict[str, Any],
    eq1: dict[str, Any],
    eq2: dict[str, Any],
    obj: dict[str, Any],
) -> tuple[dict[str, Any] | None, str | None]:
    raw = obj.get("lemma")
    extra = obj.get("lemmas")
    proposals: list[Any] = []
    if isinstance(raw, str):
        proposals.append(raw)
    if isinstance(extra, list):
        proposals.extend(extra)
    elif isinstance(extra, str):
        proposals.append(extra)
    if not proposals:
        return None, None

    reason = "lemma_unparsable"
    seen: set[str] = set()
    for proposal in proposals:
        if not isinstance(proposal, str) or proposal in seen:
            continue
        seen.add(proposal)
        if len(seen) > LLM_MAX_LEMMAS:
            break
        lemma = usable_llm_lemma(proposal)
        if lemma is None:
            continue
        proof_expr = lemma_applies_to_goal(lemma, eq2)
        if proof_expr is None:
            reason = "lemma_does_not_imply_goal"
            continue
        lemma_proof = lemma_closure_proof(
            eq1, lemma, time_budget=LLM_LEMMA_CLOSURE_TIME_BUDGET)
        if lemma_proof is None:
            reason = "lemma_not_derivable_from_hypothesis"
            continue
        return {
            "answer": make_true_answer(
                problem,
                lemma_certificate(lemma, lemma_proof, eq2["variables"], proof_expr),
            ),
            "route": "llm:true:lemma",
        }, None
    return None, reason


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
        if raw_table is None:
            return None, "false_verdict_without_table"
        table = normalize_table(raw_table)
        if table is None:
            return None, "false_table_invalid_shape"
        if not table_is_counterexample(eq1, eq2, table):
            return None, "false_table_not_counterexample"
        return {
            "answer": make_false_answer(problem, len(table), table,
                                        equations=(eq1, eq2)),
            "route": "llm:false:table",
        }, "ok"

    lemma_candidate, lemma_reject = llm_lemma_candidate(problem, eq1, eq2, obj)
    if lemma_candidate is not None:
        return lemma_candidate, "ok"

    chain = obj.get("chain")
    if chain is None and isinstance(obj.get("steps"), list):
        steps = obj["steps"]
        if steps and all(isinstance(step, dict) for step in steps):
            chain = [steps[0].get("from")]
            chain.extend(step.get("to") for step in steps)
    variables = set(eq2["variables"])
    seed_terms: list[Term] = []
    peak_raw = obj.get("peak_term")
    if isinstance(peak_raw, str):
        try:
            seed_terms.append(parse_term(peak_raw, variables))
        except ValueError:
            pass
    seed_terms.extend(parse_llm_key_terms(obj.get("key_terms"), variables))
    chain_reject_reason = "no_chain_supplied"
    if chain is not None:
        chain_terms = None
        if isinstance(chain, list) and any(
            isinstance(item, str) and not set(re.findall(r"\b([a-z])\b", item)).issubset(variables)
            for item in chain
        ):
            chain_reject_reason = "rewrite_chain_uses_non_goal_variables"
        else:
            chain_terms = parse_llm_chain_terms(chain, variables)
        if chain_terms is None and chain_reject_reason != "rewrite_chain_uses_non_goal_variables":
            chain_reject_reason = "rewrite_chain_parse_failed"
        elif chain_terms is not None:
            seed_terms = seed_terms + chain_terms
            code = chain_certificate_from_terms(eq1, eq2, chain_terms)
            if code is not None:
                return {
                    "answer": make_true_answer(problem, code),
                    "route": "llm:true:rewrite_chain",
                }, "ok"
            code = guided_chain_certificate_from_terms(eq1, eq2, chain_terms)
            if code is not None:
                return {
                    "answer": make_true_answer(problem, code),
                    "route": "llm:true:guided_chain",
                }, "ok"
            chain_reject_reason = "guided_chain_unproved_or_bad_endpoints"
    if seed_terms:
        code = seeded_closure_certificate_from_terms(eq1, eq2, seed_terms)
        if code is not None:
            return {
                "answer": make_true_answer(problem, code),
                "route": "llm:true:seeded_closure",
            }, "ok"
        chain_reject_reason += "; seeded bidirectional closure around your terms also failed"

    if lemma_reject is not None:
        chain_reject_reason = f"{lemma_reject}; {chain_reject_reason}"

    if isinstance(obj.get("proof"), str) or isinstance(obj.get("proof_body"), str):
        return None, "proof_body_unsupported"

    if not allow_raw_true:
        if isinstance(obj.get("code", obj.get("lean")), str):
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
    rendered = list(dict.fromkeys(term_to_lean(term) for term in terms))[:limit]
    return ", ".join(rendered) if rendered else "(none)"


def llm_middle_term_hints(eq1: dict[str, Any], eq2: dict[str, Any], *, limit: int = 18) -> list[Term]:
    allowed_vars = set(eq2["variables"])
    seen: set[Term] = set()
    hints: list[Term] = []

    def add(term: Term) -> None:
        if term in seen or not term_vars(term).issubset(allowed_vars):
            return
        seen.add(term)
        hints.append(term)

    for term in (eq2["lhs"], eq2["rhs"]):
        add(term)
    for term in term_subterms_tuple(eq2["lhs"]) + term_subterms_tuple(eq2["rhs"]):
        add(term)
    for term in term_subterms_tuple(eq1["lhs"]) + term_subterms_tuple(eq1["rhs"]):
        add(term)
    for seed in (eq2["lhs"], eq2["rhs"]):
        for new_term, _proof, _route in rewrite_steps_from_term(eq1, seed):
            add(new_term)

    hints.sort(key=lambda term: (0 if term in (eq2["lhs"], eq2["rhs"]) else 1, term_size(term), term_depth(term), term_to_lean(term)))
    return hints[:limit]


def solver_analysis(problem: dict[str, Any]) -> str:
    try:
        eq1 = parse_equation(str(problem["equation1"]))
        eq2 = parse_equation(str(problem["equation2"]))
    except (KeyError, ValueError):
        return "Could not parse one of the equations; return a TRUE full Lean file only if certain."
    hypothesis_subterms = list(term_subterms_tuple(eq1["lhs"]) + term_subterms_tuple(eq1["rhs"]))
    goal_subterms = list(term_subterms_tuple(eq2["lhs"]) + term_subterms_tuple(eq2["rhs"]))
    middle_hints = llm_middle_term_hints(eq1, eq2)
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
        f"candidate chain middle terms: {terms_preview(middle_hints, limit=18)}",
        "deterministic route cues: " + "; ".join(deterministic_status),
    ]
    if absorption_hypothesis(eq1):
        cues.append("This is a good TRUE candidate for absorption/collapse/congruence chaining.")
    elif projection_cue(eq1, eq2):
        cues.append("Boundary/projection cues are risky; use TRUE only if the chain is explicit and solver-provable.")
    cues.append("Admissible term syntax: variables x y z w u v; binary products as a ◇ b; parentheses are allowed.")
    cues.append("A TRUE chain must start exactly with the goal lhs and end exactly with the goal rhs.")
    cues.append("Each adjacent TRUE chain step must be one explicit hypothesis rewrite, short rewrite chain, or bounded solver-owned closure/congruence step.")
    cues.append('Use {"proof_kind":"guided_chain"} when an adjacent chain edge needs more than one direct rewrite.')
    cues.append("If the chain needs a derived fact, include a lemmas array explaining it, but keep the chain terms concrete.")
    cues.append("Prefer the guided_chain: give intermediate terms and let the solver build the Lean proof; a raw Lean file is only a fallback.")
    cues.append("This row escaped deterministic finite-countermodel search, which is thorough but NOT exhaustive, so it is very likely TRUE — build a proof. Claim FALSE only with a concrete Cayley table you have actually verified; the solver re-checks it.")
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


def log_progress(record: dict[str, Any]) -> None:
    print(json.dumps(record), file=sys.stderr)


def log_route_count_chunks(route_counts: dict[str, int], *, max_chars: int = 850) -> None:
    chunk: dict[str, int] = {}
    for route, count in sorted(route_counts.items()):
        trial = dict(chunk)
        trial[route] = count
        record = {"route": "route_counts", "routes": trial}
        if chunk and len(json.dumps(record, separators=(",", ":"))) > max_chars:
            log_stderr({"route": "route_counts", "routes": chunk})
            chunk = {route: count}
        else:
            chunk = trial
    if chunk:
        log_stderr({"route": "route_counts", "routes": chunk})


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
    except Exception as exc:
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
        allow_raw_true=marathon_allow_raw_true(),
    )
    if candidate is None:
        result["reject_reason"] = reject_reason
        result["response_chars"] = len(response_text)
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


def marathon_allow_raw_true() -> bool:
    raw = os.environ.get("MAGMA_MARATHON_ALLOW_RAW_TRUE", "")
    return raw.strip().lower() in {"1", "true", "yes", "debug"}


def run_solo() -> int:
    payload = load_json_line(sys.stdin)
    if not payload:
        return 0

    problem = payload.get("problem", payload)
    if not isinstance(problem, dict):
        return 0

    budget_info = payload.get("budget")
    budget_seconds = 0.0
    if isinstance(budget_info, dict):
        try:
            budget_seconds = float(budget_info.get("timeout_seconds") or 0.0)
        except (TypeError, ValueError):
            budget_seconds = 0.0
    if budget_seconds <= 0.0:
        budget_seconds = float(os.environ.get("JUDGE_SOLO_BUDGET_SECONDS", "3600"))

    set_effort(effort_for_seconds(budget_seconds))

    reserve = min(SOLO_FALLBACK_RESERVE_SECONDS, 0.2 * budget_seconds)
    full_deadline = _PROCESS_START + budget_seconds - reserve
    det_deadline = min(
        full_deadline,
        _PROCESS_START + SOLO_DETERMINISTIC_SHARE * budget_seconds,
    )

    attempted: set[tuple[str, str]] = set()
    arm_memory_guard()
    set_hard_deadline(det_deadline)
    try:
        solved = solve_problem(problem)
    except Exception as exc:
        log_stderr({"route": "solve:crash", "error": f"{type(exc).__name__}: {exc}"})
        solved = None
    if solved is not None:
        answer = dict(solved["answer"])
        attempted.add((str(answer.get("verdict")), str(answer.get("code"))))
        response = judge_via_solo_proxy(answer)
        if response:
            log_progress({'judge_status': response.get('status'), 'route': solved['route']})
            if response.get("status") == "accepted":
                return 0

    analysis = solver_analysis(problem)
    if solved is None:
        log_progress({
            'route': 'skip:deterministic',
            'reason': 'No deterministic certificate available; escalating through proxy LLM.',
        })
        insurance = make_true_answer(problem, fallback_true_certificate())
        insurance_key = (str(insurance.get("verdict")), str(insurance.get("code")))
        attempted.add(insurance_key)
        insurance_response = judge_via_solo_proxy(insurance)
        if insurance_response:
            log_progress({
                'judge_status': insurance_response.get('status'),
                'route': 'fallback:insurance_reflexive',
            })
            if insurance_response.get("status") == "accepted":
                return 0

    set_hard_deadline(full_deadline)

    feedback = ""
    for round_idx in range(solo_llm_rounds()):
        if time.monotonic() >= full_deadline - SOLO_LLM_ROUND_MIN_SECONDS:
            log_progress({'route': 'llm:stop_deadline', 'round': round_idx})
            break
        llm_response = send_proxy_call(
            {
                "call": "llm",
                "context": {
                    "round": str(round_idx),
                    "analysis": analysis,
                    "feedback": feedback,
                },
            }
        )
        if not llm_response or "error" in llm_response:
            log_progress({
                'route': 'llm:skip',
                'round': round_idx,
                'error': (llm_response or {}).get('error', 'no response'),
            })
            break
        response_text = str(llm_response.get("response", ""))
        candidate, reject_reason = candidate_from_llm_text_with_reason(problem, response_text)
        if candidate is None:
            feedback = (
                f"Previous answer rejected before judging: {reject_reason}. "
                "Return one valid JSON object using ONLY the goal's variables; "
                "prefer proof_kind guided_chain with small single-rewrite steps "
                "whose first term is the goal LHS and last term is the goal RHS."
            )
            log_progress({
                'route': 'llm:reject',
                'round': round_idx,
                'reason': reject_reason,
                'response_chars': len(response_text),
                'response_preview': text_preview(response_text),
            })
            continue
        feedback = ""
        answer = dict(candidate["answer"])
        key = (str(answer.get("verdict")), str(answer.get("code")))
        if key in attempted:
            log_progress({'route': 'llm:duplicate', 'round': round_idx})
            continue
        attempted.add(key)
        judge_response = judge_via_solo_proxy(answer)
        if judge_response:
            log_progress({
                'judge_status': judge_response.get('status'),
                'route': candidate['route'],
                'round': round_idx,
            })
            if judge_response.get("status") == "accepted":
                return 0
    if hypothesis_models_seen() == 0:
        log_progress({
            'route': 'fallback:skip_no_model_evidence',
            'reason': 'FALSE search inspected 0 models of the hypothesis; a speculative TRUE verdict has no evidence behind it.',
        })
        return 0
    log_stderr({
        "route": "fallback:evidence",
        "models_seen": hypothesis_models_seen(),
        "constraint_search_exhausted": constraint_search_exhausted(),
    })
    fallback_route = "fallback:unsolved_grind"
    try:
        fallback_code = grind_true_certificate(
            parse_equation(str(problem["equation2"]))["variables"]
        )
    except (KeyError, ValueError):
        fallback_route = "fallback:unsolved_exact_h"
        fallback_code = fallback_true_certificate()
    fallback = make_true_answer(problem, fallback_code)
    fallback_key = (str(fallback.get("verdict")), str(fallback.get("code")))
    if fallback_key in attempted:
        return 0
    judge_response = judge_via_solo_proxy(fallback)
    if judge_response:
        log_progress({'judge_status': judge_response.get('status'), 'route': fallback_route})
    return 0


def iter_manifest(path: str) -> list[dict[str, Any]]:
    with open(path, "r", encoding="utf-8") as manifest_file:
        return [json.loads(line) for line in manifest_file if line.strip()]


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


def marathon_row_budget(remaining: float, rows_not_yet_attempted: int) -> float:
    remaining = max(0.0, remaining)
    rows_left = max(1, rows_not_yet_attempted)
    borrowed = MARATHON_ROW_BORROW * remaining / rows_left
    reserved = MARATHON_ROW_MIN_SECONDS * (rows_left - 1)
    budget = min(borrowed, max(0.0, remaining - reserved))
    return min(remaining, max(budget, MARATHON_ROW_MIN_SECONDS))


def marathon_per_problem_budget(total_budget: float, problem_count: int, ref_seconds: float) -> float:
    if problem_count <= 0:
        return 0.25
    share = total_budget / max(1, problem_count)
    compression = total_budget / max(1.0, ref_seconds * problem_count)
    floor = max(0.2, min(4.0, 0.5 + 5.0 * compression))
    return max(floor, min(60.0, 0.05 * share))


def load_marathon_llm() -> tuple[Any | None, Any | None, Any | None]:
    lib_dir = os.environ.get("JUDGE_MARATHON_LIB_DIR")
    if not lib_dir:
        return None, None, None
    if lib_dir not in sys.path:
        sys.path.insert(0, lib_dir)
    try:
        marathon_llm = importlib.import_module("marathon_llm")
    except Exception:
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
    arm_memory_guard()
    set_hard_deadline(deadline - 20.0)
    ref_seconds = marathon_reference_seconds()
    per_problem_budget = marathon_per_problem_budget(budget_seconds, len(problems), ref_seconds)
    set_effort(effort_for_seconds(0.5 * budget_seconds / max(1, len(problems))))
    deterministic_deadline = time.monotonic() + MARATHON_DETERMINISTIC_SHARE * budget_seconds

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
    pass_deadline = min(deterministic_deadline, deadline)
    total_rows = len(prioritized)
    attempted = 0
    try:
        for priority, problem in prioritized:
            if time.monotonic() + 5.0 >= pass_deadline:
                break
            row_budget = marathon_row_budget(
                pass_deadline - time.monotonic(), total_rows - attempted)
            attempted += 1
            set_hard_deadline(time.monotonic() + row_budget)
            try:
                clear_term_caches()
                reset_memory_reclaims()
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
            except Exception as exc:
                log_stderr(
                    {
                        "route": "solve:crash",
                        "id": str(problem.get("id")),
                        "error": f"{type(exc).__name__}: {exc}",
                    }
                )
                continue
    finally:
        set_hard_deadline(deadline - 20.0)

    llm_calls = 0
    call_llm, tokens_used, budget_remaining = load_marathon_llm()
    unresolved_count = len(prioritized) - len(solved_ids)
    if unresolved_count > 0 and call_llm is None:
        log_progress({
            'route': 'llm:disabled',
            'reason': 'missing_marathon_proxy_library',
            'unresolved': unresolved_count,
            'budget_tokens': budget_tokens,
        })
    if unresolved_count > 0 and budget_tokens == 0:
        log_progress({
            'route': 'llm:disabled',
            'reason': 'zero_token_budget',
            'unresolved': unresolved_count,
            'budget_tokens': budget_tokens,
        })
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
                        "allow_raw_true": marathon_allow_raw_true(),
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
                    except Exception as exc:
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

    log_route_count_chunks(route_counts)
    log_stderr(
        {
            "submitted_deterministic": deterministic_submitted,
            "submitted_total": solved,
            "llm_calls": llm_calls,
            "budget_seconds": budget_seconds,
            "budget_tokens": budget_tokens,
            "reference_seconds_per_problem": ref_seconds,
            "per_problem_false_budget": round(per_problem_budget, 3),
            "route_kind_count": len(route_counts),
            "route_count_total": sum(route_counts.values()),
        }
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
