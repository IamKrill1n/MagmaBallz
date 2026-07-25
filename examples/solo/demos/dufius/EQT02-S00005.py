"""
Stage 2 Solver — Foundation v0.1
================================

Single-file Python solver for the SAIR Mathematics Distillation Challenge
Stage 2. Implements the architecture from stage2_strategy_note_v3.md:

    Router (Stage 1 rule engine)
      → Layer 1 deterministic templates (X1, affine, projections)
      → Brute-force counterexample search (Fin 2..4)
      → Layer 3 LLM fallback with iterative repair

Track: Solo (stdin/stdout JSON protocol).
       Adaptable to Marathon by swapping main() — see comment at bottom.

Sandbox compliance: stdlib only. No numpy, z3, networkx.
                    sympy 1.13.3 is available but not used in v0.1.

Size budget: ≤ 500 KB. Currently well under.

Reading order:
    1. PROMPT — what we ask the LLM
    2. Equation parsing (Var, Prod, parse_equation)
    3. Features (leaves, leftmost_leaf, etc.)
    4. Layer 1 templates (Lean code emitters)
    5. Affine probe library (verify-then-emit)
    6. Brute-force search
    7. Rule engine (lightweight v20 port)
    8. main() loop and protocol handling
"""

import json
import sys
import itertools
from typing import Optional


# ============================================================
# PROMPT — extracted by Solo proxy via AST parsing
# ============================================================

PROMPT = """You are a Lean 4 expert generating proofs for magma equation implications.

Question: Does {problem.equation1} (Eq1) imply {problem.equation2} (Eq2) over all magmas?

Solver's analysis:
{solver.analysis}

Previous attempts (round {history.round}):
{history.attempts}

Last error from judge: {history.last_error}

CRITICAL INSTRUCTIONS:

1. The wrapper code already runs `intro G _ h`. So h is the hypothesis Eq1.
2. The hypothesis h has type ∀ vars, EquationLHS = EquationRHS — i.e. it's UNIVERSALLY QUANTIFIED.
3. To use h, you must INSTANTIATE it: `h <var1> <var2> ...` gives a specific equality.
4. The variable order in h follows the variable order of Eq1 (alphabetical: w, x, y, z).
5. Read judge errors carefully — they tell you EXACTLY what type h instances have.

WORKED EXAMPLE for FALSE (counterexample):
  Goal: prove that hypothesis "x = x*y" does NOT imply "x*y = y*x" universally.
  Strategy: find a Fin n magma where x = x*y holds but x*y ≠ y*x somewhere.
  Output: {{"verdict": "false", "size": 2, "table": [[0,0],[1,1]]}}
  In this magma, op is left-projection (x*y = x always), so x = x*y holds, but
  x*y ≠ y*x for x=0, y=1 since 0*1=0 ≠ 1=1*0.

WORKED EXAMPLE for TRUE (proof):
  Goal: prove "x = y" implies "y = x".
  Output: {{"verdict": "true", "proof": "intro a b\\nexact (h a b).symm"}}

Respond with ONLY valid JSON, no markdown fences, no prose, no comments inside proof strings.

For TRUE: {{"verdict": "true", "proof": "<Lean tactic body>"}}
For FALSE: {{"verdict": "false", "size": <n>, "table": <n×n matrix>}}

If you provide FALSE, the solver will VERIFY your table locally before sending to judge.
Make sure your table actually satisfies Eq1 and refutes Eq2 — guessing wastes rounds.

If you don't have high confidence, output FALSE with a small table and let the local
verifier check it. Don't claim TRUE unless you can write the actual derivation."""


# ============================================================
# Equation parsing
# ============================================================

class Var:
    __slots__ = ("name",)

    def __init__(self, name: str):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self):
        return hash(("var", self.name))


class Prod:
    __slots__ = ("left", "right")

    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"({self.left}*{self.right})"

    def __eq__(self, other):
        return (
            isinstance(other, Prod)
            and self.left == other.left
            and self.right == other.right
        )

    def __hash__(self):
        return hash(("prod", self.left, self.right))


def _tokenize(s: str) -> list[str]:
    # Accept both ◇ and * as operator
    s = s.replace("◇", "*")
    import re
    return re.findall(r"[A-Za-z_][A-Za-z0-9_]*|\*|\(|\)", s)


def _parse_tokens(tokens: list[str]):
    pos = [0]

    def parse_atom():
        if pos[0] >= len(tokens):
            raise ValueError(f"unexpected end at {pos[0]}")
        tok = tokens[pos[0]]
        if tok == "(":
            pos[0] += 1
            e = parse_expr()
            assert tokens[pos[0]] == ")", f"expected ) got {tokens[pos[0]]}"
            pos[0] += 1
            return e
        else:
            pos[0] += 1
            return Var(tok)

    def parse_expr():
        left = parse_atom()
        while pos[0] < len(tokens) and tokens[pos[0]] == "*":
            pos[0] += 1
            right = parse_atom()
            left = Prod(left, right)
        return left

    return parse_expr()


def parse_equation(s: str) -> tuple:
    """Parse 'L = R' into (Tree, Tree)."""
    if "=" not in s:
        raise ValueError(f"no = in {s!r}")
    lhs_str, rhs_str = s.split("=", 1)
    return _parse_tokens(_tokenize(lhs_str)), _parse_tokens(_tokenize(rhs_str))


# ============================================================
# Features
# ============================================================

def leaves(t) -> list[Var]:
    if isinstance(t, Var):
        return [t]
    return leaves(t.left) + leaves(t.right)


def leftmost_leaf(t) -> Var:
    while isinstance(t, Prod):
        t = t.left
    return t


def rightmost_leaf(t) -> Var:
    while isinstance(t, Prod):
        t = t.right
    return t


def var_set(t) -> set:
    return {v.name for v in leaves(t)}


def var_counts(t) -> dict:
    counts = {}
    for v in leaves(t):
        counts[v.name] = counts.get(v.name, 0) + 1
    return counts


def is_bare(t) -> bool:
    return isinstance(t, Var)


def tree_eq(t1, t2) -> bool:
    """Syntactic equality of trees (same variable names)."""
    if isinstance(t1, Var) and isinstance(t2, Var):
        return t1.name == t2.name
    if isinstance(t1, Prod) and isinstance(t2, Prod):
        return tree_eq(t1.left, t2.left) and tree_eq(t1.right, t2.right)
    return False


def evaluate(t, assignment: dict, table: list[list[int]]) -> int:
    """Evaluate a tree under variable assignment using the magma table."""
    if isinstance(t, Var):
        return assignment[t.name]
    a = evaluate(t.left, assignment, table)
    b = evaluate(t.right, assignment, table)
    return table[a][b]


def equation_holds(L, R, table: list[list[int]]) -> bool:
    """Check if L = R holds for all variable assignments in the magma."""
    n = len(table)
    vars_used = sorted(var_set(L) | var_set(R))
    if not vars_used:
        return True
    for assignment_tuple in itertools.product(range(n), repeat=len(vars_used)):
        assignment = dict(zip(vars_used, assignment_tuple))
        if evaluate(L, assignment, table) != evaluate(R, assignment, table):
            return False
    return True


def equation_fails_witness(L, R, table: list[list[int]]) -> Optional[dict]:
    """Return a failing assignment if Eq fails somewhere; else None."""
    n = len(table)
    vars_used = sorted(var_set(L) | var_set(R))
    if not vars_used:
        return None
    for assignment_tuple in itertools.product(range(n), repeat=len(vars_used)):
        assignment = dict(zip(vars_used, assignment_tuple))
        if evaluate(L, assignment, table) != evaluate(R, assignment, table):
            return assignment
    return None


# ============================================================
# Lean certificate templates
# ============================================================

def emit_x1_certificate() -> str:
    """B.L = B.R syntactically — reflexivity proof."""
    return """import JudgeProblem

def submission : Goal := by
  intros
  rfl
"""


def emit_brute_force_false(size: int, table: list[list[int]]) -> str:
    """FALSE certificate: a finite magma satisfying Eq1 and refuting Eq2."""
    table_json = json.dumps(table).replace('"', '\\"')
    return f"""import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin {size}) := {{ op := finOpTable "{table_json}" }}
  refine ⟨Fin {size}, m, ?_⟩
  decideFin!
"""


def emit_left_projection_false() -> str:
    return emit_brute_force_false(2, [[0, 0], [1, 1]])


def emit_right_projection_false() -> str:
    return emit_brute_force_false(2, [[0, 1], [0, 1]])


def emit_xor_false() -> str:
    return emit_brute_force_false(2, [[0, 1], [1, 0]])


def emit_llm_proof_certificate(proof_body: str) -> str:
    """Wrap an LLM-provided proof body in the Lean submission scaffolding.

    The body is what comes after `intro G _ h <vars>;` — i.e. just the tactics
    that introduce the variables of Eq2 and prove EquationRHS using h.
    Matches the SAIR baseline pattern (EQT02-S00001).
    """
    # Strip leading "by" if LLM included it
    body = proof_body.strip()
    if body.startswith("by\n"):
        body = body[3:]
    elif body.startswith("by "):
        body = body[3:]

    # Indent each line by 2 spaces
    indented_lines = []
    for line in body.split("\n"):
        if line.strip():
            indented_lines.append("  " + line)
        else:
            indented_lines.append("")
    indented = "\n".join(indented_lines)

    return f"""import JudgeProblem

def submission : Goal := by
  intro G _ h
{indented}
"""


# ============================================================
# Affine probe library (M1-M9 from Stage 1)
# ============================================================

# (p, q, c, m): u*v = p*u + q*v + c (mod m)
AFFINE_LIBRARY = [
    ("M1", 0, 1, 1, 3),  # v + 1 mod 3
    ("M2", 1, 0, 1, 3),  # u + 1 mod 3
    ("M3", 3, 2, 0, 4),  # 3u + 2v mod 4
    ("M4", 2, 3, 0, 4),  # 2u + 3v mod 4
    ("M5", 3, 3, 0, 5),  # 3u + 3v mod 5
    ("M6", 0, 1, 1, 4),  # v + 1 mod 4
    ("M7", 1, 0, 1, 4),  # u + 1 mod 4
    ("M8", 2, 2, 0, 3),  # 2u + 2v mod 3
    ("M9", 2, 2, 0, 4),  # 2u + 2v mod 4
]


def affine_table(p: int, q: int, c: int, m: int) -> list[list[int]]:
    return [[(p * i + q * j + c) % m for j in range(m)] for i in range(m)]


def try_affine_library(L1, R1, L2, R2) -> Optional[tuple[str, list[list[int]]]]:
    """
    Find an affine magma satisfying Eq1 but failing Eq2.
    Returns (magma_name, table) or None.
    """
    for name, p, q, c, m in AFFINE_LIBRARY:
        table = affine_table(p, q, c, m)
        if equation_holds(L1, R1, table) and equation_fails_witness(L2, R2, table):
            return (name, table)
    return None


# ============================================================
# Brute-force counterexample search
# ============================================================

def brute_force_search(L1, R1, L2, R2, max_size: int = 5, time_budget: float = 60.0):
    """
    Search for a finite magma counterexample by enumerating Cayley tables.
    Returns (size, table) or None.

    For size 2: 16 tables, trivial.
    For size 3: 19,683 tables. Tractable.
    For size 4-5: structured families only (affine, projection, constant, successor).
    """
    import time
    start = time.time()

    # Size 2: full enumeration
    for table in _enumerate_tables(2):
        if time.time() - start > time_budget:
            return None
        if equation_holds(L1, R1, table) and equation_fails_witness(L2, R2, table):
            return (2, table)

    if max_size < 3:
        return None

    # Size 3: full enumeration
    for table in _enumerate_tables(3):
        if time.time() - start > time_budget:
            return None
        if equation_holds(L1, R1, table) and equation_fails_witness(L2, R2, table):
            return (3, table)

    if max_size < 4:
        return None

    # Size 4-5: structured families
    for size in (4, 5):
        if size > max_size:
            break
        for table in _structured_families(size):
            if time.time() - start > time_budget:
                return None
            if equation_holds(L1, R1, table) and equation_fails_witness(L2, R2, table):
                return (size, table)

    return None


def _enumerate_tables(n: int):
    """Yield all n×n tables of values in [0, n)."""
    cells = n * n
    for values in itertools.product(range(n), repeat=cells):
        table = [list(values[i * n:(i + 1) * n]) for i in range(n)]
        yield table


def _structured_families(n: int):
    """Yield structured n×n tables: affine, constant, projection, successor."""
    # Affine: x*y = (p*x + q*y + c) mod n
    for p in range(n):
        for q in range(n):
            for c in range(n):
                yield [[(p * i + q * j + c) % n for j in range(n)] for i in range(n)]
    # Constants
    for c in range(n):
        yield [[c for _ in range(n)] for _ in range(n)]
    # Projections
    yield [[i for _ in range(n)] for i in range(n)]
    yield [[j for j in range(n)] for _ in range(n)]
    # Successor families
    yield [[(i + 1) % n for _ in range(n)] for i in range(n)]
    yield [[(j + 1) % n for j in range(n)] for _ in range(n)]


def _structured_size_4_families():
    """Backwards-compatible alias."""
    yield from _structured_families(4)


# ============================================================
# Lightweight rule classifier (subset of Stage 1's v20)
# ============================================================

class RuleResult:
    def __init__(self, verdict: Optional[bool], rule: str, certificate: Optional[str] = None):
        self.verdict = verdict
        self.rule = rule
        self.certificate = certificate  # Lean code if directly emitable


def try_x1(L1, R1, L2, R2) -> Optional[RuleResult]:
    """X1: B.L = B.R syntactically → TRUE via reflexivity."""
    if tree_eq(L2, R2):
        return RuleResult(True, "X1", emit_x1_certificate())
    return None


def emit_singleton_certificate(eq1_str: str, eq2_str: str) -> Optional[str]:
    """
    Build a TRUE certificate for X3 (collapse-to-singleton).

    Pattern from SAIR baseline EQT02-S00001: when Eq1 has form
    `x = <term not containing x>`, |M| must be 1, so any Eq2 holds via
    the universal-equality lemma.

    Returns Lean source, or None if the pattern doesn't apply cleanly.
    """
    import re
    # Split Eq1 to get LHS variable and RHS variables
    if "=" not in eq1_str:
        return None
    lhs1, rhs1 = eq1_str.split("=", 1)
    lhs1 = lhs1.strip()
    if lhs1 != "x":
        return None  # only handle the canonical "x = ..." case for now
    rhs_vars_in_eq1 = re.findall(r'\b([a-z])\b', rhs1)
    if "x" in rhs_vars_in_eq1:
        return None  # x appears on RHS — not a collapse case
    eq1_vars = []
    seen = set()
    for v in re.findall(r'\b([a-z])\b', eq1_str):
        if v not in seen:
            seen.add(v)
            eq1_vars.append(v)
    eq2_vars = []
    seen2 = set()
    for v in re.findall(r'\b([a-z])\b', eq2_str):
        if v not in seen2:
            seen2.add(v)
            eq2_vars.append(v)
    if "=" not in eq2_str:
        return None
    eq2_lhs, eq2_rhs = eq2_str.split("=", 1)
    filler = " ".join(["a"] * (len(eq1_vars) - 1)) if len(eq1_vars) > 1 else ""

    proof_body = (
        f"  intro {' '.join(eq2_vars)}\n"
        f"  have singleton : ∀ (a b : G), a = b := "
        f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"  exact singleton ({eq2_lhs.strip()}) ({eq2_rhs.strip()})"
    )
    return f"""import JudgeProblem

def submission : Goal := by
  intro G _ h
{proof_body}
"""


def try_x3(L1, R1, L2, R2, eq1_str: str = "", eq2_str: str = "") -> Optional[RuleResult]:
    """X3: A has lone variable absent from other side → forces |M|=1."""
    if is_bare(L1) and not is_bare(R1):
        if L1.name not in var_set(R1):
            cert = emit_singleton_certificate(eq1_str, eq2_str) if eq1_str else None
            return RuleResult(True, "X3", cert)
    if is_bare(R1) and not is_bare(L1):
        if R1.name not in var_set(L1):
            # Could swap-and-emit, but for first version leave to LLM
            return RuleResult(True, "X3", None)
    return None


def try_separators(L1, R1, L2, R2) -> Optional[RuleResult]:
    """S1, S2, S4 separators → projection / XOR magma refutes."""
    # S1: LP(A) AND NOT LP(B)
    LP_A = leftmost_leaf(L1).name == leftmost_leaf(R1).name
    LP_B = leftmost_leaf(L2).name == leftmost_leaf(R2).name
    if LP_A and not LP_B:
        return RuleResult(False, "S1", emit_left_projection_false())

    # S2: RP(A) AND NOT RP(B)
    RP_A = rightmost_leaf(L1).name == rightmost_leaf(R1).name
    RP_B = rightmost_leaf(L2).name == rightmost_leaf(R2).name
    if RP_A and not RP_B:
        return RuleResult(False, "S2", emit_right_projection_false())

    # S4: XOR(A) AND NOT XOR(B) — every var has same parity both sides
    cA1, cA2 = var_counts(L1), var_counts(R1)
    cB1, cB2 = var_counts(L2), var_counts(R2)

    def xor_holds(c1, c2):
        all_v = set(c1) | set(c2)
        return all((c1.get(v, 0) % 2) == (c2.get(v, 0) % 2) for v in all_v)

    XOR_A = xor_holds(cA1, cA2)
    XOR_B = xor_holds(cB1, cB2)
    if XOR_A and not XOR_B:
        return RuleResult(False, "S4", emit_xor_false())

    return None


def try_affine_separator(L1, R1, L2, R2) -> Optional[RuleResult]:
    """Affine library M1-M9: a magma admits Eq1 and refutes Eq2."""
    result = try_affine_library(L1, R1, L2, R2)
    if result:
        name, table = result
        size = len(table)
        return RuleResult(False, name, emit_brute_force_false(size, table))
    return None


def classify(L1, R1, L2, R2, eq1_str: str = "", eq2_str: str = "") -> Optional[RuleResult]:
    """Run rule engine in priority order. Returns first firing rule."""
    # X1 first (cheap, exact)
    result = try_x1(L1, R1, L2, R2)
    if result is not None:
        return result
    # Separators (FALSE direct)
    result = try_separators(L1, R1, L2, R2)
    if result is not None:
        return result
    # Affine library (FALSE via verified probe)
    result = try_affine_separator(L1, R1, L2, R2)
    if result is not None:
        return result
    # X3 collapse (TRUE with constructed Lean proof if singleton case)
    result = try_x3(L1, R1, L2, R2, eq1_str, eq2_str)
    if result is not None:
        return result
    return None


# ============================================================
# Communication protocol
# ============================================================

def send(obj):
    """Write a JSON message to stdout (one line)."""
    sys.stdout.write(json.dumps(obj) + "\n")
    sys.stdout.flush()


def recv():
    """Read a JSON message from stdin."""
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line)


def call_judge(verdict: bool, code: str) -> dict:
    """Send a judge request, return the response."""
    send({
        "call": "judge",
        "verdict": "true" if verdict else "false",
        "code": code,
    })
    return recv()


def call_llm(context: dict) -> dict:
    """Send an LLM request, return the response."""
    send({"call": "llm", "context": context})
    return recv()


# ============================================================
# Analysis context for LLM
# ============================================================

def build_analysis(L1, R1, L2, R2, attempted_rules: list[str], witness_search_log: str) -> str:
    """Build a structured analysis string for the LLM context."""
    parts = []
    parts.append(f"Eq1: {L1} = {R1}")
    parts.append(f"Eq2: {L2} = {R2}")

    # Variable structure
    vA = sorted(var_set(L1) | var_set(R1))
    vB = sorted(var_set(L2) | var_set(R2))
    parts.append(f"Eq1 vars: {vA} ({len(vA)} distinct)")
    parts.append(f"Eq2 vars: {vB} ({len(vB)} distinct)")

    # Bare-side info
    if is_bare(L1):
        parts.append(f"Eq1 LHS is bare variable {L1.name}")
    if is_bare(L2):
        parts.append(f"Eq2 LHS is bare variable {L2.name}")

    # Leftmost/rightmost
    parts.append(f"Eq1 leftmost: L={leftmost_leaf(L1).name} R={leftmost_leaf(R1).name}")
    parts.append(f"Eq1 rightmost: L={rightmost_leaf(L1).name} R={rightmost_leaf(R1).name}")
    parts.append(f"Eq2 leftmost: L={leftmost_leaf(L2).name} R={leftmost_leaf(R2).name}")
    parts.append(f"Eq2 rightmost: L={rightmost_leaf(L2).name} R={rightmost_leaf(R2).name}")

    if attempted_rules:
        parts.append(f"Rules attempted (and failed): {', '.join(attempted_rules)}")

    if witness_search_log:
        parts.append(f"Witness search: {witness_search_log}")

    return "\n".join(parts)


# ============================================================
# LLM response handling
# ============================================================

def parse_llm_response(response_text: str) -> Optional[dict]:
    """Extract verdict and proof/table from LLM response."""
    # LLM is instructed to return ONLY JSON. Strip whitespace + try parse.
    text = response_text.strip()

    # Strip markdown fences if model added them despite instructions
    if text.startswith("```"):
        lines = text.split("\n")
        if lines[0].startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        text = "\n".join(lines)

    try:
        return json.loads(text)
    except json.JSONDecodeError:
        # Try to extract JSON object from anywhere in text
        import re
        match = re.search(r'\{[^{}]*"verdict"[^{}]*\}', text, re.DOTALL)
        if match:
            try:
                return json.loads(match.group(0))
            except Exception:
                pass
        return None


def llm_response_to_certificate(response: dict, L1=None, R1=None, L2=None, R2=None) -> Optional[tuple[bool, str]]:
    """Convert LLM response to (verdict, lean_code) or None if malformed.

    For FALSE certificates, if L1/R1/L2/R2 trees are provided, locally verify
    that the proposed magma actually satisfies Eq1 and refutes Eq2 BEFORE
    we send it to the judge. This saves wasted judge calls on garbage tables.
    """
    if not isinstance(response, dict) or "verdict" not in response:
        return None

    verdict_str = str(response["verdict"]).lower()
    if verdict_str == "true":
        proof = response.get("proof", "")
        if not proof:
            return None
        return (True, emit_llm_proof_certificate(proof))

    elif verdict_str == "false":
        size = response.get("size")
        table = response.get("table")
        if size is None and isinstance(table, list):
            size = len(table)
        if not isinstance(size, int) or not isinstance(table, list):
            return None
        if len(table) != size or any(len(row) != size for row in table):
            return None
        if not all(isinstance(x, int) and 0 <= x < size for row in table for x in row):
            return None

        # Local verification — only emit certificate if magma is a valid counterexample
        if L1 is not None:
            if not equation_holds(L1, R1, table):
                return None  # Eq1 doesn't hold — invalid candidate
            if not equation_fails_witness(L2, R2, table):
                return None  # Eq2 also holds — not a counterexample

        return (False, emit_brute_force_false(size, table))

    return None


# ============================================================
# Main solver loop
# ============================================================

def solve_problem(eq1_str: str, eq2_str: str, send_judge_fn) -> Optional[bool]:
    """
    Run the full solver pipeline on one problem.

    Args:
        eq1_str, eq2_str: equation strings.
        send_judge_fn: callable(verdict: bool, code: str) -> dict with "status".
                       In Solo mode this calls the proxy via stdin/stdout.
                       In Marathon mode it can be a no-op that just emits to JSONL.

    Returns:
        True if accepted, False if all strategies exhausted, None if not attempted.
    """
    try:
        L1, R1 = parse_equation(eq1_str)
        L2, R2 = parse_equation(eq2_str)
    except Exception:
        return None

    # Layer 1 — rule engine
    rule_result = classify(L1, R1, L2, R2, eq1_str, eq2_str)
    if rule_result and rule_result.certificate:
        resp = send_judge_fn(rule_result.verdict, rule_result.certificate)
        if resp.get("status") == "accepted":
            return True

    # Layer 1.5 — brute-force search Fin 2-3 (matches SAIR baseline reach)
    witness = brute_force_search(L1, R1, L2, R2, max_size=3, time_budget=30.0)
    if witness:
        size, table = witness
        cert = emit_brute_force_false(size, table)
        resp = send_judge_fn(False, cert)
        if resp.get("status") == "accepted":
            return True

    return False


def run_solo():
    """Solo track: stdin/stdout JSON protocol, one process per problem."""
    startup = recv()
    problem = startup["problem"]
    eq1_str = problem["equation1"]
    eq2_str = problem["equation2"]

    L1, R1 = parse_equation(eq1_str)
    L2, R2 = parse_equation(eq2_str)
    attempted = []

    # Layer 1
    rule_result = classify(L1, R1, L2, R2, eq1_str, eq2_str)
    if rule_result and rule_result.certificate:
        attempted.append(rule_result.rule)
        resp = call_judge(rule_result.verdict, rule_result.certificate)
        if resp.get("status") == "accepted":
            return

    # Layer 1.5
    witness = brute_force_search(L1, R1, L2, R2, max_size=5, time_budget=120.0)
    if witness:
        size, table = witness
        attempted.append(f"brute_force_size_{size}")
        cert = emit_brute_force_false(size, table)
        resp = call_judge(False, cert)
        if resp.get("status") == "accepted":
            return

    # Layer 3 — LLM iterative repair
    if witness:
        witness_log = f"size {witness[0]} witness was rejected by judge — try a different magma"
    else:
        witness_log = (
            "BRUTE-FORCE SEARCH RESULT: exhaustive Fin 2-3 + structured Fin 4-5 "
            "(affine, projection, constant, successor) found no counterexample. "
            "This DOES NOT MEAN Eq1 implies Eq2 — many FALSE implications require "
            "non-affine magmas at sizes 4-7+. Consider both verdicts equally likely."
        )

    for round_num in range(8):
        analysis = build_analysis(L1, R1, L2, R2, attempted, witness_log)
        llm_resp = call_llm({"analysis": analysis})
        if "error" in llm_resp:
            break

        response_text = llm_resp.get("response", "")
        parsed = parse_llm_response(response_text)
        if not parsed:
            attempted.append(f"llm_round_{round_num}_unparseable")
            continue

        cert_pair = llm_response_to_certificate(parsed, L1, R1, L2, R2)
        if not cert_pair:
            attempted.append(f"llm_round_{round_num}_malformed_or_unverified")
            continue

        verdict, code = cert_pair
        attempted.append(f"llm_round_{round_num}")
        judge_resp = call_judge(verdict, code)
        if judge_resp.get("status") == "accepted":
            return


def run_marathon():
    """Marathon track: read manifest JSONL, append answer JSONL."""
    import os
    import time

    manifest_path = os.environ["JUDGE_MARATHON_MANIFEST"]
    output_path = os.environ["JUDGE_MARATHON_OUTPUT"]
    budget_seconds = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    deadline = time.monotonic() + budget_seconds

    # Load manifest
    problems = []
    with open(manifest_path, encoding="utf-8") as fh:
        for raw in fh:
            raw = raw.strip()
            if not raw:
                continue
            try:
                problems.append(json.loads(raw))
            except json.JSONDecodeError:
                continue

    if not problems:
        return

    tail_margin = 5.0
    per_problem_cap = max(2.0, (budget_seconds - tail_margin) / len(problems))

    def append_answer(entry):
        line = json.dumps(entry, ensure_ascii=False) + "\n"
        with open(output_path, "a", encoding="utf-8") as fh:
            fh.write(line)
            fh.flush()
            try:
                os.fsync(fh.fileno())
            except OSError:
                pass

    for prob in problems:
        if time.monotonic() + tail_margin >= deadline:
            break

        eq1_str = prob["equation1"]
        eq2_str = prob["equation2"]

        try:
            L1, R1 = parse_equation(eq1_str)
            L2, R2 = parse_equation(eq2_str)
        except Exception:
            continue

        # Layer 1 — rule engine, deterministic
        rule_result = classify(L1, R1, L2, R2, eq1_str, eq2_str)
        if rule_result and rule_result.certificate:
            append_answer({
                "id": prob["id"],
                "verdict": "true" if rule_result.verdict else "false",
                "code": rule_result.certificate,
            })
            continue

        # Layer 1.5 — brute force within per-problem cap
        try:
            witness = brute_force_search(
                L1, R1, L2, R2,
                max_size=3,
                time_budget=per_problem_cap,
            )
        except Exception:
            continue

        if witness:
            size, table = witness
            append_answer({
                "id": prob["id"],
                "verdict": "false",
                "code": emit_brute_force_false(size, table),
            })


def main():
    import os
    try:
        if "JUDGE_MARATHON_MANIFEST" in os.environ:
            run_marathon()
        else:
            run_solo()
    except Exception as e:
        sys.stderr.write(f"solver exception: {type(e).__name__}: {e}\n")
        raise


if __name__ == "__main__":
    main()
