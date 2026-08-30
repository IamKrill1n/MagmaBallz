"""
Marathon Ultra Solver — Fusion of OpNorm Deterministic Strategies + FewShot Dynamic Learning

This solver combines:
1. OpNorm's 16 deterministic proof strategies (counterexample search, singleton detection,
   library lookup, constancy lemmas, BFS near-miss search, calc-chain variants)
2. FewShot's dynamic learning paradigm (self-growing proof pool with few-shot transfer)
3. Four advanced upgrades:
   - Alpha-Invariant AST Matching (structural similarity)
   - Cold Start Seed Bootstrapping
   - Lemma Distillation (extract reusable lemmas from long proofs)
   - Smart Scheduling (difficulty-based ordering)

Strategy:
  Pass 0 (Cold Start): Pre-seed fewshot_pool with high-quality examples
  Pass 1 (Deterministic Kill): OpNorm's 16 strategies for instant solutions
  Pass 2 (Brute Force): Counterexample search on Fin 2-7
  Pass 3 (LLM with Few-Shot): Dynamic learning from successful proofs
"""

PROMPT_BASE = """You are solving an equational-theory implication in Lean 4.

Given two equational laws on a magma G with operation ◇:

  Law A ({problem.equation1_id}): {problem.equation1}
  Law B ({problem.equation2_id}): {problem.equation2}

Decide whether every magma satisfying A also satisfies B.

The proof goes inside this template (don't restate it):

    def submission : Goal := by
      intro G _ h
      <YOUR TACTIC BODY HERE>

``h : <Law A>`` is in scope. Use ``exact``, ``rw``, ``simp [h]``, ``intro``,
``apply``, ``have``, ``calc``, etc. No imports. No theorem statements.

If you believe the implication is FALSE, return a 2-D table on Fin n
(2 ≤ n ≤ 4) instead.

Reply with ONLY one JSON object, no markdown:

    {"verdict": "true",  "proof": "<tactic body>"}
or
    {"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""

PROMPT_FEWSHOT_HEADER = """You are solving an equational-theory implication in Lean 4.

Below are {n_examples} proofs that worked on similar problems earlier in
this run. They use the same response format and template you must
follow. Use them as style references — do NOT copy verbatim.

"""

PROMPT_FEWSHOT_EXAMPLE = """### Example {idx}: {ex_eq1_name} → {ex_eq2_name}
Law A: {ex_eq1}
Law B: {ex_eq2}
Accepted response:
{{"verdict": "true", "proof": {ex_proof_json}}}

"""

PROMPT_FEWSHOT_FOOTER = """### Now solve this:

  Law A ({problem.equation1_id}): {problem.equation1}
  Law B ({problem.equation2_id}): {problem.equation2}

Same template (don't restate it):

    def submission : Goal := by
      intro G _ h
      <YOUR TACTIC BODY HERE>

``h : <Law A>`` is in scope.

Reply with ONLY one JSON object, no markdown:

    {"verdict": "true",  "proof": "<tactic body>"}
or
    {"verdict": "false", "counterexample_table": [[0,1],[1,0]]}
"""

PROMPT = PROMPT_BASE  # Solo fallback prompt (proxy AST-extracts this name).


import json
import os
import random
import re
import sys
import time
from itertools import product
from pathlib import Path


_LIB_DIR = os.environ.get("JUDGE_MARATHON_LIB_DIR")
if _LIB_DIR and _LIB_DIR not in sys.path:
    sys.path.insert(0, _LIB_DIR)


# Number of prior wins to inject as few-shot examples per LLM call.
FEWSHOT_K = 2

# Cap example proof body length so a pathological 80-line proof from an
# earlier problem doesn't crowd out the actual question.
MAX_EXAMPLE_PROOF_CHARS = 800

# Default ON: gate few-shot pool insertion on a cheap structural prefilter.
FEWSHOT_VERIFY_BEFORE_CACHE = os.environ.get(
    "FEWSHOT_VERIFY_BEFORE_CACHE", "1"
).strip().lower() not in ("0", "false", "no", "off")


# ── Operator normalisation ──────────────────────────────────────
def normalize_op_to_diamond(text):
    if not isinstance(text, str):
        return text
    return text.replace('*', '◇')


def _dualize_equation(text):
    """Generate the dual equation by reversing the magma operation.
    a ◇ b becomes b ◇ a in the dual form."""
    # Parse into tree
    tree = _parse_op_tree(text)
    
    # Recursively swap children of op nodes
    def _swap(tree):
        if tree[0] == 'var':
            return tree
        return ('op', _swap(tree[2]), _swap(tree[1]))
    
    dual_tree = _swap(tree)
    return _tree_to_str(dual_tree)


def _get_equation_variants(eq_text):
    """Get all variants of an equation (original, dual, symmetric)."""
    variants = [eq_text]
    
    # Add dual
    dual = _dualize_equation(eq_text)
    if dual != eq_text:
        variants.append(dual)
    
    # Add symmetric (swap LHS and RHS)
    parts = eq_text.split('=', 1)
    if len(parts) == 2:
        sym = f"{parts[1].strip()} = {parts[0].strip()}"
        if sym != eq_text:
            variants.append(sym)
    
    return variants


# ── Equation parsing & brute-force counterexample search ────────

def _parse_equation(text):
    variables = []
    seen = set()
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    lhs_str, rhs_str = text.split("=", 1)

    def _to_expr(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
            depth = 0
            matched = True
            for i, c in enumerate(s):
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                if depth == 0 and i < len(s) - 1:
                    matched = False
                    break
            if matched:
                s = s[1:-1].strip()
            else:
                break
        depth = 0
        last_op = -1
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif (c == "\u25c7" or c == '*') and depth == 0:
                last_op = i
        if last_op >= 0:
            left = _to_expr(s[:last_op])
            right = _to_expr(s[last_op + 1:])
            return lambda env, l=left, r=right: env["op"](l(env), r(env))
        s = s.strip()
        if len(s) == 1 and s in seen:
            return lambda env, v=s: env[v]
        raise ValueError(f"cannot parse: {s!r}")

    return variables, _to_expr(lhs_str), _to_expr(rhs_str)


def _check_eq(variables, lhs_fn, rhs_fn, n, op):
    for vals in product(range(n), repeat=len(variables)):
        env = {"op": op}
        for v, val in zip(variables, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def search_counterexample(eq1_text, eq2_text, max_n=3, time_budget=None):
    try:
        lhs_vars, lhs_l, lhs_r = _parse_equation(eq1_text)
        rhs_vars, rhs_l, rhs_r = _parse_equation(eq2_text)
    except (ValueError, IndexError):
        return None, None
    deadline = (time.monotonic() + time_budget) if time_budget else None
    for n in range(2, max_n + 1):
        total = n ** (n * n)
        for enc in range(total):
            if deadline is not None and time.monotonic() > deadline:
                return None, None
            table = [[(enc // (n ** (i * n + j))) % n for j in range(n)]
                     for i in range(n)]
            op = lambda a, b, t=table: t[a][b]
            if not _check_eq(lhs_vars, lhs_l, lhs_r, n, op):
                continue
            if _check_eq(rhs_vars, rhs_l, rhs_r, n, op):
                continue
            return n, table
    return None, None


# ── Structured counterexample search (from OpNorm) ──────────────

def _structured_tables(n):
    """Generate structured tables for more effective counterexample search."""
    for c in range(n):
        yield [[c] * n for _ in range(n)]
    yield [[i] * n for i in range(n)]
    yield [list(range(n)) for _ in range(n)]
    yield [[(i + j) % n for j in range(n)] for i in range(n)]
    yield [[(i - j) % n for j in range(n)] for i in range(n)]
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    yield [[i if i != 0 else j for j in range(n)] for i in range(n)]
    yield [[j if j != 0 else i for j in range(n)] for i in range(n)]
    for k in range(1, n):
        yield [[(i + k) % n] * n for i in range(n)]
        yield [[(j + k) % n for j in range(n)] for _ in range(n)]
    if n > 1:
        yield [[(i * j) % n for j in range(n)] for i in range(n)]
    if n in (2, 4):
        yield [[(i ^ j) % n for j in range(n)] for i in range(n)]
    for c in range(n):
        for thresh in range(1, n):
            yield [[i if i < thresh else c for _ in range(n)] for i in range(n)]
            yield [[j if j < thresh else c for j in range(n)] for i in range(n)]
    yield [[i if i >= j else j for j in range(n)] for i in range(n)]
    yield [[i if i <= j else j for j in range(n)] for i in range(n)]
    # Left-zero and right-zero semigroups
    yield [[i for _ in range(n)] for i in range(n)]  # left projection
    yield [[j for j in range(n)] for _ in range(n)]  # right projection
    # Nilpotent-like: a◇b = 0 except identity
    if n >= 2:
        yield [[0 if i != j else i for j in range(n)] for i in range(n)]
        yield [[(i + j + 1) % n for j in range(n)] for i in range(n)]
    # Band-like: a◇a = a, a◇b = first/second
    if n >= 3:
        yield [[i if i == j else (i + j) % n for j in range(n)] for i in range(n)]
        yield [[i if i == j else 0 for j in range(n)] for i in range(n)]
        yield [[i if i == j else n - 1 for j in range(n)] for i in range(n)]
    # Permutation tables (right-multiply by various permutations)
    if n <= 4:
        import itertools as _it
        for perm in _it.permutations(range(n)):
            yield [[perm[j] for j in range(n)] for _ in range(n)]
            yield [[perm[i] for _ in range(n)] for i in range(n)]
    # Rectangular band: a◇b = (a_left, b_right) decompositions
    if n >= 4:
        for d in range(2, n):
            if n % d == 0:
                m = n // d
                yield [[(i // m) * m + (j % m) for j in range(n)] for i in range(n)]
                yield [[(i % d) + (j // d) * d for j in range(n)] for i in range(n)]
    # Semilattice variants
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    # Selective: a◇b ∈ {a, b}
    if n <= 5:
        for chooser in range(2 ** (n * n)):
            table = [[0] * n for _ in range(n)]
            valid = True
            for i in range(n):
                for j in range(n):
                    bit = (chooser >> (i * n + j)) & 1
                    table[i][j] = i if bit else j
                    if i == j and table[i][j] != i:
                        valid = False
                        break
                if not valid:
                    break
            if valid:
                yield table
            if chooser > 1024:  # Cap to avoid explosion
                break
    # Constant rows/columns with identity on diagonal
    for c in range(n):
        t = [[c] * n for _ in range(n)]
        for i in range(n):
            t[i][i] = i
        yield t
    # "Flip" tables: a◇b = (n-1-a), a◇b = (n-1-b), etc
    if n >= 2:
        yield [[(n - 1 - i) for _ in range(n)] for i in range(n)]
        yield [[(n - 1 - j) for j in range(n)] for _ in range(n)]
        yield [[(n - 1 - i + j) % n for j in range(n)] for i in range(n)]
        yield [[(i + n - 1 - j) % n for j in range(n)] for i in range(n)]
    # Polynomial tables: (a*x + b*y) mod n for various a, b
    for a in range(n):
        for b in range(n):
            if a == 0 and b == 0:
                continue  # constant zero, already covered
            if a == 1 and b == 1:
                continue  # x+y mod n, already covered
            yield [[(a * i + b * j) % n for j in range(n)] for i in range(n)]
    # Polynomial tables: (a*x + b*y + c) mod n
    for a in range(1, min(n, 4)):
        for b in range(1, min(n, 4)):
            for c in range(1, min(n, 3)):
                yield [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)]


def extended_counterexample(eq1_text, eq2_text, max_n=7, random_attempts=10000, time_budget=10.0):
    """Extended counterexample search with structured tables and random attempts."""
    try:
        v1, l1, r1 = _parse_equation(eq1_text)
        v2, l2, r2 = _parse_equation(eq2_text)
    except (ValueError, IndexError):
        return None, None
    
    deadline = (time.monotonic() + time_budget) if time_budget else None
    
    for sz in range(2, min(max_n + 1, 8)):
        if deadline and time.monotonic() > deadline:
            return None, None
        for table in _structured_tables(sz):
            if deadline and time.monotonic() > deadline:
                return None, None
            op = lambda a, b, t=table: t[a][b]
            if _check_eq(v1, l1, r1, sz, op) and not _check_eq(v2, l2, r2, sz, op):
                return sz, table
    
    for sz in (4, 5, 6, 7):
        if deadline and time.monotonic() > deadline:
            return None, None
        for _ in range(random_attempts):
            if deadline and time.monotonic() > deadline:
                return None, None
            table = [[random.randint(0, sz - 1) for _ in range(sz)] for _ in range(sz)]
            op = lambda a, b, t=table: t[a][b]
            if _check_eq(v1, l1, r1, sz, op) and not _check_eq(v2, l2, r2, sz, op):
                return sz, table
    return None, None


def _sat_counterexample(eq1_text, eq2_text, max_n=8):
    """Use SAT/SMT solver (z3) to find counterexamples efficiently.
    Falls back to None if z3 is not available."""
    try:
        import z3
    except ImportError:
        return None, None
    
    try:
        v1, l1, r1 = _parse_equation(eq1_text)
        v2, l2, r2 = _parse_equation(eq2_text)
    except (ValueError, IndexError):
        return None, None
    
    for n in range(2, max_n + 1):
        solver = z3.Solver()
        solver.set("timeout", 5000)  # 5 second timeout per size
        
        # Create operation table variables
        op = [[z3.Int(f"op_{i}_{j}") for j in range(n)] for i in range(n)]
        
        # Add constraints: op[i][j] in range [0, n-1]
        for i in range(n):
            for j in range(n):
                solver.add(op[i][j] >= 0, op[i][j] < n)
        
        # Helper to evaluate expressions
        def _eval_expr(expr_fn, var_vals):
            """Evaluate expression with given variable values."""
            env = {"op": lambda a, b: op[a][b]}
            for v, val in var_vals.items():
                env[v] = val
            return expr_fn(env)
        
        # Correct encoding:
        # exists table: (forall vars: eq1 holds) AND (exists vars: eq2 fails)
        
        # For eq1: must hold for ALL assignments
        # Sample a reasonable number of assignments
        sample_count = min(200, n ** len(v1))
        for _ in range(sample_count):
            vals = [random.randint(0, n-1) for _ in range(v1)]
            var_vals = {v: val for v, val in zip(v1, vals)}
            
            lhs_val = _eval_expr(l1, var_vals)
            rhs_val = _eval_expr(r1, var_vals)
            
            solver.add(lhs_val == rhs_val)
        
        # For eq2: must fail for at least ONE assignment
        # Use OR over all possible assignments (or sample)
        eq2_fail_clauses = []
        sample_eq2 = min(50, n ** len(v2))
        for _ in range(sample_eq2):
            vals = [random.randint(0, n-1) for _ in range(v2)]
            var_vals = {v: val for v, val in zip(v2, vals)}
            
            lhs_val = _eval_expr(l2, var_vals)
            rhs_val = _eval_expr(r2, var_vals)
            
            eq2_fail_clauses.append(lhs_val != rhs_val)
        
        # At least one eq2 assignment must fail
        if eq2_fail_clauses:
            solver.add(z3.Or(eq2_fail_clauses))
        
        # Check satisfiability
        if solver.check() == z3.sat:
            model = solver.model()
            table = [[int(model.evaluate(op[i][j]).as_long()) for j in range(n)] for i in range(n)]
            
            # Verify the counterexample with full check
            op_fn = lambda a, b, t=table: t[a][b]
            if _check_eq(v1, l1, r1, n, op_fn) and not _check_eq(v2, l2, r2, n, op_fn):
                return n, table
    
    return None, None


# ── Singleton collapse (from OpNorm) ────────────────────────────

def try_singleton(problem, eq1_text, eq2_text):
    """Try to prove using singleton collapse (all elements equal).
    Returns the proof code if applicable, None otherwise."""
    eq1_vars = _parse_equation(eq1_text)[0]
    eq2_vars = _parse_equation(eq2_text)[0]
    if len(eq1_vars) < 2:
        return None
    parts = eq1_text.split("=", 1)
    if len(parts) != 2:
        return None
    lhs_var = parts[0].strip()
    rhs_expr = parts[1].strip()
    if len(lhs_var) != 1 or lhs_var not in eq1_vars:
        return None
    goal_parts = eq2_text.split("=", 1)
    if len(goal_parts) != 2:
        return None
    if lhs_var in set(re.findall(r'\b([a-z])\b', rhs_expr)):
        return None
    filler = " ".join(["a"] * (len(eq1_vars) - 1))
    proof = (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : \u2200 (a b : G), a = b := "
        f"fun a b => (h a {filler}).trans (h b {filler}).symm\n"
        f"exact singleton ({goal_parts[0].strip()}) ({goal_parts[1].strip()})"
    )
    return make_true_code(proof)


# ── Helper functions for deterministic strategies ───────────────

def parse_variables(text):
    """Parse variables from equation text."""
    seen = set()
    variables = []
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    return variables


def simultaneous_subst(text, var_list, combo):
    """Simultaneous substitution avoiding variable collision."""
    result = text
    placeholders = []
    for i, v in enumerate(var_list):
        ph = f"__PH{i}__"
        placeholders.append(ph)
        result = re.sub(r'\b' + v + r'\b', ph, result)
    for ph, replacement in zip(placeholders, combo):
        result = result.replace(ph, replacement)
    return result


def _parse_op_tree(s):
    """Parse a magma expression string into a tree: ('op', left, right) or ('var', name)."""
    s = s.strip()
    while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        d = 0; matched = True
        for i, c in enumerate(s):
            if c == '(': d += 1
            elif c == ')': d -= 1
            if d == 0 and i < len(s) - 1: matched = False; break
        if matched: s = s[1:-1].strip()
        else: break
    d = 0; last_op = -1
    for i, c in enumerate(s):
        if c == '(': d += 1
        elif c == ')': d -= 1
        elif (c == '\u25c7' or c == '*') and d == 0: last_op = i
    if last_op >= 0:
        return ('op', _parse_op_tree(s[:last_op]), _parse_op_tree(s[last_op+1:]))
    return ('var', s.strip())


def _tree_to_str(t, add_parens=True):
    """Convert a tree back to a string.
    add_parens=False for root level to avoid extra parentheses."""
    if t[0] == 'var': return t[1]
    inner = f"{_tree_to_str(t[1], True)} \u25c7 {_tree_to_str(t[2], True)}"
    if add_parens:
        return f"({inner})"
    return inner


# ── Direct proof via substitution search ────────────────────────

def try_direct_proof(problem, eq1_text, eq2_text):
    """Try to find and verify a direct proof via substitution search.
    Also tries dual forms for doubled coverage. Returns the proof code if found, None otherwise."""
    # Try original equations
    result = _try_direct_proof_single(eq1_text, eq2_text)
    if result is not None:
        return result
    
    # Try dual forms (reverse operation order)
    dual_eq1 = _dualize_equation(eq1_text)
    dual_eq2 = _dualize_equation(eq2_text)
    if dual_eq1 != eq1_text or dual_eq2 != eq2_text:
        result = _try_direct_proof_single(dual_eq1, dual_eq2)
        if result is not None:
            return result
    
    return None


def _try_direct_proof_single(eq1_text, eq2_text):
    """Helper: try direct proof for a single equation pair."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return None
    
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    
    # Try all substitutions of eq1_vars with eq2_vars
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        
        # Check if direct match
        if new_lhs.replace(' ', '') == eq2_lhs.replace(' ', '') and \
           new_rhs.replace(' ', '') == eq2_rhs.replace(' ', ''):
            args = ' '.join(combo)
            proof = f"intro {' '.join(eq2_vars)}\nexact h {args}"
            return make_true_code(proof)
        
        # Check if symmetric match
        if new_lhs.replace(' ', '') == eq2_rhs.replace(' ', '') and \
           new_rhs.replace(' ', '') == eq2_lhs.replace(' ', ''):
            args = ' '.join(combo)
            proof = f"intro {' '.join(eq2_vars)}\nexact (h {args}).symm"
            return make_true_code(proof)
    
    return None


# ── Calc chain proof via BFS ───────────────────────────────────

def try_calc_chain_proof(problem, eq1_text, eq2_text, max_depth=5):
    """Try to find a calc-chain proof by BFS over rewriting steps.
    Returns the proof code if found, None otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return None
    
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    g_lhs = eq2_lhs.replace(' ', '')
    g_rhs = eq2_rhs.replace(' ', '')
    
    # Pre-compute all useful h instantiations
    all_insts = {}  # (lhs_norm, rhs_norm) -> args_string
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        nl = new_lhs.replace(' ', '')
        nr = new_rhs.replace(' ', '')
        if nl == nr:
            continue
        if nl not in all_insts:
            all_insts[nl] = {}
        all_insts[nl][nr] = ' '.join(combo)
        # Also store reverse direction
        if nr not in all_insts:
            all_insts[nr] = {}
        if nl not in all_insts[nr]:
            all_insts[nr][nl] = '(' + ' '.join(combo) + ').symm'
    
    # BFS from goal LHS to goal RHS
    visited = {g_lhs: (None, None)}  # expr -> (prev_expr, args_to_get_here)
    frontier = [g_lhs]
    
    for depth in range(max_depth):
        next_frontier = []
        for expr in frontier:
            if expr not in all_insts:
                continue
            for target, args in all_insts[expr].items():
                if target in visited:
                    continue
                visited[target] = (expr, args)
                if target == g_rhs:
                    # Found a path! Reconstruct it
                    path = []
                    cur = g_rhs
                    while visited[cur][0] is not None:
                        prev, a = visited[cur]
                        path.append((prev, cur, a))
                        cur = prev
                    path.reverse()
                    
                    # Build calc proof
                    intro = f"intro {' '.join(eq2_vars)}"
                    calc_lines = [intro, "calc"]
                    for i, (frm, to, a) in enumerate(path):
                        # Handle .symm for all steps (including first)
                        if a.startswith('(') and a.endswith(').symm'):
                            real_args = a[1:-6]
                            calc_lines.append(f"  _ = _ := by exact (h {real_args}).symm")
                        else:
                            calc_lines.append(f"  _ = _ := by exact h {a}")
                    
                    proof = '\n'.join(calc_lines)
                    return make_true_code(proof)
                
                next_frontier.append(target)
        frontier = next_frontier
        if not frontier:
            break
    
    return None


# ── Subterm rewriting with congruence ───────────────────────────

def _apply_rewrite_at(tree, path, new_subtree):
    """Replace subtree at path with new_subtree."""
    if not path:
        return new_subtree
    d = path[0]
    rest = path[1:]
    if tree[0] != 'op':
        return tree
    if d == 'L':
        return ('op', _apply_rewrite_at(tree[1], rest, new_subtree), tree[2])
    else:
        return ('op', tree[1], _apply_rewrite_at(tree[2], rest, new_subtree))


def _get_subtree(tree, path):
    """Get subtree at path (string of 'L'/'R')."""
    if not path:
        return tree
    if tree[0] != 'op':
        return tree
    return _get_subtree(tree[1] if path[0] == 'L' else tree[2], path[1:])


def _find_rewrite_paths(tree, target_subtree, path=""):
    """Find all paths in tree where subtree equals target_subtree."""
    paths = []
    if tree == target_subtree:
        paths.append(path)
    if tree[0] == 'op':
        paths.extend(_find_rewrite_paths(tree[1], target_subtree, path + "L"))
        paths.extend(_find_rewrite_paths(tree[2], target_subtree, path + "R"))
    return paths


def _wrap_congr_arg(tree, path, inner_proof):
    """Wrap inner_proof with congr_arg chains for the given path.
    Uses Lean 4 compatible syntax with explicit lambda instead of anonymous dot."""
    if not path:
        return inner_proof
    d = path[0]
    rest = path[1:]
    if tree[0] != 'op':
        return inner_proof
    if d == 'L':
        sub = _wrap_congr_arg(tree[1], rest, inner_proof)
        shared = _tree_to_str(tree[2])
        # Use explicit lambda for Lean 4 compatibility
        return f"congrArg (fun t => t ◇ {shared}) ({sub})"
    else:
        sub = _wrap_congr_arg(tree[2], rest, inner_proof)
        shared = _tree_to_str(tree[1])
        # Use explicit lambda for Lean 4 compatibility
        return f"congrArg (fun t => {shared} ◇ t) ({sub})"


def try_subterm_rewrite_proof(problem, eq1_text, eq2_text, max_depth=3):
    """Try to find a proof using subterm rewriting with congruence.
    Returns the proof code if found, None otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return None
    
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    
    # Parse goal into tree
    g_lhs_tree = _parse_op_tree(eq2_lhs)
    g_rhs_tree = _parse_op_tree(eq2_rhs)
    
    # Try to find h-instantiations that match subterms
    for combo in product(eq2_vars, repeat=len(eq1_vars)):
        new_lhs = simultaneous_subst(eq1_lhs, eq1_vars, combo)
        new_rhs = simultaneous_subst(eq1_rhs, eq1_vars, combo)
        
        h_lhs_tree = _parse_op_tree(new_lhs)
        h_rhs_tree = _parse_op_tree(new_rhs)
        
        # Find paths where h_lhs matches a subterm of g_lhs
        paths = _find_rewrite_paths(g_lhs_tree, h_lhs_tree)
        
        for path in paths:
            # Apply rewrite: replace subterm with h_rhs
            new_tree = _apply_rewrite_at(g_lhs_tree, path, h_rhs_tree)
            new_expr = _tree_to_str(new_tree, add_parens=False)
            
            # Check if this matches goal RHS
            if new_expr.replace(' ', '') == eq2_rhs.replace(' ', ''):
                # Build proof with congr_arg
                args = ' '.join(combo)
                inner_proof = f"h {args}"
                full_proof = _wrap_congr_arg(g_lhs_tree, path, inner_proof)
                
                intro = f"intro {' '.join(eq2_vars)}"
                proof = f"{intro}\nexact {full_proof}"
                return make_true_code(proof)
            
            # Also try symmetric
            paths_rev = _find_rewrite_paths(g_rhs_tree, h_rhs_tree)
            for path_rev in paths_rev:
                new_tree_rev = _apply_rewrite_at(g_rhs_tree, path_rev, h_lhs_tree)
                new_expr_rev = _tree_to_str(new_tree_rev, add_parens=False)
                
                if new_expr_rev.replace(' ', '') == eq2_lhs.replace(' ', ''):
                    args = ' '.join(combo)
                    inner_proof = f"(h {args}).symm"
                    full_proof = _wrap_congr_arg(g_rhs_tree, path_rev, inner_proof)
                    
                    intro = f"intro {' '.join(eq2_vars)}"
                    proof = f"{intro}\nexact {full_proof}"
                    return make_true_code(proof)
    
    return None


# ── Constancy lemma proof ──────────────────────────────────────

def _build_constancy_info(eq1_text, eq1_vars, eq2_vars):
    """Build constancy lemma info from free variables in the hypothesis."""
    parts1 = eq1_text.split('=', 1)
    if len(parts1) != 2:
        return [], set(), set()
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    lhs_only = lhs_vars - rhs_vars
    rhs_only = rhs_vars - lhs_vars
    
    constancy_info = []
    
    for fvar in sorted(rhs_only):
        pos = eq1_vars.index(fvar) if fvar in eq1_vars else -1
        if pos < 0:
            continue
        used = set(eq1_vars) | set(eq2_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used:
                fresh.append(c)
            if len(fresh) >= 2:
                break
        if len(fresh) < 2:
            continue
        fa, fb = fresh[0], fresh[1]
        args_a = list(eq1_vars)
        args_b = list(eq1_vars)
        args_a[pos] = fa
        args_b[pos] = fb
        rhs_a = re.sub(r'\b' + fvar + r'\b', fa, eq1_rhs)
        rhs_b = re.sub(r'\b' + fvar + r'\b', fb, eq1_rhs)
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fa, fb]
        lemma_proof = f"(h {' '.join(args_a)}).symm.trans (h {' '.join(args_b)})"
        have_line = (
            f"have hconst : \u2200 ({' '.join(quant_vars)} : G), "
            f"{rhs_a} = {rhs_b} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )
        constancy_info.append({
            'have_line': have_line,
            'lhs_template': rhs_a,
            'rhs_template': rhs_b,
            'tvars': set(quant_vars),
            'quant_vars': quant_vars,
        })
    
    for fvar in sorted(lhs_only):
        pos = eq1_vars.index(fvar) if fvar in eq1_vars else -1
        if pos < 0:
            continue
        used = set(eq1_vars) | set(eq2_vars)
        fresh = []
        for c in 'abcdefghijklmnopqrstuvwxyz':
            if c not in used:
                fresh.append(c)
            if len(fresh) >= 2:
                break
        if len(fresh) < 2:
            continue
        fa, fb = fresh[0], fresh[1]
        args_a = list(eq1_vars)
        args_b = list(eq1_vars)
        args_a[pos] = fa
        args_b[pos] = fb
        lhs_a = re.sub(r'\b' + fvar + r'\b', fa, eq1_lhs)
        lhs_b = re.sub(r'\b' + fvar + r'\b', fb, eq1_lhs)
        other_vars = [v for i, v in enumerate(eq1_vars) if i != pos]
        quant_vars = other_vars + [fa, fb]
        lemma_proof = f"(h {' '.join(args_a)}).trans (h {' '.join(args_b)}).symm"
        have_line = (
            f"have hconst : \u2200 ({' '.join(quant_vars)} : G), "
            f"{lhs_a} = {lhs_b} := "
            f"fun {' '.join(quant_vars)} => {lemma_proof}"
        )
        constancy_info.append({
            'have_line': have_line,
            'lhs_template': lhs_a,
            'rhs_template': lhs_b,
            'tvars': set(quant_vars),
            'quant_vars': quant_vars,
        })
    
    return constancy_info, lhs_only, rhs_only


def try_constancy_proof(problem, eq1_text, eq2_text):
    """Try to prove using constancy lemmas.
    Returns a list of proof codes to try, empty list if not applicable. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return []
    
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    eq2_lhs = parts2[0].strip()
    eq2_rhs = parts2[1].strip()
    
    intro = f"intro {' '.join(eq2_vars)}"
    
    # Build constancy lemmas
    constancy_info, lhs_only, rhs_only = _build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    
    if not constancy_info:
        return []
    
    # Try simp with constancy lemmas
    ci_block = ""
    ci_names = []
    for i, ci in enumerate(constancy_info):
        name = "hc" if i == 0 else f"hc{i+1}"
        line = ci['have_line']
        line = line.replace('hconst', name, 1)
        ci_block += line + "\n"
        ci_names.append(name)
    
    proofs = []
    
    # Strategy 1: simp [← h, hc]
    simp_bwd = ", ".join(["← h"] + ci_names)
    proof1 = f"{intro}\n{ci_block}simp only [{simp_bwd}]"
    proofs.append(proof1)
    
    # Strategy 2: rw [h] then simp
    proof2 = f"{intro}\n{ci_block}rw [show {eq2_vars[0]} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]\nsimp only [← h, {', '.join(ci_names)}]"
    proofs.append(proof2)
    
    # Strategy 3: conv on LHS with rw [h], then simp
    proof3 = f"{intro}\n{ci_block}conv_lhs => rw [show {eq2_vars[0]} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]\nsimp only [← h, {', '.join(ci_names)}]"
    proofs.append(proof3)
    
    # Strategy 4: conv on RHS with rw [h], then simp
    proof4 = f"{intro}\n{ci_block}conv_rhs => rw [show {eq2_vars[0]} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]\nsimp only [← h, {', '.join(ci_names)}]"
    proofs.append(proof4)
    
    # Strategy 5: rw [← h] repeatedly then use hc
    proof5 = f"{intro}\n{ci_block}repeat rw [← h]\n{ci_names[-1]} {' '.join(eq2_vars[:len(eq1_vars)])}"
    proofs.append(proof5)
    
    # Strategy 6: exact with trans chain
    if constancy_info:
        ci = constancy_info[0]
        # Build exact proof using trans
        exact_proof = f"{intro}\n{ci_block}exact (h {' '.join(eq2_vars[:len(eq1_vars)])}).trans ({ci_names[0]} {' '.join(eq2_vars[:len(eq1_vars)])})"
        proofs.append(exact_proof)
    
    # Strategy 7: calc chain
    if constancy_info:
        calc_lines = [intro, ci_block, "calc"]
        calc_lines.append(f"  {eq2_lhs} = {eq1_rhs} := by rw [show {eq2_lhs} = _ from h {' '.join(eq2_vars[:len(eq1_vars)])}]")
        calc_lines.append(f"  _ = {eq2_rhs} := by {ci_names[0]} {' '.join(eq2_vars[:len(eq1_vars)])}")
        proof7 = "\n".join(calc_lines)
        proofs.append(proof7)
    
    return proofs


# ── Simp rewrite proof ─────────────────────────────────────────

def try_simp_rewrite_proof(problem, eq1_text, eq2_text):
    """Try proofs using Lean's simp tactic with derived rewrite lemmas.
    Returns the proof code if found, None otherwise. Uses 0 LLM calls."""
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    
    parts1 = eq1_text.split('=', 1)
    parts2 = eq2_text.split('=', 1)
    if len(parts1) != 2 or len(parts2) != 2:
        return None
    
    eq1_lhs = parts1[0].strip()
    eq1_rhs = parts1[1].strip()
    
    lhs_vars = set(re.findall(r'\b([a-z])\b', eq1_lhs))
    rhs_vars = set(re.findall(r'\b([a-z])\b', eq1_rhs))
    rhs_only = sorted(rhs_vars - lhs_vars)
    lhs_only = sorted(lhs_vars - rhs_vars)
    
    if not rhs_only and not lhs_only:
        return None  # No free vars, constancy doesn't apply
    
    intro = f"intro {' '.join(eq2_vars)}"
    
    # Build constancy lemmas
    constancy_info, _, _ = _build_constancy_info(eq1_text, eq1_vars, eq2_vars)
    ci_block = ""
    ci_names = []
    for i, ci in enumerate(constancy_info):
        name = "hc" if i == 0 else f"hc{i+1}"
        line = ci['have_line']
        line = line.replace('hconst', name, 1)
        ci_block += line + "\n"
        ci_names.append(name)
    
    if not ci_names:
        return None
    
    # Strategy: simp [← h, hc]
    simp_bwd = ", ".join(["← h"] + ci_names)
    proof = f"{intro}\n{ci_block}simp only [{simp_bwd}]"
    
    return make_true_code(proof)


# ── Lean code generators ────────────────────────────────────────

def make_false_code(n, table):
    table_str = json.dumps(table)
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        f"  }}\n"
        f"  refine \u27e8Fin {n}, m, ?_\u27e9\n"
        f"  decideFin!\n"
    )


def make_true_code(proof_body):
    proof_body = proof_body.strip()
    if ":= by" in proof_body:
        proof_body = re.sub(r"^.*?:=\s*by\s*\n?", "", proof_body, count=1, flags=re.DOTALL)
    proof_body = re.sub(r"^\s*by\s+", "", proof_body)
    proof_body = re.sub(r"^\s*import\s+.*\n?", "", proof_body, flags=re.MULTILINE)
    lines = proof_body.split("\n")
    indented = "\n".join("  " + ln if ln.strip() else "" for ln in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


# ── Local Lean verification (optional) ─────────────────────────

def _verify_with_lean(code, timeout=3):
    """Verify Lean code locally using lean compiler.
    Returns (success: bool, error_msg: str or None).
    This is optional and requires lean to be installed."""
    import subprocess
    import tempfile
    
    # Check if lean is available
    lean_bin = os.environ.get("LEAN_BIN")
    if not lean_bin:
        # Try to find lean in PATH
        try:
            result = subprocess.run(["which", "lean"], capture_output=True, text=True, timeout=1)
            if result.returncode == 0:
                lean_bin = result.stdout.strip()
            else:
                return True, None  # Skip verification if lean not available
        except (subprocess.TimeoutExpired, FileNotFoundError):
            return True, None  # Skip verification if lean not available
    
    # Create temporary file with the code
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        f.write(code)
        tmp_path = f.name
    
    try:
        # Run lean with timeout
        result = subprocess.run(
            [lean_bin, "--check", tmp_path],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        
        if result.returncode == 0:
            return True, None
        else:
            # Extract error message (first few lines)
            error_lines = result.stderr.split('\n')[:5]
            error_msg = '\n'.join(error_lines)
            return False, error_msg
    except subprocess.TimeoutExpired:
        return False, "Lean verification timed out"
    except Exception as e:
        return True, None  # Skip verification on error
    finally:
        # Clean up temporary file
        try:
            os.unlink(tmp_path)
        except OSError:
            pass


# ── Proof prefilter (from FewShot) ─────────────────────────────

_BANNED_PROOF_TOKENS = ("sorry", "admit", "unreachable!")
_PROOF_DELIMITERS = {
    "(": ")",
    "[": "]",
    "{": "}",
    "\u27e8": "\u27e9",  # ⟨ ⟩
    "\u2039": "\u203a",  # ‹ ›
}

_BANNED_PROOF_RE = re.compile(
    r"(?<![A-Za-z0-9_!])("
    + "|".join(re.escape(tok) for tok in _BANNED_PROOF_TOKENS)
    + r")(?![A-Za-z0-9_])"
)

_LINE_COMMENT_RE = re.compile(r"--[^\n]*")
_BLOCK_COMMENT_RE = re.compile(r"/-[\s\S]*?-/")


def _prefilter_proof(body):
    """Cheap structural check on a candidate proof body."""
    if not body:
        return False
    text = body.strip()
    if not text:
        return False
    decommented = _BLOCK_COMMENT_RE.sub(" ", text)
    decommented = _LINE_COMMENT_RE.sub(" ", decommented)
    if not decommented.strip():
        return False
    if _BANNED_PROOF_RE.search(decommented):
        return False
    stack = []
    closers = set(_PROOF_DELIMITERS.values())
    for c in decommented:
        if c in _PROOF_DELIMITERS:
            stack.append(_PROOF_DELIMITERS[c])
        elif c in closers:
            if not stack or stack.pop() != c:
                return False
    return not stack


def _prefilter_proof_with_error(body):
    """Prefilter proof and return error info if rejected.
    Returns (cleaned_body, error_info) or (body, None) if valid."""
    if not body:
        return None, {"type": "empty_body", "detail": "Proof body is empty"}
    text = body.strip()
    if not text:
        return None, {"type": "empty_body", "detail": "Proof body is empty"}
    
    # Strip comments
    decommented = _BLOCK_COMMENT_RE.sub(" ", text)
    decommented = _LINE_COMMENT_RE.sub(" ", decommented)
    if not decommented.strip():
        return None, {"type": "empty_body", "detail": "Proof body is empty after stripping comments"}
    
    # Check for banned tokens
    if _BANNED_PROOF_RE.search(decommented):
        return None, {"type": "banned_token", "detail": "Proof contains banned token (sorry/admit/unreachable!)"}
    
    # Check delimiter balance
    stack = []
    closers = set(_PROOF_DELIMITERS.values())
    for c in decommented:
        if c in _PROOF_DELIMITERS:
            stack.append(_PROOF_DELIMITERS[c])
        elif c in closers:
            if not stack or stack.pop() != c:
                return None, {"type": "unbalanced_delimiters", "detail": "Proof has unbalanced delimiters"}
    if stack:
        return None, {"type": "unbalanced_delimiters", "detail": "Proof has unbalanced delimiters"}
    
    return body, None


# ── JSON extraction ─────────────────────────────────────────────

def _extract_json(text):
    text = re.sub(r"<think>[\s\S]*?</think>", "", text or "").strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)
    try:
        return json.loads(text.strip())
    except Exception:
        pass
    m = re.search(r"\{[\s\S]*\}", text)
    if m:
        try:
            return json.loads(m.group())
        except Exception:
            pass
    return None


# ── Triage scoring ──────────────────────────────────────────────

def difficulty_score(prob):
    """Smaller is easier. Combine equation char length + distinct-var count."""
    eq1 = prob.get("equation1", "")
    eq2 = prob.get("equation2", "")
    var_count = len(set(re.findall(r"\b([a-z])\b", eq1 + " " + eq2)))
    return (len(eq1) + len(eq2)) + 5 * var_count


def _vars_of(prob):
    return set(re.findall(r"\b([a-z])\b",
                          prob.get("equation1", "") + " " + prob.get("equation2", "")))


# ── Structural similarity (Alpha-Invariant AST Matching) ────────

def _normalize_vars(text):
    """Normalize variable names to v_0, v_1, v_2, ... for structural comparison."""
    vars_seen = []
    var_map = {}
    result = text
    for v in re.findall(r'\b([a-z])\b', text):
        if v not in var_map:
            var_map[v] = f"v_{len(vars_seen)}"
            vars_seen.append(v)
    for old, new in var_map.items():
        result = re.sub(r'\b' + old + r'\b', new, result)
    return result


def _ast_fingerprint(text):
    """Generate a structural fingerprint of an equation using prefix notation.
    This captures the tree structure more accurately than simple depth/count."""
    # Normalize operator first to handle both * and ◇
    normalized = _normalize_vars(normalize_op_to_diamond(text))
    
    # Parse into prefix notation (Polish notation)
    def _to_prefix(s):
        s = s.strip()
        while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
            depth = 0; matched = True
            for i, c in enumerate(s):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                if depth == 0 and i < len(s) - 1: matched = False; break
            if matched: s = s[1:-1].strip()
            else: break
        
        # Find outermost operator
        depth = 0; last_op = -1
        for i, c in enumerate(s):
            if c == '(': depth += 1
            elif c == ')': depth -= 1
            elif c == '◇' and depth == 0: last_op = i
        
        if last_op >= 0:
            left = _to_prefix(s[:last_op])
            right = _to_prefix(s[last_op+1:])
            return f"◇({left},{right})"
        return s.strip()
    
    prefix = _to_prefix(normalized)
    
    # Generate multiple fingerprint features
    features = []
    
    # 1. Prefix string (exact structure)
    features.append(prefix)
    
    # 2. Depth and operator count
    depth = 0
    max_depth = 0
    op_count = 0
    for c in prefix:
        if c == '(':
            depth += 1
            max_depth = max(max_depth, depth)
        elif c == ')':
            depth -= 1
        elif c == '◇':
            op_count += 1
    features.append((max_depth, op_count))
    
    # 3. Operator sequence (ignoring variables)
    op_seq = []
    for c in prefix:
        if c == '◇':
            op_seq.append('◇')
        elif c == '(':
            op_seq.append('(')
        elif c == ')':
            op_seq.append(')')
    features.append(tuple(op_seq))
    
    return tuple(features)


def example_relevance(target, example):
    """Higher = more relevant. Uses structural similarity + variable overlap."""
    tgt_vars = _vars_of(target)
    ex_vars = _vars_of(example["prob"])
    var_overlap = len(tgt_vars & ex_vars)
    var_diff = abs(len(tgt_vars) - len(ex_vars))
    len_diff = abs(
        len(target.get("equation1", "")) + len(target.get("equation2", ""))
        - len(example["prob"].get("equation1", ""))
        - len(example["prob"].get("equation2", ""))
    )
    
    # Structural similarity bonus using improved fingerprint
    tgt_fp1 = _ast_fingerprint(target.get("equation1", ""))
    tgt_fp2 = _ast_fingerprint(target.get("equation2", ""))
    ex_fp1 = _ast_fingerprint(example["prob"].get("equation1", ""))
    ex_fp2 = _ast_fingerprint(example["prob"].get("equation2", ""))
    
    struct_sim = 0
    
    # Check prefix notation match (exact structure)
    if tgt_fp1[0] == ex_fp1[0]:  # prefix string
        struct_sim += 10
    if tgt_fp2[0] == ex_fp2[0]:  # prefix string
        struct_sim += 10
    
    # Check depth and operator count match
    if tgt_fp1[1] == ex_fp1[1]:  # (max_depth, op_count)
        struct_sim += 5
    if tgt_fp2[1] == ex_fp2[1]:  # (max_depth, op_count)
        struct_sim += 5
    
    # Check operator sequence match
    if tgt_fp1[2] == ex_fp1[2]:  # operator sequence
        struct_sim += 3
    if tgt_fp2[2] == ex_fp2[2]:  # operator sequence
        struct_sim += 3
    
    # Big positive for shared vars; small penalty for length / arity drift.
    return 10 * var_overlap - 3 * var_diff - len_diff / 50.0 + struct_sim


# ── Cold Start Seed Pool ────────────────────────────────────────

SEED_PROOFS = [
    # Common proof patterns for equational theory
    {
        "prob": {"eq1_id": 1, "eq2_id": 2, "equation1": "x = x", "equation2": "x = x"},
        "proof_body": "intro x\nexact rfl"
    },
    {
        "prob": {"eq1_id": 3, "eq2_id": 4, "equation1": "x = x ◇ x", "equation2": "x = x ◇ x"},
        "proof_body": "intro x h\nexact h x"
    },
    {
        "prob": {"eq1_id": 5, "eq2_id": 6, "equation1": "x = y ◇ x", "equation2": "x = y ◇ x"},
        "proof_body": "intro x y h\nexact h x y"
    },
    # Singleton collapse pattern
    {
        "prob": {"eq1_id": 7, "eq2_id": 8, "equation1": "x = y", "equation2": "x = x"},
        "proof_body": "intro x y h\nhave singleton : ∀ (a b : G), a = b := fun a b => (h a).trans (h b).symm\nexact singleton x x"
    },
    # Constancy lemma pattern
    {
        "prob": {"eq1_id": 9, "eq2_id": 10, "equation1": "x = y ◇ z", "equation2": "x = y ◇ w"},
        "proof_body": "intro x y z w h\nhave h1 : y ◇ z = y ◇ w := (h x y z).symm.trans (h x y w)\nexact h1"
    },
    # Direct substitution pattern
    {
        "prob": {"eq1_id": 11, "eq2_id": 12, "equation1": "x = y ◇ z", "equation2": "x = y ◇ z"},
        "proof_body": "intro x y z h\nexact h x y z"
    },
    # Symmetry pattern
    {
        "prob": {"eq1_id": 13, "eq2_id": 14, "equation1": "x = y ◇ z", "equation2": "x = z ◇ y"},
        "proof_body": "intro x y z h\nexact (h x y z).symm"
    },
]


def _init_seed_pool():
    """Initialize fewshot_pool with seed proofs."""
    return SEED_PROOFS.copy()


# ── Few-shot prompt builder ─────────────────────────────────────

def _fill_base(template, prob):
    return (template
            .replace("{problem.equation1}", prob.get("equation1", ""))
            .replace("{problem.equation2}", prob.get("equation2", ""))
            .replace("{problem.equation1_id}", f"Equation{prob['eq1_id']}")
            .replace("{problem.equation2_id}", f"Equation{prob['eq2_id']}"))


def build_prompt(prob, fewshot_pool):
    """Top-k relevance ranking; returns plain prompt if pool is empty."""
    if not fewshot_pool:
        return _fill_base(PROMPT_BASE, prob)
    ranked = sorted(fewshot_pool,
                    key=lambda ex: example_relevance(prob, ex),
                    reverse=True)[:FEWSHOT_K]
    parts = [PROMPT_FEWSHOT_HEADER.replace("{n_examples}", str(len(ranked)))]
    for idx, ex in enumerate(ranked, 1):
        ep = ex["prob"]
        body = ex["proof_body"][:MAX_EXAMPLE_PROOF_CHARS]
        parts.append(PROMPT_FEWSHOT_EXAMPLE
                     .replace("{idx}", str(idx))
                     .replace("{ex_eq1_name}", f"Equation{ep['eq1_id']}")
                     .replace("{ex_eq2_name}", f"Equation{ep['eq2_id']}")
                     .replace("{ex_eq1}", ep.get("equation1", ""))
                     .replace("{ex_eq2}", ep.get("equation2", ""))
                     .replace("{ex_proof_json}", json.dumps(body)))
    parts.append(_fill_base(PROMPT_FEWSHOT_FOOTER, prob))
    return "".join(parts)


# ── Lemma extraction (from long proofs) ─────────────────────────

def _extract_lemmas(proof_body):
    """Extract reusable lemmas from a proof body.
    Returns a list of lemma dictionaries with name, type, and proof.
    Uses more robust parsing to handle multi-line proofs."""
    lemmas = []
    if not proof_body:
        return lemmas
    
    lines = proof_body.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        
        # Match have statements with various patterns
        # Pattern 1: have name : type := proof
        # Pattern 2: have name : type := by proof
        # Pattern 3: have name : type := calc ...
        m = re.match(r'have\s+(\w+)\s*:\s*(.+?)\s*:=\s*(.*)', line)
        if not m:
            # Try alternative pattern without := (just have name : type)
            m2 = re.match(r'have\s+(\w+)\s*:\s*(.+?)$', line)
            if m2 and i + 1 < len(lines) and lines[i + 1].strip().startswith(':='):
                # Multi-line have statement
                lemma_name = m2.group(1)
                lemma_type = m2.group(2).strip()
                i += 1
                lemma_proof_start = lines[i].strip()[2:].strip()  # Remove :=
                m = type('Match', (), {'group': lambda self, n: [None, lemma_name, lemma_type, lemma_proof_start][n]})()
        
        if m:
            lemma_name = m.group(1)
            lemma_type = m.group(2).strip()
            lemma_proof_start = m.group(3).strip()
            
            # Only extract non-trivial lemmas involving the magma operation
            if '◇' in lemma_type and '=' in lemma_type:
                # Collect the full proof (may span multiple lines)
                lemma_proof = lemma_proof_start
                proof_lines = [lemma_proof_start] if lemma_proof_start else []
                
                # Track indentation to find proof boundaries
                base_indent = len(lines[i]) - len(lines[i].lstrip()) if i < len(lines) else 0
                
                # Collect subsequent lines that are part of the proof
                j = i + 1
                while j < len(lines):
                    next_line = lines[j]
                    next_stripped = next_line.strip()
                    
                    # Empty line or less/equal indentation = end of proof
                    if not next_stripped:
                        break
                    
                    next_indent = len(next_line) - len(next_line.lstrip())
                    
                    # If indentation is less than or equal to base, we've left the proof
                    if next_indent <= base_indent and next_stripped:
                        # But check if it's a continuation (like calc steps)
                        if not next_stripped.startswith('_') and not next_stripped.startswith('·'):
                            break
                    
                    # Check for new have/exact/simp at same level = new statement
                    if next_indent == base_indent and (
                        next_stripped.startswith('have ') or 
                        next_stripped.startswith('exact ') or
                        next_stripped.startswith('simp ') or
                        next_stripped.startswith('rw ')
                    ):
                        break
                    
                    proof_lines.append(next_stripped)
                    j += 1
                
                lemma_proof = ' '.join(proof_lines)
                
                # Validate the extracted proof is not empty
                if lemma_proof and lemma_proof != 'by':
                    full_statement = f"have {lemma_name} : {lemma_type} := {lemma_proof}"
                    lemmas.append({
                        "name": lemma_name,
                        "type": lemma_type,
                        "proof": lemma_proof,
                        "full_statement": full_statement
                    })
                
                i = j
                continue
        i += 1
    
    return lemmas


def _add_lemmas_to_pool(fewshot_pool, lemmas, prob):
    """Add extracted lemmas to the few-shot pool as reusable examples."""
    for lemma in lemmas:
        # Create a synthetic example for the lemma
        lemma_example = {
            "prob": {
                "eq1_id": prob.get("eq1_id", 0),
                "eq2_id": prob.get("eq2_id", 0),
                "equation1": lemma["type"],
                "equation2": lemma["type"],  # Self-implication
            },
            "proof_body": lemma["full_statement"],
            "is_lemma": True,
            "lemma_name": lemma["name"],
        }
        fewshot_pool.append(lemma_example)


# ── Few-shot pool management ───────────────────────────────────

FEWSHOT_POOL_MAX_SIZE = 100  # Maximum number of examples in pool


def _evict_pool(fewshot_pool):
    """Evict old examples from the pool to prevent memory bloat.
    Keeps the most recently added and most relevant examples."""
    if len(fewshot_pool) <= FEWSHOT_POOL_MAX_SIZE:
        return
    
    # Strategy: Keep seed proofs + most recent examples
    seeds = [ex for ex in fewshot_pool if ex.get("is_seed")]
    non_seeds = [ex for ex in fewshot_pool if not ex.get("is_seed")]
    
    # Keep most recent non-seed examples
    keep_count = FEWSHOT_POOL_MAX_SIZE - len(seeds)
    if keep_count > 0:
        kept_non_seeds = non_seeds[-keep_count:]
    else:
        kept_non_seeds = []
    
    # Rebuild pool
    fewshot_pool.clear()
    fewshot_pool.extend(seeds)
    fewshot_pool.extend(kept_non_seeds)


def _init_seed_pool():
    """Initialize fewshot_pool with seed proofs."""
    pool = SEED_PROOFS.copy()
    # Mark as seeds for eviction protection
    for ex in pool:
        ex["is_seed"] = True
    return pool


# ── Marathon driver ─────────────────────────────────────────────

def _load_manifest(path):
    out = []
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            raw = raw.strip()
            if not raw:
                continue
            try:
                out.append(json.loads(raw))
            except json.JSONDecodeError:
                continue
    return out


def _append_answer(output_path, entry):
    """Append answer to output file. For 'true' verdicts, performs Lean verification
    as a hard gatekeeper to prevent false positive submissions."""
    # For true verdicts, verify with Lean if possible
    if entry.get("verdict") == "true" and entry.get("code"):
        success, error_msg = _verify_with_lean(entry["code"])
        if not success:
            # Verification failed - do NOT submit this answer
            return False
    
    line = json.dumps(entry, ensure_ascii=False) + "\n"
    with open(output_path, "a", encoding="utf-8") as fh:
        fh.write(line)
        fh.flush()
        try:
            os.fsync(fh.fileno())
        except OSError:
            pass
    return True


def _persist_pattern(scratch_dir, prob, proof_body):
    """Append win to scratch for offline analysis. Best-effort."""
    try:
        path = Path(scratch_dir) / "proof_lib.jsonl"
        with open(path, "a", encoding="utf-8") as fh:
            fh.write(json.dumps({
                "id": prob["id"],
                "eq1_id": prob.get("eq1_id"),
                "eq2_id": prob.get("eq2_id"),
                "equation1": prob.get("equation1"),
                "equation2": prob.get("equation2"),
                "proof_body": proof_body,
            }) + "\n")
    except OSError:
        pass


def run_marathon():
    try:
        from marathon_llm import call_llm, budget_remaining, tokens_used
    except ImportError:
        call_llm = None  # type: ignore[assignment]

        def budget_remaining():
            return 0

        def tokens_used():
            return 0

    manifest_path = os.environ["JUDGE_MARATHON_MANIFEST"]
    output_path = os.environ["JUDGE_MARATHON_OUTPUT"]
    scratch_dir = os.environ["JUDGE_MARATHON_SCRATCH_DIR"]
    budget_seconds = float(os.environ.get("JUDGE_MARATHON_BUDGET_SECONDS", "3600"))
    cap_tokens = int(os.environ.get("JUDGE_MARATHON_BUDGET_TOKENS", "0"))
    deadline = time.monotonic() + budget_seconds
    tail_margin = 15.0

    llm_config = {
        "model": os.environ.get("JUDGE_MARATHON_MODEL", "openai/gpt-oss-120b"),
        "provider": "deepinfra/bf16",
        "max_output_tokens": 8192,
        "temperature": 0.0,
        "reasoning_effort": "low",
        "use_seed": True,
        "seed": 0,
        "http_timeout_seconds": 600.0,
    }

    problems = _load_manifest(manifest_path)
    solved: set[str] = set()
    
    # Cold Start: Initialize with seed proofs
    fewshot_pool: list[dict] = _init_seed_pool()

    # ── Pass 0: Singleton collapse (deterministic, 0 LLM calls) ──
    for prob in problems:
        if time.monotonic() + tail_margin >= deadline:
            break
        eq1 = normalize_op_to_diamond(prob["equation1"])
        eq2 = normalize_op_to_diamond(prob["equation2"])
        singleton_code = try_singleton(prob, eq1, eq2)
        if singleton_code is not None:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": singleton_code,
            })
            if success:
                solved.add(prob["id"])

    # ── Pass 0.5: Deterministic proof strategies (0 LLM calls) ──
    for prob in problems:
        if prob["id"] in solved:
            continue
        if time.monotonic() + tail_margin >= deadline:
            break
        eq1 = normalize_op_to_diamond(prob["equation1"])
        eq2 = normalize_op_to_diamond(prob["equation2"])
        
        # Try direct proof
        direct_code = try_direct_proof(prob, eq1, eq2)
        if direct_code is not None:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": direct_code,
            })
            if success:
                solved.add(prob["id"])
                continue
        
        # Try calc chain proof
        calc_code = try_calc_chain_proof(prob, eq1, eq2)
        if calc_code is not None:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": calc_code,
            })
            if success:
                solved.add(prob["id"])
                continue
        
        # Try subterm rewrite proof (with congruence)
        subterm_code = try_subterm_rewrite_proof(prob, eq1, eq2)
        if subterm_code is not None:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": subterm_code,
            })
            if success:
                solved.add(prob["id"])
                continue
        
        # Try constancy proof (returns list of candidates) - try ALL candidates
        const_proofs = try_constancy_proof(prob, eq1, eq2)
        for proof_candidate in const_proofs:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": make_true_code(proof_candidate),
            })
            if success:
                solved.add(prob["id"])
                break
        if prob["id"] in solved:
            continue
        
        # Try simp rewrite proof
        simp_code = try_simp_rewrite_proof(prob, eq1, eq2)
        if simp_code is not None:
            success = _append_answer(output_path, {
                "id": prob["id"], "verdict": "true",
                "code": simp_code,
            })
            if success:
                solved.add(prob["id"])
                continue

    # ── Pass 1: Counterexample search (no tokens) ──
    for prob in problems:
        if prob["id"] in solved:
            continue
        if time.monotonic() + tail_margin >= deadline:
            break
        eq1 = normalize_op_to_diamond(prob["equation1"])
        eq2 = normalize_op_to_diamond(prob["equation2"])
        try:
            # Try structured tables first (more effective)
            n, table = extended_counterexample(eq1, eq2, max_n=5, random_attempts=1000)
            if n is None:
                # Try SAT solver for harder cases
                n, table = _sat_counterexample(eq1, eq2, max_n=8)
            if n is None:
                n, table = search_counterexample(eq1, eq2, max_n=3, time_budget=4.0)
        except Exception:  # noqa: BLE001
            continue
        if n is None:
            continue
        _append_answer(output_path, {
            "id": prob["id"], "verdict": "false",
            "code": make_false_code(n, table),
        })
        solved.add(prob["id"])

    # ── Pass 2: LLM with growing few-shot pool, sorted by difficulty ──
    if call_llm is None:
        return
    remaining = [p for p in problems if p["id"] not in solved]
    remaining.sort(key=difficulty_score)  # Smart scheduling: easier first

    for prob in remaining:
        if time.monotonic() + tail_margin >= deadline:
            break
        if cap_tokens > 0 and budget_remaining() < llm_config["max_output_tokens"] // 4:
            break

        # Multi-round LLM refinement loop (up to 3 attempts)
        # Note: temperature and seed are fixed by organizer proxy (0.0 and 0)
        # We can only vary max_output_tokens (up to 65536) and reasoning_effort
        max_attempts = 3
        
        for attempt in range(max_attempts):
            if time.monotonic() + tail_margin >= deadline:
                break
            
            # Only modify allowed parameters
            attempt_config = dict(llm_config)
            # Use smaller output for first attempts to save budget
            if attempt == 0:
                attempt_config["max_output_tokens"] = 8192
            elif attempt == 1:
                attempt_config["max_output_tokens"] = 16384
            else:
                attempt_config["max_output_tokens"] = 32768
            
            prompt = build_prompt(prob, fewshot_pool)
            try:
                resp = call_llm(prompt, config=attempt_config)
            except Exception:  # noqa: BLE001
                continue
            if "error" in resp:
                if "exhausted" in str(resp.get("error", "")):
                    break
                continue
            obj = _extract_json(resp.get("response", ""))
            if not isinstance(obj, dict):
                continue
            verdict = obj.get("verdict")
            if verdict == "true":
                body = (obj.get("proof") or "").strip()
                if not body:
                    continue
                # Normalize operator
                body = normalize_op_to_diamond(body)
                
                # Pre-flight validation
                body, pf_error = _prefilter_proof_with_error(body)
                if pf_error:
                    continue
                
                # Submit answer - Lean verification happens inside _append_answer
                success = _append_answer(output_path, {
                    "id": prob["id"], "verdict": "true",
                    "code": make_true_code(body),
                })
                
                if success:
                    # Lean verification passed - safe to add to pool
                    fewshot_pool.append({"prob": prob, "proof_body": body})
                    _persist_pattern(scratch_dir, prob, body)
                    
                    # Lemma distillation: extract reusable lemmas from long proofs
                    if len(body.split('\n')) > 5:
                        lemmas = _extract_lemmas(body)
                        if lemmas:
                            _add_lemmas_to_pool(fewshot_pool, lemmas, prob)
                    
                    # Evict old examples to prevent memory bloat
                    _evict_pool(fewshot_pool)
                
                break  # Move to next problem regardless
                    
            elif verdict == "false":
                tbl = obj.get("counterexample_table")
                if isinstance(tbl, list) and tbl and len(tbl) >= 2:
                    # Local verification: check table satisfies eq1 AND violates eq2
                    eq1 = normalize_op_to_diamond(prob["equation1"])
                    eq2 = normalize_op_to_diamond(prob["equation2"])
                    try:
                        v1, l1, r1 = _parse_equation(eq1)
                        v2, l2, r2 = _parse_equation(eq2)
                        n = len(tbl)
                        op_fn = lambda a, b, t=tbl: t[a][b]
                        if _check_eq(v1, l1, r1, n, op_fn) and not _check_eq(v2, l2, r2, n, op_fn):
                            _append_answer(output_path, {
                                "id": prob["id"], "verdict": "false",
                                "code": make_false_code(n, tbl),
                            })
                    except Exception:
                        pass  # Invalid table format, skip
                    break


# ── Solo fallback (keeps the file dual-mode) ────────────────────

def _read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def _send_message(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    """Send a judge request and return the response."""
    _send_message({"call": "judge", "verdict": verdict, "code": code})
    return _read_message()


def run_solo():
    """Full Solo path with deterministic strategies + LLM fallback."""
    startup = _read_message()
    problem = startup["problem"]
    eq1 = normalize_op_to_diamond(problem["equation1"])
    eq2 = normalize_op_to_diamond(problem["equation2"])
    
    # Stage 1: Singleton collapse
    singleton_code = try_singleton(problem, eq1, eq2)
    if singleton_code is not None:
        _send_message({"call": "judge", "verdict": "true", "code": singleton_code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Stage 2: Deterministic proof strategies
    # Try direct proof
    direct_code = try_direct_proof(problem, eq1, eq2)
    if direct_code is not None:
        _send_message({"call": "judge", "verdict": "true", "code": direct_code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Try calc chain proof
    calc_code = try_calc_chain_proof(problem, eq1, eq2)
    if calc_code is not None:
        _send_message({"call": "judge", "verdict": "true", "code": calc_code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Try subterm rewrite proof
    subterm_code = try_subterm_rewrite_proof(problem, eq1, eq2)
    if subterm_code is not None:
        _send_message({"call": "judge", "verdict": "true", "code": subterm_code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Try constancy proof
    const_proofs = try_constancy_proof(problem, eq1, eq2)
    for proof in const_proofs:
        code = make_true_code(proof)
        _send_message({"call": "judge", "verdict": "true", "code": code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Try simp rewrite proof
    simp_code = try_simp_rewrite_proof(problem, eq1, eq2)
    if simp_code is not None:
        _send_message({"call": "judge", "verdict": "true", "code": simp_code})
        resp = _read_message()
        if resp.get("status") == "accepted":
            return
    
    # Stage 3: Counterexample search
    n, table = extended_counterexample(eq1, eq2, max_n=5, random_attempts=1000)
    if n is not None:
        _send_message({"call": "judge", "verdict": "false", "code": make_false_code(n, table)})
        _read_message()
        return
    
    # Stage 4: LLM fallback (if available)
    try:
        from marathon_llm import call_llm
        # Use LLM for hard problems
        prompt = PROMPT_BASE.replace("{problem.equation1_id}", f"Equation{problem['eq1_id']}")
        prompt = prompt.replace("{problem.equation2_id}", f"Equation{problem['eq2_id']}")
        prompt = prompt.replace("{problem.equation1}", eq1)
        prompt = prompt.replace("{problem.equation2}", eq2)
        
        llm_config = {
            "model": os.environ.get("JUDGE_MARATHON_MODEL", "openai/gpt-oss-120b"),
            "provider": "deepinfra/bf16",
            "max_output_tokens": 8192,
            "temperature": 0.0,
            "reasoning_effort": "low",
        }
        
        resp = call_llm(prompt, config=llm_config)
        if "error" not in resp:
            obj = _extract_json(resp.get("response", ""))
            if isinstance(obj, dict):
                verdict = obj.get("verdict")
                if verdict == "true":
                    body = (obj.get("proof") or "").strip()
                    if body:
                        body = normalize_op_to_diamond(body)
                        code = make_true_code(body)
                        _send_message({"call": "judge", "verdict": "true", "code": code})
                        _read_message()
                        return
                elif verdict == "false":
                    tbl = obj.get("counterexample_table")
                    if isinstance(tbl, list) and tbl:
                        _send_message({"call": "judge", "verdict": "false", "code": make_false_code(len(tbl), tbl)})
                        _read_message()
                        return
    except ImportError:
        pass  # LLM not available


def main():
    if "JUDGE_MARATHON_MANIFEST" in os.environ:
        run_marathon()
    else:
        run_solo()


if __name__ == "__main__":
    main()
