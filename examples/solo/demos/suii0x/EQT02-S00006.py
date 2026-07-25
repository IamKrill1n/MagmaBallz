"""
Conservative Solo-track MVP solver.

Single-file submission. The solver first searches deterministic finite
magmas for counterexamples, then tries a few small true-proof patterns.
It intentionally avoids external cache files, the equational_theories
library, and unbounded LLM loops.
"""

import json
import re
import sys
import time
from itertools import product


PROMPT = ""

FALSE_SEARCH_SECONDS = 20.0
MAX_TRUE_JUDGE_CALLS_PER_STRATEGY = 4
MAX_DIRECT_SUBSTITUTION_COMPOUND_POOL_SIZE = 64
MAX_DIRECT_SUBSTITUTION_COMPOUND_JUDGE_CALLS = 3
MAX_ONE_CONGR_CALC_CANDIDATES = 3
MAX_ONE_CONGR_CALC_JUDGE_CALLS = 2
MAX_TERM_POOL_CONSTANCY_CANDIDATES = 3
MAX_TERM_POOL_CONSTANCY_JUDGE_CALLS = 2


# -- Protocol ---------------------------------------------------------------

def log(msg):
    print(msg, file=sys.stderr, flush=True)


def read_message():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_message(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    send_message({"call": "judge", "verdict": verdict, "code": code})
    return read_message()


class Judge:
    def __init__(self):
        self.calls = 0

    def check(self, verdict, code, strategy):
        self.calls += 1
        log(f"judge call {self.calls}: {strategy} ({verdict})")
        result = call_judge(verdict, code)
        status = result.get("status")
        log(f"judge result {self.calls}: {status}")
        return result


# -- Parsing and local evaluation -----------------------------------------

def normalize_op_to_diamond(text):
    return text.replace("*", "◇") if isinstance(text, str) else text


def parse_variables(text):
    seen = set()
    variables = []
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen:
            seen.add(v)
            variables.append(v)
    return variables


def strip_outer_parens(s):
    s = s.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        matched = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            if depth == 0 and i < len(s) - 1:
                matched = False
                break
        if not matched:
            break
        s = s[1:-1].strip()
    return s


def parse_term(s, variables):
    s = strip_outer_parens(normalize_op_to_diamond(s))
    depth = 0
    last_op = -1
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "◇" and depth == 0:
            last_op = i
    if last_op >= 0:
        left = parse_term(s[:last_op], variables)
        right = parse_term(s[last_op + 1:], variables)
        return ("op", left, right)
    if len(s) == 1 and s in variables:
        return ("var", s)
    raise ValueError(f"cannot parse term: {s!r}")


def parse_equation(text):
    text = normalize_op_to_diamond(text)
    variables = parse_variables(text)
    lhs, rhs = text.split("=", 1)
    return variables, parse_term(lhs, variables), parse_term(rhs, variables)


def eval_term(term, env, op):
    if term[0] == "var":
        return env[term[1]]
    return op(eval_term(term[1], env, op), eval_term(term[2], env, op))


def tree_to_lean(term):
    if term[0] == "var":
        return term[1]
    return f"({tree_to_lean(term[1])} ◇ {tree_to_lean(term[2])})"


def norm_tree(term):
    if term[0] == "var":
        return term[1]
    return f"({norm_tree(term[1])}◇{norm_tree(term[2])})"


def subst_tree(term, mapping):
    if term[0] == "var":
        return mapping[term[1]]
    return ("op", subst_tree(term[1], mapping), subst_tree(term[2], mapping))


def check_equation(variables, lhs, rhs, n, table):
    op = lambda a, b: table[a][b]
    for vals in product(range(n), repeat=len(variables)):
        env = dict(zip(variables, vals))
        if eval_term(lhs, env, op) != eval_term(rhs, env, op):
            return False
    return True


def verify_counterexample(eq1_text, eq2_text, n, table):
    if not valid_table(n, table):
        return False, False
    v1, l1, r1 = parse_equation(eq1_text)
    v2, l2, r2 = parse_equation(eq2_text)
    sat1 = check_equation(v1, l1, r1, n, table)
    sat2 = check_equation(v2, l2, r2, n, table)
    return sat1, sat2


def valid_table(n, table):
    if not isinstance(table, list) or len(table) != n:
        return False
    for row in table:
        if not isinstance(row, list) or len(row) != n:
            return False
        for value in row:
            if not isinstance(value, int) or value < 0 or value >= n:
                return False
    return True


# -- Lean code generation --------------------------------------------------

def make_false_code(problem, n, table):
    table_str = json.dumps(table, separators=(",", ":"))
    return (
        "import JudgeProblem\n"
        "import JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\n"
        "open MemoFinOp\n\n"
        "def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{table_str}\"\n"
        f"  }}\n"
        f"  refine ⟨Fin {n}, m, ?_⟩\n"
        "  decideFin!\n"
    )


def make_true_code(problem, proof_body):
    lines = clean_proof_body(proof_body).splitlines()
    indented = "\n".join("  " + line if line.strip() else "" for line in lines)
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        f"{indented}\n"
    )


def make_final_true_probe_code(problem):
    return (
        "import JudgeProblem\n\n"
        "def submission : Goal := by\n"
        "  intro G _ h\n"
        "  exact h\n"
    )


def final_reject_probe(problem, judge):
    return judge.check("true", make_final_true_probe_code(problem), "final_reject_probe")


def clean_proof_body(proof_body):
    proof_body = normalize_op_to_diamond(proof_body or "")
    proof_body = re.sub(r"<think>[\s\S]*?</think>", "", proof_body).strip()
    proof_body = re.sub(r"^```(?:lean)?\s*\n?", "", proof_body)
    proof_body = re.sub(r"\n?```\s*$", "", proof_body)
    proof_body = re.sub(r"^\s*import\s+.*\n?", "", proof_body, flags=re.MULTILINE)
    proof_body = re.sub(r"^\s*by\s+", "", proof_body)
    if re.match(r"^\s*(theorem|def)\s+", proof_body) and ":= by" in proof_body:
        proof_body = re.sub(r"^.*?:=\s*by\s*\n?", "", proof_body, count=1, flags=re.DOTALL)
    return proof_body.strip()


def proof_body_allowed(proof_body):
    banned = ["sorry", "admit", "sorryAx", "import ", "theorem ", "def submission"]
    lower = proof_body.lower()
    return not any(tok.lower() in lower for tok in banned)


# -- Deterministic false search -------------------------------------------

def table_key(table):
    return tuple(tuple(row) for row in table)


def exhaustive_tables(n):
    total = n ** (n * n)
    for enc in range(total):
        yield [[(enc // (n ** (i * n + j))) % n for j in range(n)] for i in range(n)]


def product_tables(n):
    for p in range(2, n):
        if n % p != 0:
            continue
        q = n // p
        for a1 in range(p):
            for b1 in range(p):
                for c1 in range(p):
                    for a2 in range(q):
                        for b2 in range(q):
                            for c2 in range(q):
                                if a1 == b1 == c1 == a2 == b2 == c2 == 0:
                                    continue
                                table = [[0] * n for _ in range(n)]
                                for i in range(n):
                                    for j in range(n):
                                        ix, iy = divmod(i, q)
                                        jx, jy = divmod(j, q)
                                        rx = (a1 * ix + b1 * jx + c1) % p
                                        ry = (a2 * iy + b2 * jy + c2) % q
                                        table[i][j] = rx * q + ry
                                yield table


def rectangular_band_tables(n):
    for p in range(2, n):
        if n % p != 0:
            continue
        q = n // p
        yield [[(i // q) * q + (j % q) for j in range(n)] for i in range(n)]
        yield [[(j // q) * q + (i % q) for j in range(n)] for i in range(n)]


def projection_exception_tables(n):
    base_left = [[i for _ in range(n)] for i in range(n)]
    base_right = [[j for j in range(n)] for _ in range(n)]
    for base in (base_left, base_right):
        for i in range(n):
            for j in range(n):
                for c in range(n):
                    if base[i][j] == c:
                        continue
                    t = [row[:] for row in base]
                    t[i][j] = c
                    yield t
        for row in range(n):
            for c in range(n):
                t = [r[:] for r in base]
                t[row] = [c] * n
                yield t
        for col in range(n):
            for c in range(n):
                t = [r[:] for r in base]
                for i in range(n):
                    t[i][col] = c
                yield t


def structured_tables(n):
    for c in range(n):
        yield [[c] * n for _ in range(n)]

    yield [[i for _ in range(n)] for i in range(n)]      # left projection
    yield [[j for j in range(n)] for _ in range(n)]      # right projection
    yield [[min(i, j) for j in range(n)] for i in range(n)]
    yield [[max(i, j) for j in range(n)] for i in range(n)]
    yield [[(i + j) % n for j in range(n)] for i in range(n)]
    yield [[(i - j) % n for j in range(n)] for i in range(n)]

    for a in range(n):
        for b in range(n):
            for c in range(n):
                yield [[(a * i + b * j + c) % n for j in range(n)] for i in range(n)]

    for c in range(n):
        yield [[i if i == j else c for j in range(n)] for i in range(n)]
        yield [[i if i == j else i for j in range(n)] for i in range(n)]
        yield [[i if i == j else j for j in range(n)] for i in range(n)]
        yield [[i if i == j else (i + j + c) % n for j in range(n)] for i in range(n)]

    yield from rectangular_band_tables(n)
    yield from product_tables(n)
    yield from projection_exception_tables(n)


def find_counterexample(eq1_text, eq2_text, deadline):
    v1, l1, r1 = parse_equation(eq1_text)
    v2, l2, r2 = parse_equation(eq2_text)
    tested = 0
    seen = set()

    def is_counterexample(n, table):
        nonlocal tested
        tested += 1
        if time.monotonic() > deadline:
            raise TimeoutError
        return (
            check_equation(v1, l1, r1, n, table)
            and not check_equation(v2, l2, r2, n, table)
        )

    for n in (2, 3):
        log(f"strategy false_exhaustive_fin_{n}: start")
        for table in exhaustive_tables(n):
            if is_counterexample(n, table):
                log(f"strategy false_exhaustive_fin_{n}: found after {tested} candidates")
                return n, table, f"false_exhaustive_fin_{n}", tested
        log(f"strategy false_exhaustive_fin_{n}: exhausted, tested={tested}")

    for n in range(4, 8):
        log(f"strategy false_structured_fin_{n}: start")
        for table in structured_tables(n):
            key = (n, table_key(table))
            if key in seen:
                continue
            seen.add(key)
            if is_counterexample(n, table):
                log(f"strategy false_structured_fin_{n}: found after {tested} candidates")
                return n, table, f"false_structured_fin_{n}", tested
        log(f"strategy false_structured_fin_{n}: finished, tested={tested}")

    return None, None, "false_search_none", tested


# -- Deterministic true proof strategies ----------------------------------

def try_judged_true(problem, proof_body, judge, strategy):
    if not proof_body_allowed(proof_body):
        log(f"strategy {strategy}: rejected locally by proof filter")
        return False
    result = judge.check("true", make_true_code(problem, proof_body), strategy)
    return result.get("status") == "accepted"


def try_singleton(problem, eq1_text, eq2_text, judge):
    log("strategy true_singleton: start")
    eq1_vars = parse_variables(eq1_text)
    eq2_vars = parse_variables(eq2_text)
    if len(eq1_vars) < 2 or "=" not in eq1_text or "=" not in eq2_text:
        return False
    lhs, rhs = [part.strip() for part in eq1_text.split("=", 1)]
    if len(lhs) != 1 or lhs not in eq1_vars:
        return False
    if lhs in set(parse_variables(rhs)):
        return False

    goal_lhs, goal_rhs = [part.strip() for part in eq2_text.split("=", 1)]
    filler_count = max(len(eq1_vars) - 1, 0)
    filler = " ".join(["a"] * filler_count)
    h_a = f"h a {filler}" if filler else "h a"
    h_b = f"h b {filler}" if filler else "h b"
    proof = (
        f"intro {' '.join(eq2_vars)}\n"
        f"have singleton : ∀ (a b : G), a = b := "
        f"fun a b => ({h_a}).trans ({h_b}).symm\n"
        f"exact singleton ({goal_lhs}) ({goal_rhs})"
    )
    return try_judged_true(problem, proof, judge, "true_singleton")


def h_instances(eq1_text, eq2_vars, max_compound=False):
    eq1_vars, eq1_lhs, eq1_rhs = parse_equation(eq1_text)
    terms = [("var", v) for v in eq2_vars]
    if max_compound:
        terms += [("op", ("var", a), ("var", b)) for a in eq2_vars for b in eq2_vars]
    for combo in product(terms, repeat=len(eq1_vars)):
        mapping = dict(zip(eq1_vars, combo))
        lhs = subst_tree(eq1_lhs, mapping)
        rhs = subst_tree(eq1_rhs, mapping)
        if norm_tree(lhs) == norm_tree(rhs):
            continue
        args = " ".join(tree_to_lean(t) for t in combo)
        yield lhs, rhs, args


def try_direct_substitution(problem, eq1_text, eq2_text, judge):
    log("strategy true_direct_substitution: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    target_l = norm_tree(goal_lhs)
    target_r = norm_tree(goal_rhs)
    calls = 0
    for lhs, rhs, args in h_instances(eq1_text, eq2_vars, max_compound=False):
        proof_term = None
        if norm_tree(lhs) == target_l and norm_tree(rhs) == target_r:
            proof_term = f"h {args}"
        elif norm_tree(lhs) == target_r and norm_tree(rhs) == target_l:
            proof_term = f"(h {args}).symm"
        if proof_term:
            proof = f"intro {' '.join(eq2_vars)}\nexact {proof_term}"
            calls += 1
            if try_judged_true(problem, proof, judge, "true_direct_substitution"):
                return True
            if calls >= MAX_TRUE_JUDGE_CALLS_PER_STRATEGY:
                return False
    return False


def term_size(term):
    if term[0] == "var":
        return 1
    return 1 + term_size(term[1]) + term_size(term[2])


def subterms(term):
    yield term
    if term[0] == "op":
        yield from subterms(term[1])
        yield from subterms(term[2])


def term_pool(goal_vars, goal_lhs=None, goal_rhs=None):
    terms = [("var", v) for v in goal_vars]
    terms += [("op", ("var", a), ("var", b)) for a in goal_vars for b in goal_vars]
    for root in (goal_lhs, goal_rhs):
        if root is None:
            continue
        terms += [t for t in subterms(root) if term_size(t) <= 5]

    deduped = {}
    for t in terms:
        deduped.setdefault(norm_tree(t), t)
    return sorted(deduped.values(), key=lambda t: (term_size(t), norm_tree(t)))


def match_pattern(pattern, target, mapping):
    if pattern[0] == "var":
        v = pattern[1]
        current = mapping.get(v)
        if current is None:
            mapping = dict(mapping)
            mapping[v] = target
            return mapping
        return mapping if norm_tree(current) == norm_tree(target) else None
    if target[0] != "op":
        return None
    mapping = match_pattern(pattern[1], target[1], mapping)
    if mapping is None:
        return None
    return match_pattern(pattern[2], target[2], mapping)


def mapping_uses_term_pool(mapping, allowed):
    return all(norm_tree(t) in allowed for t in mapping.values())


def direct_term_pool_candidate(eq1_vars, eq1_lhs, eq1_rhs, goal_lhs, goal_rhs, allowed):
    mapping = match_pattern(eq1_lhs, goal_lhs, {})
    if mapping is None:
        return None
    mapping = match_pattern(eq1_rhs, goal_rhs, mapping)
    if mapping is None:
        return None
    if not all(v in mapping for v in eq1_vars):
        return None
    if not mapping_uses_term_pool(mapping, allowed):
        return None
    args = " ".join(tree_to_lean(mapping[v]) for v in eq1_vars)
    return f"h {args}"


def try_direct_substitution_compound(problem, eq1_text, eq2_text, judge):
    log("strategy true_direct_substitution_compound: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    eq1_vars, eq1_lhs, eq1_rhs = parse_equation(eq1_text)
    pool = term_pool(eq2_vars, goal_lhs, goal_rhs)
    if len(pool) > MAX_DIRECT_SUBSTITUTION_COMPOUND_POOL_SIZE:
        pool = pool[:MAX_DIRECT_SUBSTITUTION_COMPOUND_POOL_SIZE]
    allowed = {norm_tree(t) for t in pool}

    candidates = []
    checked = 0

    checked += 1
    direct = direct_term_pool_candidate(eq1_vars, eq1_lhs, eq1_rhs, goal_lhs, goal_rhs, allowed)
    if direct is not None:
        candidates.append((direct, "direct"))

    checked += 1
    reverse = direct_term_pool_candidate(eq1_vars, eq1_lhs, eq1_rhs, goal_rhs, goal_lhs, allowed)
    if reverse is not None:
        candidates.append((f"({reverse}).symm", "symm"))

    log(
        "strategy true_direct_substitution_compound: "
        f"pool={len(pool)} checked={checked} candidates={len(candidates)}"
    )
    calls = 0
    seen = set()
    for proof_term, kind in candidates:
        if proof_term in seen:
            continue
        seen.add(proof_term)
        proof = f"intro {' '.join(eq2_vars)}\nexact {proof_term}"
        calls += 1
        if try_judged_true(problem, proof, judge, "true_direct_substitution_compound"):
            log(f"strategy true_direct_substitution_compound: accepted {kind}; judge_calls={calls}")
            return True
        if calls >= MAX_DIRECT_SUBSTITUTION_COMPOUND_JUDGE_CALLS:
            break
    log(f"strategy true_direct_substitution_compound: judge_calls={calls}; no acceptance")
    return False


def try_calc_chain(problem, eq1_text, eq2_text, judge):
    log("strategy true_calc_chain: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    target_l = norm_tree(goal_lhs)
    target_r = norm_tree(goal_rhs)
    nodes = {target_l: goal_lhs, target_r: goal_rhs}
    edges = {}

    for lhs, rhs, args in h_instances(eq1_text, eq2_vars, max_compound=False):
        nl = norm_tree(lhs)
        nr = norm_tree(rhs)
        nodes.setdefault(nl, lhs)
        nodes.setdefault(nr, rhs)
        edges.setdefault(nl, []).append((nr, f"h {args}"))
        edges.setdefault(nr, []).append((nl, f"(h {args}).symm"))

    calls = 0
    for mid, proof1 in edges.get(target_l, []):
        if mid == target_r:
            proof = (
                f"intro {' '.join(eq2_vars)}\n"
                "calc\n"
                f"  {tree_to_lean(goal_lhs)} = {tree_to_lean(goal_rhs)} := {proof1}"
            )
            calls += 1
            if try_judged_true(problem, proof, judge, "true_calc_chain_1"):
                return True
            if calls >= MAX_TRUE_JUDGE_CALLS_PER_STRATEGY:
                return False

    for mid, proof1 in edges.get(target_l, []):
        for end, proof2 in edges.get(mid, []):
            if end != target_r:
                continue
            proof = (
                f"intro {' '.join(eq2_vars)}\n"
                "calc\n"
                f"  {tree_to_lean(goal_lhs)} = {tree_to_lean(nodes[mid])} := {proof1}\n"
                f"  _ = {tree_to_lean(goal_rhs)} := {proof2}"
            )
            calls += 1
            if try_judged_true(problem, proof, judge, "true_calc_chain_2"):
                return True
            if calls >= MAX_TRUE_JUDGE_CALLS_PER_STRATEGY:
                return False
    return False


def h_proof_between(eq1_vars, eq1_lhs, eq1_rhs, left, right, allowed):
    direct = direct_term_pool_candidate(eq1_vars, eq1_lhs, eq1_rhs, left, right, allowed)
    if direct is not None:
        return direct
    reverse = direct_term_pool_candidate(eq1_vars, eq1_lhs, eq1_rhs, right, left, allowed)
    if reverse is not None:
        return f"({reverse}).symm"
    return None


def h_edges_from_left(eq1_vars, eq1_lhs, eq1_rhs, left, pool, allowed, limit=16):
    edges = []

    def add_edges(pattern, result, wrapper):
        nonlocal edges
        mapping = match_pattern(pattern, left, {})
        if mapping is None or not mapping_uses_term_pool(mapping, allowed):
            return
        missing = [v for v in eq1_vars if v not in mapping]
        for combo in product(pool, repeat=len(missing)):
            full = dict(mapping)
            full.update(dict(zip(missing, combo)))
            if not mapping_uses_term_pool(full, allowed):
                continue
            right = subst_tree(result, full)
            if norm_tree(right) == norm_tree(left):
                continue
            args = " ".join(tree_to_lean(full[v]) for v in eq1_vars)
            edges.append((right, wrapper(args)))
            if len(edges) >= limit:
                return

    add_edges(eq1_lhs, eq1_rhs, lambda args: f"h {args}")
    if len(edges) < limit:
        add_edges(eq1_rhs, eq1_lhs, lambda args: f"(h {args}).symm")
    return edges[:limit]


def congr_arg_between(eq1_vars, eq1_lhs, eq1_rhs, left, right, allowed):
    if left[0] != "op" or right[0] != "op":
        return None
    if norm_tree(left[2]) == norm_tree(right[2]):
        inner = h_proof_between(eq1_vars, eq1_lhs, eq1_rhs, left[1], right[1], allowed)
        if inner is not None:
            return f"congrArg (fun t : G => t ◇ {tree_to_lean(left[2])}) ({inner})"
    if norm_tree(left[1]) == norm_tree(right[1]):
        inner = h_proof_between(eq1_vars, eq1_lhs, eq1_rhs, left[2], right[2], allowed)
        if inner is not None:
            return f"congrArg (fun t : G => {tree_to_lean(left[1])} ◇ t) ({inner})"
    return None


def try_one_congr_calc_chain(problem, eq1_text, eq2_text, judge):
    log("strategy true_one_congr_calc_chain: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    eq1_vars, eq1_lhs, eq1_rhs = parse_equation(eq1_text)
    pool = term_pool(eq2_vars, goal_lhs, goal_rhs)
    if len(pool) > MAX_DIRECT_SUBSTITUTION_COMPOUND_POOL_SIZE:
        pool = pool[:MAX_DIRECT_SUBSTITUTION_COMPOUND_POOL_SIZE]
    allowed = {norm_tree(t) for t in pool}
    candidates = []
    seen = set()

    for mid, proof1 in h_edges_from_left(eq1_vars, eq1_lhs, eq1_rhs, goal_lhs, pool, allowed):
        proof2 = congr_arg_between(eq1_vars, eq1_lhs, eq1_rhs, mid, goal_rhs, allowed)
        if proof2 is None:
            continue
        proof = (
            f"intro {' '.join(eq2_vars)}\n"
            "calc\n"
            f"  {tree_to_lean(goal_lhs)} = {tree_to_lean(mid)} := {proof1}\n"
            f"  _ = {tree_to_lean(goal_rhs)} := {proof2}"
        )
        if proof in seen:
            continue
        seen.add(proof)
        candidates.append(proof)
        if len(candidates) >= MAX_ONE_CONGR_CALC_CANDIDATES:
            break

    log(f"strategy true_one_congr_calc_chain: candidates={len(candidates)}")
    calls = 0
    for proof in candidates[:MAX_ONE_CONGR_CALC_JUDGE_CALLS]:
        calls += 1
        if try_judged_true(problem, proof, judge, "true_one_congr_calc_chain"):
            log(
                "strategy true_one_congr_calc_chain: "
                f"accepted {problem.get('id', '?')}; judge_calls={calls}"
            )
            return True
    log(f"strategy true_one_congr_calc_chain: judge_calls={calls}; no acceptance")
    return False


def combo_side_terms(eq1_text, eq2_vars):
    eq1_vars, eq1_lhs, eq1_rhs = parse_equation(eq1_text)
    term_vars = [("var", v) for v in eq2_vars]
    for combo in product(term_vars, repeat=len(eq1_vars)):
        mapping = dict(zip(eq1_vars, combo))
        args = " ".join(tree_to_lean(t) for t in combo)
        yield eq1_vars, combo, args, subst_tree(eq1_lhs, mapping), subst_tree(eq1_rhs, mapping)


def try_simple_constancy(problem, eq1_text, eq2_text, judge):
    log("strategy true_simple_constancy: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    target_l = norm_tree(goal_lhs)
    target_r = norm_tree(goal_rhs)
    eq1_vars, raw_lhs, raw_rhs = parse_equation(eq1_text)
    lhs_vars = set(re.findall(r"\b([a-z])\b", eq1_text.split("=", 1)[0]))
    rhs_vars = set(re.findall(r"\b([a-z])\b", eq1_text.split("=", 1)[1]))
    calls = 0

    for pos, var in enumerate(eq1_vars):
        lhs_only = var in lhs_vars and var not in rhs_vars
        rhs_only = var in rhs_vars and var not in lhs_vars
        if not lhs_only and not rhs_only:
            continue

        combos = list(combo_side_terms(eq1_text, eq2_vars))
        for _, combo_a, args_a, lhs_a, rhs_a in combos:
            for _, combo_b, args_b, lhs_b, rhs_b in combos:
                if all(i == pos or norm_tree(combo_a[i]) == norm_tree(combo_b[i]) for i in range(len(eq1_vars))):
                    if norm_tree(combo_a[pos]) == norm_tree(combo_b[pos]):
                        continue
                    if rhs_only:
                        left, right = rhs_a, rhs_b
                        term = f"(h {args_a}).symm.trans (h {args_b})"
                    else:
                        left, right = lhs_a, lhs_b
                        term = f"(h {args_a}).trans (h {args_b}).symm"

                    if norm_tree(left) == target_l and norm_tree(right) == target_r:
                        proof_term = term
                    elif norm_tree(left) == target_r and norm_tree(right) == target_l:
                        proof_term = f"({term}).symm"
                    else:
                        continue

                    proof = f"intro {' '.join(eq2_vars)}\nexact {proof_term}"
                    calls += 1
                    if try_judged_true(problem, proof, judge, "true_simple_constancy"):
                        return True
                    if calls >= MAX_TRUE_JUDGE_CALLS_PER_STRATEGY:
                        return False
    return False


def constancy_proof_for(eq1_vars, side_term, lhs_only, target_l, target_r, allowed, default_term):
    m_a = match_pattern(side_term, target_l, {})
    m_b = match_pattern(side_term, target_r, {})
    if m_a is None or m_b is None:
        return None
    if not mapping_uses_term_pool(m_a, allowed) or not mapping_uses_term_pool(m_b, allowed):
        return None

    diff_positions = []
    args_a = []
    args_b = []
    for i, v in enumerate(eq1_vars):
        a = m_a.get(v, default_term)
        b = m_b.get(v, default_term)
        args_a.append(tree_to_lean(a))
        args_b.append(tree_to_lean(b))
        if norm_tree(a) != norm_tree(b):
            diff_positions.append(i)

    if len(diff_positions) != 1:
        return None
    args_a = " ".join(args_a)
    args_b = " ".join(args_b)
    if lhs_only:
        return f"(h {args_a}).trans (h {args_b}).symm", diff_positions[0]
    return f"(h {args_a}).symm.trans (h {args_b})", diff_positions[0]


def congr_arg_candidate(eq1_vars, side_term, lhs_only, goal_lhs, goal_rhs, allowed, default_term):
    if goal_lhs[0] != "op" or goal_rhs[0] != "op":
        return None
    if norm_tree(goal_lhs[2]) == norm_tree(goal_rhs[2]):
        proof = constancy_proof_for(
            eq1_vars, side_term, lhs_only, goal_lhs[1], goal_rhs[1], allowed, default_term
        )
        if proof is not None:
            return f"congr_arg (fun t : G => t ◇ {tree_to_lean(goal_lhs[2])}) ({proof[0]})"
    if norm_tree(goal_lhs[1]) == norm_tree(goal_rhs[1]):
        proof = constancy_proof_for(
            eq1_vars, side_term, lhs_only, goal_lhs[2], goal_rhs[2], allowed, default_term
        )
        if proof is not None:
            return f"congr_arg (fun t : G => {tree_to_lean(goal_lhs[1])} ◇ t) ({proof[0]})"
    return None


def try_constancy_term_pool(problem, eq1_text, eq2_text, judge):
    log("strategy true_constancy_term_pool: start")
    eq2_vars, goal_lhs, goal_rhs = parse_equation(eq2_text)
    eq1_vars, eq1_lhs, eq1_rhs = parse_equation(eq1_text)
    lhs_vars = set(re.findall(r"\b([a-z])\b", eq1_text.split("=", 1)[0]))
    rhs_vars = set(re.findall(r"\b([a-z])\b", eq1_text.split("=", 1)[1]))
    pool = term_pool(eq2_vars)
    if not pool:
        return False
    default_term = pool[0]
    allowed = {norm_tree(t) for t in pool}
    candidates = []
    seen = set()

    def add_candidate(proof_term, kind):
        if proof_term is None:
            return
        key = (kind, proof_term)
        if key in seen or len(candidates) >= MAX_TERM_POOL_CONSTANCY_CANDIDATES:
            return
        seen.add(key)
        candidates.append((proof_term, kind))

    for pos, var in enumerate(eq1_vars):
        lhs_only = var in lhs_vars and var not in rhs_vars
        rhs_only = var in rhs_vars and var not in lhs_vars
        if not lhs_only and not rhs_only:
            continue
        side_term = eq1_lhs if lhs_only else eq1_rhs

        direct = constancy_proof_for(
            eq1_vars, side_term, lhs_only, goal_lhs, goal_rhs, allowed, default_term
        )
        if direct is not None and direct[1] == pos:
            add_candidate(direct[0], "direct")
        direct_rev = constancy_proof_for(
            eq1_vars, side_term, lhs_only, goal_rhs, goal_lhs, allowed, default_term
        )
        if direct_rev is not None and direct_rev[1] == pos:
            add_candidate(f"({direct_rev[0]}).symm", "direct")

        add_candidate(
            congr_arg_candidate(
                eq1_vars, side_term, lhs_only, goal_lhs, goal_rhs, allowed, default_term
            ),
            "congr_arg",
        )
        rev = congr_arg_candidate(
            eq1_vars, side_term, lhs_only, goal_rhs, goal_lhs, allowed, default_term
        )
        if rev is not None:
            add_candidate(f"({rev}).symm", "congr_arg")

    log(f"strategy true_constancy_term_pool: candidates={len(candidates)}")
    calls = 0
    for proof_term, kind in candidates[:MAX_TERM_POOL_CONSTANCY_JUDGE_CALLS]:
        proof = f"intro {' '.join(eq2_vars)}\nexact {proof_term}"
        calls += 1
        if try_judged_true(problem, proof, judge, "true_constancy_term_pool"):
            log(f"strategy true_constancy_term_pool: accepted {kind}; judge_calls={calls}")
            return True
    log(f"strategy true_constancy_term_pool: judge_calls={calls}; no acceptance")
    return False


def run_true_strategies(problem, eq1_text, eq2_text, judge):
    strategies = [
        try_singleton,
        try_direct_substitution,
        try_direct_substitution_compound,
        try_calc_chain,
        try_one_congr_calc_chain,
        try_simple_constancy,
        try_constancy_term_pool,
    ]
    for strategy in strategies:
        if strategy(problem, eq1_text, eq2_text, judge):
            log(f"accepted strategy: {strategy.__name__}")
            return True
    return False


# -- Main ------------------------------------------------------------------

def main():
    startup = read_message()
    problem = startup["problem"]
    problem["equation1"] = normalize_op_to_diamond(problem["equation1"])
    problem["equation2"] = normalize_op_to_diamond(problem["equation2"])
    eq1_text = problem["equation1"]
    eq2_text = problem["equation2"]
    problem_id = problem.get("id", "?")
    log(f"problem {problem_id}: Equation{problem.get('eq1_id')} -> Equation{problem.get('eq2_id')}")
    judge = Judge()

    false_deadline = time.monotonic() + FALSE_SEARCH_SECONDS
    try:
        n, table, strategy, tested = find_counterexample(eq1_text, eq2_text, false_deadline)
    except TimeoutError:
        n, table, strategy, tested = None, None, "false_search_timeout", 0
        log("strategy false_search: timeout")

    if n is not None:
        sat1, sat2 = verify_counterexample(eq1_text, eq2_text, n, table)
        log(f"strategy {strategy}: local verify hypothesis={sat1} goal={sat2}")
        if sat1 and not sat2:
            result = judge.check("false", make_false_code(problem, n, table), strategy)
            if result.get("status") == "accepted":
                log(f"accepted strategy: {strategy}; tested_tables={tested}; judge_calls={judge.calls}")
                return
        else:
            log(f"strategy {strategy}: rejected locally despite search hit")

    if run_true_strategies(problem, eq1_text, eq2_text, judge):
        log(f"problem {problem_id}: solved; judge_calls={judge.calls}")
        return

    log(f"problem {problem_id}: no accepted certificate; judge_calls={judge.calls}; last_false_strategy={strategy}")
    if judge.calls == 0:
        result = final_reject_probe(problem, judge)
        log(f"problem {problem_id}: final_reject_probe result={result.get('status')}; judge_calls={judge.calls}")


if __name__ == "__main__":
    main()
