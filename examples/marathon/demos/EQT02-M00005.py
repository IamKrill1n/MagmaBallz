#!/usr/bin/env python3
"""
WILL v1 — Riemann Labs SAIR Stage 2 Marathon Solver
═════════════════════════════════════════════════════════════════
Weak-model In-context Lean Learner

  PROFESSOR LAMBEAU
    The problem on the board took us two years to prove. It's
    in the proceedings of Stockholm. Whoever solved it —

  WILL
    (under his breath, mopping)
    Yeah, well. It's not that hard.

  LAMBEAU
    This is a Lean 4 proof of an equational implication over
    magmas. It took the ETP community two hundred contributors.

  WILL
    (writes on the board)
    intro x y z
    have h1 := h x x x
    have h2 := h (x ◇ x) x x
    grind

  — paraphrased from a movie about an MIT janitor who could see it

─────────────────────────────────────────────────────────────

Good WILL Hunting is a marathon solver for the SAIR Mathematics
Distillation Challenge. ~51 KB. No oracle. No hardcoded proofs. No
22-million-entry bitmatrix. Just a careful eye, a few deterministic
patterns, a structural prior, and an LLM in the back room with a
problem-specific instruction sheet for when the chalkboard runs out.

The name unpacks twice. Once for the architecture:

  Weak-model     — built to make a small open-source model competitive,
                   not to throw a frontier model at the problem
  In-context     — all knowledge is in the prompt and the run-state cache,
                   nothing is fine-tuned, nothing is pre-loaded
  Lean           — the verifier; the only judge that matters
  Learner        — the marathon-mode few-shot adapts mid-run, learning
                   the shape of THIS competition's problems as it goes

And once for the philosophy: the kid solving the chalkboard problem
without a graduate degree.

Companion to EULER (Solo track):
  EULER carries the library. Knows the field. Cites everyone.
  WILL walks past the board, glances up, writes the answer in the margin.

  Most magma problems don't need a genius.
  They need someone organized enough to try the cheap thing first.

The competition rewards generalizable, transferable strategies. WILL is
built around the named techniques the Equational Theories Project itself
uses — Greedy Extension, Fresh Generator, Finite Invertibility, Free
Magma, Direct Sum, Aristotle, Constancy — and tries each one in cost
order before reaching for the LLM. The transferable skill is the
ordering, not any one technique.

Architecture:
  Pass 1: Counterexample search
            — exhaustive Fin 2-3
            — then structural shapes (projections, modular, cyclic, affine)
            — then bounded random search for Fin 4-5
            — all deadline-bounded
  Pass 2: Structural proof search
            — exact match, .symm, .symm.trans chains
            — constancy collapse (h with a free variable)
            — constant-magma collapse
  Pass 3: Tactic battery
            — solved_patterns cache from earlier problems goes first
            — then grind, simp, have+grind ladder, convert, reversed-h
  Pass 4: LLM with structurally-branched, problem-specific prompt
            — structural_precheck() computes a verdict prior + strategy
            — build_system_prompt() returns ONE strategy's instructions,
              not a menu (per Cazares 2026 findings)
            — in-run few-shot examples (last 3 accepted proofs)
            — one-shot .symm preflight repair on direction-flip errors

Less Is More refactor (Cazares 2026, arXiv:2604.18897):

  WILL's Pass 4 prompt is informed directly by the "Less Is More" paper,
  which documented a saturation region for static single-prompt approaches
  at ~71-79% balanced accuracy and showed three actionable findings:

    1. Ordering matters more than content (AN45c vs AN38: +7.5pp purely
       from moving the trivial-magma check to before the CE table).
    2. Merging complementary strategies in one prompt produces AVERAGE,
       not MAXIMUM performance (AN38 = arithmetic mean of AN35 + AN35b).
    3. Pure structural classification (Heath's distilled-rules-12)
       scored 80% on hard2 with zero algebraic reasoning — the
       "router hypothesis."

  WILL's response:
    • structural_precheck() implements the router hypothesis. Six
      strategy classes (constancy, aristotle, have_grind, grind_alone,
      finite_ce, structural_ce) chosen by syntactic features alone.
    • build_system_prompt() returns a strategy-specific prompt, not
      a monolithic one. ~200-400 tokens per call vs. v0's ~2,100.
    • Inside each branch, the highest-leverage decision comes first
      and the output format spec comes LAST (lost-in-the-middle:
      reasoning at start/end, format at end where attention is weaker).

Marathon-mode features:
  • solved_patterns cache  — accepted proof bodies from earlier problems
    prepended to the tactic battery on later ones; the run learns its own
    local solution style.
  • few-shot examples       — last 3 accepted (problem, proof) pairs
    injected into the LLM context for in-run cognitive transfer.
  • adaptive budget         — difficulty triage drives per-problem spend:
    easy / medium / hard at 0.5× / 1.0× / 1.5× of the per-problem mean.
  • robust orchestration    — each problem wrapped in try/except so one
    crashed problem cannot kill the batch.

Attribution — techniques borrowed from the SAIR Contributor Network:
  • twophase  (SAIR Official)  — analyze-then-implement LLM structure
                                 + temperature escalation, in Pass 4
  • fewshot   (SAIR Official)  — in-run example cache shaped the
                                 marathon design directly
  • opnorm    (SAIR Official)  — cache-first tactic ordering convinced
                                 me Pass 3's cache-priority was worth it
  • back1sair (community)      — temperature escalation pattern
                                 (0.0 → 0.3 → 0.6) ported into Pass 4

External:
  • Cazares (2026), "Less Is More: Cognitive Load and the Single-Prompt
    Ceiling in LLM Mathematical Reasoning" (arXiv:2604.18897)
    — the router hypothesis and the saturation-region findings drive
      Pass 4's branched-prompt architecture
  • Terence Tao et al., The Equational Theories Project (arXiv:2512.07087)
    — Pass 4 prompt's named-techniques section maps to the ETP's
      ManuallyProved classification (Greedy Extension, Free Magma,
      Finite Invertibility, Direct Sum, Fresh Generator)
  • Axiom Math / AXLE proof verification engine (Carina Hong et al.)
    — the 5,000× verification speedup is what made this architecture
      feasible without ever leaving a chalkboard-sized footprint

Known limitations:
  • No Vampire / Mace4 / Prover9 integration. The ETP itself was solved
    largely by ATPs in waves; not having an ATP in the loop is the
    biggest single capability gap. v2 direction if the judge env allows.

  How do you like them apples.

═══════════════════════════════════════════════════════════════════════
PUBLIC DESCRIPTION — SAIR Stage 2 Submission
═══════════════════════════════════════════════════════════════════════

  Solver:      Good WILL Hunting v1 (Marathon track)
  Team:        Riemann Labs
  Author:      Christopher Brock
  Companion:   EULER Phi v7 (Solo track)

  EULER and WILL are siblings — same team, opposite philosophies.

    EULER is the professor. 400KB of oracle bitmatrix, 501 Aristotle-
    verified proofs, 1430 pre-computed counterexamples, BFS tree-rewrite
    engines, 13 structural proof strategies. It carries the library. It
    cites everyone. It scores 99.8% on the practice set because it has
    already seen the answers.

    WILL is the janitor. 51KB. No lookup tables. No hardcoded proofs.
    Four deterministic passes (CE search, structural proof, tactic
    battery, LLM) and a branched prompt that routes to one of six
    strategy-specific instruction sheets based on syntactic features
    alone. It learns mid-run: successful proofs from early problems
    seed the tactic cache for later ones, and few-shot examples give
    the LLM context from this competition's problems, not a training
    corpus.

    EULER dominates when the test set overlaps with training data.
    WILL dominates when it doesn't.

  The transferable contribution is the prompt architecture:
    • structural_precheck() — a pure syntactic router that classifies
      problems into 6 strategy classes with no algebraic reasoning
    • build_system_prompt() — returns ONE strategy's instructions per
      LLM call, not a menu of competing patterns (informed by the
      Cazares 2026 "Less Is More" findings on single-prompt ceilings)
    • Argument construction algorithm — systematic goal-subterm
      instantiation for the HAVE+GRIND pattern, the dominant winner
      in Aristotle-proved equational implications

  The name: Weak-model In-context Lean Learner.
  The reference: a movie about seeing the answer without the degree.
"""

import json, random, re, sys, time
from itertools import product as iproduct

# ═══════════════════════════════════════════════════════════════════════
# JUDGE PROTOCOL
# ═══════════════════════════════════════════════════════════════════════

def read_msg():
    line = sys.stdin.readline()
    if not line: sys.exit(0)
    return json.loads(line.strip())

def send_msg(msg):
    print(json.dumps(msg), flush=True)

def call_judge(verdict, code):
    send_msg({"call": "judge", "verdict": verdict, "code": code})
    return read_msg()

def call_llm(context):
    send_msg({"call": "llm", "context": context})
    return read_msg()

# ═══════════════════════════════════════════════════════════════════════
# LEAN CODE GENERATION
# ═══════════════════════════════════════════════════════════════════════

def lean_true(body, high_hb=False):
    hb = "set_option maxHeartbeats 12800000 in\n" if high_hb else ""
    indented = "\n".join("  " + l if l.strip() else "" for l in body.strip().split("\n"))
    return f"import JudgeProblem\n\n{hb}def submission : Goal := by\n  intro G _ h\n{indented}\n"

def lean_false(n, table):
    return (
        "import JudgeProblem\nimport JudgeDecide.DecideBang\n"
        "import JudgeFinOp.MemoFinOp\nopen MemoFinOp\n\n"
        f"def submission : Goal := by\n"
        f"  let m : Magma (Fin {n}) := {{\n"
        f"    op := finOpTable \"{json.dumps(table)}\"\n"
        f"  }}\n  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n"
    )

# ═══════════════════════════════════════════════════════════════════════
# EQUATION UTILITIES
# ═══════════════════════════════════════════════════════════════════════

def norm(text): return text.replace("*", "◇") if isinstance(text, str) else text

def variables_of(text):
    seen, out = set(), []
    for v in re.findall(r"\b([a-z])\b", text):
        if v not in seen: seen.add(v); out.append(v)
    return out

def analyse(eq):
    lhs, rhs = [s.strip() for s in eq.split("=", 1)]
    lv = set(re.findall(r"\b([a-z])\b", lhs))
    rv = set(re.findall(r"\b([a-z])\b", rhs))
    return {"lhs": lhs, "rhs": rhs, "lhs_vars": lv, "rhs_vars": rv,
            "lhs_only": lv - rv, "rhs_only": rv - lv,
            "op_count": eq.count("◇") + eq.count("*")}

def _parse_expr(text, var_set):
    text = text.strip()
    while len(text) >= 2 and text[0] == "(" and text[-1] == ")":
        depth, ok = 0, True
        for i, c in enumerate(text):
            depth += (c == "(") - (c == ")")
            if depth == 0 and i < len(text) - 1: ok = False; break
        if ok: text = text[1:-1].strip()
        else: break
    depth, op_pos = 0, -1
    for i, c in enumerate(text):
        depth += (c == "(") - (c == ")")
        if c == "◇" and depth == 0: op_pos = i
    if op_pos >= 0:
        left = _parse_expr(text[:op_pos], var_set)
        right = _parse_expr(text[op_pos+1:], var_set)
        return lambda env, l=left, r=right: env["op"](l(env), r(env))
    text = text.strip()
    if text in var_set:
        return lambda env, v=text: env[v]
    raise ValueError(f"parse: {text}")

def compile_eq(text):
    vs = variables_of(text)
    vs_set = set(vs)
    lhs_str, rhs_str = text.split("=", 1)
    return vs, _parse_expr(lhs_str, vs_set), _parse_expr(rhs_str, vs_set)

def check_eq(vs, lhs_fn, rhs_fn, n, op):
    for combo in iproduct(range(n), repeat=len(vs)):
        env = {"op": op}
        for v, val in zip(vs, combo): env[v] = val
        if lhs_fn(env) != rhs_fn(env): return False
    return True

# ═══════════════════════════════════════════════════════════════════════
# PASS 1: COUNTEREXAMPLE SEARCH (deadline-bounded, Fin 2-5)
# ═══════════════════════════════════════════════════════════════════════

def find_ce(eq1, eq2, max_n=5, deadline=None):
    """Exhaustive CE search on small magmas, supplemented by bounded random
    search on larger magmas. Deadline-bounded throughout.

    Exhaustive guarantee: every Fin 2 table (16) and every Fin 3 table
    (~20K) is checked if the deadline allows. Random supplement covers
    Fin 4-5 where exhaustive is intractable.

    Returns (n, flat_table) or (None, None)."""
    try:
        vs1, l1, r1 = compile_eq(eq1)
        vs2, l2, r2 = compile_eq(eq2)
    except Exception:
        return None, None

    # Phase A: exhaustive enumeration up to the largest tractable size
    for n in range(2, min(max_n, 3) + 1):
        if deadline and time.time() > deadline:
            return None, None
        total_tables = n ** (n * n)
        check_interval = max(1, min(10000, total_tables // 100))
        for enc in range(total_tables):
            if deadline and enc % check_interval == 0 and time.time() > deadline:
                return None, None
            table = [(enc // (n ** k)) % n for k in range(n * n)]
            op = lambda a, b, t=table, sz=n: t[a * sz + b]
            if check_eq(vs1, l1, r1, n, op):
                if not check_eq(vs2, l2, r2, n, op):
                    return n, table

    # Phase B: structural shapes for n = 3..max_n. Cheap, high hit-rate.
    for n in range(3, max_n + 1):
        if deadline and time.time() > deadline:
            return None, None
        for shape in _structural_shapes(n):
            op = lambda a, b, t=shape, sz=n: t[a * sz + b]
            if check_eq(vs1, l1, r1, n, op):
                if not check_eq(vs2, l2, r2, n, op):
                    return n, shape

    # Phase C: bounded random search on Fin 4-5
    for n in range(4, max_n + 1):
        if deadline and time.time() > deadline:
            return None, None
        # Cap attempts; bail early if deadline nears
        max_attempts = 15000 if n == 4 else 5000
        for _ in range(max_attempts):
            if deadline and time.time() > deadline:
                return None, None
            table = [random.randint(0, n - 1) for _ in range(n * n)]
            op = lambda a, b, t=table, sz=n: t[a * sz + b]
            if check_eq(vs1, l1, r1, n, op):
                if not check_eq(vs2, l2, r2, n, op):
                    return n, table
    return None, None


def _structural_shapes(n):
    """Yield flat tables of common counterexample shapes on Fin n."""
    # Constant magmas
    for c in range(n):
        yield [c] * (n * n)
    # Left projection: i ◇ j = i
    yield [i for i in range(n) for _ in range(n)]
    # Right projection: i ◇ j = j
    yield [j for _ in range(n) for j in range(n)]
    # Addition mod n
    yield [(i + j) % n for i in range(n) for j in range(n)]
    # Subtraction mod n
    yield [(i - j) % n for i in range(n) for j in range(n)]
    # Multiplication mod n
    yield [(i * j) % n for i in range(n) for j in range(n)]
    # Cyclic successor: i ◇ j = (i + 1) mod n
    yield [(i + 1) % n for i in range(n) for _ in range(n)]
    # Anti-cyclic: i ◇ j = (j + 1) mod n
    yield [(j + 1) % n for _ in range(n) for j in range(n)]
    # XOR-style for prime n (works as mul-add)
    if n >= 2:
        yield [(i + 2 * j) % n for i in range(n) for j in range(n)]
        yield [(2 * i + j) % n for i in range(n) for j in range(n)]

# ═══════════════════════════════════════════════════════════════════════
# PASS 2: STRUCTURAL PROOF
# ═══════════════════════════════════════════════════════════════════════

def _subst(expr, var_map):
    """Substitute variables in an expression string. Long names first to
    avoid partial-match bugs (though we use single-letter vars, this is
    defensive)."""
    result = expr
    for v, rep in sorted(var_map.items(), key=lambda x: -len(x[0])):
        result = re.sub(r'\b' + v + r'\b', rep, result)
    return result

def find_proof(eq1, eq2):
    """Structural proof search: exact, symm, .symm.trans chains, constancy,
    and constant-magma collapse."""
    v1 = variables_of(eq1)
    v2 = variables_of(eq2)
    info1 = analyse(eq1)
    info2 = analyse(eq2)
    intro = "intro " + " ".join(v2) if v2 else "intro"
    lhs1, rhs1 = info1["lhs"], info1["rhs"]
    lhs2, rhs2 = info2["lhs"], info2["rhs"]

    # Build argument pool from goal vars + compound terms
    atoms = v2[:4] if v2 else ["a"]
    compounds = [f"({a} ◇ {b})" for a in atoms[:3] for b in atoms[:3]]
    pool = list(atoms) + compounds[:6]
    nv1 = min(len(v1), 5)

    all_combos = list(iproduct(pool[:6], repeat=nv1))
    if len(v1) > nv1:
        all_combos = [c + (atoms[0],) * (len(v1) - nv1) for c in all_combos]
    combos = list(dict.fromkeys(all_combos))[:80]

    # exact h <args> and .symm
    for combo in combos:
        args = list(combo[:len(v1)])
        var_map = {v1[i]: args[i] for i in range(len(v1))}
        il = _subst(lhs1, var_map).strip()
        ir = _subst(rhs1, var_map).strip()
        if il == lhs2 and ir == rhs2:
            return f"{intro}\n  exact h {' '.join(args)}"
        if ir == lhs2 and il == rhs2:
            return f"{intro}\n  exact (h {' '.join(args)}).symm"

    # .symm.trans chains
    inst_cache = {}
    for combo in combos[:30]:
        args = list(combo[:len(v1)])
        var_map = {v1[i]: args[i] for i in range(len(v1))}
        il = _subst(lhs1, var_map).strip()
        ir = _subst(rhs1, var_map).strip()
        inst_cache[tuple(args)] = (il, ir)

    items = list(inst_cache.items())
    for i, (a1, (il1, ir1)) in enumerate(items):
        for j, (a2, (il2, ir2)) in enumerate(items):
            if i == j: continue
            if il1 == il2:
                if ir1 == lhs2 and ir2 == rhs2:
                    return (f"{intro}\n  exact (h {' '.join(a1)}).symm.trans "
                            f"(h {' '.join(a2)})")
                if ir2 == lhs2 and ir1 == rhs2:
                    return (f"{intro}\n  exact (h {' '.join(a2)}).symm.trans "
                            f"(h {' '.join(a1)})")

    # Constancy: h with a free variable forces a singleton
    if info1["lhs_only"] and len(lhs1.strip()) == 1:
        filler = " ".join(["a"] * (len(v1) - 1)) if len(v1) > 1 else ""
        filler_with_space = f" {filler}" if filler else ""
        return (f"{intro}\n"
                f"  have singleton : ∀ (a b : G), a = b := "
                f"fun a b => (h a{filler_with_space}).trans (h b{filler_with_space}).symm\n"
                f"  exact singleton ({lhs2}) ({rhs2})")

    if info1["rhs_only"] and len(rhs1.strip()) == 1:
        filler = " ".join(["a"] * (len(v1) - 1)) if len(v1) > 1 else ""
        filler_with_space = f" {filler}" if filler else ""
        return (f"{intro}\n"
                f"  have singleton : ∀ (a b : G), a = b := "
                f"fun a b => (h a{filler_with_space}).symm.trans (h b{filler_with_space})\n"
                f"  exact singleton ({lhs2}) ({rhs2})")

    # Constant-magma collapse: substitute free→bound and check match.
    # FIX from v8 review: emit the substituted args explicitly so the
    # resulting Lean code typechecks. The collapse map tells us how to
    # specialize h, not which goal vars to pass.
    free = info1["lhs_only"] | info1["rhs_only"]
    bound = [v for v in v1 if v not in free]
    if bound and free:
        for fv in sorted(free):
            for bv in bound:
                # Build args list for h: replace fv-position with bv's value
                # in the goal's variable space.
                collapsed = _subst(eq1, {fv: bv})
                c_info = analyse(collapsed)
                if c_info["lhs"] == lhs2 and c_info["rhs"] == rhs2:
                    # h takes original-v1 args; supply bv (a goal var) where fv was
                    args = [bv if v == fv else v for v in v1]
                    # All args must be in v2 — if not, this collapse can't be
                    # expressed with the goal's variables alone
                    if all(a in v2 or a == bv for a in args):
                        return f"{intro}\n  exact h {' '.join(args)}"

    return None

# ═══════════════════════════════════════════════════════════════════════
# PASS 3: TACTIC BATTERY (with solved_patterns cache injection)
# ═══════════════════════════════════════════════════════════════════════

def build_tactics(eq1, eq2, cached_patterns=None):
    """Generate ranked tactic candidates. Cached patterns from earlier
    marathon problems get priority — if a pattern worked once in this
    run, it's likely to work again on similar problems."""
    v1 = variables_of(eq1)
    v2 = variables_of(eq2)
    intro = "intro " + " ".join(v2) if v2 else "intro"
    info1 = analyse(eq1)
    tactics = []

    # Marathon priority: cached patterns first (lightly re-templated)
    if cached_patterns:
        for pattern in cached_patterns[:5]:
            # Patterns are stored as raw proof bodies. Re-template the
            # intro line to match this problem's variables.
            body = re.sub(r"^\s*intro[^\n]*\n", "", pattern)
            tactics.append(f"{intro}\n{body}")

    # T1: grind alone
    tactics.append(f"{intro}\n  grind")

    # T2: simp only [h]
    tactics.append(f"{intro}\n  simp only [h]")

    # T3: have + grind (the big winner)
    if v2:
        a = v2[0]
        tactics.append(f"{intro}\n  have h1 := h {' '.join([a]*len(v1))}\n  grind")
        args = [f"({a} ◇ {a})"] + [a] * (len(v1) - 1)
        tactics.append(f"{intro}\n  have h1 := h {' '.join(args)}\n  grind")

    # T4: Two haves + grind
    if v2:
        a = v2[0]
        b = v2[1] if len(v2) > 1 else a
        h1_args = " ".join([a] * len(v1))
        h2_args = " ".join(([b] + [a] * (len(v1) - 1))[:len(v1)])
        tactics.append(f"{intro}\n  have h1 := h {h1_args}\n  have h2 := h {h2_args}\n  grind")
        h2c_args = " ".join([f"({a} ◇ {a})"] + [a] * (len(v1) - 1))
        tactics.append(f"{intro}\n  have h1 := h {h1_args}\n  have h2 := h {h2c_args}\n  grind")

    # T5: Three haves + grind
    if v2:
        a = v2[0]
        h1 = " ".join([a] * len(v1))
        h2 = " ".join([f"({a} ◇ {a})"] + [a] * (len(v1) - 1))
        h3 = " ".join([a, f"({a} ◇ {a})"] + [a] * (len(v1) - 2)) if len(v1) > 1 else h1
        tactics.append(
            f"{intro}\n  have h1 := h {h1}\n  have h2 := h {h2}\n  have h3 := h {h3}\n  grind")

    # T6: Reversed hypothesis + grind
    quant = " ".join(f"({v} : G)" for v in v1)
    rhs1, lhs1 = info1["rhs"], info1["lhs"]
    tactics.append(
        f"{intro}\n  have h' : ∀ {quant}, {rhs1} = {lhs1} := "
        f"fun {' '.join(v1)} => (h {' '.join(v1)}).symm\n  grind")

    # T7: convert pattern
    if v2 and len(v1) > 1:
        explicit = " ".join(v2[:1])
        wildcards = " _" * (len(v1) - 1)
        tactics.append(f"{intro}\n  convert h {explicit}{wildcards} using 1\n  grind")

    return tactics

# ═══════════════════════════════════════════════════════════════════════
# PASS 4: LLM WITH PATTERN-AWARE PROMPT + FEW-SHOT EXAMPLES
# ═══════════════════════════════════════════════════════════════════════

# ═══════════════════════════════════════════════════════════════════════
# DIFF 1 + DIFF 3 (Less Is More): branched system prompt builder.
#
# The monolithic v5 prompt was ~2,100 tokens. The Cazares (2026) paper
# documents a saturation region at ~71-79% balanced accuracy for static
# single-prompt approaches. Two of the paper's findings drive this design:
#
#   • Ordering matters more than content (AN45c vs AN38: +7.5pp purely
#     from moving the trivial-magma check before the CE table).
#   • Merging complementary strategies in one prompt produces AVERAGE,
#     not MAXIMUM, performance (AN38 = arithmetic mean of AN35 + AN35b).
#
# Response: branch the prompt by the structural precheck's primary
# strategy. The model sees ONE strategy, not a menu, and the highest-
# leverage decision comes first.
# ═══════════════════════════════════════════════════════════════════════

# The output format spec, kept as a constant so all branches share it.
# Placed at the END of each prompt — "lost in the middle" research shows
# attention is weakest in the middle and strongest at start/end. The
# reasoning rule goes first; the format goes last.
_OUTPUT_SPEC = """RESPONSE FORMAT
Output ONLY valid JSON. No markdown, no commentary, no chain-of-thought.

  TRUE:  {"verdict":"true","proof":"<tactics after intro G _ h>"}
  FALSE: {"verdict":"false","n":<size>,"table":[flat row-major table]}"""


def _prompt_constancy():
    """Branch: h has a free variable. CONSTANCY pattern, no menu."""
    return """h has a FREE VARIABLE — appears on only one side.

This is the single strongest True signal in equational implication
over magmas. h forces all elements of the magma equal; therefore
ANY goal is vacuously true. Use the CONSTANCY pattern exclusively.

CONSTANCY pattern (use EXPLICIT filler args, never underscores —
Lean does not infer those positions):

  intro x y
  have s : ∀ (a b : G), a = b :=
    fun a b => (h a a a).trans (h b a a).symm
  exact s _ _

Adapt the filler args to h's variable count:
  • 2-var h:    fun a b => (h a a).trans (h b a).symm
  • 3-var h:    fun a b => (h a a a).trans (h b a a).symm
  • 4-var h:    fun a b => (h a a a a).trans (h b a a a).symm

Do NOT attempt counterexample search. Do NOT use HAVE+GRIND.
The verdict is true; the only question is the proof shape.

""" + _OUTPUT_SPEC


def _prompt_aristotle():
    """Branch: h is single-variable. HAVE+GRIND with goal subterms."""
    return """h is a single-variable law (Aristotle family).

The dominant proof shape for this class is multiple instantiations
of h at goal subterms, then grind for congruence closure.

ARGUMENT CONSTRUCTION:
  STEP 1. List the goal's subterms.
          E.g. goal (x ◇ y) ◇ z = x ◇ (y ◇ z)
          → subterms {x, y, z, x◇y, y◇z, (x◇y)◇z, x◇(y◇z)}
  STEP 2. First instantiation: at one goal variable.
            have h1 := h x
  STEP 3. Second: at a compound goal subterm.
            have h2 := h (x ◇ y)
  STEP 4. Third: at a different compound subterm.
            have h3 := h (y ◇ z)
  STEP 5. grind.

Each `have` is a new equation grind can use for congruence closure.
2-5 haves usually suffice. If grind fails, ADD MORE.

EXAMPLE:
  intro x y z
  have h1 := h x
  have h2 := h (x ◇ y)
  have h3 := h (y ◇ z)
  grind

If grind fails, try:
  simp only [h]
  simp only [h, ← h]

""" + _OUTPUT_SPEC


def _prompt_have_grind():
    """Branch: default. HAVE+GRIND with goal subterms, full algorithm."""
    return """Use HAVE + GRIND with goal subterms as arguments.

This is the dominant winning pattern (~35% success rate). Each
`have` gives grind a new equation for congruence closure.

ARGUMENT CONSTRUCTION ALGORITHM:
  STEP 1. List the goal's subterms.
          If goal is (x ◇ y) ◇ z = x ◇ (y ◇ z), subterms are
          {x, y, z, x◇y, y◇z, (x◇y)◇z, x◇(y◇z)}.
  STEP 2. First have: all-same.
            have h1 := h x x x ...    (gives grind the diagonal)
  STEP 3. Second have: one position holds a compound subterm.
            have h2 := h (x ◇ y) x x ...
  STEP 4. Third have: a DIFFERENT position holds the subterm.
            have h3 := h x (x ◇ y) x ...
  STEP 5. Fourth have if needed: a SECOND subterm in some position.
            have h4 := h (y ◇ z) x x ...
  STEP 6. grind.

Do NOT use random variable permutations. Use GOAL SUBTERMS in
systematic positions. This is the difference between solving and
burning tokens.

If grind fails with "unsolved goals", ADD A HAVE with a goal subterm
not yet used. If you get "type mismatch", check h's variable order
positionally — h takes args in ITS OWN order, not the goal's.

Fallback shapes (in order):
  • exact h <args>                          (direct)
  • exact (h <args>).symm                   (reversed)
  • exact (h <args1>).symm.trans (h <args2>)  (midpoint match)
  • simp only [h]
  • simp only [h, ← h]
  • convert h <args using 1; grind

""" + _OUTPUT_SPEC


def _prompt_grind_alone():
    """Branch: h and goal have similar structure. Try grind first."""
    return """h and the goal have similar variable structure. The implication
likely closes via Lean's grind tactic alone or with a single
specialization of h.

PRIMARY ATTEMPT (try first):
  intro <goal vars>
  grind

If grind fails, escalate to:
  intro <goal vars>
  have h1 := h <goal vars>
  grind

If grind still fails, fall through to HAVE+GRIND with goal-subterm
arguments (the standard pattern — instantiate h at compound subterms
of the goal, then grind).

Do NOT reach for counterexamples first. Structural similarity here
is a strong True signal.

""" + _OUTPUT_SPEC


def _prompt_finite_ce():
    """Branch: goal has more vars than h, or other False signal."""
    return """The implication is likely FALSE. Goal asks for something h
cannot constrain — extra variables, deeper nesting, or structurally
incompatible shape.

COUNTEREXAMPLE PROTOCOL:
Counterexample = flat row-major operation table on Fin N.
  Fin 2: [a, b, c, d] means op(0,0)=a, op(0,1)=b, op(1,0)=c, op(1,1)=d.
  Fin 3: 9 entries. Fin 4: 16. Fin 5: 25.

The table must SATISFY h for all assignments AND VIOLATE goal for
at least one. The judge checks both with decideFin!.

SIZE SELECTION:
  • Fin 2: only for very weak h (idempotence, one ◇ op).
  • Fin 3: default. 19,683 raw tables but most are symmetric.
  • Fin 4: when h has 2+ free variables.
  • Fin 5: only after Fin 4 fails — when h needs a fresh generator.

STRUCTURAL SHAPES TO TRY FIRST:
  • Left projection:  i ◇ j = i              ([0,0,1,1] on Fin 2)
  • Right projection: i ◇ j = j              ([0,1,0,1] on Fin 2)
  • Constant:         i ◇ j = c              (one value everywhere)
  • Addition:         i ◇ j = (i+j) mod n
  • Subtraction:      i ◇ j = (i−j) mod n
  • Cyclic succ:      i ◇ j = (i+1) mod n
  • Bilinear:         i ◇ j = (a·i + b·j + c) mod p

Before emitting: verify h holds for every assignment in your
proposed table. Common mistake: forgetting that h's free variables
constrain ALL assignments, not just diagonal ones.

""" + _OUTPUT_SPEC


def _prompt_structural_ce():
    """Branch: same as finite_ce but with stronger 'h is weak' framing."""
    return """h is too weak (shallow / few operations) for what the goal asks.
This is a classic FALSE signal — the implication almost certainly
fails. Search for a small finite counterexample.

GO STRAIGHT TO STRUCTURAL SHAPES on Fin 2-3:

  Fin 2 candidates (16 total, all worth trying):
    [0,0,0,0]   constant 0
    [1,1,1,1]   constant 1
    [0,0,1,1]   left projection
    [0,1,0,1]   right projection
    [0,1,1,0]   addition mod 2
    [0,0,0,1]   AND-like
    [0,1,1,1]   OR-like

  Fin 3 candidates (try in this order):
    Addition mod 3:     i ◇ j = (i+j) mod 3
    Multiplication:     i ◇ j = (i*j) mod 3
    Left projection
    Right projection
    Subtraction mod 3

For each, verify h holds and goal fails. The first one that works
is your counterexample.

Do NOT attempt a proof. Do NOT use HAVE+GRIND. h is too weak.

""" + _OUTPUT_SPEC


# Strategy dispatch table — maps precheck strategy names to builders.
_PROMPT_BUILDERS = {
    "constancy":      _prompt_constancy,
    "aristotle":      _prompt_aristotle,
    "have_grind":     _prompt_have_grind,
    "grind_alone":    _prompt_grind_alone,
    "finite_ce":      _prompt_finite_ce,
    "structural_ce":  _prompt_structural_ce,
}


def build_system_prompt(precheck=None):
    """Diff 3 (Less Is More): branched prompt by structural precheck.

    Args:
      precheck: dict from structural_precheck(), or None for default.

    Returns: a complete system prompt as a string, sized ~600-1000 tokens
    (vs. ~2,100 for the v5 monolithic prompt). The model sees ONE strategy
    aligned with the structural analysis, not a menu of competing patterns.
    """
    if precheck is None:
        return _prompt_have_grind()  # safest default
    strategy = precheck.get("primary_strategy", "have_grind")
    builder = _PROMPT_BUILDERS.get(strategy, _prompt_have_grind)
    return builder()


# Legacy export for any caller that imports SYSTEM_PROMPT directly.
# The default (have_grind) is what an un-prechecked call gets.
SYSTEM_PROMPT = build_system_prompt(None)


def _subterms_of(expr):
    """Extract subterms for hint generation. Returns a set."""
    result = set()
    expr = expr.strip()
    result.add(expr)
    depth, op_pos = 0, -1
    for i, c in enumerate(expr):
        depth += (c == "(") - (c == ")")
        if c == "◇" and depth == 0: op_pos = i
    if op_pos >= 0:
        l, r = expr[:op_pos].strip(), expr[op_pos+1:].strip()
        if l.startswith("(") and l.endswith(")"): l = l[1:-1].strip()
        if r.startswith("(") and r.endswith(")"): r = r[1:-1].strip()
        result |= _subterms_of(l)
        result |= _subterms_of(r)
    return result


def _max_depth(expr):
    """Maximum nesting depth of ◇ operators in an expression.
    Used by the structural precheck — depth-heavy goals against
    shallow h are a False signal."""
    expr = expr.strip()
    if "◇" not in expr:
        return 0
    # Strip outermost balanced parens
    while len(expr) >= 2 and expr[0] == "(" and expr[-1] == ")":
        depth, ok = 0, True
        for i, c in enumerate(expr):
            depth += (c == "(") - (c == ")")
            if depth == 0 and i < len(expr) - 1:
                ok = False; break
        if ok: expr = expr[1:-1].strip()
        else: break
    depth, op_pos = 0, -1
    for i, c in enumerate(expr):
        depth += (c == "(") - (c == ")")
        if c == "◇" and depth == 0:
            op_pos = i
    if op_pos < 0:
        return 0
    left = expr[:op_pos].strip()
    right = expr[op_pos + 1:].strip()
    return 1 + max(_max_depth(left), _max_depth(right))


def structural_precheck(eq1, eq2):
    """Diff 2 (Less Is More): pure structural feature analysis before
    the LLM is invoked. Computes a verdict prior and a recommended
    strategy from syntactic features alone, with NO algebraic reasoning.

    This is WILL's version of Heath's "distilled-rules-12" structural
    classifier from the Cazares (2026) Contributor Network analysis,
    which scored 80% on hard2 with hand-coded syntactic rules.

    The signals here are deliberately weak — confidence values are
    calibrated against typical ETP problem distributions, not against
    a specific test set, so they generalize across splits.

    Returns:
      {
        "likely_verdict": "true" | "false" | "unknown",
        "confidence":      float in [0, 1],
        "primary_strategy": "constancy" | "aristotle" | "have_grind" |
                            "finite_ce" | "structural_ce" | "grind_alone",
        "free_vars":       sorted list of free vars in h,
        "rationale":       short human-readable string
      }
    """
    info1 = analyse(eq1)
    info2 = analyse(eq2)
    v1 = variables_of(eq1)
    v2 = variables_of(eq2)

    free = info1["lhs_only"] | info1["rhs_only"]
    h_depth = max(_max_depth(info1["lhs"]), _max_depth(info1["rhs"]))
    g_depth = max(_max_depth(info2["lhs"]), _max_depth(info2["rhs"]))
    h_ops = info1["op_count"]
    g_ops = info2["op_count"]

    # SIGNAL 1: Free variable in h. Strongest True signal in the field.
    # Heath's classifier weights this heavily; AN45c's "trivial magma
    # exit gate" is the same feature.
    if free:
        return {
            "likely_verdict":   "true",
            "confidence":       0.90,
            "primary_strategy": "constancy",
            "free_vars":        sorted(free),
            "rationale":        f"h has free var(s) {sorted(free)} — "
                                f"forces constant magma; goal vacuously true",
        }

    # SIGNAL 2: Aristotle pattern — h has exactly one variable.
    # Single-var laws like (x ◇ x = x), (x = x ◇ x) are the
    # "dominant winner" class per the Cazares analysis. BUT:
    # very simple single-var laws (idempotence alone) are weak
    # axioms — they can be falsified by left-absorb, right-absorb,
    # and many others. We only call this True with confidence when
    # the goal isn't asking for something stronger than h could
    # plausibly imply.
    if len(v1) == 1:
        # Idempotence-class h: op_count ≤ 1 and goal has more vars
        # than h has → almost certainly False. Don't claim True here.
        if h_ops <= 1 and len(v2) > len(v1):
            return {
                "likely_verdict":   "false",
                "confidence":       0.60,
                "primary_strategy": "structural_ce",
                "free_vars":        [],
                "rationale":        f"h is weak single-var law ({h_ops} ops); "
                                    f"goal has more vars ({len(v2)} > {len(v1)}) — "
                                    f"likely False, search structural shapes",
            }
        return {
            "likely_verdict":   "true" if g_ops <= 5 else "unknown",
            "confidence":       0.70 if g_ops <= 5 else 0.50,
            "primary_strategy": "aristotle",
            "free_vars":        [],
            "rationale":        f"h is single-variable (Aristotle family); "
                                f"instantiate at goal subterms",
        }

    # SIGNAL 3: h short and shallow, goal long and deep → likely False.
    # Lost-in-the-middle paper documents this as the "weak h" pattern.
    if h_ops <= 2 and g_ops >= 5 and h_depth < g_depth:
        return {
            "likely_verdict":   "false",
            "confidence":       0.65,
            "primary_strategy": "structural_ce",
            "free_vars":        [],
            "rationale":        f"h has {h_ops} ops at depth {h_depth}, "
                                f"goal has {g_ops} ops at depth {g_depth} — "
                                f"h too weak; search structural shapes",
        }

    # SIGNAL 4: Goal has more variables than h → usually False or
    # reducible to grind. Per the paper's edge-cases section.
    if len(v2) > len(v1):
        return {
            "likely_verdict":   "false",
            "confidence":       0.55,
            "primary_strategy": "finite_ce",
            "free_vars":        [],
            "rationale":        f"goal has {len(v2)} vars but h has {len(v1)} — "
                                f"h cannot constrain extra vars",
        }

    # SIGNAL 5: Same variable count and similar structure → grind-alone
    # is often enough. This is Q3's "same variable structure" case from
    # the existing v5 prompt.
    if len(v1) == len(v2) and abs(h_ops - g_ops) <= 1 and abs(h_depth - g_depth) <= 1:
        return {
            "likely_verdict":   "true",
            "confidence":       0.50,
            "primary_strategy": "grind_alone",
            "free_vars":        [],
            "rationale":        "h and goal have similar structure; "
                                "grind may close in one step",
        }

    # DEFAULT: no structural signal dominates. Fall back to HAVE+GRIND
    # with goal-subterm arguments, which is the dominant winner per
    # the Cazares findings (Pattern 2 in the prompt).
    return {
        "likely_verdict":   "unknown",
        "confidence":       0.30,
        "primary_strategy": "have_grind",
        "free_vars":        [],
        "rationale":        "no dominant structural signal; "
                            "default to HAVE+GRIND with goal subterms",
    }


def llm_solve(problem, eq1, eq2, attempts, deadline, few_shot=None):
    """LLM call with structurally-branched prompt and few-shot examples
    from earlier in this marathon run.

    Diff 2 (Less Is More): runs structural_precheck first to get a
    verdict prior and a primary strategy. The strategy drives which
    branched system prompt is used; the verdict prior is surfaced to
    the model as a hint it can override but starts anchored to.
    """
    info1 = analyse(eq1)
    info2 = analyse(eq2)
    v1 = variables_of(eq1)
    v2 = variables_of(eq2)

    # Run the structural precheck FIRST. Its output drives both the
    # prompt branch and the analysis hints. This is the bridge from
    # WILL's deterministic logic into the LLM call.
    precheck = structural_precheck(eq1, eq2)

    hints = []
    # The precheck's rationale goes first — it's the most informative
    # signal we have and the LLM should anchor on it.
    hints.append(
        f"Structural precheck: likely_verdict={precheck['likely_verdict']}, "
        f"confidence={precheck['confidence']:.2f}, "
        f"strategy={precheck['primary_strategy']} — {precheck['rationale']}"
    )
    free = info1["lhs_only"] | info1["rhs_only"]
    if free:
        hints.append(f"h has free vars {sorted(free)} — set them freely")
    if len(v2) < len(v1):
        hints.append(f"Goal has fewer vars ({v2}) than h ({v1}) — specialize")

    # Sort for stable prompt hashing (fix from v8 review)
    goal_subs = _subterms_of(info2["lhs"]) | _subterms_of(info2["rhs"])
    useful_subs = sorted(
        [s for s in goal_subs if "◇" in s and len(s) < 25],
        key=lambda s: (len(s), s),  # stable secondary sort
    )
    if useful_subs:
        hints.append(f"Goal subterms to use as h arguments: {useful_subs[:4]}")

    rnd = len(attempts)
    temp_hint = ""
    if rnd >= 2:
        temp_hint = "\nBe more creative. Try unusual argument combinations."
    if rnd >= 4:
        # On round 4+, the precheck's prior is empirically wrong on this
        # problem. Flip the strategy: if precheck said true, try false,
        # and vice versa. This is the Cazares paper's distribution-shift
        # protection — when local heuristics fail, swap them.
        temp_hint = (
            "\nPrevious attempts have failed. The structural precheck's "
            "prior may be wrong. Try the OPPOSITE verdict."
        )

    # Add equation IDs if available (fix from v8 review)
    eq_ids = []
    if problem.get("equation1_id") or problem.get("eq1_id"):
        eq_ids.append(str(problem.get("equation1_id") or problem.get("eq1_id")))
    if problem.get("equation2_id") or problem.get("eq2_id"):
        eq_ids.append(str(problem.get("equation2_id") or problem.get("eq2_id")))
    id_line = f"\nETP equation ids: {' → '.join(eq_ids)}" if eq_ids else ""

    # Few-shot block: format past successes from this run
    fewshot_block = ""
    if few_shot:
        examples = []
        for ex in few_shot[-3:]:  # last 3
            ex_eq1 = ex.get("eq1", "")
            ex_eq2 = ex.get("eq2", "")
            ex_verdict = ex.get("verdict", "")
            ex_body = ex.get("body", "")
            examples.append(
                f"  h: {ex_eq1}\n  goal: {ex_eq2}\n"
                f"  verdict: {ex_verdict}\n  solution: {ex_body[:300]}"
            )
        if examples:
            fewshot_block = (
                "\n══ EXAMPLES FROM THIS RUN ══\n" + "\n\n".join(examples)
            )

    # Diff 3: build the system prompt from the precheck's strategy.
    # On round 4+, fall through to the default (have_grind) so the LLM
    # gets a different prompt shape after the strategy-specific one fails.
    if rnd >= 4:
        system_prompt = build_system_prompt(None)  # default have_grind
    else:
        system_prompt = build_system_prompt(precheck)

    context = {
        "system": system_prompt + fewshot_block,
        "round": str(rnd),
        "problem_summary": (
            f"h: ∀ {' '.join(v1)}, {eq1}\n"
            f"goal: ∀ {' '.join(v2)}, {eq2}\n"
            f"Analysis: {'; '.join(hints)}"
            f"{id_line}{temp_hint}"
        ),
        "previous_attempts": "\n".join(attempts[-3:]) if attempts else "none",
    }

    result = call_llm(context)
    if "error" in result:
        return None

    text = result.get("response", "")
    text = re.sub(r"<think>[\s\S]*?</think>", "", text).strip()
    text = re.sub(r"^```(?:json)?\s*\n?", "", text)
    text = re.sub(r"\n?```\s*$", "", text)

    try:
        data = json.loads(text.strip())
    except Exception:
        m = re.search(r"\{[\s\S]*\}", text)
        if not m: return None
        try: data = json.loads(m.group())
        except Exception: return None

    return data

# ═══════════════════════════════════════════════════════════════════════
# CORE SOLVER (per-problem)
# ═══════════════════════════════════════════════════════════════════════

def solve(problem, budget, run_state):
    """Solve a single problem. run_state is the shared marathon dict
    containing solved_patterns and few_shot_examples."""
    eq1 = norm(problem["equation1"])
    eq2 = norm(problem["equation2"])
    t0 = time.time()
    deadline = t0 + budget

    def _T(proof, hb=False):
        return call_judge("true", lean_true(proof, hb)).get("status") == "accepted"
    def _F(n, table):
        return call_judge("false", lean_false(n, table)).get("status") == "accepted"

    def _record_true(body):
        run_state["solved_patterns"].append(body)
        run_state["few_shot"].append({
            "eq1": eq1, "eq2": eq2, "verdict": "true", "body": body
        })

    def _record_false(n, table):
        run_state["few_shot"].append({
            "eq1": eq1, "eq2": eq2, "verdict": "false",
            "body": f"n={n}, table={table}"
        })

    # ── Pass 1: Quick CE search (Fin 2-3) ────────────────────────────
    n, table = find_ce(eq1, eq2, max_n=3, deadline=t0 + 2.0)
    if n is not None and _F(n, table):
        _record_false(n, table)
        return "accepted"

    # ── Pass 2: Structural proof ─────────────────────────────────────
    proof = find_proof(eq1, eq2)
    if proof and _T(proof):
        _record_true(proof)
        return "accepted"

    # ── Pass 3: Tactic battery (cached patterns first) ──────────────
    tactics = build_tactics(eq1, eq2, cached_patterns=run_state["solved_patterns"])
    for tactic in tactics[:10]:
        if time.time() > deadline - 60: break
        if _T(tactic, hb=True):
            _record_true(tactic)
            return "accepted"

    # ── Pass 3.5: Extended CE search (Fin 4-5, deadline-bounded) ─────
    # Give Pass 3.5 a fresh 120s window from RIGHT NOW, capped by the
    # remaining problem budget. Using `t0 + 120` (the problem's start
    # time + 120s) would skip Pass 3.5 entirely on problems where the
    # earlier passes already burned through that budget.
    extended_deadline = min(deadline - 30, time.time() + 120)
    if time.time() < extended_deadline:
        n, table = find_ce(eq1, eq2, max_n=5, deadline=extended_deadline)
        if n is not None and _F(n, table):
            _record_false(n, table)
            return "accepted"

    # ── Pass 4: LLM loop with few-shot examples ─────────────────────
    attempts = []
    while time.time() < deadline - 10:
        data = llm_solve(
            problem, eq1, eq2, attempts, deadline,
            few_shot=run_state["few_shot"],
        )
        if data is None: break

        verdict = data.get("verdict")
        if verdict == "true":
            proof_body = data.get("proof", "")
            if not proof_body: continue
            proof_body = re.sub(r"^\s*intro\s+G\s+_\s+h\s*\n?", "", proof_body)
            proof_body = re.sub(r"^\s*by\s+", "", proof_body)
            r = call_judge("true", lean_true(proof_body, high_hb=True))
            status = r.get("status")
            attempts.append(f"Tried true: {proof_body[:100]}... → {status}")
            if status == "accepted":
                _record_true(proof_body)
                return "accepted"

            # .symm preflight repair: if the proof was rejected with what
            # looks like a flipped-direction error (type mismatch on goal
            # equality), retry once with a .symm wrapped around an exact.
            # This is the cheapest possible salvage — one extra judge call
            # for what's typically a 50/50 direction mistake from the LLM.
            err = (r.get("error") or "").lower()
            looks_flipped = (
                "type mismatch" in err
                or "expected" in err and "got" in err
            )
            if looks_flipped and "exact " in proof_body and ".symm" not in proof_body:
                # Wrap the first `exact <term>` in `.symm`
                repaired = re.sub(
                    r"exact (h(?:\s+\S+)*)",
                    r"exact (\1).symm",
                    proof_body,
                    count=1,
                )
                if repaired != proof_body:
                    r2 = call_judge("true", lean_true(repaired, high_hb=True))
                    attempts.append(f"Repair .symm: → {r2.get('status')}")
                    if r2.get("status") == "accepted":
                        _record_true(repaired)
                        return "accepted"

        elif verdict == "false":
            tbl = data.get("table")
            n_val = data.get("n")
            if tbl and n_val:
                r = call_judge("false", lean_false(n_val, tbl))
                attempts.append(f"Tried false Fin {n_val}: {tbl[:10]}... → {r.get('status')}")
                if r.get("status") == "accepted":
                    _record_false(n_val, tbl)
                    return "accepted"

    return "unsolved"

# ═══════════════════════════════════════════════════════════════════════
# MARATHON ORCHESTRATION
# ═══════════════════════════════════════════════════════════════════════

def difficulty(problem):
    """Triage: 0 = free var on either side (likely false or quick constancy),
    1 = simple, 2 = hard."""
    eq1 = norm(problem["equation1"])
    info = analyse(eq1)
    if info["lhs_only"] or info["rhs_only"]: return 0
    if info["op_count"] <= 3: return 1
    return 2

# Budget multipliers by difficulty. Easy problems get less, hard problems
# get more, total weighted sum is preserved against the per-problem mean.
BUDGET_MULTIPLIER = {0: 0.5, 1: 1.0, 2: 1.5}

def run_marathon(problems, total_budget):
    """Solve a batch of problems with adaptive budget and cross-problem
    learning via solved_patterns + few_shot."""
    deadline = time.time() + total_budget
    n_problems = len(problems)

    run_state = {
        "solved_patterns": [],   # accepted proof bodies, prepended to tactics
        "few_shot": [],          # recent (eq, verdict, body) for LLM context
    }

    # Triage and compute adaptive per-problem budget
    triaged = [(i, p, difficulty(p)) for i, p in enumerate(problems)]
    weight_sum = sum(BUDGET_MULTIPLIER[d] for _, _, d in triaged)
    # Reserve 5% for final report / safety margin
    usable_budget = (total_budget - 30) * 0.95
    per_unit = usable_budget / max(weight_sum, 1.0)

    # Solve easy problems first to seed the cache, then harder ones can
    # benefit from learned patterns
    ordered = sorted(triaged, key=lambda x: x[2])
    results = [None] * n_problems

    for orig_idx, problem, diff in ordered:
        remaining = deadline - time.time()
        if remaining < 20:
            break  # not enough time for another problem

        problem_budget = min(
            per_unit * BUDGET_MULTIPLIER[diff],
            remaining - 15,
        )
        if problem_budget < 15:
            continue  # too little budget to be useful

        # Robust orchestration: a crash in one problem must not poison
        # the entire batch. The marathon runner has to be fault-tolerant.
        try:
            results[orig_idx] = solve(problem, problem_budget, run_state)
        except Exception as exc:
            # Log to stderr; the judge protocol owns stdout
            print(f"[WILL] problem {orig_idx} crashed: "
                  f"{type(exc).__name__}: {exc}", file=sys.stderr)
            results[orig_idx] = "unsolved"

    return results, run_state

# ═══════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════

def main():
    startup = read_msg()

    if "problems" in startup:
        # Marathon mode
        problems = startup["problems"]
        budget = startup.get("budget_seconds", 3600.0)
        results, run_state = run_marathon(problems, budget)
        solved = sum(1 for r in results if r == "accepted")
        send_msg({
            "status": "done",
            "solved": solved,
            "total": len(problems),
            "cached_patterns": len(run_state["solved_patterns"]),
        })
    else:
        # Solo mode (still supported, single-problem)
        problem = startup.get("problem", startup)
        budget = startup.get("budget_seconds", 3600.0)
        run_state = {"solved_patterns": [], "few_shot": []}
        result = solve(problem, budget, run_state)
        send_msg({"status": result})

if __name__ == "__main__":
    main()
