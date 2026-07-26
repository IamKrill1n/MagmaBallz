# EQT02-M00006 Solver Compendium

*SAIR Mathematics Distillation Challenge — Equational Theories, Stage 2*

A single consolidated reference for the contestant solver: what it does today
(Part I), how it compares to every other solver seen so far (Part II), and the
one planned extension (Part III).

## Provenance

This document started as a compilation of three source documents that were scattered
across two directories. Parts I and II preserve their sources' content. **Part III no
longer does** — it was substantively reframed on 2026-07-26 (rule-list generalization
of route 12 instead of a standalone completion prover; frontier collision instead of a
joinability test; no reduction order). The original draft is superseded, not merged.

| Part | Source file | Written | Original location |
|---|---|---|---|
| I | `SOLVER_DOCS.md` | 2026-06-23 | `~/dev/MagmaBallz/` (untracked) |
| II | `SOLVER_ANALYSIS_NOTES.md` | 2026-07-26 | `~/dev/MagmaBallz/` (untracked) |
| III | `saturation-engine-improvement-plan.md` | 2026-07-25 | `~/dev/SAIR-document-PNM/` |

Deliberately **not** included: the organizer-owned framework docs (`README.md`,
`CONTRIBUTING.md`, `docs/{solo,marathon}_mode.md`, `rules/*`, both `TUTORIAL.md`
files, `docs/agents/*`). A second checkout of those exists under
`~/dev/SAIR/equational-theories-lean-stage2/`, verified byte-identical to the
copies already in this repo — folding them in would only duplicate what is one
directory away.

Two stale paths were found while compiling. Both have since been corrected at the
source, so Part III below reads as fixed:

- Part III named its target as `~/dev/SAIR/EQT02-M00006.py`, which does not exist.
  The solver lives at `~/dev/MagmaBallz/EQT02-M00006.py`.
- Part III's Phase 0 placed the judge setup commands "in
  `equational-theories-lean-stage2/`". There is no such subdirectory here — the
  framework is checked out flat, so `docs/`, `examples/`, `judge/`, `pipeline/`,
  `rules/`, `scripts/`, and `tests/` are all top-level and every command runs from
  the repo root. `CLAUDE.md` carried the same assumption in four places and has been
  corrected too.

Neither Part I nor Part II ever referenced the nested path — worth stating, since
the framework's own docs do, and will keep doing so: upstream, the framework really
is a nested clone. Read any `equational-theories-lean-stage2/` prefix in
organizer-owned docs as relative to this repo's root.

Part III's one checkable dependency does hold: `examples/problems/eq_size5.txt` is
present.

---

# Part I — The submission: `EQT02-M00006.py`

## Overview

This file is a **Stage 2 automated theorem prover** for magma equational theory problems. It is a competition submission for the [Lean 4 Equational Theories](https://leanprover-community.github.io/) project.

Each problem asks: **does Equation1 imply Equation2 in every magma?**

A **magma** is just a set with one binary operation `◇` — no other axioms (no associativity, no identity, nothing). The solver must produce either:
- A **TRUE certificate**: a Lean 4 proof that every magma satisfying eq1 also satisfies eq2
- A **FALSE certificate**: a finite magma (given as a multiplication table) where eq1 holds but eq2 does not

## Architecture

```
┌─────────────────────────────────────────────────────┐
│                  EQT02-M00006.py                    │
│                                                     │
│  ┌──────────────┐   ┌────────────────────────────┐  │
│  │   Parsing    │   │    Proof Search Engine     │  │
│  │  + Term DSL  │   │  (deterministic routes)    │  │
│  └──────────────┘   └────────────────────────────┘  │
│                                                     │
│  ┌───────────────────────────────────────────────┐  │
│  │         Counterexample Search Engine          │  │
│  │   (named tables, families, brute force)       │  │
│  └───────────────────────────────────────────────┘  │
│                                                     │
│  ┌───────────────────────────────────────────────┐  │
│  │          LLM / Judge Integration              │  │
│  │      (via external proxy — not direct)        │  │
│  └───────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────┘
         │                        │
    stdin/stdout              output file
    (Solo mode)            (Marathon mode)
         │                        │
   ┌─────▼──────────┐    ┌────────▼──────┐
   │  Competition   │    │  Competition  │
   │  Proxy Harness │    │     Judge     │
   │ (LLM + Judge)  │    │               │
   └────────────────┘    └───────────────┘
```

**Responsibility split:**

| Responsibility | This file | External |
|---|---|---|
| Proof strategy and route ordering | YES | |
| Lean 4 code generation | YES | |
| Local counterexample verification | YES | |
| Actual LLM HTTP calls | | Proxy / `marathon_llm` module |
| Lean compilation and judging | | Competition judge |

## Data model

### Terms

Terms are represented as nested Python tuples:

```python
Term = tuple[Any, ...]

("var", "x")              # variable x
("op", left, right)       # left ◇ right
```

Example: `x ◇ (y ◇ z)` becomes `("op", ("var", "x"), ("op", ("var", "y"), ("var", "z")))`

### Equations

```python
{
    "variables": ["x", "y", "z"],   # in order of appearance
    "lhs": Term,
    "rhs": Term,
    "lhs_text": "x ◇ y",
    "rhs_text": "z",
    "text": "x ◇ y = z"
}
```

### Problems

```python
{
    "id": "42",
    "eq1_id": 10,
    "eq2_id": 20,
    "equation1": "x ◇ y = y ◇ x",   # hypothesis
    "equation2": "x = x ◇ x",        # goal to prove/disprove
}
```

## Parsing

| Function | Description |
|---|---|
| `strip_outer_parens(text)` | Removes redundant outer parentheses from a string |
| `parse_term(text, variables)` | Parses a term string into nested tuples; uses `◇` or `*` as the operator |
| `parse_equation(text)` | Splits `lhs = rhs`, collects variables in order of appearance, parses both sides |

Parsing is strict — throws `ValueError` if the input cannot be parsed.

## Term utilities

All cached with `@lru_cache` for performance.

| Function | Description |
|---|---|
| `term_vars(term)` | Set of variable names appearing in a term |
| `term_size(term)` | Number of nodes in the term tree |
| `term_depth(term)` | Maximum nesting depth |
| `term_to_lean(term)` | Renders term as Lean 4 syntax, e.g. `(x ◇ (y ◇ z))` |
| `dual_term(term)` | Swaps left and right children recursively (mirrors the term) |
| `term_subterms(term)` | All subterms including the term itself |
| `boundary_vars(term)` | Leftmost and rightmost variable in the term |
| `subterm_paths(term)` | All paths from root to every subterm node |
| `term_at_path(term, path)` | Retrieve subterm at a given path |
| `replace_subterm(term, path, replacement)` | Replace subterm at path with a new term |
| `context_to_lean(term, path)` | Renders a "context" (term with a hole at path) for use in `congrArg` |

## Evaluation and matching

| Function | Description |
|---|---|
| `eval_term(term, env)` | Evaluates a term under a variable assignment and a concrete `op` function |
| `instantiate_term(term, subst)` | Substitutes all variables using a `{var: Term}` map |
| `instantiate_term_if_bound(term, subst)` | Like above, but returns `None` if any variable is missing from the map |
| `match_term(pattern, target, subst)` | One-way pattern matching (like unification but pattern-only); fills `subst` in place |
| `equation_holds(equation, table)` | Tests whether an equation holds for all assignments in a finite table |
| `table_is_counterexample(eq1, eq2, table)` | True if eq1 holds in `table` but eq2 does not |

## Certificate generators

These functions produce Lean 4 source code strings ready for the judge.

### `reflexive_true_certificate()`

Used when eq1 == eq2. The proof is just `exact h`.

```lean
import JudgeProblem
def submission : Goal := by
  intro G _ h
  exact h
```

### `false_certificate(n, table)`

Embeds a counterexample table into Lean and uses `decideFin!` to mechanically verify it.

```lean
import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp

def submission : Goal := by
  let m : Magma (Fin 3) := {
    op := finOpTable "[[0,1,2],[1,2,0],[2,0,1]]"
  }
  refine Exists.intro (Fin 3) ?_
  refine Exists.intro m ?_
  decideFin!
```

### `singleton_true_certificate(...)`

Used when eq1 forces the magma to have only one element. Proves `∀ a b : G, a = b` and then uses it for eq2.

### `substitution_true_certificate(eq2_vars, call_expr)`

Used when eq2 follows by directly substituting into eq1 once. Generates `exact <call_expr>`.

### `projection_true_certificate(eq2_vars, proof_expr)`

Used when eq1 is a projection law. Similar shape to substitution.

## TRUE proof routes

Tried in priority order. Each route is a function that returns `(route_name, lean_code)` or `None`.

### 1. Reflexive
`is_reflexive_problem` — eq1 and eq2 are the same equation. Trivially true.

### 2. Singleton
`singleton_route(eq1)` — eq1 has a variable on one side that doesn't appear on the other side, e.g. `x = y ◇ z`. This forces all elements to be equal (singleton magma), making every equation true.

### 3. Collapse routes
These detect specific structural patterns in eq1 that force a singleton magma via a chain of equational reasoning, then conclude eq2.

| Route | Pattern detected in eq1 |
|---|---|
| `middle_self_collapse` | `a = (b ◇ a) ◇ c` — derives `b = a ◇ c` then all-equal |
| `front_double_self_collapse` | `a = b ◇ (a ◇ (a ◇ c))` — derives row-constancy then all-equal |
| `alternating_front_self_collapse` | `a = b ◇ (a ◇ (b ◇ c))` — uses equational closure to derive all-equal |
| `mirrored_alternating_front_self_collapse` | Mirror variant of above |

### 4. Derived law routes
These detect when eq1 implies a known useful law, then prove eq2 under that law.

| Route | Law derived from eq1 |
|---|---|
| `sandwich_left_projection` | `x = x ◇ y` (left projection) |
| `square_twist_comm` | `a ◇ b = b ◇ a` (commutativity), via `a ◇ b = (b ◇ b) ◇ a` |

### 5. Direct substitution
`direct_substitution_route(eq1, eq2)` — eq2's lhs matches eq1's lhs and eq2's rhs matches eq1's rhs under the same substitution. The proof is a single call to `h`.

Also handles the symmetric case (eq1 flipped) using `.symm`.

### 6. Bridge route
`bridge_route(eq1, eq2)` — both sides of eq2 can each be matched to one side of eq1, and the "other" sides from both matches are the same term. Proof is `(left_call).trans (right_call).symm`.

### 7. Completed bridge
`completed_bridge_route(eq1, eq2)` — like bridge, but variables left unbound after matching are filled in by trying terms from the goal's subterm pool. Up to 2500 trials.

### 8. Projection route
`projection_true_route(eq1, eq2)` — eq1 is a left- or right-projection law. Recursively proves that both sides of eq2 reduce to the same variable via projection steps.

### 9. Rewrite chain (BFS)
`find_rewrite_chain(eq1, eq2)` — BFS starting from eq2's lhs, applying eq1 as a rewrite rule at any subterm position, trying to reach eq2's rhs. Depth limit: `REWRITE_CHAIN_MAX_DEPTH = 2`.

### 10. Special absorption routes

| Route | Description |
|---|---|
| `self_square_absorption_route` | eq1 has shape `x = (y ◇ x) ◇ (y ◇ x)`, proves specific goal form |
| `repeat_tail_absorption_route` | Specific pattern with repeated tail structure |
| `c9_e1072_collapse_route` | Recognizes a specific equation shape and reduces to Equation 19 (`x = y ◇ (z ◇ x)`) |

### 11. Absorption closure
`absorption_closure_route(eq1, eq2)` — applies when eq1 has an absorption-like hypothesis (one side is a variable appearing on the other). Does bidirectional BFS where each step tries applying eq1 with "filled" free variables from a term pool.

### 12. Equational closure (general)
`equational_closure_route(eq1, eq2)` — most general route. Bidirectional BFS from both sides of eq2, expanding by applying eq1 in any direction at any subterm, filling free variables from the term pool. Finds a meeting point and chains the proofs.

> This is the route Part III generalizes. Its edge generator is hardwired to the
> single hypothesis `eq1`; the saturation work makes it take a *rule list*, with
> today's behavior recovered exactly when that list is `[eq1]`. There is no separate
> `true:saturation` route.

## FALSE proof routes — counterexample search

`find_counterexample(eq1, eq2)` tries tables in this order:

### 1. Named witness tables
Pre-defined small tables known to refute many equations:

| Name | Description |
|---|---|
| LP | Left projection: `x ◇ y = x` |
| RP | Right projection: `x ◇ y = y` |
| C0 | Constant zero |
| XOR | Bitwise XOR on {0,1} |
| AND, OR, NAND, NOR, IMP, NIMP, XNOR | Boolean operations |
| A2 | Asymmetric 2-element |
| Z3A, Z3B | Cyclic group Z3 with two orientations |
| T3L, T3R, S4A–S4F, S5A–S5D | Larger hand-picked tables up to size 5 |

### 2. Structured family tables
Parameterized families generated programmatically:
- Min/max semilattices on Zn
- Left/right successor spines
- Conditional tables (if-left-0, if-right-0)
- Negated sum tables
- Rectangle band tables (r × c products)

### 3. Affine family tables
Tables of the form `(ax + by + c) mod n` for various `a, b, c` over modular arithmetic fields.

### 4. Quadratic family tables
Tables of the form `(ax + by + c·xy + d) mod n`, `(ax + by + c·x²) mod n`, `(ax + by + c·y²) mod n`.

### 5. Brute-force enumeration
For small n (up to `ENUMERATION_MAX_N = 3`), exhaustively enumerates all n^(n²) possible operation tables.

### 6. Dual search
If the above all fail, tries the same search on the **dual problem** (swap operand order everywhere). A counterexample to the dual corresponds to a transposed counterexample to the original.

## Proof expression helpers

These construct Lean 4 proof term strings (not full certificates, just expressions):

| Function | Description |
|---|---|
| `chain_trans(prefix, proof)` | Chains two proofs: `(prefix).trans (proof)` |
| `combine_meeting_proofs(left, right)` | Combines left-side and right-side proofs at a meeting term |
| `proof_between_terms(eq1, src, dst)` | Finds a one-step or direct proof that `src = dst` using eq1 |
| `proof_between_terms_guided(eq1, vars, src, dst)` | Like above but also tries rewrite chains and mini-closure |
| `rewrite_steps_from_term(eq1, term)` | All single-step rewrites of `term` using eq1 at any subterm position |
| `context_to_lean(term, path)` | Renders context (term with hole) for `congrArg (fun t => ...)` |
| `commutative_term_proof(src, dst)` | Proves `src = dst` assuming commutativity |
| `projection_term_proof(eq1, term, side)` | Reduces a compound term to a variable using a projection law |

## LLM integration

When deterministic routes fail, the solver escalates to an LLM.

### Prompt (`PROMPT`)
The LLM is given:
- The problem ID, both equations
- Solver analysis (which deterministic routes failed, subterms, variable info)
- History of previous attempts
- Exact JSON response format expected

The LLM may return one of four shapes:
1. `{"verdict":"true","proof_kind":"rewrite_chain","chain":["lhs","...","rhs"]}` — rewrite chain, verified locally
2. `{"verdict":"true","proof_kind":"guided_chain","chain":[...]}` — chain where steps may need closure, verified locally
3. `{"verdict":"true","proof":"intro x y\n  exact ..."}` — raw Lean proof body, sanitized then sent to judge
4. `{"verdict":"false","counterexample_table":[[0,1],[1,0]]}` — finite table, verified locally before Lean is emitted

### LLM response processing

`candidate_from_llm_text_with_reason(problem, text)` processes raw LLM output:
1. Strips `<think>` blocks, markdown fences
2. Extracts JSON object
3. For FALSE: calls `table_is_counterexample` to verify locally
4. For TRUE chains: calls `chain_certificate_from_terms` or `guided_chain_certificate_from_terms`
5. For raw Lean: calls `sanitize_lean_code` to check for banned keywords and import restrictions

### Lean sanitizer (`sanitize_lean_code`)
Rejects any Lean code that:
- Exceeds size limits (`MAX_LEAN_CODE_BYTES = 100,000`)
- Contains banned keywords: `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `macro`, `elab`, `#eval`, `#check`, `Teorth`, etc.
- Uses imports outside the allowed set: `{JudgeProblem, JudgeDecide.DecideBang, JudgeFinOp.MemoFinOp, JudgeMagma.Magma}`
- Does not define a `submission` function
- Does not import `JudgeProblem`

> Part II, §3 records that this sanitizer has no counterpart in any demo solver —
> `EQT02-M00006.py` is the only file surveyed that implements the documented
> contract.

### LLM config
```python
LLM_CONFIG = {
    "model": "openai/gpt-oss-120b",
    "provider": "deepinfra/bf16",
    "max_output_tokens": 4096,
    "temperature": 0.0,
    "reasoning_effort": "low",
    "use_seed": True,
    "seed": 0,
    "http_timeout_seconds": 45.0,
}
```

## Execution modes

### Solo mode (`run_solo`)

Activated when `JUDGE_MARATHON_MANIFEST` is **not** set.

**Communication:** All I/O happens via `stdin`/`stdout` in newline-delimited JSON. A competition proxy sits in between and owns the actual LLM and judge HTTP connections.

**Flow:**
```
stdin  →  read problem JSON
        →  run solve_problem()
        →  if found: send {"call":"judge", "verdict":..., "code":...} to stdout
           read judge response from stdin
           if accepted → done
        →  for each LLM round:
             send {"call":"llm", "context":{...}} to stdout
             read LLM text response from stdin
             parse candidate from response
             send to judge
             if accepted → done
        →  submit fallback reflexive certificate
```

**LLM rounds:** controlled by `MAGMA_SOLO_LLM_ROUNDS` env variable (default: 2).

### Marathon mode (`run_marathon`)

Activated when both `JUDGE_MARATHON_MANIFEST` and `JUDGE_MARATHON_OUTPUT` are set.

**Communication:**
- Reads problems from `JUDGE_MARATHON_MANIFEST` (newline-delimited JSON)
- Writes accepted answers to `JUDGE_MARATHON_OUTPUT` (newline-delimited JSON)
- LLM calls go through an externally loaded `marathon_llm` module from `JUDGE_MARATHON_LIB_DIR`

**Flow:**
```
1. Load all problems, compute priority, sort
2. Deterministic pass: solve each problem, write answers to output file
3. LLM pass (if token budget > 0 and module available):
   - Sort unsolved problems by LLM priority score
   - Fire batches of up to 10 parallel LLM calls (ThreadPoolExecutor)
   - For each LLM response: verify candidate locally, append to output file
   - Stop if time/token budget exhausted
4. Print summary stats to stderr
```

**Time budget:** `JUDGE_MARATHON_BUDGET_SECONDS` (default: 3600 seconds)
**Token budget:** `JUDGE_MARATHON_BUDGET_TOKENS` (default: 0, disabling LLM)
**Max LLM calls:** `MARATHON_LLM_MAX_CALLS = 24`
**Batch size:** `MARATHON_LLM_BATCH_SIZE = 10`

## Priority system

Problems are assigned a priority tuple `(tier, size, hint)` by `problem_priority`:

| Tier | Condition |
|---|---|
| 0 | Reflexive (eq1 == eq2) |
| 1 | Singleton or collapse route detected |
| 2 | Sandwich projection, square-twist comm, direct substitution |
| 3 | Bridge route |
| 4 | Projection cue (likely FALSE) |
| 5 | Absorption hypothesis (likely TRUE) |
| 6 | Unknown (finite search needed) |

A separate `llm_problem_priority` scores problems for the LLM pass, preferring absorption-like hypotheses and simple variable structures (more likely to benefit from LLM reasoning).

## Key constants

| Constant | Value | Purpose |
|---|---|---|
| `MAX_LEAN_CODE_BYTES` | 100,000 | Max size for any Lean submission |
| `MAX_FALSE_CERT_BYTES` | 20,000 | Max size for FALSE certificates |
| `ENUMERATION_MAX_N` | 3 | Max table size for brute-force search |
| `STRUCTURED_MAX_N` | 7 | Max table size for structured families |
| `REWRITE_CHAIN_MAX_DEPTH` | 2 | BFS depth for basic rewrite chain |
| `ABSORPTION_CHAIN_MAX_DEPTH` | 3 | BFS depth for absorption closure |
| `EQUATIONAL_CLOSURE_CHAIN_MAX_DEPTH` | 4 | BFS depth for general closure |
| `LLM_MAX_ROUNDS` | 2 | Max LLM attempts in Solo mode |
| `MARATHON_LLM_MAX_CALLS` | 24 | Max total LLM calls in Marathon mode |
| `LLM_HTTP_TIMEOUT_SECONDS` | 45.0 | Timeout per LLM HTTP request |

## Output format

### Accepted answer (Marathon output file, one line per problem):
```json
{"id":"42","verdict":"true","code":"import JudgeProblem\n\ndef submission : Goal := by\n  ..."}
```

### Accepted FALSE answer:
```json
{"id":"42","verdict":"false","code":"import JudgeProblem\nimport JudgeDecide.DecideBang\n..."}
```

### Stderr logging:
The solver logs all routing decisions, LLM call results, and final stats to stderr as JSON lines for debugging.

---

# Part II — Competitive landscape: the Solo demo solvers

Session notes of 2026-07-26. Captured to disk because the session transcript was
not being persisted (inherited `CLAUDE_CODE_CHILD_SESSION` marker).

Scope: `examples/solo/demos/` — 11 files, 8 directories.

## 1. Duplication map (verified by `diff` / function-set comparison)

| File | Status |
|---|---|
| `emily/EQT02-S00011.py` | Exact duplicate of `S00012.py` apart from one leading blank line |
| `emily/EQT02-S00019.py` | 40-line retune of `opnorm/solver.py`; identical 77-function inventory |
| `twophase/solver.py` | Superseded by `opnorm` (same 75 functions + 2) |
| `dufius/EQT02-S00005.py` | Superseded by `S00007` (42 of 49 functions byte-identical) |

Distinct solvers: **opnorm, eulerv5, dufius/S00007, suii0x, baseline, owen**
(+ `emily/S00012` as a small variant).

## 2. Per-solver summary

### opnorm (4667 L) — repair-centric reference solver
Single-phase "MATCH-COLLAPSE" LLM prompt over ~11 reachable deterministic routes:
3 counterexample tiers (exhaustive Fin<=3 -> structured/product families Fin 2-7 +
5k random -> backtracking Fin 4-5, 10 s), then singleton -> direct substitution ->
calc-chain BFS -> compound calc -> constancy -> hybrid -> deep-constancy ->
simp-rewrite -> bidirectional subexpression BFS (120k states, 30 s).

Distinctive machinery is the repair layer:
- `preflight_proof` — local tactic banlist before spending a judge call
- `try_symm_repair` — flip `.symm`, resubmit
- `extract_calc_intermediates` — seeds a bounded BFS rerun from a rejected LLM proof
- `parse_lean_error` -> `build_fix_hint` — typed judge stderr into a natural-language directive

Temps `[0.3, 0.5, 0.7, 0.9]`. Round loop unbounded (harness enforces wall clock).

Caveats found: ~1,100 lines of `try_*` strategies defined but never called from
`main()`; two library-lookup routes permanently stubbed to `False`; several JSON
side-tables referenced by path but not shipped. The docstring's "16 strategies"
overstates what actually executes.

### eulerv5 (3177 L) — ships the answer key
`_MATRIX_BLOB` decompresses to exactly 2,754,205 bytes = 4694^2 bits
(`_MATRIX_N = 4694`) — an O(1) oracle for every ordered pair of the 4,694 known
Equational Theories Project equations. Verified by decompressing it.
Backed by 390 machine-verified proofs (`_AB`, 90,240 bytes) and 238 verified
counterexample tables.

Everything else — bidirectional meet-in-the-middle rewrite BFS with `CONST`/`LCONST`
transitions, five zero-LLM specialized engines, a 50-candidate tactic sweep,
invertibility patterns from Tao's Lean files, an LLM tier — exists only for the
out-of-corpus residual. Hence the direction predictor (2 s counterexample probe +
`find_proof` probe) before choosing an attack.

Budget-aware: `llm_reserve = min(30, 0.3*budget)`, round count = `budget/45`.
Only demo with Marathon support, though it gates on `JUDGE_MARATHON_MANIFEST`
alone, not the documented two-var pair.

Tactic heuristics reverse-engineered from an external proof corpus — comments cite
frequency stats ("compound terms... 71% of successful instantiations").

### dufius/S00007 (3758 L) — data + unification, judge-call economics
Organizing principle: **judge calls are the scarce resource** (comment at line 3688
puts a rejection at ~5 min of Lean compile).

Cascade:
- **Layer 0** `_oracle_verdict` — routing signal only
- **Layer 0b** bundled witness (oracle FALSE) — re-verified locally, 1 judge call
- **Layer 0c** `_try_auto_proof` — unification, 1-step + four 2-step chain shapes
- **Layer 0d** SimpleRewrites lookup (oracle TRUE)
- **Layer 1** rule engine: X1 reflexive; S1/S2 leftmost/rightmost-leaf projection;
  S4 XOR parity; affine library M1-M9
- **Layer 1.5** brute force — exhaustive Fin 2 (16) and Fin 3 (19,683), structured
  families only at Fin 4-5. Budget 20 s if oracle silent, 120 s if oracle said FALSE.
  Skipped entirely if oracle said TRUE.
- **Layer 3** LLM, <=8 rounds

Oracle design (better than a raw truth table): `_oracle_verdict` never reads a
stored verdict, it infers — a bundled magma satisfying Eq1 and not Eq2 => FALSE
(and you hold the proof); a SimpleRewrites recipe exists => TRUE (ditto); neither
=> unknown. Both directions backed by a constructive artifact, re-verified locally.
Storage is compact because the DB stores 1,683 magmas each with its *set* of
satisfied equations, indexed per-equation smallest-first — one magma covers every
pair it separates.

The third branch does the real work: "no witness in our DB" is treated as evidence
of TRUE, driving the short brute-force budget, the prompt's `DEFAULT TO TRUE` block,
and the explanation given to the model.

LLM circuit breakers: `MAX_CONSECUTIVE_UNVERIFIED = 3`, `MAX_JUDGE_REJECTIONS = 2`
(cited evidence: "gpt-oss-120b that fails the first two cert attempts effectively
never recovers later"), plus an oracle-disagreement guard that discards
contradicting verdicts without a judge call. Rejected tables accumulate and the
last 5 are fed back as a do-not-repeat list.

Brittleness found:
- Oracle-suppression guard is applied at Layers 1 and 3 but **not** at 0c
- `emit_singleton_certificate` requires `lhs1 == "x"` literally (line 3193)
- `try_x3`'s second branch returns a `RuleResult` with no certificate and is inert
- Fin 4-5 not exhaustive; sporadic counterexamples there are invisible
- `solve_problem` (line 3462) is dead code — never called
- No Lean sanitization: no size cap, no import allowlist, no `sorry`/`axiom` scan
- Marathon dropped, not moved — `run_marathon` from S00005 has no trace

### suii0x (922 L) — zero LLM by construction
`PROMPT = ""`, no `call_llm` anywhere. 20 s structured counterexample search
(exhaustive Fin 2-3, then constant/projection/min-max/affine-grid/band/product/
projection-exception families to Fin 7), then 7 closed-form TRUE synthesizers built
around a 64-entry term pool: singleton, direct substitution (var-only and compound),
1-2 hop calc chains, one-`congrArg` bridging, constancy.

Nothing deeper than 2 hops or one congruence. Vestigial `<think>`-tag stripping
suggests an LLM path was removed. Ends with a deliberate doomed `exact h` canary so
a run is never zero-judge-call.

No shared ancestor with dufius — zero function-name overlap, unrelated naming
conventions. Convergence is from the framework contract, not lineage.

### baseline (294 L)
Brute force Fin<=3 -> singleton-collapse pattern -> unbounded LLM loop, on the
documented stdio protocol, relying on the proxy's `{history.*}` injection.

### owen (152 L)
Pure LLM passthrough, 8 fixed rounds, no deterministic reasoning. Tightest feedback
discipline of the small solvers. **Uses an HTTP session REST API**
(`PIPELINE_API_BASE`, verified via `urllib` import), not the stdio contract.

### emily/S00012 (180 L)
owen's HTTP scaffolding with the LLM stage deleted and baseline's table-enumeration
algorithm ported in (same bit-packing formula, renamed variables; extended to a
120k-sample Fin 4 tier). Structurally can only ever answer FALSE.

## 3. Cross-cutting observations

**Three mutually exclusive strategic bets:**
- *Precompute* (eulerv5, dufius) — ship verified answers/witnesses as compressed
  data, reserve reasoning for the residual. Depends on the judge's ID numbering
  matching the mined corpus.
- *Search* (suii0x, emily/S00019) — spend CPU on finite countermodels so a verified
  Fin table replaces uncertain proof attempts. S00019's entire 40-line diff is this:
  `max_n` 5->6, random 5k->16k, backtracking `(4,5)`->`(4,5,6)` at 10 s->22 s, and
  colder temps `[0.12...0.85]` because after an aggressive search the LLM should be
  literal, not creative.
- *Repair* (opnorm, twophase) — assume the LLM lands close, invest in typed error
  parsing, `.symm` toggling, BFS completion of near-miss proofs.

**Nobody sanitizes Lean.** None of the demos has `sanitize_lean_code`, an import
allowlist, or byte-size caps. Local gates are semantic (table satisfies Eq1, refutes
Eq2 — every solver does check this before a judge call) plus regex tactic banlists.
`EQT02-M00006.py` is the only file in the repo implementing the documented contract.

**Nobody caches term operations.** No `@lru_cache` in any demo. opnorm and eulerv5
each maintain two parallel term representations with duplicated parsing logic.

**Convergent design.** Independently authored solvers landed on the same shapes:
singleton-collapse detection, affine `(ai+bj+c) mod n` families, `finOpTable` +
`decideFin!` FALSE certificates, local table verification before judging. The last
three are forced by `judge/verify.py`'s support modules; the first two are genuine
independent discovery.

## 4. FINDING: `_try_auto_proof`'s plain `trans` row has its link pair swapped

**File:** `examples/solo/demos/dufius/EQT02-S00007.py`, line ~2952
**Status:** verified empirically, not yet filed as an issue

### The mechanism

A two-hop chain `(h sigma).trans (h tau)` imposes three constraints:

1. `sigma(L1) = L2` — left end
2. `tau(R1) = R2` — right end
3. `sigma(R1) = tau(L1)` — the joint (this shared expression is M)

Constraints 1 and 2 are matching problems solved against the goal's two ends.
Constraint 3 has no unknowns left, so it is a structural-equality *check*, not a
solve. M is never searched for — each half computes a candidate midpoint and the
check asks whether they agree.

### The four orientations

Rule: whichever side of the assumption matches the goal, the *other* side is the
midpoint end.

| # | Shape | sigma from | tau from | correct joint |
|---|---|---|---|---|
| 1 | `(h s).trans (h t)` | L1~L2 | R1~R2 | `s(R1) = t(L1)` |
| 2 | `(h s).trans (h t).symm` | L1~L2 | L1~R2 | `s(R1) = t(R1)` |
| 3 | `(h s).symm.trans (h t)` | R1~L2 | R1~R2 | `s(L1) = t(L1)` |
| 4 | `(h s).symm.trans (h t).symm` | R1~L2 | L1~R2 | `s(L1) = t(R1)` |

Rows 2, 3 and 4 are wired correctly. **Row 1's link pair is written as `(L1, R1)`,
which yields `s(L1)` vs `t(R1)` — row 4's condition.** By construction those are
just `L2` and `R2`, so the check tests whether the goal's own two sides are
identical. It should be `(R1, L1)`.

### Repro

```python
# assumption: x * y = (y * x) * y
# goal:       a * b = (b * (b * a)) * b
# valid proof: (h a b).trans (h (b*a) b)
sigma(R1) = ((b*a)*b)
tau(L1)   = ((b*a)*b)
  joint sigma(R1)==tau(L1)?          True     <- the chain is valid
  what the code actually compares?   False    <- wrong pair
_try_auto_proof -> None
```

With only that row's pair swapped to `(R1, L1)`:

```
_try_auto_proof -> ('intro a b\n  exact (h a b).trans (h (b*a) b)', '2_trans')
```

### Impact

The most natural two-hop shape — no `.symm` anywhere — never fires. Everything
reaching it falls through to brute force and then the LLM.

Second-order: when the goal is reflexive, the broken check *passes* and a
certificate is emitted without the real joint ever being verified — likely
ill-typed, costing a judge call. The X1 rule that properly handles reflexive goals
sits at Layer 1, which runs *after* this detector.

### A limitation that survives the fix

Matching `L1` against `L2` only binds variables occurring in `L1`. If the assumption
has a variable appearing only on its right side, sigma leaves it unbound and
`sigma(R1)` still contains a loose variable — at which point the joint is an
equation to *solve*, not an identity to check. Verified:

```python
# assumption: x = y * x ,  goal: a = c * (b * a)
# valid chain exists: (h a b).trans (h (b*a) c)
sigma = {x: a}          # y never bound
sigma(R1) = (y*a)       tau(L1) = (b*a)
-> None   (even on the link-corrected build)
```

Concrete improvement: at the joint, *match* `sigma(R1)` against `tau(L1)` instead of
testing equality. Then `y` binds to `b` and the chain goes through.

Other limits, not fixable within this design: depth capped at two; both matches are
against the whole side, so rewrites inside a subexpression are invisible
(`match(x*x, (a*a)*b) = None`, verified); no derived lemmas; matching is exact with
no normalization.

### Next step

Per `CONTRIBUTING.md` this is a substantive correctness change and needs a filed
issue before a PR. Issues live under `.scratch/<feature>/`.

## 5. eulerv5 BFS: near-misses, expression comparison, and closure

### The BFS itself (`proof_bfs_v5`, ~line 1928)

Bidirectional. A forward frontier grows from the goal's LEFT side, a backward
frontier from the goal's RIGHT side, applying instantiated hypothesis rewrites at
any subterm position (`gen()` recurses into `("op", l, r)` at path `"L"`/`"R"`).

Bookkeeping:

```python
fwd = {start: None}   # norm -> (prev_norm, path, args, symm, prev_tree, this_tree)
bwd = {target: None}
state_cap = max(20000, min(500000, int(time_limit * 8000)))
```

Generated terms are capped at `_tsize5(...) <= 20` nodes.

Two extra rewrite kinds beyond plain `h` / `h.symm`: `CONST` and `LCONST`, which
exploit variables free on only one side of the hypothesis to jump between
differently-instantiated but semantically linked subterms.

**Success = collision.** `if nn in bwd` — exact identity of canonical strings. At
that point the forward path proves `left = M`, the backward path proves
`M = right`, and the recorded paths reconstruct a `calc` chain (each step wrapped
via `_wrap5` according to the rewrite path).

### What a "near-miss" is

If the frontiers never collide the search fails, but up to 500k expressions were
explored. The failure path harvests some of them (line ~2149):

```python
for nn in fwd:
    if nn in bwd: continue
    overlap = sum(1 for c in nn if c in target)
    if overlap > len(target) * 0.5:
        _last_bfs_near_misses.append((nn, overlap, total_states))
_last_bfs_near_misses.sort(key=lambda x: -x[1])
_last_bfs_near_misses = _last_bfs_near_misses[:5]
```

A near-miss is an expression the FORWARD search actually reached — so a proof that
`goal_left = E` already exists (replay the recorded rewrites) — but which never
linked up to the backward frontier.

**Purpose:** `_build_llm_hints` (line ~1499) injects the top 3 into the LLM prompt,
but only when the oracle says the verdict is TRUE:

```
BFS NEAR-MISS RESULTS (use these!):
  Near-miss: <expression> (overlap: N)
  BFS explored <N> states.
  The gap between the nearest expression and the goal
  is a bounded sub-problem. Close it with constancy or congr_arg.
```

This is the strongest idea in eulerv5's design: a failed deterministic search hands
the model a *partial result*, converting total failure into a reduced problem, and
the state count tells the model the cheap paths are already exhausted.

Sibling mechanism: `_last_tactic_failures` injects the tactic sweep's failures as
"TACTIC SWEEP ALREADY TRIED (do NOT re-propose these)" with Lean's actual errors.

### FINDING: the near-miss score does not measure similarity

`sum(1 for c in nn if c in target)` counts, per character of the candidate, whether
that character occurs ANYWHERE in the target. The alphabet is only variable letters,
the operator, and parentheses — so almost every candidate scores its own full
length. Verified:

```
'(x-y)-x'              len= 7  overlap= 7
'(y-x)-y'              len= 7  overlap= 7
'((x-x)-(y-y))-(x-y)'  len=19  overlap=19
```

Two structurally unrelated expressions of equal length score identically, and a
large unrelated expression outscores an exact structural neighbour. Since the list
sorts by overlap descending, **the ranking is effectively longest-first** — and the
longest states are the deepest, most-rewritten ones, i.e. the least likely to be
near the goal. The `> len(target) * 0.5` threshold is likewise a length filter.

Two available improvements, both already in the file or the data structure:
- `_string_overlap5` (line 2341) computes a longest-common-substring score and does
  measure shared structure. It ranks `rw` chains but is not used here.
- Depth-in-the-search is a better proxy for "close" than length. It is recoverable
  by walking `prev_norm` back to `start`, and the expansion loop
  (`for depth in range(max_depth)`) knows it while building — but it is neither
  stored per state nor used for ranking.

Impact is bounded: near-miss scores never affect correctness, only which hint the
model sees. Term size is also capped at 20 nodes, so the length bias has a ceiling.

### How expressions get compared (two distinct mechanisms)

**Exact — affects correctness.** Every expression is rendered to a canonical string
by `_tnorm5`; those strings are the dict keys. "Same expression" means identical
canonical string, i.e. structural tree equality by proxy. Used for the collision
test and for dedup. Matching is the other exact comparison: directional, all-or-
nothing. Proofs are only ever built on exact agreement.

**Heuristic — affects ranking only.** `_string_overlap5` and the near-miss counter.
A bad similarity score can waste an attempt or produce an unhelpful hint; it can
never produce a wrong certificate, because anything that becomes a certificate still
passes exact matching and then the judge. This is why the sloppiness is tolerable
here in a way it would not be in the collision test.

### When is something "closed"?

Three gates, only the last authoritative:

1. **In the search** — collision (`nn in bwd`), exact.
2. **Before submitting** — `preflight_v5` rejects `sorry`/`admit`, the banned
   automation list (`aesop, omega, norm_num, ring, field_simp, decide, tauto,
   linarith, positivity, polyrith, nlinarith`), bare `simp` without `only`,
   underscore-typed `have`, and references to the nonexistent
   `equational_theories` library. FALSE tables are checked against both equations
   by `check_equation`. These are filters against WASTING a judge call, not
   judgments of correctness.
3. **The judge** — compiles and returns one of the five statuses. No solver decides
   a proof is correct; it only decides a candidate is worth a compile. The Lean
   kernel decides closure. Same reason a counterexample table is a certificate
   rather than a claim: the judge recomputes both laws over every assignment.

**Closed in the term sense** (no free variables) is a separate and load-bearing
notion. A substitution yields a closed expression only if every variable was bound.
This is precisely the dufius limitation in section 4: when sigma is solved from one
side and a variable occurs only on the other, `sigma(R1)` retains a loose variable
and structural equality against a closed expression fails. Closedness is the
precondition for the joint check to be meaningful. eulerv5's `CONST`/`LCONST`
transitions go the other way — they deliberately exploit one-sided free variables to
generate additional rewrites.

## 6. eulerv5 BFS: the graph model, and what the search is actually for

### Nodes are expressions, not equations

```python
start, target = _tnorm5(glt), _tnorm5(grt)   # goal's LEFT tree, goal's RIGHT tree
fwd = {start: None}
bwd = {target: None}
```

- **node** = a single expression (keyed by its canonical string from `_tnorm5`)
- **edge** = one application of the hypothesis at one subterm position, carrying its
  justification (`h args`, `(h args).symm`, or a `CONST|…`/`LCONST|…` step)
- **path from A to B** = a proof that `A = B`

The equation is not a node — it is the *pair of endpoints*, and the proof is the
route between them. "Does `L2 = R2` hold" becomes "are these two nodes connected,
and can you exhibit a path." Provable equality is graph connectivity.

`L1 = R1` is therefore not an edge but the **edge generator**: every (instantiation
x position x direction) triple is a different edge. Edges are effectively
undirected, since `.symm` supplies the reverse (the `symm` flag rides in the stored
tuple and `_wrap5` inserts `.symm` on reconstruction).

Because the search is for a *connection between two known nodes* rather than for a
node with some property, bidirectional search is the natural shape: two balls of
radius d/2 beat one ball of radius d, and the branching factor here is severe.

### What it searches for: a frontier collision

Not a proof, and not the goal — a single expression present in **both** frontiers.
The code says it directly:

```python
fwd[nn] = (nm, path, args, symm, t, nt)
total_states += 1

# Check: does this meet the backward frontier?
if nn in bwd:
```

The backward-expansion loop mirrors it with `if nn in fwd`. On collision:

```python
fwd_chain, cur = [], nn
while fwd[cur] is not None:
    fwd_chain.append(fwd[cur]); cur = fwd[cur][0]
fwd_chain.reverse()
# ... same walk on bwd ...
bwd_chain_flipped = [(prev, p, a, not s, prev_t, this_t) for ... in bwd_chain]
```

The `not s` flip is the key detail: the backward chain was built travelling
right-to-left, so replaying it inside a left-to-right `calc` means reading every
step in the opposite direction — exactly toggling `.symm`. The two halves are then
concatenated, one `calc` line per edge, with the final line's target forced to `gr`
(the goal's right side as literally written) so the chain terminates on the goal
rather than on the normalized form.

Nothing is re-derived at collision time; the parent links already hold the proof.

### The output is always a single flat chain

No branching, no auxiliary lemmas, no combining two independently-derived facts.

**This is not an expressiveness loss in principle.** For pure equational reasoning,
if `L2 = R2` follows from `L1 = R1` at all then it follows by *some* sequence of
one-at-a-time rewrites — tree-shaped equational proofs always flatten into chains
(Birkhoff: derivability and rewrite-connectivity coincide).

**The cost of flatness is length**, and length hits the budget. A `have` lemma
proved once and used three times becomes a flat chain that redoes the work three
times, so a proof that is short with a lemma can sit far past `max_depth` without
one.

> This is exactly the gap Part III sets out to close, and the argument there is the
> same one: path search is complete in principle, exponentially long in practice.

### The real limits (all in `gen`/`comps`, ~line 1955)

```python
def comps(sub):
    free = [v for v in e1v if v not in sub]
    if not free: return [dict(sub)]
    if len(free) > 3: return []              # gives up entirely
    pp = e2v if len(free) >= 3 else pool     # 3 free -> goal vars only
    for combo in _product5(pp, repeat=len(free)):
        ...
        if len(out) >= 200: break            # capped
```

Unifying the hypothesis against the current subterm pins down part of the
instantiation; the rest must be guessed. Hard limits:

- **more than 3 unpinned variables -> no rewrite generated at all**, position skipped
- with exactly 3, completions come only from the goal's variables, not the pool
- at most 200 completions per position
- generated terms dropped if `_tsize5(...) > 20` nodes
- plus `state_cap` (20k-500k, scaled by time budget), `max_depth`, wall clock

So the binding constraints are instantiation guessing and the term-size ceiling, not
the shape of the output. A valid chain passing through a 25-node intermediate is
invisible no matter how much time is allowed. And a failed search never means "no
proof exists" — only "not within these caps."

### The rest of eulerv5 is not flat

Only the BFS is. The hardcoded blob ships genuinely tree-shaped proofs with nested
lemmas and reused intermediates (see ~line 362):

```
have h1    : x = ((x ◇ x) ◇ x) ◇ (x ◇ x)                := h x x
have h2    : x ◇ x = (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := h (x ◇ x) x
have hA_eq : (x ◇ x) ◇ x = (x ◇ (x ◇ x)) ◇ x := by ...
```

Those are precomputed from the mined corpus, not constructed by the BFS. Generating
that shape is left to the specialized engines and the LLM.

---

# Part III — Improvement plan: a saturation engine

*Drafted 2026-07-25. Reframed 2026-07-26 — see "The actual shape" below; the original
draft specified a standalone completion prover with a joinability goal test, which is
not what this needs to be.*

## Background and motivation

The solver's TRUE-direction deterministic routes are all **path-shaped**: they search
for a linear chain of single rewrite steps from the goal's LHS to its RHS (the most
general being `equational_closure_route`, a bidirectional BFS at depth 4). By
Birkhoff's completeness theorem this proof format is complete *in principle* — every
true equational consequence is reachable by a chain of "replace equals by equals"
steps. In practice, DAG-shaped proofs (derive lemma q from h, derive lemma r from h,
combine q and r to reach the goal) flatten into chains that are exponentially longer,
pass through terms exceeding any size cap, and require h-instantiations no finite
pool will name. Path search cannot find them.

The missing mechanism is **saturation** (Knuth–Bendix completion / superposition):
maintain a growing set of *proved* equations, generate critical pairs (the
"q AND r → u" inferences), and feed them back into the search. This is the engine
class behind E-prover — which the competing EULER v5 solver used *offline* to hardcode
6 proofs ("E-Prover family"), but which no known contestant solver runs *at runtime*.
It is an unoccupied niche: zero-token proofs for problems that currently fall through
to the LLM.

Target file: `~/dev/MagmaBallz/EQT02-M00006.py` (the contestant submission).

## The actual shape: one rule becomes many

The precise defect in every path route is narrower than "the output is a chain."
It is that **the search has exactly one rewrite rule.**

`filled_absorption_steps` (~line 1675) takes a single `eq1`, sets
`sides = (eq1["lhs"], eq1["rhs"])`, and matches subterms against those two patterns
and nothing else. Every edge in the entire bidirectional search is *apply `h`, at some
position, in some direction, under some instantiation*. Part II §6 records the same
structure in eulerv5: "`L1 = R1` is therefore not an edge but the **edge generator**."
The search space is large in positions × directions × instantiations, and one-dimensional
in rules.

So the engine is not a replacement for the BFS and does not need its own goal test.
It is:

> derive additional equations `r`, `s`, … from `h` up front — then run **the existing
> bidirectional walk from `L2` to `R2`** with `{h, r, s, …}` as the rule set instead
> of `{h}`.

Two halves, cleanly separated:

- **Generator** — critical pairs between known equations. Unification supplies the
  instantiation, so this is the one way to produce genuinely new facts *without*
  reintroducing the pool-guessing problem: the overlap tells you which term to build.
  Output is a set of proved equations, each carrying its own short proof.
- **Consumer** — `equational_closure_route`, structurally unchanged, with its edge
  generator looping over a rule list where it currently reads one `eq1`.

Consequences of this framing, all of which simplify the original draft:

1. **No normal forms, no joinability test.** The goal test stays frontier collision —
   plain reachability, with both directions of every equation always available.
2. **No reduction order is required for correctness.** LPO/KBO was only needed because
   normal forms need orientation and joinability needs confluence. Neither is now in
   play. An ordering is still wanted to keep the lemma set from exploding, but it is a
   *pruning heuristic*: a bug there costs recall, never soundness.
3. **Lemma reuse is free.** If the walk cites `r` at two different steps, the emitted
   proof is a DAG without anything having been designed for it.
4. **Certificate emission mostly already exists.** Each edge's justification is built by
   `call_expression(eq1["variables"], subst_full)` (~line 1733) → `h a b` or
   `(h a b).symm`, `congrArg`-wrapped for context. `call_expression` already carries a
   `name: str = "h"` parameter (line 1240) that the closure path never exercises.
   Citing `lem_k a b` needs no new machinery.

Insertion point is therefore **not** a new route after route 12 — it is a
generalization *of* route 12, with today's behavior recovered exactly when the rule
set is `[h]`.

## Scope gate: order-5 problems only

The existing deterministic routes already perform well on the order ≤ 4 band
(equation IDs 1–4694, the fully settled Equational Theories Project corpus). The
saturation engine is therefore **gated to order-5 problems** — the band where the
private eval set applies pressure and where no lookup or memorized route can help.

Gate implementation (`is_order5(problem)`), either signal:
- `eq1_id` / `eq2_id` outside 1–4694 (or absent from the known-ID table), or
- operation count in either equation ≥ 5 (order = number of `◇` applications).

Under the generalized-route framing the gate is not "which engine runs" but **how
many lemmas the generator is allowed to derive**. Order ≤ 4 sets the lemma budget to
zero, so the rule set is `[h]` and route 12 executes exactly today's search with
today's output — zero added latency, and regression risk that is structural rather
than merely tested-for. Optional loosening later: if Phase 0 shows a nonempty
order ≤ 4 TRUE residue and Solo budget is ample, raise the budget above zero there
behind an additional budget check — out of scope for the initial build.

## Phase 0 — Build an order-5 practice set and measure the residue (1 day)

Complication introduced by the scope gate: the bundled public sets (`normal`,
`hard1`–`hard3`) carry equation IDs within 1–4694, i.e. they are order ≤ 4 —
there is **no public labeled order-5 problem set** to measure against. So Phase 0
has two steps:

1. **Generate a practice set**: sample law pairs from
   `examples/problems/eq_size5.txt` (~62 K order-5 laws, bundled in the framework
   repo). Label what can be labeled cheaply and deterministically:
   - FALSE labels from the existing counterexample search (small-table refutation
     is order-agnostic and fast);
   - TRUE labels from short offline E-prover runs (Phase 4 tooling, pulled
     forward);
   - unlabeled pairs are kept but excluded from recall metrics.
2. **Measure the residue** on the TRUE-labeled pairs: problems where every current
   deterministic route fails. This is the engine's addressable market.

- Success metric, fixed now: *number of order-5 residue problems closed at zero
  tokens, with zero regressions on the order ≤ 4 public sets.*
- Go/no-go gate: if the residue is tiny, stop here at the cost of a day.

Requires the framework's local judge (`bash scripts/setup.sh` +
`source .env.judge`, run from the repo root) and a local `eprover` binary
(offline only).

## Phase 1a — Lemma generator (1–2 days)

Pure Python, reusing the existing term representation (`("var", x)` / `("op", l, r)`
tuples — must remain hashable tuples per project CLAUDE.md).

- **Lemma** = `(lhs_tree, rhs_tree, provenance)`;
  provenance = `(parent_ids, overlap_position, substitution, orientation)` —
  recorded from birth, because Phase 2 lives off it.
- **Init set**: `h` in both orientations, plus the lemmas the derived-law routes
  already produce (projection, commutativity, pivot/constancy shapes).
- **Loop** (given-clause style):
  1. Pop the smallest unprocessed lemma.
  2. Form critical pairs against all processed lemmas: unify one lemma's LHS with
     each **non-variable** subterm position of the other's LHS, variables renamed
     apart. (Variable positions yield subsumed pairs and inflate the branching
     factor for nothing — the original draft said "each subterm position".)
  3. Discard trivial / oversized / duplicate / subsumed results.
- **No goal check here.** The generator does not look at the goal; it hands a rule
  set to Phase 1b, which does the goal-directed work. This is the split that removes
  the reduction-order requirement — there is no normalization step to orient.
- **Caps, all deterministic** (no randomness — preserves the competition's
  same-input-same-verdict requirement):
  - term size ≤ 15
  - lemma set ≤ 200 (keep smallest)
  - ~1–3 s wall-clock
  - fixed tie-breaking: size, then lexicographic.
- **Testing**: property test cross-checking the unifier against brute-force equality
  on small terms. Variable-renaming bugs are the classic failure mode of hand-rolled
  critical-pair code and they fail silently.

## Phase 1b — Multi-rule closure route (1 day)

Generalize the consumer to take a rule *list*:

- `filled_absorption_steps(eq1, …)` → `filled_absorption_steps(rules, …)`, looping
  the existing position × direction × instantiation logic over each rule. The
  `len(needed) > 3: continue` give-up and the pool-fill logic stay as they are;
  they are now per-rule rather than global.
- Each generated step records **which rule** justified it, so the proof string
  becomes `call_expression(rule.variables, subst, name=rule.lean_name)`.
- `equational_closure_route` passes `[eq1]` when the lemma budget is zero, which is
  the order ≤ 4 path and must be byte-identical to today's output.

Recall on the Phase 0 residue is measurable at the end of 1b, before any Lean
exists. Second go/no-go gate: if recall is near zero under realistic caps, stop
before investing in proof reconstruction.

## Phase 2 — Certificate emission (1 day — smaller than first drafted)

The original draft treated this as a bespoke DAG serializer and called it the risky
part. Under the two-halves framing it is **the existing chain reconstruction, run at
two levels**:

- **Main chain**: unchanged. The frontier-collision reconstruction already emits one
  `calc` line per edge; the only difference is that an edge's proof string may read
  `lem_k a b` instead of `h a b`. `call_expression`'s `name` parameter already
  supports this.
- **Each cited lemma**: emitted as
  `have lem_k : ∀ …, A = B := by intro …; calc …`, where the `calc` body is the same
  reconstruction applied to the sub-chain that proved that lemma. Only lemmas the
  main chain actually cites are emitted.
- Ordering: topologically sort the cited lemmas (a lemma may cite an earlier lemma).
  Provenance-from-birth is what makes this cheap.
- Existing helpers cover the term-level work: `term_to_lean`, `subterm_paths`,
  `context_to_lean` (see Part I).
- All output passes through the existing `sanitize_lean_code`, then the local judge.
- **Fallback**: any lemma whose calc reconstruction fails gets a `by grind` proof
  seeded with its parents — less certain, but rescues partial wins.
- Acceptance bar: every Phase-1b win converts to a locally `accepted` certificate.

## Phase 3 — Route integration (1 day)

- **Generalize route 12; do not add route 13.** `equational_closure_route` keeps its
  position in the priority table. There is no `true:saturation` route. Step labels
  gain the rule name so traces stay readable.
- **Apply the scope gate as a lemma budget**: `is_order5(problem)` false ⇒ budget 0
  ⇒ rule set `[eq1]` ⇒ today's exact search. No bypass branch to maintain.
- Gate the generator on remaining budget; in Marathon mode, derive lemmas only for
  problems the triage pass ranks worth the added 1–3 s.
- **Salvage on failure**: pipe the top derived lemmas into the LLM prompt as proved
  context (stronger than EULER v5's near-miss trick — see Part II §5, where that
  trick's ranking is shown to be length-biased) and into the closure route's
  term pool.
- Update `SOLVER_DOCS.md` in the same change; re-verify the file stays under 500 KB
  (generator ≈ 10–15 KB of source; ~380 KB headroom exists).

## Phase 4 — Offline E-prover distillation (parallel track, 1–2 days)

E-prover runs offline only (the competition sandbox cannot execute binaries) — use
it as a factory, not a dependency:

1. Translate residue pairs to TPTP unit-equality format (one axiom, one negated
   conjecture, one binary function symbol); run `eprover` with short timeouts over
   the whole public residue.
2. Use the output three ways, in order of generality:
   - **(a) Cap tuning**: if E's proofs for solvable pairs routinely need term size 18
     or 300 lemmas, tune the runtime caps from measurement instead of guessing.
   - **(b) Lemma-shape mining**: recurring derived-lemma shapes across E's proofs
     become additional init families, starting the runtime search several steps ahead.
   - **(c) Hardcoding** (least general): for stubborn high-value pairs, translate E's
     proof to Lean and embed it — noting the private eval set will not repeat public
     pairs exactly.

## Phase 5 — Regression + determinism gate (½ day)

- Full rerun over the public sets.
- Assert every previously-solved problem still solves with an identical verdict.
  Because order ≤ 4 sets the lemma budget to zero and the rule list is then `[eq1]`,
  the order ≤ 4 search is *the same code path with the same input*, not a parallel
  one — so this should be byte-identical, and any diff is a bug in the
  generalization rather than an acceptable drift.
- Rerun the order-5 practice set from Phase 0 and report net new solves there.
- Count net new solves; measure added wall-clock (matters under Marathon's
  compressed budget).
- Run the whole set twice; require byte-identical output.

## Risk summary

| Risk | Mitigation |
|---|---|
| Unification / variable-renaming bugs | Property tests vs brute-force small-term checks (Phase 1a) |
| Regression on order ≤ 4 | Structural, not tested-for: budget 0 ⇒ rule list `[eq1]` ⇒ same code path (Phase 1b, Phase 5) |
| Proof reconstruction failures | Provenance-from-birth; reuse of the existing chain reconstruction; `by grind` fallback per lemma (Phase 2) |
| Critical-pair blow-up on generative hypotheses | Hard caps; given-clause ordering; non-variable overlap positions only; cap values tuned from E-prover evidence (Phase 4a) |
| Lemma set explosion degrading BFS branching | Ordering heuristic on the rule set — costs recall only, never soundness, since no goal test depends on it |
| Size budget | Generator ≈ 10–15 KB source vs ~380 KB headroom |
| Wasted effort | Two cheap go/no-go gates: Phase 0 (residue size), Phase 1b (oracle-measured recall) |

**Dropped from the original draft**: the joinability/normal-form goal test, and with
it the LPO/KBO reduction order it required. The goal test is frontier collision, as
it already is; reachability needs no orientation and no confluence.

**Total estimate**: roughly one week of focused work.

---

# Appendix — Open items

Carried over from the source documents; none of these has been actioned.

| # | Item | Source | Status |
|---|---|---|---|
| 1 | `dufius/EQT02-S00007.py` `_try_auto_proof` plain-`trans` link pair written `(L1, R1)`, should be `(R1, L1)` (~line 2952) | Part II §4 | Verified by patching and re-running. Filed: `.scratch/demo-solver-defects/issues/01-dufius-trans-link-pair-swapped.md` — `ready-for-human`. Demo file unchanged. |
| 2 | `eulerv5/solver.py` near-miss scoring `sum(1 for c in nn if c in target)` degenerates to measuring length; hints rank longest-first (~line 2155) | Part II §5 | Verified. Affects hint quality only, never correctness. Filed: `.scratch/demo-solver-defects/issues/02-eulerv5-near-miss-score-measures-length.md` — `ready-for-human`. Demo file unchanged. |
| 3 | Saturation engine, Phases 0–5 | Part III | Planned, not started. Reframed 2026-07-26: generalize route 12's edge generator to a rule list rather than add a standalone route; goal test stays frontier collision. |
| 4 | Stale paths in the plan (`~/dev/SAIR/EQT02-M00006.py`) and in `CLAUDE.md` (nested `equational-theories-lean-stage2/`) | Provenance | Fixed at the source, 2026-07-26. |
| 5 | Joint-*matching* improvement to `_try_auto_proof` (match `sigma(R1)` against `tau(L1)` rather than test equality) — survives the item-1 fix | Part II §4 | Described, deliberately left as a separate change; not filed. |

Items 1 and 2 both touch `examples/solo/demos/`, which is organizer-owned framework
code. Per `CONTRIBUTING.md` a substantive correctness change there requires a filed
issue before a PR — "write the code first, discuss later" is explicitly rejected.
Both are now filed under `.scratch/demo-solver-defects/`, with a `spec.md` covering
the shared context. They are marked `ready-for-human` rather than `ready-for-agent`
because whether upstream wants demo/tutorial solvers fixed at all is a maintainer
call, not one to make from here.
