# EQT02-M00006.py — Solver Documentation

## Overview

This file is a **Stage 2 automated theorem prover** for magma equational theory problems. It is a competition submission for the [Lean 4 Equational Theories](https://leanprover-community.github.io/) project.

Each problem asks: **does Equation1 imply Equation2 in every magma?**

A **magma** is just a set with one binary operation `◇` — no other axioms (no associativity, no identity, nothing). The solver must produce either:
- A **TRUE certificate**: a Lean 4 proof that every magma satisfying eq1 also satisfies eq2
- A **FALSE certificate**: a finite magma (given as a multiplication table) where eq1 holds but eq2 does not

---

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

---

## Data Model

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

---

## Parsing

| Function | Description |
|---|---|
| `strip_outer_parens(text)` | Removes redundant outer parentheses from a string |
| `parse_term(text, variables)` | Parses a term string into nested tuples; uses `◇` or `*` as the operator |
| `parse_equation(text)` | Splits `lhs = rhs`, collects variables in order of appearance, parses both sides |

Parsing is strict — throws `ValueError` if the input cannot be parsed.

---

## Term Utilities

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

---

## Evaluation and Matching

| Function | Description |
|---|---|
| `eval_term(term, env)` | Evaluates a term under a variable assignment and a concrete `op` function |
| `instantiate_term(term, subst)` | Substitutes all variables using a `{var: Term}` map |
| `instantiate_term_if_bound(term, subst)` | Like above, but returns `None` if any variable is missing from the map |
| `match_term(pattern, target, subst)` | One-way pattern matching (like unification but pattern-only); fills `subst` in place |
| `equation_holds(equation, table)` | Tests whether an equation holds for all assignments in a finite table |
| `table_is_counterexample(eq1, eq2, table)` | True if eq1 holds in `table` but eq2 does not |

---

## Certificate Generators

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

---

## TRUE Proof Routes

Tried in priority order. Each route is a function that returns `(route_name, lean_code)` or `None`.

### 1. Reflexive
`is_reflexive_problem` — eq1 and eq2 are the same equation. Trivially true.

### 2. Singleton
`singleton_route(eq1)` — eq1 has a variable on one side that doesn't appear on the other side, e.g. `x = y ◇ z`. This forces all elements to be equal (singleton magma), making every equation true.

### 3. Collapse Routes
These detect specific structural patterns in eq1 that force a singleton magma via a chain of equational reasoning, then conclude eq2.

| Route | Pattern detected in eq1 |
|---|---|
| `middle_self_collapse` | `a = (b ◇ a) ◇ c` — derives `b = a ◇ c` then all-equal |
| `front_double_self_collapse` | `a = b ◇ (a ◇ (a ◇ c))` — derives row-constancy then all-equal |
| `alternating_front_self_collapse` | `a = b ◇ (a ◇ (b ◇ c))` — uses equational closure to derive all-equal |
| `mirrored_alternating_front_self_collapse` | Mirror variant of above |

### 4. Derived Law Routes
These detect when eq1 implies a known useful law, then prove eq2 under that law.

| Route | Law derived from eq1 |
|---|---|
| `sandwich_left_projection` | `x = x ◇ y` (left projection) |
| `square_twist_comm` | `a ◇ b = b ◇ a` (commutativity), via `a ◇ b = (b ◇ b) ◇ a` |

### 5. Direct Substitution
`direct_substitution_route(eq1, eq2)` — eq2's lhs matches eq1's lhs and eq2's rhs matches eq1's rhs under the same substitution. The proof is a single call to `h`.

Also handles the symmetric case (eq1 flipped) using `.symm`.

### 6. Bridge Route
`bridge_route(eq1, eq2)` — both sides of eq2 can each be matched to one side of eq1, and the "other" sides from both matches are the same term. Proof is `(left_call).trans (right_call).symm`.

### 7. Completed Bridge
`completed_bridge_route(eq1, eq2)` — like bridge, but variables left unbound after matching are filled in by trying terms from the goal's subterm pool. Up to 2500 trials.

### 8. Projection Route
`projection_true_route(eq1, eq2)` — eq1 is a left- or right-projection law. Recursively proves that both sides of eq2 reduce to the same variable via projection steps.

### 9. Rewrite Chain (BFS)
`find_rewrite_chain(eq1, eq2)` — BFS starting from eq2's lhs, applying eq1 as a rewrite rule at any subterm position, trying to reach eq2's rhs. Depth limit: `REWRITE_CHAIN_MAX_DEPTH = 2`.

### 10. Special Absorption Routes

| Route | Description |
|---|---|
| `self_square_absorption_route` | eq1 has shape `x = (y ◇ x) ◇ (y ◇ x)`, proves specific goal form |
| `repeat_tail_absorption_route` | Specific pattern with repeated tail structure |
| `c9_e1072_collapse_route` | Recognizes a specific equation shape and reduces to Equation 19 (`x = y ◇ (z ◇ x)`) |

### 11. Absorption Closure
`absorption_closure_route(eq1, eq2)` — applies when eq1 has an absorption-like hypothesis (one side is a variable appearing on the other). Does bidirectional BFS where each step tries applying eq1 with "filled" free variables from a term pool.

### 12. Equational Closure (General)
`equational_closure_route(eq1, eq2)` — most general route. Bidirectional BFS from both sides of eq2, expanding by applying eq1 in any direction at any subterm, filling free variables from the term pool. Finds a meeting point and chains the proofs.

---

## FALSE Proof Routes — Counterexample Search

`find_counterexample(eq1, eq2)` tries tables in this order:

### 1. Named Witness Tables
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

### 2. Structured Family Tables
Parameterized families generated programmatically:
- Min/max semilattices on Zn
- Left/right successor spines
- Conditional tables (if-left-0, if-right-0)
- Negated sum tables
- Rectangle band tables (r × c products)

### 3. Affine Family Tables
Tables of the form `(ax + by + c) mod n` for various `a, b, c` over modular arithmetic fields.

### 4. Quadratic Family Tables
Tables of the form `(ax + by + c·xy + d) mod n`, `(ax + by + c·x²) mod n`, `(ax + by + c·y²) mod n`.

### 5. Brute-Force Enumeration
For small n (up to `ENUMERATION_MAX_N = 3`), exhaustively enumerates all n^(n²) possible operation tables.

### 6. Dual Search
If the above all fail, tries the same search on the **dual problem** (swap operand order everywhere). A counterexample to the dual corresponds to a transposed counterexample to the original.

---

## Proof Expression Helpers

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

---

## LLM Integration

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

### LLM Response Processing

`candidate_from_llm_text_with_reason(problem, text)` processes raw LLM output:
1. Strips `<think>` blocks, markdown fences
2. Extracts JSON object
3. For FALSE: calls `table_is_counterexample` to verify locally
4. For TRUE chains: calls `chain_certificate_from_terms` or `guided_chain_certificate_from_terms`
5. For raw Lean: calls `sanitize_lean_code` to check for banned keywords and import restrictions

### Lean Sanitizer (`sanitize_lean_code`)
Rejects any Lean code that:
- Exceeds size limits (`MAX_LEAN_CODE_BYTES = 100,000`)
- Contains banned keywords: `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `macro`, `elab`, `#eval`, `#check`, `Teorth`, etc.
- Uses imports outside the allowed set: `{JudgeProblem, JudgeDecide.DecideBang, JudgeFinOp.MemoFinOp, JudgeMagma.Magma}`
- Does not define a `submission` function
- Does not import `JudgeProblem`

### LLM Config
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

---

## Execution Modes

### Solo Mode (`run_solo`)

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

### Marathon Mode (`run_marathon`)

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

---

## Priority System

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

---

## Key Constants

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

---

## Output Format

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
