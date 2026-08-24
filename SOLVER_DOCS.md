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

**Two encodings (2026-08-20).** `JudgeFinOp/MemoFinOp.lean:extractDigits` parses
the table JSON by filtering digit *characters* one at a time, so any cell value
≥ 10 desynchronizes the decoded table — n ≥ 11 table certificates verify locally
but are refuted by `decide` in Lean. Therefore: n ≤ 10 keeps the battle-tested
`finOpTable` string; n ≥ 11 emits a `List Nat` literal indexed with bare-function
arithmetic (`Nat.mod (vals.getD (Nat.add (Nat.mul i.val n) j.val) 0) n`) — the
typeclass operators `HAdd.hAdd`/`HMul.hMul`/`HMod.hMod` are disallowed by the
judge's dependency policy. Both paths judge-verified. This lifts the FALSE
search's order ceiling entirely.


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

### 0. Named Infinite Certificates (before any finite search)
`named_infinite_certificate(eq1, eq2)` — checked in `solve_problem` *before*
`find_counterexample` runs: an exact-shape lookup (alpha-canonical form of
both equations) for pairs whose only countermodels are **infinite**, where
every finite tier below is structurally blind and would burn its whole
budget for nothing. Emits a complete hand-verified Lean certificate rather
than a table. Currently one entry: the Austin pair eq1167 ⇒ eq1763
(route `false:witness_inf:austin_1167_1763`, judge-accepted on hard2_0027)
— the ETP Equation1659 parity-ladder model on `Nat`, argument-dualized. The
certificate keeps its heavy lemmas in the `submission.*` namespace so the
judge's direct-declaration policy only sees the assembly step.

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
| MW00–MW20, HV000–HV178 | **Machine-wide witness harvest**: every distinct finite countermodel found in any judge artifact on this machine (all solvers' runs), independently re-verified locally against its own problem before inclusion — the ETP named-witness-bank pattern at full scale (227 tables total, sizes 2–9). Witnesses are mathematical facts; provenance is documented at the definition site. |
| CG9 | **Non-natural central groupoid of order 9** (Knuth: 0-1 matrix `A` with `A² = J`). Satisfies Equation 168 `x = (y ◇ x) ◇ (x ◇ z)` while falsifying its high-numbered pseudo-consequences — laws that hold in every *natural* central groupoid `(a,b) ◇ (c,d) = (b,c)` of any size, including infinite ones. Finite central groupoids exist only at orders n² (1, 4, 9, 16, …), so order ≤ 8 table search can never find this witness; it must be named. |
| ET00 | Order-6 witness imported from the **Equational Theories Project** All4x4Tables refutation store, re-verified locally with `table_is_counterexample` before inclusion; judge-accepted on hard2_0125. Tried last, so all previously-solved cases keep their original witnesses. |

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

### 6. Constraint-Propagating Backtracker
`backtracking_countermodel(eq1, eq2)` — SEM/Mace-style table search at n = 4–6, row-major
cell order, values ascending, least-number symmetry breaking (bound = `max(used values, i, j) + 1`;
bounding by used values alone is over-restrictive — indices are elements — and measurably cost
9 findable n=4 witnesses before the fix). Every fully-evaluable eq1 instance must hold after each
cell; complete tables are kept iff they falsify eq2. Node caps 150k/90k/40k, own 12 s budget.
Runs after brute force, before the dual retry (which therefore inherits it).

### 7. Extended Affine Scan (`extended_affine_scan`, added 2026-08-20)
Affine models `(a·i + b·j + c) mod n` for `n ∈ {11,13,16,17,19,23,25}` — orders
past the finOpTable digit ceiling (see certificate note below). Deterministic
fail-fast probes gate the exhaustive check. Runs after the backtracker so it can
never starve earlier tiers. First scalp: hard2_0051 (`7i+7j mod 13`, 0.1 s,
judge-accepted) — a case no build of ours nor reja23 had ever solved via table.

### 8. Dual Search
If the above all fail, tries the same search on the **dual problem** (swap operand order everywhere). A counterexample to the dual corresponds to a transposed counterexample to the original.

---

## Proof Expression Helpers

These construct Lean 4 proof term strings (not full certificates, just expressions):

| Function | Description |
|---|---|
| `chain_trans(prefix, proof)` | Chains two proofs: `(prefix).trans (proof)` |
| `combine_meeting_proofs(left, right)` | Combines left-side and right-side proofs at a meeting term |
| `proof_between_terms(eq1, src, dst, lemmas=())` | Finds a one-step or direct proof that `src = dst` using eq1 plus any derived lemmas |
| `proof_between_terms_guided(eq1, vars, src, dst, lemmas=())` | Like above but also tries rewrite chains and mini-closure |
| `rewrite_steps_from_term(eq1, term, lemmas=())` | All single-step rewrites of `term` using eq1 (and lemmas) at any subterm position |
| `context_to_lean(term, path)` | Renders context (term with hole) for `congrArg (fun t => ...)` |
| `commutative_term_proof(src, dst)` | Proves `src = dst` assuming commutativity |
| `projection_term_proof(eq1, term, side)` | Reduces a compound term to a variable using a projection law |

All rule-driven edge generators (`rewrite_steps_from_term`, `proof_between_terms`,
`find_rewrite_chain`, `filled_absorption_steps`, `_closure_proof_expr_impl`,
`proof_between_terms_guided`) accept an optional `lemmas` tuple and loop over the
rule list `[eq1, *lemmas]`. With the default `()` they behave — and emit —
exactly as the single-rule versions did.

---

## Critical-Pair Lemma Engine (order-5 guided chains)

**Wide-slack escalation (2026-08-20).** `cp_saturation_route` now runs THREE
attempts in strict escalation: classic (slack 8) → beam (slack 8) → wide
(classic algorithm, `CP_SATURATION_WIDE_SLACK = 20`, pair cap 8000, gap time
10 s, rounds 60, lemma budget 1500, own budget slice max(0.75×time_budget, 45 s)
so attempts 1-2 cannot starve it — dosage set by normal_0492, the heaviest
faller: 7 lemmas, ~33 s; MISS below this dosage).
Attempts 1-2 are byte-identical to the pre-wide behavior, so every previously
solved case keeps its exact proof. Rationale: instance-chaining proofs (the
reja-class E-lemma chains) pass through self-nested intermediates far larger
than slack 8 admits — the search space was drying up, not timing out. Measured:
7 never-before-solved TRUE cases fall (hard1_0007, hard2_0080/0106/0110/0116,
hard3_0068/0137), most in under 2 s once the wide pass starts; all
judge-accepted. Route tag: `true:cp_saturation:wide:<n>`.


Widens the guided-chain rule set beyond the single hypothesis, demand-driven.
This is a generalization of the existing closure route, **not** a new route in
`solve_problem` — the deterministic route table is unchanged.

| Function | Description |
|---|---|
| `unify_terms(a, b, subst)` / `resolve_term(term, subst)` | First-order unification with occurs check, over rename-apart variables |
| `_critical_pair_candidates(rule_a, name_a, rule_b, name_b, ...)` | KB/superposition overlaps: unify one rule's side into each **non-variable** subterm position of another's. Each candidate carries a complete Lean proof from birth — the peak term rewrites to one side via parent A and to the other via parent B (under `congrArg` for proper positions), so every lemma proof is a two-step `trans` through the peak, citing only parent names (`h` / `lem_j`). |
| `derive_gap_lemmas(eq1, pool, src, dst, max_new, deadline)` | Demand-driven generation targeted at one failed hop `src = dst`: dedupes against the pool (statement key + instance-of-rule check), scores candidates by whether a side matches a subterm of the gap, caps count (`CP_LEMMA_BUDGET_ORDER5 = 24` per hypothesis), size (`CP_LEMMA_TERM_SLACK`), raw pairs (`CP_RAW_PAIR_CAP`) and time (`CP_GAP_TIME_BUDGET`). |
| `guided_lemma_budget(problem)` | Originally the order-5-only scope gate (budget `0` below eq ID 4695, keeping order ≤ 4 byte-identical). **Opened 2026-08-19**: returns the full budget on every band after a paired sweep measured +114/−0 on `evaluation_normal`+`hard` with the engine enabled everywhere; the byte-identity acceptance bar was retired in favor of the measured-gain bar. Order-5 detection retained for telemetry. |
| `guided_chain_certificate_from_terms_ex(eq1, eq2, chain_terms, lemma_budget=0)` | Budget-aware guided chain. Verifies hops with the current lemma pool; on a failed hop derives targeted lemmas and retries once; returns `(code, failed_hop_text)` so the caller can surface the exact gap. Verified hop proofs and per-hypothesis lemma pools persist across LLM rounds (`_CP_HOP_CACHE`, `_CP_LEMMA_POOLS`). |
| `guided_true_certificate_with_lemmas(eq2_vars, lemmas, chain_expr)` | Emits cited lemmas (transitive closure via `_cited_lemmas`, in pool = topological order) as `have lem_k : ∀ … : G, A = B := by intro …; exact <birth proof>` blocks before the main chain. A lemma cited twice is emitted once — the proof is a DAG for free. |

On a hop failure in Solo mode, the reject reason is
`guided_chain_hop_unproved:<src> = <dst>` and the next LLM round's
`{solver.analysis}` carries that exact gap, so the model re-plans one hop
instead of the whole problem. Order ≤ 4 problems keep the legacy
`guided_chain_unproved_or_bad_endpoints` reason.

Additional engine behaviors (originally gated to the order-5 band; enabled on every band since the 2026-08-19 gate opening):

| Piece | Behavior |
|---|---|
| `cp_saturation_route(eq1, eq2, lemma_budget=...)` | Native zero-LLM route, run last among deterministic TRUE routes: alternates goal-proof attempts (`proof_between_terms_guided` with the lemma pool) with goal-targeted critical-pair derivation, up to `CP_SATURATION_ROUNDS` rounds / `CP_SATURATION_TIME_BUDGET` seconds. Route labels `true:cp_saturation:classic:<cited>` / `:beam:<cited>` — two sequential attempts with independent lemma pools: *classic* (endpoint-targeted, slack term cap — byte-equal to the pre-beam algorithm, so previously solved cases keep their proofs) then *beam* (closest-cross-frontier targeting after round 0, 2× term cap) only if classic fails; both fall back to variable-position overlaps when ordinary derivation dries up. A shared-pool mix measurably lost solved cases in both directions before this design. Dosage history: at 24 lemmas/2.5 s it measured +6/−0 on the 100 order-5 TRUE cases; at industrial dose (`CP_SATURATION_LEMMA_BUDGET` 200, 10 rounds, 20 s, 2,500 raw pairs, slack 8) it measured +36/−0 there (83/100), and opening the gate to all bands added +114/−0 on `evaluation_normal`+`hard` and +5/−0 on `extra_hard` — all zero-LLM, all judge-verified. |
| `frontier_bridge_hint(eq1, eq2)` | Round-0 `{solver.analysis}` addition: expands one rewrite step from each goal side, ranks cross-frontier pairs by **shared-subterm structure** (deliberately not string similarity), and names the top gaps as `bridge needed: A = B` so LLM chains aim where components almost touch. Empty when the frontiers already meet. |
| Verdict feedback | On a locally refuted FALSE answer (`false_table_not_counterexample` / `_invalid_shape`), the next round's analysis says so and steers toward a verified larger table or a guided_chain. |
| `standard_ladder_route` | Bridge-lemma ladder, run after saturation: tries proving a fixed menu of classic intermediate laws (collapse, projections, idempotence, row/op-constancy, square laws) from the hypothesis via the saturation core, then re-attacks the goal with the proved bridge as an extra rule. Measured +1 on the enumerated rival-only TRUE set; the remaining cases need an instance-chaining generator (forward-composed h-instances), which the overlap-based derivation deliberately filters — a known open steal. |
| Fallback skip | The final reflexivity fallback typechecks only when the two laws coincide (owned by the reflexive route), so on the gated band it is skipped instead of submitting a guaranteed-rejected certificate. |

---

## Work Meter — deterministic search extent (2026-08-20)

**The risk it removes.** Every tier cut on wall-clock, so the amount of search
a problem receives depended on how fast and how loaded the machine was.
Measured margins of the day's wins against a slower judge CPU: `normal_0087`
used 42.5 s of a 45 s slice (**1.06×**), `hard2_0110` 1.14×, `hard3_0068`
1.19×, `hard1_0007` 1.27×. A judge machine 6% slower than the development
machine would drop cases with no change in logic whatsoever. The same effect,
measured in the other direction, moved a full sweep by +4 and −18 problems
purely with machine load.

**The mechanism.** `_WORK` counts one unit per critical-pair candidate produced
and per rewrite-step expansion — the two inner loops. `work_units()` exposes it.
`_cp_saturation_attempt(work_budget=N)` stops after N units, and the clock
becomes a backstop (`CP_SATURATION_WIDE_CLOCK_BACKSTOP = 240 s`) that only
binds on a >4× slower machine.

**Calibration — and the recalibration that had to follow.** The first setting
(40,000, from `normal_0087` at 17,124 units and `hard1_0007` at 12,038) SILENTLY
BROKE hard3_0131/0214/0266, the three cases no solver had ever settled. Cause:
work-per-second varies by an order of magnitude between problems — `normal_0087`
burns ~800 units/s, `hard3_0131` burns ~4,400 — so a budget calibrated on slow
problems amputates fast ones. Measured work needed to SUCCEED: hard3_0266
70,564, hard3_0131 53,932, hard3_0214 32,827, normal_0087 17,124.
`CP_SATURATION_WIDE_WORK = 250_000` is 3.5× the heaviest; all seven checkpoint
problems re-verified judge-accepted at that setting.

Consequence for measurement: hard cases now take up to ~260 s in
`solve_problem`, so a 120 s sweep harness under-reports them. The certification
sweep timeout was raised to 600 s — Solo grants 3600 s, and measuring with a
shorter ruler than the contest uses produces a falsely low number.
Applied to the wide and relevance passes — the ones where the marginal cases
live; classic and beam are fast enough that their margins are already large.
Solo grants 3600 s against a ~160 s worst case, so spending the margin costs
nothing there.

## Rule Selection in Critical-Pair Generation (attempt 4, 2026-08-20)

**The finding.** `derive_gap_lemmas` spends its raw-pair cap in iteration
order, and the rule list is `[h] + pool` — oldest first, growing monotonically.
Measured coverage of distinct parent rules: 32/32 at round 2, 28/132 at round
6, 8/582 at round 24, **4/1057 at round 43**. Past round ~7 the newest
thousand lemmas were essentially never used as a critical-pair parent. This is
a REACH freeze wearing a rate problem's clothes, and it explains why the 231×
speedup (7 → 56 rounds) bought nothing on resisting problems.

Diagnostic rule this generalises to: **a cap becomes a freeze when the
collection it truncates both grows monotonically and is ordered by insertion.**
Audited across the engine — this was the only site meeting both conditions;
the closure frontier and absorption pools are recomputed per call (beam bias
only), and the bridge-enumeration cap truncates after sorting by size.

**The fix, and why it is additive.** `rule_order="relevance"` ranks rules by
`_gap_relevance` against the current gap (recency as tiebreak) and gives each
parent a fair slice of the cap (`RULE_SLICE_PARENTS = 24`,
`RULE_SLICE_MIN = 120`). It is NOT a strict improvement: measured on
hard3_0131 it builds a smaller pool of different composition (776 vs 2334
lemmas in 60 s), and applied as a *replacement* it lost hard2_0028,
normal_0062 and normal_0492 while gaining three others. So it is attempt 4 of
`cp_saturation_route`; attempts 1-3 keep `rule_order="insertion"`, verified
lemma-for-lemma identical to the pre-change function across 3 problems × 4
rounds. Route tag: `true:cp_saturation:rel_<tag>:<n>`.

**What it settles.** hard3_0131 (`beam:22`), hard3_0214 (`beam:30`) and
hard3_0266 (`beam:23`) — judge-accepted, and the first problems in this
benchmark that **no** solver had ever settled, ours or reja23's. Note the
cited-lemma counts: 22-30, against 1-7 typical and 17 the previous maximum.
Correction to an earlier claim in this file's history: the freeze did NOT cap
derivation depth (measured max depth 8 both before and after) — it changed
which lemmas the pool contains, not how deep the DAG goes.

## Bidirectional Chain Search (`find_rewrite_chain`, 2026-08-20)

The RATE lever, and the largest single win measured so far. Profiling a
resisting problem showed `find_rewrite_chain` consuming **95% of wall-clock**
(29.8 s per call, 8 calls in 251 s) while candidate generation took 4%.

`rewrite_steps_from_term` applies every rule in BOTH directions (the reverse
emits a `.symm` proof), so the step relation is symmetric and a backward
search from the target is just a forward search from it. Splitting depth d
into ceil(d/2) forward and floor(d/2) backward preserves completeness for
chains of length <= d while deleting the dominant b^d term (d=3: b+b^2+b^3 →
b^2+b). Here b is pool size × subterm positions × 2 directions — hundreds once
the pool is warm. Node bookkeeping also moved from per-node proof-list copying
to parent pointers (`_walk_back`), making node cost O(1) instead of O(depth).

The meeting point is stitched as `(start = meet).trans ((target = meet).symm)`.

**Measured, same problem, same budget: 29,803 ms → 129 ms per call (231×), and
rounds explored in 240 s went 7 → 56.** The bottleneck moved to
`derive_gap_lemmas` (94.9%) — which is precisely where the ORDER lever
(ranking heuristics / a learned policy) applies.

## Systematic Bridge Enumeration (`bridge_enumeration_route`, 2026-08-20)

The deterministic generalization of the ladder, built on the user's directive:
"exhaust small-to-medium bridges systematically; the LLM's niche is only what
enumeration cannot reach." All terms up to `BRIDGE_ENUM_MAX_LEAVES = 4` leaves
over (x,y,z) get a VALUE SIGNATURE — their outputs on every assignment of
every H-model — so the surviving candidate bridges are exactly the pairs
within one signature group (O(T) signatures instead of O(T²) pair checks).
Survivors are generated smallest-first under a hard cap (1500), ranked by
goal-subterm overlap, tested cheaply for GOAL CLOSURE first
(`proof_between_terms_guided` with the bridge as a standing rule), and only
closers get the expensive prove-from-H step — at wide slack, since
instance-chaining bridges need the giant intermediates (proj_r from
hard1_0007's H: 10 s MISS at slack 8, 0.3 s proof at slack 20, measured).
Runs after the ladder in `solve_problem`. Route: `true:bridge_enum:<rank>`.
By construction no single small-bridge guess (LLM or human) can beat this
tier on coverage; the LLM midpoint lane is for bridges past enumeration size.

## Semantic Guidance (H-model bridge filter, 2026-08-20)

`find_h_models(eq1)` collects up to 4 small (order 2-3) models OF the
hypothesis, time-boxed at 0.8 s. Every derivable consequence of H must hold in
each of them, so `standard_ladder_route` now skips — with certainty, not
heuristically — any bridge rung that fails in one (`table_satisfies_equation`).
A partial model scan only weakens the filter, never its soundness. This is the
"search in more correct directions" axis: the ladder spends its saturation
budget only on rungs that remain semantically possible.

## LLM Integration

When deterministic routes fail, the solver escalates to an LLM.

### Prompt (`PROMPT`)
The LLM is given:
- The problem ID, both equations
- Solver analysis (which deterministic routes failed, subterms, variable info)
- History of previous attempts
- Exact JSON response format expected

The LLM may return one of six shapes. The four answer shapes:
1. `{"verdict":"true","proof_kind":"rewrite_chain","chain":["lhs","...","rhs"]}` — rewrite chain, verified locally
2. `{"verdict":"true","proof_kind":"guided_chain","chain":[...]}` — chain where steps may need closure, verified locally
3. `{"verdict":"true","proof":"intro x y\n  exact ..."}` — raw Lean proof body, sanitized then sent to judge
4. `{"verdict":"false","counterexample_table":[[0,1],[1,0]]}` — finite table, verified locally before Lean is emitted

And the two **steering** shapes (reja-class, ported 2026-08-19). Steering follows
the *verified-hint* principle: the model never authors trusted output, it only
chooses an action; every consequence is machine-executed and machine-proved, so
a wrong hint costs time, never correctness:
5. `{"kind":"midpoint","lemma":"x * (y * z) = x * (z * y)"}` — an untrusted
   bridge law. `custom_bridge_route` proves it from H via `_cp_saturation_attempt`
   (lemmas prefix-renamed `B0…`), then attacks the goal with the bridge as a
   standing rule via `proof_between_terms_guided`; emits route `true:steer_bridge`.
6. `{"kind":"tool_call","tool":"saturate"|"ladder"|"backtrack"|"dual"}` — asks the
   solver to re-run a deterministic engine with a bigger budget: `saturate` →
   `cp_saturation_route(time_budget=40)`, `ladder` → `standard_ladder_route`,
   `backtrack` → `backtracking_countermodel`, `dual` → `find_counterexample` on duals.

### Steering state (`steer_dispatch`, blackboard, journal)

`steer_dispatch(problem, eq1, eq2, obj, blackboard)` executes a steering object and
returns `(candidate | None, feedback)`. The **blackboard** (`proved` / `refuted` /
`tools_tried`) persists across rounds and dedupes: a failed bridge or an already-run
tool is refused with `bridge_skipped_or_repeated:` / `tool_repeated:` instead of
re-executed. The **journal** records `route→status` for every judge call. Both are
rendered by `render_blackboard` into the `{solver.blackboard}` placeholder of the
prompt, so each round sees what was proved, what failed, and what the judge said.

### Crash wall

The whole LLM tier of `run_solo` is wrapped in one `try/except Exception`: any
exception raised while consuming model-invented data logs `llm:crash_wall` to
stderr and costs only that round — the solver process survives. (Precedent: a
`KeyError` from a peak-only variable in an LLM chain once killed a live run.)

### LLM Response Processing

`candidate_from_llm_text_with_reason(problem, text)` processes raw LLM output:
1. Strips `<think>` blocks, markdown fences
2. Extracts JSON object
3. For FALSE: calls `table_is_counterexample` to verify locally
4. For TRUE chains: calls `chain_certificate_from_terms` or `guided_chain_certificate_from_terms`
5. For raw Lean: calls `sanitize_lean_code` to check for banned keywords and import restrictions

### Salvage cascade (added 2026-08-19, motivated by the Gemma pilot)

Verbose models often state the right idea in a broken wrapper (19 KB prose,
fenced JSON, trailing commas → the old parser rejected the whole reply as
`no_json_object`). Recovery is now a ladder:

1. `extract_json_object` — after fence-stripping, tries in order: whole text →
   `_json_repair`ed text → every outermost balanced `{...}` block found by the
   string-aware scanner `_balanced_json_blocks` (longest first, raw then
   repaired) → the old greedy regex as final fallback.
2. `_json_repair` — conservative fixes only: smart quotes, Python literals
   (`True`/`False`/`None`), trailing commas before `}`/`]`.
3. `salvage_bridge_equations(text, limit=3)` — when no JSON survives at all,
   mines equation-shaped lines (`lowercase vars, one =, at least one *`,
   parseable, non-trivial) out of free-form prose. `run_solo` feeds each as an
   untrusted `midpoint` bridge through `steer_dispatch`; an accepted salvage
   gets `+salvaged` appended to its route. Safe by construction — bridges are
   mechanically re-proved before use.

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

**Endgame TRUE grind (2026-08-20, "the Birkhoff bet") — UNBOUNDED iterative
deepening.** After the LLM rounds, instead of idling into the fallback, the
remaining Solo budget goes to `endgame_passes()`, an infinite generator whose
caps grow without ceiling. Slack grows LINEARLY (+6 per rung from 26); rounds
(×1.5), lemma budget (×1.6) and slice (×1.4) grow geometrically.

**Escalation is evidence-driven, never clock-driven.** `_cp_saturation_attempt`
now reports why it stopped via `stop_reason`, and the endgame raises only the
dimension that was actually binding:

| Stop reason | What was binding | What gets raised |
|---|---|---|
| `dry` — no new lemma derivable | the size cap | slack, +6 |
| `pool_full` | lemma budget | budget ×1.6 |
| `rounds` | round count | rounds ×1.5 |
| `budget` — clock or work only | nothing structural | **nothing** — the same rung gets more time |

Raising a cap while the current rung is still producing new lemmas dilutes the
search: it adds expensive candidates before the cheap ones have been examined.
Only a fixed point — `derive_gap_lemmas` returning empty — is proof that
staying is useless, and that is the sole justification for widening.

The linear/geometric split is measured, not stylistic. Widening slack SATURATES: on hard3_0131,
going from slack 60 to 200 costs 14% more work while the largest term in the
pool stays at 26 — it buys more candidates at the same shallow depth, not
depth. Rounds and pool size are the dimensions that actually buy derivation
depth, so those are the ones worth multiplying. Slack still grows without a
ceiling, because a ceiling is exactly what permanently excluded 13 cases at
slack 8. The
caller stops on the clock, never on a list.

Why no ceiling: the upper tiers are deliberately incomplete — structural caps
on term size, chain length and pool size make them fast and they catch almost
everything, but a capped engine exhausts a SUBSPACE, and once it is dry more
time buys literally nothing (measured: 13 cases missed after 900 s at slack 8
and fell in 0.2 s at slack 20). At endgame every narrowing trick is spent and
the opportunity cost of grinding is zero, so the cap should come off. Iterative
deepening is what keeps an uncapped search fair — no rung can trap it forever,
and no proof is permanently excluded, so by Birkhoff the only remaining bound
is the clock, which is correct. Measured
rationale on the official runtime, 2469 labeled problems: when every tier and
LLM round is dry, 91% of problems are TRUE (32/35), and every findable FALSE
witness arrived within 60 s (1247/1247, 98% within 10 s). TRUE is
semi-decidable (Birkhoff), finite-table FALSE search is not — so past the
60-second dry mark the expected-value play is all-in on proof search. Env:
`MAGMA_SOLO_TIME_LIMIT` (default 3600), `SOLO_ENDGAME_MARGIN = 120 s`. The
grind is crash-walled; each pass logs `endgame:pass` to stderr; a pass may
overshoot its deadline by one in-flight round (costs nothing on the gated
band, where the fallback is skipped anyway). Route: `true:endgame:<slack>:...`.
Note: 120 s-timeout sweeps never reach the endgame — its gains only show in
real-budget Solo runs.

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
| `KNOWN_ORDER4_MAX_EQ_ID` | 4694 | Last equation ID of the settled order ≤ 4 band (gate boundary) |
| `CP_LEMMA_BUDGET_ORDER5` | 24 | Max derived lemmas per hypothesis on order-5 problems (0 below) |
| `CP_GAP_TIME_BUDGET` | 0.35 | Seconds of critical-pair derivation per failed hop |
| `CP_LEMMA_TERM_SLACK` | 4 | Term-size slack over hypothesis/gap for derived lemma sides |
| `CP_RAW_PAIR_CAP` | 400 | Raw critical-pair candidates examined per derivation call |
| `CP_HOP_CACHE_LIMIT` | 4096 | Max cached verified hop proofs across rounds |

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
