# LLM usage and search in MagmaBallz solvers

Date: 2026-08-29  
Repository snapshot: `3257571d184416b055f80adc51fd7badefef1a1e`

## Conclusion

The claim is **substantially right about solver architecture and search-space growth, but too strong about LLM usage across contestants**.

- It is strongly verified for the underlying Equational Theories Project (ETP). Its authors report extensive use of automated theorem provers and finite-model tools, but only “fairly limited” use of modern LLMs. They conclude that publicly available LLMs were less effective than ATPs and that the project largely moved away from them. The same project obtained 96.3% of its false implications from brute force over magmas of size at most four. [ETP paper, §§5.1, 7, 11, 14](https://arxiv.org/html/2512.07087)
- It is verified that the solver code visible in this repository is overwhelmingly **search-heavy**. All six documented reference demos perform deterministic finite-countermodel search before any possible LLM call. In a wider audit of the 15 Solo-like solver files, 14 contain substantial deterministic model or proof search.
- A fresh 30-second routing probe over `examples/problems/sample_20.json` supports that reading for all three official Solo references: 42/60 solver-case runs produced Lean-accepted certificates before LLM assistance, while the proxy saw 134 judge calls and only 10 attempted LLM requests. This is not a normal end-to-end score because credentials were deliberately absent and the official budget is much longer.
- It is **not** verified that most competition solvers use little LLM inference. Five of six official demos and 11 of 15 Solo-like files have an LLM path. Several Solo solvers allow repeated calls until the wall-clock deadline. Source inspection establishes ordering and capability, not actual calls, tokens, latency, or accelerator compute.
- The search-space warning is correct. A labeled magma of size `n` has `n^(n²)` possible operation tables; moving from size four to five raises the raw space from 4,294,967,296 to 298,023,223,876,953,125 tables. Proof search has a separate exponential term/rewrite space. Both theory and measured runs show a cheap-success region followed by a difficult residue that consumes the search budget.

The defensible version of the claim is:

> Most solver artifacts visible in this repository put deterministic countermodel and proof search at the center of the design, often using an LLM only after or alongside those searches. This works well on easy cases, but both model and proof spaces grow combinatorially. The available evidence does not establish low LLM consumption for most private competition entrants.

## Scope and methodology

The word “solver” can refer to three different populations. They must not be conflated.

1. **Official reference demos:** the three Solo and three Marathon demos documented in the repository [README](../README.md#examples--tutorial).
2. **Visible Solo-like artifacts:** the root submission plus 14 Python files under `examples/solo/demos/`. These include archived versions and close relatives, not 15 statistically independent contestants.
3. **Actual competition entries:** private submissions not present in this checkout. The official publication policy says Stage 2 solvers may be made public only after evaluation, so no representative source corpus or token telemetry is currently available and no “most contestants” estimate is possible. [Official competition overview](https://competition.sair.foundation/competitions/mathematics-distillation-challenge-equational-theories-stage2/overview)

The empirical work used four methods:

- manual control-flow inspection, classifying a file as LLM-capable only when a runtime path issues an LLM request, not merely because it defines a `PROMPT`;
- inspection of exact search bounds and route ordering in the solver sources;
- a fresh, 30-second routing probe of four visible Solo solvers on the bundled 20-problem sample, with both supported API-key variables explicitly unset;
- a fresh deterministic countermodel-portfolio reproduction on the bundled `hard1` and `hard2` false-labeled development slice.

No upstream LLM inference was made for this report. In the routing probe, every attempted request failed immediately because no API key was available; the attempts are useful only for locating the transition from deterministic search to LLM fallback. The fresh countermodel run did not invoke Lean; it locally checked the candidate tables against both equations. The relevant Python unit suite was also rerun with bytecode writes disabled: 12/12 tests passed, but that validates implementation behavior rather than solver accuracy.

## Empirical finding 1: visible solvers are search-heavy, not LLM-free

### The six official demos

| Demo | Deterministic work before the LLM | LLM policy |
|---|---|---|
| Solo `baseline` | Exhaustive Fin 2–3 countermodels; singleton proof | Repeated fallback calls until success, API error, or wall timeout |
| Solo `twophase` | Stored witnesses; exhaustive Fin 2–3; structured/random/backtracking Fin 4–5; deterministic proof routes and bounded BFS | One analysis call, then repeated implementation/repair calls |
| Solo `opnorm` | Exhaustive and structured countermodels; backtracking; a portfolio of deterministic proof routes; bidirectional BFS | Repeated structured fallback/repair calls |
| Marathon `baseline` | Exhaustive Fin 2–3 countermodels | None |
| Marathon `triage` | Fin 2–3 countermodel pass across the batch | One pass per survivor, then a budget-gated retry for no-shows |
| Marathon `fewshot` | Fin 2–3 countermodel pass across the batch | One call per survivor, with accepted-looking proofs reused as later few-shot context |

Sources: [Solo baseline](../examples/solo/demos/baseline/solver.py), [twophase](../examples/solo/demos/twophase/solver.py), [opnorm](../examples/solo/demos/opnorm/solver.py), [Marathon baseline](../examples/marathon/demos/baseline/solver.py), [triage](../examples/marathon/demos/triage/solver.py), [fewshot](../examples/marathon/demos/fewshot/solver.py), and the two [tutorials](../examples/solo/TUTORIAL.md) and [Marathon tutorial](../examples/marathon/TUTORIAL.md).

Thus:

- 6/6 perform deterministic countermodel search first;
- 5/6 are LLM-capable;
- 1/6 is zero-LLM.

This supports **search-first**, but it contradicts the simple reading “most do not use an LLM.” It also cannot establish “do not use a lot”: the Solo baseline, twophase, and opnorm loops have no per-problem call cap in their source and stop only on success, error, or the external wall-clock limit. The competition contract permits repeated calls and caps each call at 65,536 output tokens [Solo specification](../docs/solo_mode.md#reference-configuration).

### The wider 15-file Solo audit

The broader source audit produced:

| Architecture | Files | Count |
|---|---|---:|
| Deterministic search only / zero LLM | Emily S11, Emily S12, `generalized`, suii0x | 4 |
| Deterministic search first, LLM fallback | root M00006, Solo baseline, dufius S05/S07, Emily S19, eulerv5, opnorm, twophase | 8 |
| Mixed hybrid with conditional early LLM collaboration plus large mechanical tool/search portfolios | reja S22/S23 | 2 |
| LLM-only | owen | 1 |

Consequently, 14/15 contain substantial deterministic search, while 11/15 integrate an LLM. The count must not be interpreted as an entrant survey: Emily S11/S12 differ by one line; opnorm and Emily S19 are near-identical; twophase is in the same family; dufius and reja each have sequential versions. The repository’s own [solver analysis](../SOLVER_ANALYSIS_NOTES.md) also warns about these lineages.

Static source inspection therefore verifies this narrower statement: **mechanical search is nearly universal in the visible code, and the LLM is usually one component of a hybrid**.

## Empirical finding 2: fresh runs on `examples/problems/sample_20.json`

All four solvers were run from the repository snapshot above with the real proxy and Lean judge, sandbox mode `none`, and a 30-second per-problem limit. The machine used Python 3.14.3, Lean 4.30.0-rc2, WSL2 Linux, and an Intel Core i5-13500H exposed as 16 logical CPUs. `sample_20.json` has no answer labels, so “accepted” below means the submitted certificate was accepted by Lean, not agreement with a stored label.

| Solver | Condition | Accepted / 20 | Judge calls | Attempted LLM requests | Problems reaching LLM | Wall time |
|---|---|---:|---:|---:|---:|---:|
| `baseline` | LLM-capable; keys unset | 14 | 14 | 6 | 6 | 24.882 s |
| `twophase` | LLM-capable; keys unset | 14 | 41 | 2 | 2 | 216.902 s |
| `opnorm` | LLM-capable; keys unset | 14 | 79 | 2 | 2 | 219.833 s |
| `generalized` | zero-LLM by construction | 15 | 15 | 0 | 0 | 145.146 s |

Across the three official Solo references, this is 60 solver-case runs, 42 certificates accepted before any LLM assistance, 134 judge calls, 10 attempted LLM requests, and 461.617 seconds. The low request count does **not** estimate normal LLM use: six baseline survivors reached the disabled LLM immediately, while four `twophase` and four `opnorm` survivors spent the 30-second cap in deterministic generation and judge checks before reaching an LLM. With the official 3,600-second Solo budget, those solvers can search longer and their unbounded fallback loops can make more calls.

The time distribution shows the hard-residue effect. The five unresolved `generalized` cases used 107.118 of 145.146 seconds (73.8%). The six unresolved cases used 145.903 of 216.902 seconds (67.3%) for `twophase` and 151.154 of 219.833 seconds (68.8%) for `opnorm`. Easy accepted cases were usually much cheaper; unsuccessful bounded search dominated elapsed time.

The runs used `pipeline.proxy.run_solver` as follows; the three LLM-capable submissions were run under `env -u OPENAI_API_KEY -u OPENROUTER_API_KEY`:

```python
config = load_config()
config["solver"]["timeout_seconds"] = 30
config["sandbox"]["mode"] = "none"
problems = load_problems("examples/problems/sample_20.json")
for submission in submissions:
    for problem in problems:
        result = run_solver(submission, problem, config)
        # aggregate solved, judge_calls, llm_calls, and elapsed time
```

This probe verifies routing and deterministic search effort. It is deliberately **not** a comparative solver benchmark: it has only 20 cases, no upstream LLM, a shortened budget, one machine, and no repeated trials. In particular, equal 14/20 results for the three references say nothing about how their LLM stages compare under normal competition conditions.

## Empirical finding 3: a fresh countermodel-only reproduction

On 2026-08-29 UTC, the deterministic prototype in [`.scratch/generalizing-solo-solver/prototypes/countermodel_portfolio.py`](../.scratch/generalizing-solo-solver/prototypes/countermodel_portfolio.py) was rerun at the repository snapshot above:

```text
/usr/bin/time -f 'wall=%e user=%U maxrss_kb=%M' \
  python3 .scratch/generalizing-solo-solver/prototypes/countermodel_portfolio.py \
  --portfolio exhaustive_first_seeded \
  --max-backtrack-nodes 2000 \
  --pseudo-random-count 250
```

The cohort was all 145 false-labeled cases in the bundled `hard1` and `hard2` development sets. Labels selected the offline slice and were not exposed during candidate generation. The portfolio exhausts orders 2–3, tries structured families at orders 4–7, performs deterministic seeded order-4 backtracking with 2,000 assigned-cell nodes per case, and finally runs a hash-derived diagnostic stream.

Result: 99/145 cases (68.3%) received a locally validated countermodel. The run considered 2,353,167 distinct complete tables, performed 20,846,919 equation-assignment checks and 102,675 backtracking nodes, skipped 31,836 duplicate table generations, and used 20.80 s wall / 20.74 s user time with 738,552 KB maximum RSS. First discoveries were 6 at exhaustive order 2, 34 at exhaustive order 3, 38 in structured families, and 21 in seeded backtracking. Full method and controls: [prototype results](../.scratch/generalizing-solo-solver/prototypes/countermodel-portfolio-results.md).

This demonstrates why portfolios beat raw enumeration: useful algebraic families and constraint propagation find medium-size witnesses without approaching the full Fin 4–7 table spaces. It does not prove completeness on the 46-case residue and does not produce judge-checked Lean certificates.

## External domain evidence: the ETP itself used little LLM assistance

The competition is based on the ETP, but the project and the competition are not the same population. With that caveat, the ETP provides unusually direct primary evidence:

- Its authors say they used Vampire, Prover9, and Mace4 extensively, with superposition/saturation and equational reasoning as the main proof techniques. [ETP §7](https://arxiv.org/html/2512.07087#S7)
- They say modern LLM use was fairly limited: user-interface code, code completion, and one successful ChatGPT guess of a complete rewrite system. On most hard implications that resisted automation, LLMs did not add useful suggestions beyond the human participants. [ETP §11](https://arxiv.org/html/2512.07087#S11)
- In their conclusion, they report that public LLMs were significantly less effective than ATPs for automatic proof generation, and the project largely moved away from LLM use. [ETP §14](https://arxiv.org/html/2512.07087#S14)
- Brute force over all magmas of sizes 2–4 took 165 CPU-hours and refuted 13,632,566 implications: 61.9% of all pairs and 96.3% of the false pairs. The authors call exhaustive size-5 search infeasible even after an estimated 240-fold symmetry reduction. [ETP §5.1](https://arxiv.org/html/2512.07087#S5.SS1)

This strongly supports the claim as a description of the **underlying research campaign**. It does not establish the behavior of current private Stage 2 solvers.

## Why the search spaces become large

### Finite countermodel search

A binary operation on a labeled `n`-element carrier is an `n × n` table. Every one of its `n²` cells has `n` choices, hence:

`number of labeled magmas = n^(n²)`.

| Carrier size `n` | Tables |
|---:|---:|
| 2 | 16 |
| 3 | 19,683 |
| 4 | 4,294,967,296 |
| 5 | 298,023,223,876,953,125 |
| 6 | 10,314,424,798,490,535,546,171,949,056 |

The ETP’s formal blueprint gives the same formula and sequence [Basic theory of magmas](https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html).

For a law with `v` variables, a candidate table has `n^v` assignments to check. A naive implication scan therefore costs approximately

`n^(n²) × (|E₁| n^v₁ + |E₂| n^v₂)`

term-node evaluations at one carrier size. Early rejection, symmetry breaking, SAT encodings, constraint propagation, and structured families can reduce real work enormously, but not the raw worst-case. The local implementations exhibit the `product(range(n), repeat=v)` assignment loop directly, for example in [M00006](../EQT02-M00006.py) and [`generalized`](../examples/solo/demos/generalized/solver.py).

Finite search is also intrinsically one-sided for this task. A found table certifies `E₁ ⇏ E₂`; failure through a chosen size or family proves only that no witness was found there. Unrestricted and finite entailment differ in general, so some false unrestricted implications have no finite countermodel at all. [ETP mathematical foundations](https://arxiv.org/html/2512.07087#S1.SS1)

The large space is not merely an asymptotic warning. The ETP reports a Mace4 case where exhausting size 10 took 2.5 minutes and size 11 exceeded seven hours. Adding a mathematically derived invariant reduced size 11 below one second; an unhelpful additional condition made performance worse. [ETP Example 7.1](https://arxiv.org/html/2512.07087#S7.SS3.SSS8)

### Equational proof search

Birkhoff completeness gives a positive semi-decision procedure: `E₁ ⇒ E₂` holds exactly when the two sides of `E₂` are connected by a finite sequence of substitutions and rewrites using `E₁`. However, deciding arbitrary equational implication is undecidable. [ETP §1.1](https://arxiv.org/html/2512.07087#S1.SS1)

Even the term vocabulary grows rapidly. With `v` variables, the number of binary terms containing exactly `k` operation nodes is

`Catalan(k) × v^(k+1)`.

The ETP blueprint proves this count [Free-magma word count](https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html). For four variables it is 172,032 terms at `k = 5` and 70,447,529,984 at `k = 10`. A rewrite search then multiplies this vocabulary by rewrite positions, two orientations, and possible substitutions. Deduplication and bidirectional search help but do not remove the combinatorial growth.

The source bounds confirm that this is a practical concern rather than speculative complexity:

- M00006 caps basic, absorption, and general closure depths at 2, 3, and 4 [source](../EQT02-M00006.py);
- opnorm/twophase cap their bidirectional subexpression search at 120,000 visited states and 30 seconds [opnorm](../examples/solo/demos/opnorm/solver.py);
- eulerv5 scales its cap with time but limits it to 500,000 states [source](../examples/solo/demos/eulerv5/solver.py);
- `generalized` caps rewrite expansion at 30,000 nodes, depth 5, term size 21, a term pool of 32, and at most 96 completions per missing-variable pattern [source](../examples/solo/demos/generalized/solver.py).

These bounds make the implementations terminating and budget-aware, but also incomplete.

## LLM versus search is a false dichotomy

An LLM can generate a whole certificate, but leading neural theorem provers usually use the model **inside a search algorithm**:

- ReProver retrieves premises, has an LLM propose tactics from each proof state, checks them in Lean, and combines them with best-first search. [LeanDojo/ReProver paper](https://arxiv.org/abs/2306.15626)
- DeepSeek-Prover-V1.5 combines an LLM with proof-assistant feedback and RMaxTS, a Monte Carlo tree-search variant. Its reported gains come with budgets ranging from 128 whole-proof samples to thousands of search samples per problem. [DeepSeek-Prover-V1.5 paper](https://arxiv.org/abs/2408.08152)

Therefore an LLM does not automatically eliminate search; it can serve as a learned policy that ranks tactics, terms, premises, invariants, or countermodel families. Conversely, a small number of remote API calls can hide substantial inference compute, while a local neural prover may generate thousands of short candidates without making any remote API call. “Number of LLM calls” and “amount of LLM compute” are different metrics.

For this competition, the promising design axis is **unguided versus well-guided search**, not search versus LLM. The ETP’s own data show why: proof/model parameters can change runtimes by orders of magnitude, and a derived invariant cut one model-exhaustion run from over seven hours to under one second. LLMs could be useful for choosing a direction, proposing intermediate lemmas or invariants, ranking solver configurations, and selecting structured model families, while the deterministic engine constructs and the Lean judge checks the final certificate.

## What remains unverified

The following would be needed to turn the architectural conclusion into a competition-wide empirical claim:

- source or telemetry from a representative set of submitted solvers;
- per-problem LLM calls, prompt/output tokens, model latency, and estimated inference compute;
- deterministic states/tables/assignments explored and peak memory;
- accepted score split by zero-LLM, LLM-assisted, and post-LLM mechanical routes;
- matched-budget ablations of the same solver with LLM guidance enabled and disabled;
- stratification by true/false label, equation order, and public versus held-back distribution.

Until those data exist, “most competition solvers do not use a lot of LLMs” should be reported as a plausible observation, not a verified population statistic.

## Primary sources

- Matthew Bolan et al., [*The Equational Theories Project: Advancing Collaborative Mathematical Research at Scale*](https://arxiv.org/abs/2512.07087), 2025.
- Equational Theories Project, [*Basic theory of magmas*](https://teorth.github.io/equational_theories/blueprint/basic-theory-chapter.html), formal blueprint.
- Ralph McKenzie, [*On spectra, and the negative solution of the decision problem for identities having a finite nontrivial model*](https://doi.org/10.2307/2271899), 1975.
- William McCune, [*Mace4 Reference Manual and Guide*](https://arxiv.org/abs/cs/0310055), 2003.
- Kaiyu Yang et al., [*LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*](https://arxiv.org/abs/2306.15626), 2023.
- Huajian Xin et al., [*DeepSeek-Prover-V1.5: Harnessing Proof Assistant Feedback for Reinforcement Learning and Monte-Carlo Tree Search*](https://arxiv.org/abs/2408.08152), 2024.
