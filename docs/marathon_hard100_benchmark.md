# Marathon extra-hard/order-5 100-problem benchmark

Date: 2026-09-01

## Executive summary

`solverV4.py` (solverV3 + the standard-aux superposition phase ported from the
structural-cache SOLO solver) scores **98/100 accepted in 109.1 seconds**, with
zero incorrect submissions. Its accepted set is a strict superset of
`solverV3.py`, which scores **91/100 in 145.2 seconds** in the same batch.

V4 accepts every extra-hard problem and 78/80 order-5 problems: 50/50 false and
48/50 true. Its only two misses (`evaluation_order5_0006`,
`evaluation_order5_0124`) are the two problems every solver in this repository
has ever failed. This matches the ceiling predicted in the previous benchmark
run (90 + 8 complementary wins = 98), now achieved by a single solver.

## Benchmark definition

The locked profile is
[`benchmarks/marathon_hard100.json`](../benchmarks/marathon_hard100.json), and
the solver-visible manifest is
[`benchmarks/marathon_hard_order5_100_v2.jsonl`](../benchmarks/marathon_hard_order5_100_v2.jsonl).

| Tier | Problems | Share |
| --- | ---: | ---: |
| Extra-hard | 20 | 20% |
| Order-5 | 80 | 80% |
| **Total** | **100** | **100%** |

The benchmark is intentionally the hardest slice of the track: every problem is
either extra-hard or order-5, with order-5 dominating. Selection uses seed
`20260901`, exact per-tier true/false quotas (10/10 extra-hard, 40/40 order-5),
and alternating hidden source labels after sampling. The source labels are
removed from every solver-visible row. The final source-label balance is exactly
50 false and 50 true. The manifest is generated deterministically by
[`scripts/generate_marathon_manifest.py`](../scripts/generate_marathon_manifest.py);
a provenance unit test pins the manifest to the generator.

Each solver receives the same global budget:

- Wall time: 300 seconds.
- LLM tokens: 0.
- Scoring: accepted certificates; lower solver wall time breaks score ties.
- Solver wall time excludes the later Lean scoring pass.

This is an offline deterministic comparison. It evaluates native search,
problem ordering, certificate construction, and budget behavior; it does not
measure token-enabled LLM recovery.

## Overall results

Same-batch head-to-head (run `20260901_101158`):

| Rank | Solver | Accepted | Attempted | False accepted | True accepted | Solver wall |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | `solverV4.py` | **98/100** | 98 | **50/50** | **48/50** | **109.1 s** |
| 2 | `solverV3.py` | 91/100 | 91 | **50/50** | 41/50 | 145.2 s |

V4 is a strict superset of V3's accepted set: V3-only wins = 0, V4-only wins =
7. Neither solver submitted any incorrect or malformed certificate; every miss
is a row whose budget expired before a certificate was produced.

Reference runs from earlier batches (same manifest, single-run variance):

| Solver | Accepted | False accepted | True accepted | Solver wall |
| --- | ---: | ---: | ---: | ---: |
| `structural_cache_marathon.py` | 90/100 (best) | 43/50 | 47/50 | 296.6 s |
| `solverV3.py` | 89–91/100 across runs | 50/50 | 39–41/50 | 145–147 s |

## Results by difficulty

| Solver | Extra-hard | Order-5 |
| --- | ---: | ---: |
| `solverV4.py` | **20/20** | **78/80** |
| `solverV3.py` | **20/20** | 71/80 |

## What changed in V4

`solverV4.py` = `solverV3.py` + one new engine: the
`standard_aux_superposition` phase ported from
`my_submission/solo_variants/structural_cache.py` (the phase behind every
structural-cache-exclusive win in the previous benchmark run). It derives a
standard auxiliary law — `const` (`a = b`), `proj_l` (`a ◇ b = a`),
`proj_r` (`a ◇ b = b`), or `rowconst` (`a ◇ b = a ◇ c`) — from the hypothesis
via bounded proof-carrying superposition, then consumes the lemma to close the
goal. The port runs early in `solve_problem_pass` (before counterexample
search, mirroring structural_cache's phase order) with a 3-second budget.

Two adaptations were required beyond the mechanical port:

1. **Judge-free soundness.** structural_cache verifies every candidate body
   against the Lean judge before submitting; solverV4 has no local judge in
   marathon mode. The port's grind-based consumer
   (`grounded_assumption_grind_body`) can build tails that fail Lean, so it
   was removed — V4 only submits proof-carrying superposition bodies (the
   direct and secondary-bridge consumers). Without this, the phase submitted
   3 incorrect certificates on false order-5 problems.
2. **Size cap.** The 1,300-line ported closure plus solverV3 exceeds the
   512,000-byte single-file limit, so the closure is zlib+base85-encoded and
   exec'd at load time (the same trick structural_cache uses for its caches).

V4's route log shows 14 `true:standard_aux_superposition` wins (more than the
8 exclusive wins of the port, because it also wins problems V3 handled via
slower routes). The seven V4-only acceptances over V3's best run:

| Problem | Tier | Source label | Equation IDs |
| --- | --- | --- | --- |
| `evaluation_order5_0016` | Order-5 | True | 10278 → 17625 |
| `evaluation_order5_0052` | Order-5 | True | 20769 → 5525 |
| `evaluation_order5_0058` | Order-5 | True | 31335 → 38127 |
| `evaluation_order5_0074` | Order-5 | True | 35948 → 31587 |
| `evaluation_order5_0084` | Order-5 | True | 39993 → 31590 |
| `evaluation_order5_0126` | Order-5 | True | 39983 → 24070 |
| `evaluation_order5_0138` | Order-5 | True | 11963 → 15157 |

(These are exactly the port's exclusive wins minus `evaluation_order5_0182`,
which V3 also wins in some runs.)

## Remaining misses

Only two problems defeat V4 — the same two that defeat every other solver in
this repository:

| Problem | Tier | Source label | Equation IDs |
| --- | --- | --- | --- |
| `evaluation_order5_0006` | Order-5 | True | 26506 → 20227 |
| `evaluation_order5_0124` | Order-5 | True | 21548 → 16976 |

## Interpretation

- **The port pays off immediately.** The single additive phase converts the
  benchmark's hardest slice from 90/100 to 98/100 while reducing wall time
  (109.1 s vs 145.2 s): the early true-side check closes order-5 true
  implications in milliseconds instead of letting them fall into expensive
  constraint search.
- **Soundness required one cut.** The grind-based consumer was the only
  non-proof-carrying path in the phase; removing it (and the local judge
  loop that had masked it in structural_cache) restored the phase to the
  same soundness standard as V3's other routes.
- **V4 is the strongest solver in the repository** on the hardest slice, with
  headroom: 109.1 s of a 300 s budget.
- Because this profile has zero LLM tokens, token-enabled LLM recovery remains
  unevaluated.

## Reproduction

```bash
python3 -m pipeline.marathon_benchmark \
  --profile benchmarks/marathon_hard100.json \
  --candidate solverV3=my_submission/marathon/solverV3.py \
  --candidate solverV4=my_submission/marathon/solverV4.py \
  --only solverV3 --only solverV4
```

The manifest is regenerated deterministically with:

```bash
python3 scripts/generate_marathon_manifest.py \
  --profile benchmarks/marathon_hard100.json
```

Raw results for the head-to-head run are under
`pipeline/results/marathon_hard100/20260901_101158/`. The aggregate summary,
per-solver summaries, answers, and logs are retained there locally; the
`pipeline/results/` tree is intentionally gitignored.

Validation performed before the run:

- 100 unique solver-visible IDs.
- Expected tier counts: 20 extra-hard / 80 order-5.
- Exactly 50 false and 50 true source labels, alternating in manifest order.
- No solver-visible `answer` fields.
- Manifest provenance and generator unit tests passed (including a test that
  the committed manifest is byte-identical to fresh generator output).