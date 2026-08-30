# Marathon hard/order-5 100-problem benchmark

Date: 2026-08-30

## Executive summary

`solverV3.py` wins the larger benchmark with **95/100 accepted in 124.1
seconds**. The strongest demo, `EQT02-M00010.py`, scores **93/100 in 142.6
seconds**. V3 therefore gains two accepted problems, loses none, and uses 18.5
seconds less solver wall time (13.0% faster).

V3 accepts every normal, hard, and extra-hard problem. Its five misses are all
true order-5 implications. It finds all 50 false counterexamples and proves 45
of the 50 true implications.

## Benchmark definition

The locked profile is
[`benchmarks/marathon_hard100.json`](../benchmarks/marathon_hard100.json), and
the solver-visible manifest is
[`benchmarks/marathon_hard_order5_100_v1.jsonl`](../benchmarks/marathon_hard_order5_100_v1.jsonl).

| Tier | Problems | Share |
| --- | ---: | ---: |
| Normal | 10 | 10% |
| Hard | 30 | 30% |
| Extra-hard | 25 | 25% |
| Order-5 | 35 | 35% |
| **Total** | **100** | **100%** |

Hard, extra-hard, and order-5 problems comprise 90% of the benchmark. Selection
uses seed `20260830`, exact per-tier true/false quotas, and alternating hidden
source labels after sampling. The source labels are removed from every
solver-visible row. The final source-label balance is exactly 50 false and 50
true.

Each solver receives the same global budget:

- Wall time: 300 seconds.
- LLM tokens: 0.
- Scoring: accepted certificates; lower solver wall time breaks score ties.
- Solver wall time excludes the later Lean scoring pass.

This is an offline deterministic comparison. It evaluates native search,
problem ordering, certificate construction, and budget behavior; it does not
measure token-enabled LLM recovery.

## Overall results

| Rank | Solver | Accepted | Attempted | False accepted | True accepted | Solver wall |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 1 | `solverV3.py` | **95/100** | 95 | **50/50** | **45/50** | **124.1 s** |
| 2 | `EQT02-M00010.py` | 93/100 | 93 | 50/50 | 43/50 | 142.6 s |
| 3 | `solverV2.py` | 93/100 | 93 | 50/50 | 43/50 | 144.2 s |
| 4 | `EQT02-M00009.py` | 29/100 | 29 | 29/50 | 0/50 | 34.5 s |
| 5 | `solverV1.py` | 21/100 | 21 | 0/50 | 21/50 | 285.7 s |
| 6–9 | baseline, triage, few-shot, M00005 | 0/100 | 0 | 0/50 | 0/50 | 0.5 s each |

V2 is byte-identical to M00010 and acts as a reproducibility control. Their
1.6-second wall difference is ordinary single-run variance; their accepted
sets and route counts are identical.

## Results by difficulty

| Solver | Normal | Hard | Extra-hard | Order-5 |
| --- | ---: | ---: | ---: | ---: |
| `solverV3.py` | **10/10** | **30/30** | **25/25** | **30/35** |
| `EQT02-M00010.py` | 10/10 | 29/30 | 25/25 | 29/35 |
| `solverV2.py` | 10/10 | 29/30 | 25/25 | 29/35 |
| `EQT02-M00009.py` | 5/10 | 9/30 | 0/25 | 15/35 |
| `solverV1.py` | 5/10 | 13/30 | 1/25 | 2/35 |
| baseline, triage, few-shot, M00005 | 0/10 | 0/30 | 0/25 | 0/35 |

## V3 versus the strongest demo

V3 accepts two true implications that M00010 and V2 leave unattempted:

| Problem | Tier | Source label | Equation IDs |
| --- | --- | --- | --- |
| `evaluation_hard_0162` | Hard | True | 743 → 2903 |
| `evaluation_order5_0160` | Order-5 | True | 8408 → 29872 |

V3 loses no M00010 acceptance. Its aggregate route log contains one additional
`true:derived_cp_closure` success and one additional `true:egg_collapse`
success. This supports the intended optimization: after cheap counterexample
search, V3 tries bounded equational closure before expensive constraint search
for non-absorption hypotheses. On the 100-problem set, that change improves
both coverage and wall time.

V3's remaining misses are:

| Problem | Tier | Source label | Equation IDs |
| --- | --- | --- | --- |
| `evaluation_order5_0004` | Order-5 | True | 13760 → 37949 |
| `evaluation_order5_0132` | Order-5 | True | 33275 → 34497 |
| `evaluation_order5_0038` | Order-5 | True | 12029 → 23162 |
| `evaluation_order5_0074` | Order-5 | True | 35948 → 31587 |
| `evaluation_order5_0084` | Order-5 | True | 39993 → 31590 |

## Interpretation

- Order-5 true implications are the remaining bottleneck. V3 is perfect on
  the other 65 problems and on every false problem.
- M00009 and V1 have complementary failure profiles: M00009 accepts only false
  cases, while V1 accepts only true cases. M00009's inexpensive countermodel
  layer is productive; V1's repeated local Lean validation is too costly under
  the compressed global budget.
- Baseline, triage, and few-shot parse `◇` but the evaluation corpus uses `*`,
  so they emit no answers on this manifest. M00005 uses the Solo stdin/stdout
  protocol rather than Marathon manifest/output files. Their zero scores are
  compatibility results, not evidence that their intended LLM strategies have
  no value.
- Because this profile has zero LLM tokens, token-enabled ranking, few-shot
  transfer, and repair behavior remain unevaluated.

## Reproduction

```bash
python3 -m pipeline.marathon_benchmark \
  --profile benchmarks/marathon_hard100.json \
  --candidate solverV1=my_submission/marathon/solverV1.py \
  --candidate solverV2=my_submission/marathon/solverV2.py \
  --candidate solverV3=my_submission/marathon/solverV3.py
```

Raw results for this run are under
`pipeline/results/marathon_hard100/20260830_122346/`. The aggregate summary,
per-solver summaries, answers, and logs are retained there locally; the
`pipeline/results/` tree is intentionally gitignored.

Validation performed before the run:

- 100 unique solver-visible IDs.
- Expected tier counts: 10/30/25/35.
- Exactly 50 false and 50 true source labels, alternating in manifest order.
- No solver-visible `answer` fields.
- Benchmark provenance and balance unit tests passed.
