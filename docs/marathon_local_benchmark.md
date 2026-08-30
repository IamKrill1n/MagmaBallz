# Local Marathon benchmark

The locked development profile is [`benchmarks/marathon.json`](../benchmarks/marathon.json):

- 24 public evaluation problems: six each from normal, hard, extra-hard,
  and order-5.
- Source positions 1, 2, 67, 68, 133, and 134 give three true/false pairs
  spread across each 200-problem source file.
- The manifest is round-robin interleaved by difficulty so manifest-order
  solvers do not receive one entire easy tier first.
- `answer` is removed from every solver-visible row.
- Every solver gets the same 180-second wall budget and zero LLM tokens.
  This is a deterministic, no-cost iteration gate, not the official Marathon
  budget. Token-enabled evaluations still use `scripts/run_marathon.py`.

Run every solver under `examples/marathon/demos`:

```bash
python3 -m pipeline.marathon_benchmark
```

Add a versioned candidate, or select only named solvers:

```bash
python3 -m pipeline.marathon_benchmark \
  --candidate solverV1=my_submission/marathon/solverV1.py

python3 -m pipeline.marathon_benchmark \
  --candidate solverV1=my_submission/marathon/solverV1.py \
  --only EQT02-M00010 --only solverV1
```

`--dry-run` validates the manifest and prints discovery without launching
solvers. Results, logs, answers, per-tier scores, and the aggregate scoreboard
are written under ignored `pipeline/results/marathon_local/`.

## Current result

The initial all-demo run is stored locally at
`pipeline/results/marathon_local/20260830_080522/`. The winning comparison is
at `pipeline/results/marathon_local/20260830_081324/`.

| Solver | Accepted | Solver wall time |
| --- | ---: | ---: |
| `my_submission/marathon/solverV3.py` | 24/24 | 1.5 s |
| `EQT02-M00010.py` | 24/24 | 13.5 s |
| `EQT02-M00009.py` | 7/24 | 8.5 s |
| `my_submission/marathon/solverV1.py` | 6/24 | 165.6 s |
| baseline, triage, few-shot, M00005 | 0/24 | 0.5 s each |

V2 adopted the strongest deterministic base and tied M00010 at 24/24 in
13.5 seconds. Profiling V2 showed four constraint-countermodel calls consuming
12 seconds before equational closure solved the same rows. V3 keeps cheap
counterexample witnesses first, but runs bounded equational closure before the
expensive constraint search for non-absorption hypotheses. That generic
cost-band change preserved all 24 answers and reduced solver wall time by 12
seconds.
