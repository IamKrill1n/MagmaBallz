# Lightweight hard SOLO benchmark

`benchmarks/solo_hard_100.json` defines the deterministic development benchmark
for `my_submission/solver.py` and its strategy variants.

- 100 cases: 25 each from `hard1`, `hard2`, `hard3`, and order-5.
- 47 TRUE and 53 FALSE labels. Labels are stripped before solver startup.
- The fixed selection favors previously fast cases but retains the two residual
  failures from the prior 130-case hard run. This keeps iteration short without
  turning the suite into a smoke test.
- Eight workers and a 300-second per-case safety cap.
- Accuracy is correct judge-accepted verdicts divided by all 100 cases.
- This is a public development benchmark, not a held-out generalization claim.

Run the primary solver:

```bash
python3 -m pipeline.solo_benchmark --profile benchmarks/solo_hard_100.json
```

Run one single-file strategy variant:

```bash
python3 -m pipeline.solo_benchmark \
  --profile benchmarks/solo_hard_100.json \
  --submission my_submission/solo_variants/true_cache.py
```

Results are fingerprinted and resumable under
`pipeline/results/solo_hard_100/`.
