# Local SOLO benchmark

The canonical local SOLO benchmark is defined by
[`benchmarks/solo.json`](../benchmarks/solo.json) and executed with:

```bash
python3 -m pipeline.solo_benchmark
```

This is a local regression benchmark, not the official competition budget.

## Locked profile

- Submission: `examples/solo/demos/generalized/solver.py` (zero LLM).
- Inputs: every `.json` and `.jsonl` recursively under `examples/problems/`,
  excluding `examples/problems/marathon/`.
- Duplicate policy: run entries once per source file. Thus the 20 entries shared
  by `sample_20.json` and `normal.jsonl` are intentionally run twice.
- Timeout: 120 seconds per normal problem; 300 seconds when either the source
  path or `difficulty` contains `hard` or `order5`.
- Labels: retained only for offline scoring and stripped before the solver is
  started.
- Execution: eight concurrent workers (one per physical core on the reference
  local machine); one fresh solver process per problem.
- Resume: completed rows are reused only when the solver, profile, pipeline
  config, and every problem file have the same combined fingerprint.
- Raw outputs: `pipeline/results/solo_local/` (gitignored). Each run records its
  manifest, per-source JSONL rows, and aggregate `summary.json`.

Use `python3 -m pipeline.solo_benchmark --dry-run` to inspect selection and tier
counts without running solvers. `--workers N` changes concurrency only, not any
per-problem budget.

## Current run

Pending completion.
