# Spec: the Equation 168 wall in Solo solver coverage

Status: ready-for-human

## Context

Four solver lineages existed with no end-to-end score recorded anywhere in the
repo. A measurement sweep on 2026-08-18 judged 492 cases across five solvers to
establish a baseline and find where coverage is actually lost.

The answer is concentrated to an unusual degree. On the full
`evaluation_extra_hard` corpus the strongest solver takes **161/161** of every
problem that does *not* use Equation 168 as its hypothesis, and **8/39** of the
ones that do. The entire residual — all 31 unsolved cases — is Equation 168,
and all 31 are FALSE-labelled.

Equation 168 is `x = (y ◇ x) ◇ (x ◇ z)`. It is the hypothesis in 74 of the 800
problems (9.3%) across the four `evaluation_*` corpora, every instance FALSE,
concentrated in the hard tiers (39 `extra_hard`, 33 `hard`, 2 `normal`).

Nothing in `pipeline/`, `judge/` or `scripts/` was modified. The harness used to
produce these numbers calls `pipeline.proxy.run_solver` from outside the
framework and lives in `harness/` here; promoting it to `scripts/` would be a
framework change and should follow the `CONTRIBUTING.md` issue-first process
first.

## Issues

- `issues/01-eq168-countermodel-wall.md` — the coverage wall itself, with the 31
  unsolved case IDs as a ready regression set.
- `issues/02-unvalidated-countermodel-submissions.md` — solvers submitting
  countermodels the judge disproves, when a local pre-check would suppress them.

## Reproducing

```bash
source .env.judge

# stage solvers as submission dirs first: .scratch/eq168-wall/subs/<name>/solver.py
python3 .scratch/eq168-wall/harness/scoreboard.py \
    --solvers reja23 --corpora evaluation_extra_hard \
    --timeout 120 --workers 3 --no-llm --tag xh_full

python3 .scratch/eq168-wall/harness/analyze.py results/xh_full.jsonl
```

`--no-llm` strips the API key from the harness environment, so the proxy's LLM
path returns an error and each solver falls through to its deterministic routes.
That measures the reasoning engine alone — the oracle-disabled axis `CONTEXT.md`
is built around — and costs nothing to run.

Raw per-case results for every run are in `results/`. Sampling is deterministic
and label-stratified, so a rerun reproduces the same case selection.
