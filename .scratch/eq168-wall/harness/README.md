# Measurement harness

`scoreboard.py` — head-to-head Solo solver comparison. Calls
`pipeline.proxy.run_solver` directly; **nothing in `pipeline/` is modified**,
which is why this lives under `.scratch/` rather than `scripts/`. Promoting it
to `scripts/` would be a framework change and needs the `CONTRIBUTING.md`
issue-first process.

What it adds over `pipeline.runner` / `scripts/submit.py`, which are built for
driving one submission rather than comparing several:

- parallel workers (`--workers`; Lean+Mathlib is memory-hungry, 3 is safe on 16 GB)
- per-run budget override (`--timeout`), instead of editing `pipeline/config.json`
- deterministic label-stratified sampling (`--sample`) — see the warning below
- `--no-llm`, which strips the API key so the proxy's LLM path errors and each
  solver falls through to its deterministic routes: the oracle-disabled axis,
  free to run
- multi-solver x multi-corpus fan-out with per-case JSONL and an aggregate table

## Layout

```
.scratch/eq168-wall/
  subs/<name>/solver.py     # stage each solver here (not committed)
  corpora/<name>.jsonl      # corpora not in examples/problems/ (not committed)
  results/<tag>.jsonl       # one row per judged case
  harness/
```

Corpora resolve from `examples/problems/` first, then `corpora/`. The
`evaluation_*` sets live on `prototype/gpt5.6sol`, not on `main`.

## Usage

```bash
source .env.judge

python3 .scratch/eq168-wall/harness/scoreboard.py \
    --solvers reja23,generalized --corpora evaluation_extra_hard \
    --sample 20 --timeout 120 --workers 3 --no-llm --tag myrun

python3 .scratch/eq168-wall/harness/analyze.py results/myrun.jsonl
```

Omit `--no-llm` to bill the configured provider (`pipeline/config.json` defaults
to OpenRouter). Omit `--sample` to run the whole corpus.

## Sampling: why stratified

The `evaluation_*` corpora alternate labels strictly `F,T,F,T,...`. A plain
evenly-spread stride of 200/20 = 10 aliases against that period and returns 20
FALSE cases and zero TRUE ones — which silently reports ~100% accuracy, since
FALSE is much the easier half. `sample()` splits by label first and is immune to
any such ordering. Do not replace it with a naive stride.
