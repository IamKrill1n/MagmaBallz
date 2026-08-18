#!/usr/bin/env python3
"""Head-to-head scoreboard for Solo solvers.

Lives outside the repo on purpose: `pipeline/` is organizer-owned and
issue-first, so this only *calls* it (proxy.run_solver) and never edits it.

Adds what pipeline.runner lacks for comparison work: parallelism, a
per-run timeout override, corpus sampling, and an --no-llm mode that
strips the API key from the environment so the proxy's LLM path returns
an error. --no-llm is the "reasoning engine only" axis from CONTEXT.md —
and it is free.

Usage:
  scoreboard.py --solvers generalized,suii0x --corpora hard1 \
      --sample 20 --timeout 300 --no-llm --workers 4
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent          # .scratch/eq168-wall/tools
BASE = HERE.parent                              # .scratch/eq168-wall
REPO = BASE.parents[1]                          # repo root
SUBS = BASE / "subs"                            # one dir per solver, each with solver.py
OUT = BASE / "results"

sys.path.insert(0, str(REPO))
from pipeline.proxy import load_config, load_problems, run_solver  # noqa: E402

# Corpora resolve from examples/problems/ first; anything not on this branch
# (the evaluation_* sets live on prototype/gpt5.6sol) can be dropped here.
CORPUS_DIR = BASE / "corpora"


def resolve_corpus(name: str) -> Path:
    local = REPO / "examples" / "problems" / f"{name}.jsonl"
    if local.exists():
        return local
    staged = CORPUS_DIR / f"{name}.jsonl"
    if staged.exists():
        return staged
    raise SystemExit(f"corpus not found: {name}")


def sample(problems: list[dict], n: int | None) -> list[dict]:
    """Deterministic label-stratified subset — no RNG, so runs are reproducible.

    Stratifying is not a nicety here. The evaluation_* corpora alternate
    strictly F,T,F,T,..., so a plain evenly-spread stride of 200/20 = 10
    aliases against that period and returns 20 FALSE cases and no TRUE
    ones. Splitting by label first makes the sample immune to any such
    ordering, and TRUE/FALSE are each half the score.
    """
    if n is None or n >= len(problems):
        return problems

    def spread(items: list[dict], k: int) -> list[dict]:
        if k <= 0 or not items:
            return []
        k = min(k, len(items))
        stride = len(items) / k
        return [items[int(i * stride)] for i in range(k)]

    true_side = [p for p in problems if p.get("answer") is True]
    false_side = [p for p in problems if p.get("answer") is False]
    if not true_side or not false_side:  # unlabeled corpus — fall back
        stride = len(problems) / n
        return [problems[int(i * stride)] for i in range(n)]

    picked = spread(true_side, n // 2) + spread(false_side, n - n // 2)
    order = {id(p): i for i, p in enumerate(problems)}
    return sorted(picked, key=lambda p: order[id(p)])


def run_one(sub: str, problem: dict, config: dict) -> dict:
    t0 = time.time()
    try:
        result = run_solver(SUBS / sub, problem, config)
    except Exception as exc:  # a crashed solver must not kill the sweep
        result = {"solved": False, "verdict": None, "llm_calls": 0,
                  "judge_calls": 0, "log": [{"type": "error", "message": repr(exc)}]}
    # Judge entries nest the verdict under "response" (pipeline/proxy.py:1003).
    statuses = []
    for entry in result.get("log", []):
        if entry.get("type") != "judge":
            continue
        response = entry.get("response") or {}
        statuses.append(str(response.get("status")
                            or response.get("error_code")
                            or response.get("error", "?")))
    return {
        "solver": sub,
        "id": problem["id"],
        "expected": problem.get("answer"),
        "solved": bool(result.get("solved")),
        "verdict": result.get("verdict"),
        "judge_statuses": statuses,
        "llm_calls": result.get("llm_calls", 0),
        "judge_calls": result.get("judge_calls", 0),
        "elapsed": round(time.time() - t0, 1),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--solvers", required=True)
    ap.add_argument("--corpora", required=True)
    ap.add_argument("--sample", type=int, default=None)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--no-llm", action="store_true")
    ap.add_argument("--tag", default="run")
    args = ap.parse_args()

    if args.no_llm:
        # The proxy reads these at call time from *this* process's env.
        for key in ("OPENAI_API_KEY", "OPENROUTER_API_KEY"):
            os.environ.pop(key, None)

    config = load_config(None)
    config["solver"]["timeout_seconds"] = args.timeout

    solvers = args.solvers.split(",")
    corpora = args.corpora.split(",")
    OUT.mkdir(parents=True, exist_ok=True)

    jobs = []
    for corpus in corpora:
        problems = sample(load_problems(str(resolve_corpus(corpus))), args.sample)
        for sub in solvers:
            for problem in problems:
                jobs.append((corpus, sub, problem))

    print(f"scoreboard: {len(jobs)} cases "
          f"({len(solvers)} solvers x {len(corpora)} corpora), "
          f"timeout={args.timeout}s workers={args.workers} "
          f"llm={'OFF' if args.no_llm else 'ON'}", flush=True)

    rows: list[dict] = []
    done = 0
    out_path = OUT / f"{args.tag}.jsonl"
    with out_path.open("w") as fh, ThreadPoolExecutor(args.workers) as pool:
        futures = {pool.submit(run_one, sub, problem, config): (corpus, sub, problem)
                   for corpus, sub, problem in jobs}
        for fut in as_completed(futures):
            corpus, sub, problem = futures[fut]
            row = fut.result()
            row["corpus"] = corpus
            rows.append(row)
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            done += 1
            mark = "OK " if row["solved"] else "-- "
            print(f"[{done}/{len(jobs)}] {mark}{sub:<12} {row['id']:<26} "
                  f"{str(row['verdict']):<6} {row['elapsed']:>6}s "
                  f"judge={row['judge_calls']} {','.join(filter(None, row['judge_statuses']))[:60]}",
                  flush=True)

    print(f"\n{'=' * 72}\nSCOREBOARD  ({out_path})\n{'=' * 72}")
    print(f"{'solver':<14}{'corpus':<20}{'accepted':>10}{'n':>6}{'med s':>8}")
    for sub in solvers:
        for corpus in corpora:
            cell = [r for r in rows if r["solver"] == sub and r["corpus"] == corpus]
            if not cell:
                continue
            times = sorted(r["elapsed"] for r in cell)
            print(f"{sub:<14}{corpus:<20}"
                  f"{sum(r['solved'] for r in cell):>10}{len(cell):>6}"
                  f"{times[len(times) // 2]:>8.0f}")


if __name__ == "__main__":
    main()
