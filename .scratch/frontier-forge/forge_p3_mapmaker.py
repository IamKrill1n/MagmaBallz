#!/usr/bin/env python3
"""Frontier Forge P3: the Mapmaker's construction generators.

Three factories, all seeded and deterministic:
  G-TRUE   derivation walks: apply the hypothesis k times from a seed term;
           the walked chain IS the (vaulted) proof. Modes: plain, mountain
           (intermediates forced to grow well beyond both endpoints).
  G-FALSE  monster-first: find a fresh model of a sparse-spectrum hypothesis
           by backtracking search (not in any bank), pick a target law the
           monster breaks, vault the monster.
  Tags     every problem records generator + mode + seed (bet-breaker tags).

Problems (questions only) -> .scratch/frontier-forge/generated_v1.jsonl
Vaulted answers           -> <scratchpad>/vault/answers_v1.jsonl  (OUTSIDE repo)
Hardness is NOT asserted here: the sieve must still certify every problem
against the current champion build at full budget.
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import random
import sys
import time
from itertools import product

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[1]
# Durable and OUTSIDE the repo: answers must survive reboots but never be
# pushed to the shared remote where miners (or rivals) could read them.
VAULT_DIR = pathlib.Path.home() / "dev/active/MagmaBallz-vault"
VAULT_DIR.mkdir(parents=True, exist_ok=True)

spec = importlib.util.spec_from_file_location("m6", REPO / "EQT02-M00006.py")
m6 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m6)

SEED = 20260819
N_WALK_PLAIN = 40
N_WALK_MOUNTAIN = 40
N_MONSTER = 40
WALK_STEPS = (6, 14)          # steps range (beyond every solver's chain depth)
MOUNTAIN_PEAK_FACTOR = 2.5    # peak must exceed factor * max(endpoint sizes)


def canon_problem(h_text: str, lhs, rhs) -> dict | None:
    goal = f"{m6.term_to_lean(lhs)} = {m6.term_to_lean(rhs)}".replace("◇", "*")
    try:
        eq2 = m6.parse_equation(goal)
    except ValueError:
        return None
    if eq2["lhs"] == eq2["rhs"]:
        return None
    return {"equation1": h_text, "equation2": goal}


def derivation_walk(eq1, rng, mountain: bool):
    """Walk k rewrite steps from a seed term; return (start, end, chain, peak)."""
    variables = eq1["variables"]
    seed_var = ("var", variables[0])
    pool = [("var", v) for v in variables]
    pool += [("op", a, b) for a in pool for b in pool][:6]
    current = rng.choice(pool[2:] or pool)
    chain = [current]
    steps = rng.randint(*WALK_STEPS)
    peak = m6.term_size(current)
    for step_idx in range(steps):
        options = m6.rewrite_steps_from_term(eq1, current)
        if not options:
            options = m6.filled_absorption_steps(
                eq1, current, pool, max_size=60, max_depth=12, max_fills=40)
        if not options:
            break
        if mountain:
            half = steps // 2
            key = (lambda o: m6.term_size(o[0])) if step_idx < half else (
                lambda o: -m6.term_size(o[0]))
            options = sorted(options, key=key, reverse=True)
            pick = options[rng.randrange(min(3, len(options)))]
        else:
            pick = options[rng.randrange(len(options))]
        current = pick[0]
        chain.append(current)
        peak = max(peak, m6.term_size(current))
    return chain[0], current, chain, peak


def gen_walks(laws, rng, n, mountain):
    out = []
    tag = "walk_mountain" if mountain else "walk_plain"
    attempts = 0
    while len(out) < n and attempts < n * 60:
        attempts += 1
        law_id, text = laws[rng.randrange(len(laws))]
        try:
            eq1 = m6.parse_equation(text)
        except ValueError:
            continue
        start, end, chain, peak = derivation_walk(eq1, rng, mountain)
        if len(chain) < 5 or start == end:
            continue
        endpoints = max(m6.term_size(start), m6.term_size(end))
        if mountain and peak < MOUNTAIN_PEAK_FACTOR * endpoints:
            continue
        prob = canon_problem(text, start, end)
        if prob is None:
            continue
        pid = f"forge3_{tag}_{law_id}_{attempts}"
        out.append({
            "id": pid, "eq1_law": law_id, "answer_hint": None,
            "provenance": f"{tag}:steps={len(chain)-1}:peak={peak}:seed={SEED}",
            **prob,
        })
        VAULT.write(json.dumps({
            "id": pid, "verdict": "true",
            "chain": [m6.term_to_lean(t) for t in chain],
        }) + "\n")
    return out


def gen_monsters(laws, rng, n):
    """Fresh model of a sparse hypothesis via existence-backtracking; pick a
    target the monster breaks and the bank cannot separate."""
    out = []
    sigs = {}
    for line in open(HERE / "bank" / "signatures.jsonl"):
        r = json.loads(line)
        if r["sig"]:
            sigs[r["law"]] = r["sig"]
    feats = {}
    for line in open(HERE / "bank" / "features.jsonl"):
        r = json.loads(line)
        if "error" not in r:
            feats[r["law"]] = r
    sparse = [(i, feats[i]["text"]) for i in feats
              if i in sigs and feats[i]["vars"] <= 4
              and 0 < sigs[i].count("1") <= 8]
    attempts = 0
    while len(out) < n and attempts < n * 40:
        attempts += 1
        law_id, text = sparse[rng.randrange(len(sparse))]
        try:
            eq1 = m6.parse_equation(text)
        except ValueError:
            continue
        # existence search: model of H at n=5/6 (goal check disabled by using
        # an unsatisfiable "counterexample" target: x = x never falsifiable,
        # so we call the raw DFS via a trivially-true eq2 and accept eq1-models)
        found = None
        for size in (5, 6):
            r = m6.backtracking_countermodel(
                eq1, m6.parse_equation("x = y"), sizes=(size,))
            if r:
                found = r
                break
        if not found:
            continue
        n_size, table = found
        # pick a target the monster refutes and the bank cannot
        hbits = [k for k, c in enumerate(sigs[law_id]) if c == "1"]
        cands = [t for t in sigs
                 if t != law_id and feats[t]["vars"] <= 4
                 and all(sigs[t][k] != "0" for k in hbits)]
        rng.shuffle(cands)
        for target in cands[:300]:
            eq2 = m6.parse_equation(feats[target]["text"])
            if m6.table_is_counterexample(eq1, eq2, table):
                pid = f"forge3_monster_{law_id}_{target}"
                out.append({
                    "id": pid, "eq1_law": law_id, "eq2_law": target,
                    "equation1": text, "equation2": feats[target]["text"],
                    "provenance": f"monster:n={n_size}:seed={SEED}",
                })
                VAULT.write(json.dumps({
                    "id": pid, "verdict": "false", "table": table,
                }) + "\n")
                break
    return out


def main():
    rng = random.Random(SEED)
    laws = []
    for idx, line in enumerate(open(REPO / "examples/problems/eq_size5.txt"), 1):
        text = line.strip()
        if text and idx % 13 == 0:      # deterministic thinning
            laws.append((idx, text))
    global VAULT
    VAULT = open(VAULT_DIR / "answers_v1.jsonl", "w")
    t0 = time.time()
    problems = []
    problems += gen_walks(laws, rng, N_WALK_PLAIN, mountain=False)
    print(f"walk_plain: {len(problems)}", flush=True)
    n0 = len(problems)
    problems += gen_walks(laws, rng, N_WALK_MOUNTAIN, mountain=True)
    print(f"walk_mountain: {len(problems)-n0}", flush=True)
    n0 = len(problems)
    problems += gen_monsters(laws, rng, N_MONSTER)
    print(f"monsters: {len(problems)-n0}", flush=True)
    VAULT.close()
    with open(HERE / "generated_v1.jsonl", "w") as f:
        for p in problems:
            f.write(json.dumps(p) + "\n")
    print(f"TOTAL {len(problems)} constructed problems in "
          f"{(time.time()-t0)/60:.1f} min; answers vaulted outside repo",
          flush=True)


if __name__ == "__main__":
    main()
