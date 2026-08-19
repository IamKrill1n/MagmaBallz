#!/usr/bin/env python3
"""Frontier Forge P2: pair generation + sieve -> frontier_v1.jsonl.

Deterministic. Uses the P1 signature bank to (a) discard pairs the bank
already refutes (those become free FALSE labels), then (b) runs the current
solver portfolio on the survivors; whatever nobody solves is the frontier.

Outputs (in .scratch/frontier-forge/):
  labeled_v1.jsonl   bank-separated pairs: instant FALSE + witness name
  frontier_v1.jsonl  pairs the whole deterministic portfolio fails
Provenance fields on every row.
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[1]
BANK = HERE / "bank"

spec = importlib.util.spec_from_file_location("m6", REPO / "EQT02-M00006.py")
m6 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m6)

HYP_COUNT = 120          # hypothesis laws to draw
TGT_PER_HYP = 12         # candidate targets per hypothesis
SOLVER_BUDGET = 12.0     # false_time_budget per pair (saturation adds its own)
PAIR_TEST_CAP = 700      # max survivors run through the solver
MAX_SIG_POP = 6          # "sparse spectrum" hypothesis filter (popcount of 1s)


def main() -> None:
    feats = {}
    for line in open(BANK / "features.jsonl"):
        r = json.loads(line)
        if "error" not in r:
            feats[r["law"]] = r
    sigs = {}
    for line in open(BANK / "signatures.jsonl"):
        r = json.loads(line)
        if r["sig"]:
            sigs[r["law"]] = r["sig"]
    models = json.load(open(BANK / "models.json"))
    print(f"{len(feats)} laws, {len(sigs)} signatures, {len(models)} models", flush=True)

    # hypothesis pool: 3-var laws with sparse known spectra (eq168-shaped)
    def singleton_forcing(f) -> bool:
        # a bare-variable side whose variable is absent from the other side
        # forces |S| = 1 (every implication trivially TRUE) — not frontier
        eq = m6.parse_equation(f["text"])
        for a, b in ((eq["lhs"], eq["rhs"]), (eq["rhs"], eq["lhs"])):
            if a[0] == "var" and str(a[1]) not in m6.term_vars(b):
                return True
        return False

    hyp_pool = sorted(
        law for law, f in feats.items()
        if f["vars"] == 3 and law in sigs
        and 0 < sigs[law].count("1") <= MAX_SIG_POP
        and not singleton_forcing(f)
    )
    hyps = hyp_pool[:: max(1, len(hyp_pool) // HYP_COUNT)][:HYP_COUNT]
    print(f"hypothesis pool {len(hyp_pool)}, drawn {len(hyps)}", flush=True)

    # target pool: any law with a signature, 2-4 vars
    tgt_pool = sorted(law for law, f in feats.items()
                      if 2 <= f["vars"] <= 4 and law in sigs)

    labeled = open(HERE / "labeled_v1.jsonl", "w")
    candidates: list[tuple[int, int]] = []
    for hi, h in enumerate(hyps):
        sh = sigs[h]
        hbits = [k for k, c in enumerate(sh) if c == "1"]
        # bank-inseparable targets BY CONSTRUCTION: every model satisfying the
        # hypothesis also satisfies the target (random targets are separated
        # ~100% of the time for sparse hypotheses — measured, v1 found zero)
        compatible = [t for t in tgt_pool if t != h
                      and all(sigs[t][k] != "0" for k in hbits)]
        # deterministic spread over the compatible set
        step = max(1, len(compatible) // TGT_PER_HYP)
        chosen = compatible[(hi % max(1, step))::step][:TGT_PER_HYP]
        candidates.extend((h, t) for t in chosen)
        # keep a small sample of separated pairs as free FALSE labels
        for off in range(6):
            t = tgt_pool[(hi * 7919 + off * 104729) % len(tgt_pool)]
            if t == h:
                continue
            st = sigs[t]
            sep = next((k for k in hbits if st[k] == "0"), None)
            if sep is not None:
                labeled.write(json.dumps({
                    "eq1_law": h, "eq2_law": t,
                    "equation1": feats[h]["text"], "equation2": feats[t]["text"],
                    "answer": False, "witness_model": models[sep]["name"],
                    "provenance": "bank_separated",
                }) + "\n")
    labeled.close()
    print(f"bank-inseparable candidates: {len(candidates)}", flush=True)

    frontier = open(HERE / "frontier_v1.jsonl", "w")
    solved_ctr = frontier_ctr = 0
    t0 = time.time()
    for n, (h, t) in enumerate(candidates[:PAIR_TEST_CAP], 1):
        problem = {
            "id": f"forge_{h}_{t}",
            "eq1_id": 100000 + h, "eq2_id": 100000 + t,  # out-of-band ids
            "equation1": feats[h]["text"], "equation2": feats[t]["text"],
        }
        try:
            res = m6.solve_problem(problem, false_time_budget=SOLVER_BUDGET)
        except Exception as exc:  # noqa: BLE001 — a crash must not kill the sieve
            res = None
            print(f"  solver error on {problem['id']}: {exc!r}", flush=True)
        if res is not None:
            solved_ctr += 1
        else:
            frontier_ctr += 1
            frontier.write(json.dumps({
                "id": problem["id"],
                "eq1_law": h, "eq2_law": t,
                "equation1": problem["equation1"],
                "equation2": problem["equation2"],
                "provenance": "sieve_v1: 3var sparse-spectrum hyp, bank-inseparable, portfolio-unsolved",
            }) + "\n")
            frontier.flush()
        if n % 50 == 0:
            print(f"{n}/{min(len(candidates), PAIR_TEST_CAP)} "
                  f"solved={solved_ctr} frontier={frontier_ctr} "
                  f"({(time.time()-t0)/n:.1f}s/pair)", flush=True)
    frontier.close()
    print(f"DONE: solved={solved_ctr} frontier={frontier_ctr} "
          f"in {(time.time()-t0)/60:.0f} min", flush=True)


if __name__ == "__main__":
    main()
