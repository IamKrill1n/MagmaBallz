#!/usr/bin/env python3
"""Frontier Forge P1: law features + signature bank over eq_size5.txt.

Deterministic, checkpointed, resumable. Output:
  .scratch/frontier-forge/bank/features.jsonl   one row per law
  .scratch/frontier-forge/bank/signatures.jsonl one bitstring per law
  .scratch/frontier-forge/bank/models.json      the model bank (provenance)

Bank policy: all 16 order-2 tables, structured families n<=5, natural central
groupoids 4/9, CG9 plus every distinct non-natural order-9 CG from the A^2=J
search, and a few order-7 family samples. Laws with >4 variables are evaluated
only against models of order <= 4 (cost control; recorded in the row).
"""
from __future__ import annotations

import importlib.util
import itertools
import json
import pathlib
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[1]
BANK = HERE / "bank"
BANK.mkdir(exist_ok=True)

spec = importlib.util.spec_from_file_location("m6", REPO / "EQT02-M00006.py")
m6 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m6)


def natural_cg(k: int) -> list[list[int]]:
    n = k * k
    t = [[0] * n for _ in range(n)]
    for a, b, c, d in itertools.product(range(k), repeat=4):
        t[k * a + b][k * c + d] = k * b + c
    return t


def nonnatural_cg9(limit: int = 40) -> list[list[list[int]]]:
    """All (up to `limit`) order-9 central groupoids via the A^2=J search."""
    eq168 = m6.parse_equation("x = (y * x) * (x * z)")
    n = 9
    weight3 = [frozenset(c) for c in itertools.combinations(range(n), 3)]
    found: list[list[list[int]]] = []

    def op_from_rows(rows):
        t = [[0] * n for _ in range(n)]
        for x in range(n):
            for y in range(n):
                zs = [z for z in rows[x] if y in rows[z]]
                if len(zs) != 1:
                    return None
                t[x][y] = zs[0]
        return t

    def search(rows):
        if len(found) >= limit:
            return
        i = len(rows)
        if i == n:
            t = op_from_rows(rows)
            if t and m6.equation_holds(eq168, t):
                found.append(t)
            return
        for cand in weight3:
            newrows = rows + [cand]
            ok = True
            for x in range(i + 1):
                for y in range(n):
                    c2 = sum(1 for z in newrows[x] if z <= i and y in newrows[z])
                    if c2 > 1:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                search(newrows)
                if len(found) >= limit:
                    return
    search([])
    return found


def build_bank() -> list[dict]:
    models: list[dict] = []

    def add(name: str, table):
        models.append({"name": name, "n": len(table), "table": table})

    for idx, cells in enumerate(itertools.product(range(2), repeat=4)):
        add(f"n2_{idx:02d}", [[cells[0], cells[1]], [cells[2], cells[3]]])
    seen = {json.dumps(mdl["table"]) for mdl in models}
    for route, table in m6.structured_family_tables(max_n=5):
        key = json.dumps(table)
        if key not in seen:
            seen.add(key)
            add(f"fam:{route}", table)
    for route, table in m6.structured_family_tables(max_n=7):
        if len(table) in (6, 7):
            key = json.dumps(table)
            if key not in seen and len([x for x in models if x["n"] >= 6]) < 24:
                seen.add(key)
                add(f"fam7:{route}", table)
    add("naturalCG4", natural_cg(2))
    add("naturalCG9", natural_cg(3))
    for i, t in enumerate(nonnatural_cg9()):
        key = json.dumps(t)
        if key not in seen:
            seen.add(key)
            add(f"CG9_{i:02d}", t)
    return models


def law_features(eq) -> dict:
    lhs, rhs = eq["lhs"], eq["rhs"]
    return {
        "vars": len(eq["variables"]),
        "ops": (m6.term_size(lhs) - 1) // 2 + (m6.term_size(rhs) - 1) // 2,
        "lhs_is_var": lhs[0] == "var",
        "one_sided": sorted(
            (m6.term_vars(lhs) | m6.term_vars(rhs))
            - (m6.term_vars(lhs) & m6.term_vars(rhs))
        ),
    }


def main() -> None:
    models = build_bank()
    json.dump(models, open(BANK / "models.json", "w"))
    print(f"bank: {len(models)} models "
          f"(orders {sorted(set(mdl['n'] for mdl in models))})", flush=True)
    parsed_models = [(mdl["name"], mdl["n"], mdl["table"]) for mdl in models]

    done = 0
    start_at = 0
    sig_path = BANK / "signatures.jsonl"
    feat_path = BANK / "features.jsonl"
    if sig_path.exists():  # resume
        start_at = sum(1 for _ in open(sig_path))
        print(f"resuming at law {start_at}", flush=True)
    sig_f = open(sig_path, "a")
    feat_f = open(feat_path, "a")

    t0 = time.time()
    for idx, line in enumerate(open(REPO / "examples/problems/eq_size5.txt"), 1):
        if idx <= start_at:
            continue
        text = line.strip()
        try:
            eq = m6.parse_equation(text)
        except ValueError:
            sig_f.write(json.dumps({"law": idx, "sig": None}) + "\n")
            feat_f.write(json.dumps({"law": idx, "error": "parse"}) + "\n")
            continue
        feats = law_features(eq)
        max_order = 4 if feats["vars"] > 4 else 9
        bits = []
        for _name, n, table in parsed_models:
            if n > max_order:
                bits.append("x")  # not evaluated
            else:
                bits.append("1" if m6.equation_holds(eq, table) else "0")
        sig_f.write(json.dumps({"law": idx, "sig": "".join(bits)}) + "\n")
        feat_f.write(json.dumps({"law": idx, "text": text, **feats}) + "\n")
        done += 1
        if done % 2000 == 0:
            sig_f.flush(); feat_f.flush()
            rate = done / (time.time() - t0)
            eta = (62576 - idx) / rate / 3600
            print(f"{idx}/62576  ({rate:.0f} laws/s, eta {eta:.1f}h)", flush=True)
    sig_f.close(); feat_f.close()
    print(f"DONE {done} laws in {(time.time()-t0)/60:.0f} min", flush=True)


if __name__ == "__main__":
    main()
