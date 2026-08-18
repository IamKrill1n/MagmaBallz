import json, collections, pathlib, sys
BASE = pathlib.Path(__file__).resolve().parent.parent
p = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else BASE / "results/nollm.jsonl"
rows = [json.loads(l) for l in p.read_text().splitlines() if l.strip()]
sols = sorted({r["solver"] for r in rows})
corps = sorted({r["corpus"] for r in rows})
print(f"n={len(rows)}\n")

st = collections.Counter()
for r in rows:
    for s in r["judge_statuses"]:
        st[(r["solver"], s)] += 1
keys = sorted({k[1] for k in st})
print("judge statuses by solver:")
print(f"{'solver':<14}" + "".join(f"{k:>17}" for k in keys))
for s in sols:
    print(f"{s:<14}" + "".join(f"{st.get((s, k), 0):>17}" for k in keys))

print("\naccepted, by solver x expected label:")
acc = collections.Counter(); tot = collections.Counter()
for r in rows:
    lab = "TRUE" if r["expected"] else "FALSE"
    tot[(r["solver"], lab)] += 1
    if r["solved"]:
        acc[(r["solver"], lab)] += 1
print(f"{'solver':<14}{'TRUE':>12}{'FALSE':>12}{'total':>12}")
for s in sols:
    a = acc[(s, "TRUE")], tot[(s, "TRUE")], acc[(s, "FALSE")], tot[(s, "FALSE")]
    print(f"{s:<14}{f'{a[0]}/{a[1]}':>12}{f'{a[2]}/{a[3]}':>12}"
          f"{f'{a[0] + a[2]}/{a[1] + a[3]}':>12}")

print("\naccepted, by solver x corpus:")
print(f"{'solver':<14}" + "".join(f"{c.replace('evaluation_', ''):>16}" for c in corps))
for s in sols:
    cells = []
    for c in corps:
        sub = [r for r in rows if r["solver"] == s and r["corpus"] == c]
        cells.append(f"{sum(r['solved'] for r in sub)}/{len(sub)}")
    print(f"{s:<14}" + "".join(f"{x:>16}" for x in cells))
