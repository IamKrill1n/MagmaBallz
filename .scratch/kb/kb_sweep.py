"""Quét KB trên nhiều bài: đo phủ TRUE và kiểm AN TOÀN (không được 'chứng minh' bài FALSE)."""
import importlib.util, json, sys, time, glob, collections
REPO = "/Users/nhatminh/dev/active/MagmaBallz"
spec = importlib.util.spec_from_file_location("s", REPO + "/EQT02-M00006.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
sys.path.insert(0, REPO + "/.scratch/kb")
import kb_core as kb

secs = float(sys.argv[1]); corpora = sys.argv[2:]
rows = []
for c in corpora:
    for l in open(f"{REPO}/examples/problems/{c}.jsonl", encoding="utf-8"):
        rows.append((c, json.loads(l)))
stat = collections.Counter(); bad = []
t0 = time.time()
for c, r in rows:
    e1 = m.parse_equation(r["equation1"]); e2 = m.parse_equation(r["equation2"])
    res = kb.complete(e1["lhs"], e1["rhs"], e2["lhs"], e2["rhs"],
                      deadline=time.monotonic() + secs)
    lab = r.get("answer")
    if res["proved"]:
        stat[f"{c}:proved:{res['how']}"] += 1
        if lab is False:
            bad.append((r["id"], res["how"]))       # NGUY HIỂM: chứng minh bài SAI
    else:
        stat[f"{c}:no:{res['stop']}"] += 1
for k in sorted(stat): print(f"  {k:44s} {stat[k]}")
print(f"CẢNH BÁO chứng minh bài FALSE: {len(bad)} {bad[:5]}")
print(f"{len(rows)} bài, {time.time()-t0:.0f}s")
