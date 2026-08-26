"""Thử lõi KB trên bài order-5 trượt + hồi quy bài đã giải."""
import importlib.util, json, sys, time, glob
REPO = "/Users/nhatminh/dev/active/MagmaBallz"
spec = importlib.util.spec_from_file_location("s", REPO + "/EQT02-M00006.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
sys.path.insert(0, REPO + "/.scratch/kb")
import kb_core as kb

probs = {}
for p in glob.glob(REPO + "/examples/problems/*.jsonl"):
    for l in open(p, encoding="utf-8"):
        r = json.loads(l); probs[r["id"]] = r

secs = float(sys.argv[1])
for pid in sys.argv[2:]:
    r = probs[pid]
    e1 = m.parse_equation(r["equation1"]); e2 = m.parse_equation(r["equation2"])
    t0 = time.time()
    res = kb.complete(e1["lhs"], e1["rhs"], e2["lhs"], e2["rhs"],
                      deadline=time.monotonic() + secs)
    print("{:26s} nhan={:5s} proved={} how={} stop={} R={} E={} cap={} {:.0f}s".format(
        pid, str(r.get("answer")), res["proved"], res.get("how"), res["stop"],
        len(res["rules"]), len(res.get("eqs", [])), res["stats"]["pairs"],
        time.time() - t0), flush=True)
