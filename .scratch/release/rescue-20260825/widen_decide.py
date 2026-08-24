"""Hai câu hỏi quyết định chuyện nới bậc affine:
   1. 5 bài kia HIỆN GIỜ solver có giải được không? (nếu có -> nới được 0)
   2. Chứng chỉ FALSE ở bậc 27..43 judge Lean có nhận không?"""
import importlib.util, json, os, pathlib, sys, time
REPO="/Users/nhatminh/dev/active/MagmaBallz"
sys.path.insert(0,REPO)
spec=importlib.util.spec_from_file_location("m6",REPO+"/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)
from judge.verify import verify_answer
probs={}
for f in pathlib.Path(REPO+"/examples/problems").glob("*.jsonl"):
    for l in f.open():
        q=json.loads(l); probs[q["id"]]=q
SPD="/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad"
g=json.load(open(SPD+"/widen_gain.json"))

print("=== CÂU 1: 5 bài này solver hiện có giải được không? ===", flush=True)
now={}
for pid in sorted(g):
    q=probs[pid]; t0=time.time()
    try:
        r=m6.solve_problem({"id":pid,"eq1_id":1,"eq2_id":2,
            "equation1":q["equation1"],"equation2":q["equation2"]},
            false_time_budget=120)
    except Exception as exc:
        r=None; print("   lỗi",exc, flush=True)
    now[pid]=str(r.get("route")) if r else None
    print(f"  {pid:<24} {'GIẢI ĐƯỢC: '+now[pid] if now[pid] else 'KHÔNG GIẢI ĐƯỢC'}"
          f"   {time.time()-t0:.0f}s", flush=True)
chua = [p for p,v in now.items() if not v]
print(f"\n  -> nới bậc chỉ đáng giá nếu số này > 0: {len(chua)} bài chưa giải được: {chua}", flush=True)

print("\n=== CÂU 2: judge Lean có nhận chứng chỉ bậc 27..43 không? ===", flush=True)
for pid,(n,a,b,c) in sorted(g.items()):
    e1=m6.parse_equation(probs[pid]["equation1"].replace("◇","*"))
    e2=m6.parse_equation(probs[pid]["equation2"].replace("◇","*"))
    v=max(len(e1["variables"]),len(e2["variables"]))
    if n**v > 5_000_000:
        print(f"  {pid:<24} bậc {n}: BỎ QUA — {n**v:,} phép, Lean không kham nổi", flush=True)
        continue
    table=[[(a*x+b*y+c)%n for y in range(n)] for x in range(n)]
    try:
        code=m6.false_certificate(n,table)
    except Exception as exc:
        print(f"  {pid:<24} bậc {n}: sinh cert LỖI {exc}", flush=True); continue
    sạch=m6.sanitize_lean_code(code, verdict="false")
    ans=json.dumps({"answer":"false","lean_code":code})
    t0=time.time()
    try:
        res=verify_answer(probs[pid], ans)
        st=res.get("status")
    except Exception as exc:
        st=f"lỗi hạ tầng: {exc}"
    print(f"  {pid:<24} bậc {n} ({v} biến, {n**v:,} phép, cert {len(code):,} byte): "
          f"{st}   sạch={sạch}   {time.time()-t0:.0f}s", flush=True)
