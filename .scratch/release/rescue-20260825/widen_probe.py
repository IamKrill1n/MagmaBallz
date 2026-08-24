import importlib.util, json, pathlib, sys, time
sys.path.insert(0,"/Users/nhatminh/dev/active/MagmaBallz")
spec=importlib.util.spec_from_file_location("m6","/Users/nhatminh/dev/active/MagmaBallz/EQT02-M00006.py")
m6=importlib.util.module_from_spec(spec); spec.loader.exec_module(m6)
probs={}
for f in pathlib.Path("/Users/nhatminh/dev/active/MagmaBallz/examples/problems").glob("*.jsonl"):
    for l in f.open():
        q=json.loads(l); probs[q["id"]]=q
WIDE=(27,29,31,32,37,41,43,47,49,53,59,61,64)
gain={}
t0=time.time()
for pid,q in sorted(probs.items()):
    try:
        a=m6.parse_equation(q["equation1"].replace("◇","*")); b=m6.parse_equation(q["equation2"].replace("◇","*"))
    except Exception: continue
    if m6.extended_affine_scan(a,b): continue      # bậc <=25 đã ăn
    for n in WIDE:
        hit=None
        for aa in range(n):
            for bb in range(n):
                for c in (0,1):
                    if m6._affine_holds(a,aa,bb,c,n) and not m6._affine_holds(b,aa,bb,c,n):
                        hit=(n,aa,bb,c); break
                if hit: break
            if hit: break
        if hit:
            gain[pid]=hit; break
print(f"quét {len(probs)} bài trong {time.time()-t0:.0f}s")
print(f"SỐ BÀI MỚI mà bậc 27..64 phá được (bậc <=25 bó tay): {len(gain)}")
for pid,h in sorted(gain.items())[:40]:
    print(f"  {pid:<24} bậc {h[0]}  a={h[1]} b={h[2]} c={h[3]}   nhãn={probs[pid].get('answer')}")
json.dump({k:list(v) for k,v in gain.items()}, open("/private/tmp/claude-501/-Users-nhatminh-dev-active-MagmaBallz/5aa77320-10be-4643-8ecb-555c1ad24f06/scratchpad/widen_gain.json","w"))
